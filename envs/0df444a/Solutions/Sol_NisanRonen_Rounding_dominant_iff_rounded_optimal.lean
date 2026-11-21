-- Prove2me | solution 1 for NisanRonen.Rounding.dominant_iff_rounded_optimal
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T20:23:02.718183+00:00
-- url     : https://prove2.me/submissions/8d9c8357-2a09-4000-8abe-f5f5675326d3

import Mathlib
import Definitions.Def_NisanRonen_Rounding_IsDominant
import Definitions.Def_NisanRonen_Rounding_IsExactRoundedSolver

namespace Aux_NisanRonen_Rounding_dominant_iff_rounded_optimal

open NisanRonen.Rounding

lemma roundUp_mono {δ u v : ℝ} (hδ : 0 < δ) (h : u ≤ v) : roundUp δ u ≤ roundUp δ v := by
  unfold roundUp
  apply mul_le_mul_of_nonneg_left _ hδ.le
  exact_mod_cast Int.ceil_mono (div_le_div_of_nonneg_right h hδ.le)

lemma rm_mono {n k : ℕ} [NeZero n] {δ : ℝ} (hδ : 0 < δ) (x : Fin k → Fin n)
    (τ τ' : Fin k → ℝ) (h : ∀ j, τ j ≤ τ' j) :
    roundedMakespan δ x τ ≤ roundedMakespan δ x τ' := by
  unfold roundedMakespan NisanRonen.Rounding.makespan
  apply Finset.sup'_le
  intro m _
  have hm : m ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ m
  refine le_trans ?_ (Finset.le_sup' (f := load x (fun j => roundUp δ (τ' j))) hm)
  unfold load
  exact Finset.sum_le_sum (fun j _ => roundUp_mono hδ (h j))

lemma utility_eq {n k : ℕ} [NeZero n] (f : List (Fin n → ℕ) → List (Fin n)) (δ : ℝ)
    (s : Fin n → Strategy n k) (i : Fin n) :
    utility f δ s i = -roundedMakespan δ (allocOf f δ (fun l => (s l).decl))
      (corr i (allocOf f δ (fun l => (s l).decl)) (fun l => (s l).decl)
        (actualTimes f δ s)) := by
  simp only [utility]
  ring

/-- Utility of an arbitrary strategy, with the executed times read off the strategy. -/
lemma utility_sigma {n k : ℕ} [NeZero n] (f : List (Fin n → ℕ) → List (Fin n)) (δ : ℝ)
    (s : Fin n → Strategy n k) (i : Fin n) (σ : Strategy n k) :
    utility f δ (Function.update s i σ) i =
      -roundedMakespan δ (allocOf f δ (fun l => (Function.update s i σ l).decl))
        (corr i (allocOf f δ (fun l => (Function.update s i σ l).decl))
          (fun l => (Function.update s i σ l).decl)
          (σ.exec (allocOf f δ (fun l => (Function.update s i σ l).decl)))) := by
  rw [utility_eq]
  have hc : corr i (allocOf f δ (fun l => (Function.update s i σ l).decl))
      (fun l => (Function.update s i σ l).decl) (actualTimes f δ (Function.update s i σ)) =
      corr i (allocOf f δ (fun l => (Function.update s i σ l).decl))
          (fun l => (Function.update s i σ l).decl)
          (σ.exec (allocOf f δ (fun l => (Function.update s i σ l).decl))) := by
    funext j
    simp only [corr, actualTimes]
    by_cases hj : allocOf f δ (fun l => (Function.update s i σ l).decl) j = i
    · rw [if_pos hj, if_pos hj, hj, Function.update_self]
    · rw [if_neg hj, if_neg hj]
  rw [hc]

lemma decl_update_eq {n k : ℕ} (s : Fin n → Strategy n k) (i : Fin n) (σ : Strategy n k)
    (ti : Fin k → ℝ) :
    Function.update (fun l => (Function.update s i σ l).decl) i ti =
      Function.update (fun l => (s l).decl) i ti := by
  funext l
  by_cases h : l = i
  · rw [h]; simp only [Function.update_self]
  · simp only [Function.update_of_ne h]

/-- Utility of the truthful strategy. -/
lemma utility_truth {n k : ℕ} [NeZero n] (f : List (Fin n → ℕ) → List (Fin n)) (δ : ℝ)
    (s : Fin n → Strategy n k) (i : Fin n) (ti : Fin k → ℝ) :
    utility f δ (Function.update s i (⟨ti, fun _ => ti⟩ : Strategy n k)) i =
      -roundedMakespan δ (allocOf f δ (Function.update (fun l => (s l).decl) i ti))
        (corrStar (allocOf f δ (Function.update (fun l => (s l).decl) i ti))
          (Function.update (fun l => (s l).decl) i ti)) := by
  rw [utility_sigma]
  have hD : (fun l => (Function.update s i (⟨ti, fun _ => ti⟩ : Strategy n k) l).decl) =
      Function.update (fun l => (s l).decl) i ti := by
    funext l
    by_cases h : l = i
    · rw [h]; simp only [Function.update_self] <;> rfl
    · simp only [Function.update_of_ne h]
  rw [hD]
  have hc : corr i (allocOf f δ (Function.update (fun l => (s l).decl) i ti))
      (Function.update (fun l => (s l).decl) i ti)
      ((⟨ti, fun _ => ti⟩ : Strategy n k).exec
        (allocOf f δ (Function.update (fun l => (s l).decl) i ti))) =
      corrStar (allocOf f δ (Function.update (fun l => (s l).decl) i ti))
        (Function.update (fun l => (s l).decl) i ti) := by
    funext j
    simp only [corr, corrStar]
    by_cases hj : allocOf f δ (Function.update (fun l => (s l).decl) i ti) j = i
    · rw [if_pos hj, hj, Function.update_self]
    · rw [if_neg hj]
  rw [hc]

/-- Any valid deviation is bounded by the truthful rounded make-span at its allocation. -/
lemma utility_dev {n k : ℕ} [NeZero n] {a b δ : ℝ} (hδ : 0 < δ)
    (f : List (Fin n → ℕ) → List (Fin n)) (s : Fin n → Strategy n k) (i : Fin n)
    (ti : Fin k → ℝ) (σ' : Strategy n k) (hσ' : IsValid a b ti i σ') :
    utility f δ (Function.update s i σ') i ≤
      -roundedMakespan δ (allocOf f δ (fun l => (Function.update s i σ' l).decl))
        (corrStar (allocOf f δ (fun l => (Function.update s i σ' l).decl))
          (Function.update (fun l => (s l).decl) i ti)) := by
  rw [utility_sigma]
  obtain ⟨Y, hY⟩ : ∃ Y, Y = allocOf f δ (fun l => (Function.update s i σ' l).decl) :=
    ⟨_, rfl⟩
  rw [← hY]
  have hge : ∀ j, corrStar Y (Function.update (fun l => (s l).decl) i ti) j ≤
      corr i Y (fun l => (Function.update s i σ' l).decl) (σ'.exec Y) j := by
    intro j
    simp only [corr, corrStar]
    by_cases hj : Y j = i
    · rw [if_pos hj, hj, Function.update_self]
      exact hσ'.2 Y j hj
    · rw [if_neg hj]; simp only [Function.update_of_ne hj, le_refl]
  have := rm_mono hδ Y _ _ hge
  linarith

end Aux_NisanRonen_Rounding_dominant_iff_rounded_optimal

open NisanRonen.Rounding Aux_NisanRonen_Rounding_dominant_iff_rounded_optimal in
theorem solution {n k : ℕ} [NeZero n] {a b δ : ℝ} (ha : 0 < a) (hab : a < b)
    (hδ : 0 < δ) (f : List (Fin n → ℕ) → List (Fin n)) (hf : IsExactRoundedSolver f δ a b)
    (t : Fin n → Fin k → ℝ) (ht : ∀ i j, a ≤ t i j ∧ t i j ≤ b) (i : Fin n) (σ : Strategy n k)
    (hσ : IsValid a b (t i) i σ) :
    IsDominant f δ a b i (t i) σ ↔
      ∀ s : Fin n → Strategy n k,
        (∀ l, l ≠ i → ∀ j, a ≤ (s l).decl j ∧ (s l).decl j ≤ b) →
        let d : Fin n → Fin k → ℝ := fun l => (Function.update s i σ l).decl
        let x := allocOf f δ d
        ∀ y : Fin k → Fin n,
          roundedMakespan δ x (corr i x d (σ.exec x)) ≤
            roundedMakespan δ y (corrStar y (Function.update d i (t i))) := by
  have Dbox : ∀ s : Fin n → Strategy n k,
      (∀ l, l ≠ i → ∀ j, a ≤ (s l).decl j ∧ (s l).decl j ≤ b) →
      ∀ l j, a ≤ Function.update (fun l => (s l).decl) i (t i) l j ∧
        Function.update (fun l => (s l).decl) i (t i) l j ≤ b := by
    intro s hs l j
    by_cases h : l = i
    · rw [h, Function.update_self]; exact ht i j
    · rw [Function.update_of_ne h]; exact hs l h j
  constructor
  · rintro ⟨_, hdom⟩ s hs
    dsimp only
    intro y
    have h1 := hdom s hs ⟨t i, fun _ => t i⟩ ⟨fun j => ht i j, fun x j _ => le_rfl⟩
    rw [utility_truth, utility_sigma] at h1
    have h2 := (hf k _ (Dbox s hs)).2 y
    rw [decl_update_eq]
    linarith
  · intro h
    refine ⟨hσ, ?_⟩
    intro s hs σ' hσ'
    have h1 := utility_dev hδ f s i (t i) σ' hσ'
    have h2 := h s hs (allocOf f δ (fun l => (Function.update s i σ' l).decl))
    rw [decl_update_eq] at h2
    rw [utility_sigma f δ s i σ]
    linarith
