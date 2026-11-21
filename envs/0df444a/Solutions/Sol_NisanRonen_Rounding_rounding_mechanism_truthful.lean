-- Prove2me | solution 1 for NisanRonen.Rounding.rounding_mechanism_truthful
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T20:16:12.332184+00:00
-- url     : https://prove2.me/submissions/555df03e-da29-4c39-be9f-52f57958e828

import Mathlib
import Definitions.Def_NisanRonen_Rounding_IsDominant
import Definitions.Def_NisanRonen_Rounding_truthStrategy
import Definitions.Def_NisanRonen_Rounding_IsExactRoundedSolver

namespace Aux_NisanRonen_Rounding_rounding_mechanism_truthful

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

end Aux_NisanRonen_Rounding_rounding_mechanism_truthful

open NisanRonen.Rounding Aux_NisanRonen_Rounding_rounding_mechanism_truthful in
theorem solution {n k : ℕ} [NeZero n] {a b δ : ℝ} (ha : 0 < a) (hab : a < b)
    (hδ : 0 < δ) (f : List (Fin n → ℕ) → List (Fin n)) (hf : IsExactRoundedSolver f δ a b)
    (t : Fin n → Fin k → ℝ) (ht : ∀ i j, a ≤ t i j ∧ t i j ≤ b) :
    ∀ i : Fin n, IsDominant f δ a b i (t i) (truthStrategy (t i)) := by
  intro i
  refine ⟨⟨fun j => ht i j, fun x j _ => le_rfl⟩, ?_⟩
  intro s hs σ' hσ'
  obtain ⟨D, hD⟩ : ∃ D : Fin n → Fin k → ℝ,
      D = fun l => if l = i then t i else (s l).decl := ⟨_, rfl⟩
  have hDi : D i = t i := by rw [hD]; simp
  have hDl : ∀ l, l ≠ i → D l = (s l).decl := by
    intro l h; rw [hD]; simp [h]
  have hDbox : ∀ l j, a ≤ D l j ∧ D l j ≤ b := by
    intro l j
    by_cases h : l = i
    · rw [h, hDi]; exact ht i j
    · rw [hDl l h]; exact hs l h j
  have hdeclT : (fun l => (Function.update s i (truthStrategy (t i)) l).decl) = D := by
    funext l
    by_cases h : l = i
    · rw [h, hDi]; simp [truthStrategy]
    · rw [hDl l h, Function.update_of_ne h]
  have hdecl' : ∀ l, l ≠ i → (Function.update s i σ' l).decl = D l := by
    intro l h
    rw [hDl l h, Function.update_of_ne h]
  rw [utility_eq, utility_eq, hdeclT]
  -- truthful side
  obtain ⟨X, hX⟩ : ∃ X, X = allocOf f δ D := ⟨_, rfl⟩
  have hcorrT : corr i (allocOf f δ D) D (actualTimes f δ (Function.update s i (truthStrategy (t i))))
      = corrStar X D := by
    funext j
    simp only [corr, corrStar, actualTimes]
    rw [hdeclT, ← hX]
    by_cases hj : X j = i
    · rw [if_pos hj, hj, Function.update_self]
      simp [hDi, truthStrategy]
    · rw [if_neg hj]
  rw [hcorrT, ← hX]
  -- deviating side
  obtain ⟨d'', hd''⟩ : ∃ d'' : Fin n → Fin k → ℝ,
      d'' = fun l => (Function.update s i σ' l).decl := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = allocOf f δ d'' := ⟨_, rfl⟩
  have hge : ∀ j, corrStar Y D j ≤ corr i Y d'' (actualTimes f δ (Function.update s i σ')) j := by
    intro j
    simp only [corr, corrStar, actualTimes]
    rw [← hd'', ← hY]
    by_cases hj : Y j = i
    · rw [if_pos hj, hj, Function.update_self, hDi]
      exact hσ'.2 Y j hj
    · rw [if_neg hj, hd'']
      exact le_of_eq (congrFun (hdecl' _ hj) j).symm
  have h1 := rm_mono hδ Y _ _ hge
  have h2 := (hf k D hDbox).2 Y
  rw [← hX] at h2
  rw [← hd'', ← hY]
  linarith
