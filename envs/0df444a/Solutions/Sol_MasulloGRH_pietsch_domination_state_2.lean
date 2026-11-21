-- Prove2me | solution 2 for MasulloGRH.pietsch_domination_state
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:49:51.548286+00:00
-- url     : https://prove2.me/submissions/b7705de6-5edd-4461-8171-d63248247338

import Mathlib

-- The auxiliary namespace below is reproduced from the accepted Prove2Me proof af18df50 of
-- MasulloGRH.pietsch_hilbertian_two_summing (same account, session masullo-a5).

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

open Topology Filter BoundedContinuousFunction

universe u

namespace PietschAux

/-- Cauchy–Schwarz for a positive semidefinite binary quadratic form. -/
theorem cs_real (A B M : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ s t : ℝ, 0 ≤ s ^ 2 * A - 2 * s * t * M + t ^ 2 * B) : M ^ 2 ≤ A * B := by
  by_cases hA0 : A = 0
  · subst hA0
    have hM : M = 0 := by
      by_contra hM
      have h1 := h ((B + 1) / (2 * M)) 1
      have e : 2 * ((B + 1) / (2 * M)) * 1 * M = B + 1 := by field_simp
      rw [e, mul_zero, one_pow, one_mul] at h1
      linarith
    rw [hM]
    simp
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
    have h1 := h M A
    by_contra hc
    rw [not_le] at hc
    nlinarith [mul_pos hApos (sub_pos.2 hc)]

theorem sum_get {α : Type*} (l : List α) (g : α → ℝ) :
    ∑ i : Fin l.length, g (l.get i) = (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.sum_cons, ← ih]
    simp [Fin.sum_univ_succ]

theorem sum_map_sub' {α : Type*} (l : List α) (g p : α → ℝ) :
    (l.map fun x => g x - p x).sum = (l.map g).sum - (l.map p).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

theorem sum_map_neg' {α : Type*} (l : List α) (g : α → ℝ) :
    (l.map fun x => -g x).sum = -(l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

theorem sum_map_le {α : Type*} (l : List α) (g p : α → ℝ) (h : ∀ x, g x ≤ p x) :
    (l.map g).sum ≤ (l.map p).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h x) ih

section ball

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

/-- The dual unit ball of the seminorm `q`, regarded as a discrete space. -/
def Ball (q : Seminorm ℂ E) : Type u := {f : StrongDual ℂ E // ∀ y, ‖f y‖ ≤ q y}

instance (q : Seminorm ℂ E) : TopologicalSpace (Ball q) := ⊥

instance (q : Seminorm ℂ E) : DiscreteTopology (Ball q) := ⟨rfl⟩

/-- The functional underlying a point of the ball. -/
def ev (q : Seminorm ℂ E) (k : Ball q) : StrongDual ℂ E := Subtype.val k

theorem ev_le (q : Seminorm ℂ E) (k : Ball q) (x : E) : ‖ev q k x‖ ≤ q x := Subtype.property k x

/-- A point of the ball from a functional bounded by `q`. -/
def mkBall (q : Seminorm ℂ E) (f : StrongDual ℂ E) (hf : ∀ y, ‖f y‖ ≤ q y) : Ball q := ⟨f, hf⟩

theorem ev_mkBall (q : Seminorm ℂ E) (f : StrongDual ℂ E) (hf : ∀ y, ‖f y‖ ≤ q y) :
    ev q (mkBall q f hf) = f := rfl

instance (q : Seminorm ℂ E) : Nonempty (Ball q) :=
  ⟨mkBall q 0 fun y => by simpa using apply_nonneg q y⟩

variable (p q : Seminorm ℂ E)

/-- The bounded function `f ↦ |f x|` on the ball. -/
noncomputable def a (x : E) : Ball q →ᵇ ℝ :=
  ofNormedAddCommGroupDiscrete (fun k => ‖ev q k x‖) (q x) (fun k => by
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact ev_le q k x)

theorem a_apply (x : E) (k : Ball q) : a q x k = ‖ev q k x‖ := rfl

/-- The sublinear functional `sup`. -/
noncomputable def P (φ : Ball q →ᵇ ℝ) : ℝ := ⨆ k, φ k

theorem bdd (φ : Ball q →ᵇ ℝ) : BddAbove (Set.range fun k => φ k) :=
  ⟨‖φ‖, by
    rintro _ ⟨k, rfl⟩
    exact (Real.le_norm_self _).trans (φ.norm_coe_le_norm k)⟩

theorem le_P (φ : Ball q →ᵇ ℝ) (k : Ball q) : φ k ≤ P q φ := le_ciSup (bdd q φ) k

theorem P_le (φ : Ball q →ᵇ ℝ) (C : ℝ) (h : ∀ k, φ k ≤ C) : P q φ ≤ C := ciSup_le h

theorem P_add (φ ψ : Ball q →ᵇ ℝ) : P q (φ + ψ) ≤ P q φ + P q ψ :=
  P_le q _ _ fun k => add_le_add (le_P q φ k) (le_P q ψ k)

theorem P_smul (c : ℝ) (hc : 0 < c) (φ : Ball q →ᵇ ℝ) : P q (c • φ) = c * P q φ := by
  unfold P
  rw [Real.mul_iSup_of_nonneg hc.le]
  rfl

/-- The function `f ↦ ∑ (|f xᵢ| - p xᵢ)` attached to a finite list of vectors. -/
noncomputable def ψ (l : List E) : Ball q →ᵇ ℝ :=
  ofNormedAddCommGroupDiscrete (fun k => (l.map fun x => ‖ev q k x‖ - p x).sum)
    ((l.map fun x => q x + p x).sum) (fun k => by
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · have := sum_map_le l (fun x => -(q x + p x)) (fun x => ‖ev q k x‖ - p x) (fun x => by
          have h1 := norm_nonneg (ev q k x)
          have h2 := apply_nonneg q x
          linarith)
        have e := sum_map_neg' l (fun x => q x + p x)
        linarith
      · exact sum_map_le l _ _ (fun x => by
          have h1 := ev_le q k x
          have h2 := apply_nonneg p x
          linarith))

theorem ψ_apply (l : List E) (k : Ball q) :
    ψ p q l k = (l.map fun x => ‖ev q k x‖ - p x).sum := rfl

theorem smul_one_apply (c : ℝ) (k : Ball q) : (c • (1 : Ball q →ᵇ ℝ)) k = c := by
  simp

theorem ψ_nil : ψ p q [] = 0 := by
  ext k
  simp [ψ_apply]

theorem ψ_append (l₁ l₂ : List E) : ψ p q (l₁ ++ l₂) = ψ p q l₁ + ψ p q l₂ := by
  ext k
  simp [ψ_apply, List.map_append, List.sum_append]

theorem ψ_smul (c : ℝ) (hc : 0 < c) (l : List E) :
    ψ p q (l.map fun x => (c : ℂ) • x) = c • ψ p q l := by
  ext k
  change ψ p q (l.map fun x => (c : ℂ) • x) k = c * ψ p q l k
  rw [ψ_apply, ψ_apply, List.map_map, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro x _
  simp only [Function.comp_apply, map_smul, smul_eq_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hc.le, map_smul_eq_mul]
  ring

/-- The absolutely summing hypothesis says `sup ψ ≥ 0`. -/
theorem ψ_nonneg
    (hAS : ∀ (n : ℕ) (x : Fin n → E) (c : ℝ),
      (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → ∑ i, ‖f (x i)‖ ≤ c) →
      ∑ i, p (x i) ≤ c) (l : List E) : 0 ≤ P q (ψ p q l) := by
  have key := hAS l.length (fun i => l.get i) ((l.map p).sum + P q (ψ p q l)) (fun f hf => by
    rw [sum_get l (fun x => ‖f x‖)]
    have h1 := le_P q (ψ p q l) (mkBall q f hf)
    rw [ψ_apply, sum_map_sub', ev_mkBall] at h1
    linarith)
  rw [sum_get l p] at key
  linarith

/-- The Mazur–Orlicz sublinear functional. -/
noncomputable def P' (v : Ball q →ᵇ ℝ) : ℝ := ⨅ l : List E, P q (v + ψ p q l)

end ball

end PietschAux

open PietschAux in
theorem solution (E : Type u)
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (p q : Seminorm ℂ E)
    (hAS : ∀ (n : ℕ) (x : Fin n → E) (c : ℝ),
      (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → ∑ i, ‖f (x i)‖ ≤ c) →
      ∑ i, p (x i) ≤ c) :
    ∃ Λ : (StrongDual ℂ E → ℝ) → ℝ,
      (∀ φ ψ : StrongDual ℂ E → ℝ,
        (∃ M : ℝ, ∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → |φ f| ≤ M) →
        (∃ M : ℝ, ∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → |ψ f| ≤ M) →
        Λ (φ + ψ) = Λ φ + Λ ψ) ∧
      (∀ (r : ℝ) (φ : StrongDual ℂ E → ℝ),
        (∃ M : ℝ, ∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → |φ f| ≤ M) →
        Λ (r • φ) = r * Λ φ) ∧
      (∀ φ ψ : StrongDual ℂ E → ℝ,
        (∃ M : ℝ, ∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → |φ f| ≤ M) →
        (∃ M : ℝ, ∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → |ψ f| ≤ M) →
        (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → φ f ≤ ψ f) → Λ φ ≤ Λ ψ) ∧
      Λ (fun _ => 1) = 1 ∧
      ∀ x : E, p x ≤ Λ (fun f => ‖f x‖) := by
  classical
  have hψ0 : ∀ l : List E, 0 ≤ P q (ψ p q l) := ψ_nonneg p q hAS
  have hbb : ∀ v : Ball q →ᵇ ℝ, BddBelow (Set.range fun l : List E => P q (v + ψ p q l)) := by
    intro v
    refine ⟨-P q (-v), ?_⟩
    rintro _ ⟨l, rfl⟩
    have h1 := P_add q (v + ψ p q l) (-v)
    have e : v + ψ p q l + -v = ψ p q l := by abel
    rw [e] at h1
    have h2 := hψ0 l
    change -P q (-v) ≤ P q (v + ψ p q l)
    linarith
  have hP'le : ∀ (v : Ball q →ᵇ ℝ) (l : List E), P' p q v ≤ P q (v + ψ p q l) :=
    fun v l => ciInf_le (hbb v) l
  have hsub : ∀ v₁ v₂ : Ball q →ᵇ ℝ, P' p q (v₁ + v₂) ≤ P' p q v₁ + P' p q v₂ := by
    intro v₁ v₂
    have h1 : ∀ l₁ l₂ : List E,
        P' p q (v₁ + v₂) ≤ P q (v₁ + ψ p q l₁) + P q (v₂ + ψ p q l₂) := by
      intro l₁ l₂
      refine (hP'le (v₁ + v₂) (l₁ ++ l₂)).trans ?_
      have e : v₁ + v₂ + ψ p q (l₁ ++ l₂) = (v₁ + ψ p q l₁) + (v₂ + ψ p q l₂) := by
        rw [ψ_append]; abel
      rw [e]
      exact P_add q _ _
    have h2 : ∀ l₂ : List E, P' p q (v₁ + v₂) - P q (v₂ + ψ p q l₂) ≤ P' p q v₁ := by
      intro l₂
      refine le_ciInf fun l₁ => ?_
      have := h1 l₁ l₂
      linarith
    have h3 : P' p q (v₁ + v₂) - P' p q v₁ ≤ P' p q v₂ := by
      refine le_ciInf fun l₂ => ?_
      have := h2 l₂
      linarith
    linarith
  have hhom_le : ∀ (c : ℝ), 0 < c → ∀ v : Ball q →ᵇ ℝ, P' p q (c • v) ≤ c * P' p q v := by
    intro c hc v
    have h1 : P' p q (c • v) / c ≤ P' p q v := by
      refine le_ciInf fun l => ?_
      rw [div_le_iff₀ hc]
      have h2 := hP'le (c • v) (l.map fun x => (c : ℂ) • x)
      rw [ψ_smul p q c hc, ← smul_add, P_smul q c hc] at h2
      linarith
    rw [div_le_iff₀ hc] at h1
    linarith
  have hhom : ∀ (c : ℝ), 0 < c → ∀ v : Ball q →ᵇ ℝ, P' p q (c • v) = c * P' p q v := by
    intro c hc v
    refine le_antisymm (hhom_le c hc v) ?_
    have h1 := hhom_le c⁻¹ (inv_pos.2 hc) (c • v)
    rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at h1
    have h2 : c * P' p q v ≤ c * (c⁻¹ * P' p q (c • v)) := mul_le_mul_of_nonneg_left h1 hc.le
    rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at h2
    exact h2
  have hP'0 : 0 ≤ P' p q 0 := by
    refine le_ciInf fun l => ?_
    rw [zero_add]
    exact hψ0 l
  -- Hahn–Banach (Mazur–Orlicz)
  obtain ⟨L, -, hL⟩ := exists_extension_of_le_sublinear
    (⟨⊥, 0⟩ : (Ball q →ᵇ ℝ) →ₗ.[ℝ] ℝ) (P' p q) hhom hsub (fun x => by
      have hx : (x : Ball q →ᵇ ℝ) = 0 := (Submodule.mem_bot ℝ).1 x.2
      rw [hx]
      simpa using hP'0)
  have hLP : ∀ v : Ball q →ᵇ ℝ, L v ≤ P q v := by
    intro v
    refine (hL v).trans ?_
    have := hP'le v []
    rwa [ψ_nil, add_zero] at this
  have hLψ : ∀ l : List E, 0 ≤ L (ψ p q l) := by
    intro l
    have h1 := (hL (-ψ p q l)).trans (hP'le (-ψ p q l) l)
    rw [neg_add_cancel, map_neg] at h1
    have h2 : P q (0 : Ball q →ᵇ ℝ) ≤ 0 := P_le q _ _ fun k => le_rfl
    linarith
  have hLmono : ∀ u v : Ball q →ᵇ ℝ, (∀ k, u k ≤ v k) → L u ≤ L v := by
    intro u v huv
    have h1 := hLP (u - v)
    have h2 : P q (u - v) ≤ 0 := P_le q _ _ fun k => by
      rw [coe_sub, Pi.sub_apply]
      linarith [huv k]
    rw [map_sub] at h1
    linarith
  have hL1 : L 1 = 1 := by
    have h1 : L 1 ≤ 1 := (hLP 1).trans (P_le q _ _ fun k => le_rfl)
    have h2 : L (-1) ≤ -1 := (hLP (-1)).trans (P_le q _ _ fun k => le_rfl)
    rw [map_neg] at h2
    linarith
  -- transport to arbitrary functions on the dual: restrict to the ball when bounded there
  let Bd : (StrongDual ℂ E → ℝ) → Prop := fun φ =>
    ∃ M : ℝ, ∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → |φ f| ≤ M
  let res : (φ : StrongDual ℂ E → ℝ) → Bd φ → (Ball q →ᵇ ℝ) := fun φ hφ =>
    ofNormedAddCommGroupDiscrete (fun k => φ (ev q k)) hφ.choose (fun k => by
      rw [Real.norm_eq_abs]
      exact hφ.choose_spec (ev q k) (fun y => ev_le q k y))
  have res_apply : ∀ φ (hφ : Bd φ) (k : Ball q), res φ hφ k = φ (ev q k) := fun _ _ _ => rfl
  let Λ : (StrongDual ℂ E → ℝ) → ℝ := fun φ => if hφ : Bd φ then L (res φ hφ) else 0
  have Λ_eq : ∀ φ (hφ : Bd φ), Λ φ = L (res φ hφ) := fun φ hφ => dif_pos hφ
  have bd_add : ∀ φ ψ, Bd φ → Bd ψ → Bd (φ + ψ) := by
    rintro φ ψ ⟨M, hM⟩ ⟨N, hN⟩
    exact ⟨M + N, fun f hf => (abs_add_le _ _).trans (add_le_add (hM f hf) (hN f hf))⟩
  have bd_smul : ∀ (r : ℝ) φ, Bd φ → Bd (r • φ) := by
    rintro r φ ⟨M, hM⟩
    refine ⟨|r| * M, fun f hf => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM f hf) (abs_nonneg r)
  refine ⟨Λ, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ ψ hφ hψ
    rw [Λ_eq _ (bd_add φ ψ hφ hψ), Λ_eq _ hφ, Λ_eq _ hψ, ← map_add]
    congr 1
  · intro r φ hφ
    rw [Λ_eq _ (bd_smul r φ hφ), Λ_eq _ hφ, ← smul_eq_mul, ← map_smul]
    congr 1
  · intro φ ψ hφ hψ hle
    rw [Λ_eq _ hφ, Λ_eq _ hψ]
    exact hLmono _ _ fun k => hle (ev q k) (fun y => ev_le q k y)
  · have h1 : Bd (fun _ => (1 : ℝ)) := ⟨1, fun _ _ => by simp⟩
    rw [Λ_eq _ h1]
    have : res (fun _ => (1 : ℝ)) h1 = 1 := by ext k; rfl
    rw [this, hL1]
  · intro x
    have hb : Bd (fun f => ‖f x‖) := ⟨q x, fun f hf => by
      rw [abs_of_nonneg (norm_nonneg _)]; exact hf x⟩
    rw [Λ_eq _ hb]
    have hra : res (fun f => ‖f x‖) hb = a q x := by ext k; rfl
    rw [hra]
    have h1 := hLψ [x]
    have e : ψ p q [x] = a q x - (p x) • (1 : Ball q →ᵇ ℝ) := by
      ext k
      simp [ψ_apply, a_apply]
    rw [e, map_sub, map_smul, hL1, smul_eq_mul, mul_one] at h1
    linarith
