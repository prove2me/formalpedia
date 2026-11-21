-- Prove2me | solution 1 for MasulloGRH.pietsch_hilbertian_two_summing
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:32:27.590437+00:00
-- url     : https://prove2.me/submissions/af18df50-b99f-48d2-909c-4af0d594bb15

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

open MasulloGRH Topology Filter BoundedContinuousFunction

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
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (hE : IsHLCS E)
    (p q : Seminorm ℂ E) (hp : Continuous p) (hq : Continuous q)
    (hAS : ∀ (n : ℕ) (x : Fin n → E) (c : ℝ),
      (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → ∑ i, ‖f (x i)‖ ≤ c) →
      ∑ i, p (x i) ≤ c) :
    ∃ h : Seminorm ℂ E, Continuous h ∧ (∀ x, p x ≤ h x) ∧ (∀ x, h x ≤ q x) ∧
      (∀ x y, h (x + y) ^ 2 + h (x - y) ^ 2 = 2 * h x ^ 2 + 2 * h y ^ 2) ∧
      ∀ (n : ℕ) (x : Fin n → E) (c : ℝ),
        (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → ∑ i, ‖f (x i)‖ ^ 2 ≤ c) →
        ∑ i, h (x i) ^ 2 ≤ c := by
  have hEg : IsTopologicalAddGroup E := by
    obtain ⟨ι, _, P0, hP0⟩ := hE.1
    exact hP0.topologicalAddGroup
  have hψ0 : ∀ l : List E, 0 ≤ P q (ψ p q l) := ψ_nonneg p q hAS
  -- the Mazur–Orlicz functional is bounded below, sublinear and below `sup`
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
  have hadd : ∀ v₁ v₂ : Ball q →ᵇ ℝ, P' p q (v₁ + v₂) ≤ P' p q v₁ + P' p q v₂ := by
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
  -- Hahn–Banach
  obtain ⟨Λ, -, hΛ⟩ := exists_extension_of_le_sublinear
    (⟨⊥, 0⟩ : (Ball q →ᵇ ℝ) →ₗ.[ℝ] ℝ) (P' p q) hhom hadd (fun x => by
      have hx : (x : Ball q →ᵇ ℝ) = 0 := (Submodule.mem_bot ℝ).1 x.2
      rw [hx]
      simpa using hP'0)
  have hΛP : ∀ v : Ball q →ᵇ ℝ, Λ v ≤ P q v := by
    intro v
    refine (hΛ v).trans ?_
    have := hP'le v []
    rwa [ψ_nil, add_zero] at this
  have hΛψ : ∀ l : List E, 0 ≤ Λ (ψ p q l) := by
    intro l
    have h1 := (hΛ (-ψ p q l)).trans (hP'le (-ψ p q l) l)
    rw [neg_add_cancel, map_neg] at h1
    have h2 : P q (0 : Ball q →ᵇ ℝ) ≤ 0 := P_le q _ _ fun k => le_rfl
    linarith
  have hmono : ∀ u v : Ball q →ᵇ ℝ, (∀ k, u k ≤ v k) → Λ u ≤ Λ v := by
    intro u v huv
    have h1 := hΛP (u - v)
    have h2 : P q (u - v) ≤ 0 := P_le q _ _ fun k => by
      rw [coe_sub, Pi.sub_apply]
      linarith [huv k]
    rw [map_sub] at h1
    linarith
  have hΛ1 : Λ 1 = 1 := by
    have h1 : Λ 1 ≤ 1 := (hΛP 1).trans (P_le q _ _ fun k => le_rfl)
    have h2 : Λ (-1) ≤ -1 := (hΛP (-1)).trans (P_le q _ _ fun k => le_rfl)
    rw [map_neg] at h2
    linarith
  have hsq : ∀ w : Ball q →ᵇ ℝ, 0 ≤ Λ (w * w) := by
    intro w
    have := hmono 0 (w * w) fun k => by
      rw [coe_mul, Pi.mul_apply]
      exact mul_self_nonneg _
    rwa [map_zero] at this
  have hCS : ∀ u v : Ball q →ᵇ ℝ, Λ (u * v) ^ 2 ≤ Λ (u * u) * Λ (v * v) := by
    intro u v
    refine cs_real _ _ _ (hsq u) (hsq v) fun s t => ?_
    have h1 := hsq (s • u - t • v)
    have e : (s • u - t • v) * (s • u - t • v) =
        (s ^ 2) • (u * u) - (2 * s * t) • (u * v) + (t ^ 2) • (v * v) := by
      ext k
      simp only [coe_mul, coe_sub, coe_add, coe_smul, Pi.mul_apply, Pi.sub_apply, Pi.add_apply,
        smul_eq_mul]
      ring
    rw [e, map_add, map_sub, map_smul, map_smul, map_smul] at h1
    simpa [smul_eq_mul] using h1
  -- the quadratic form and the Hilbertian seminorm
  let Q : E → ℝ := fun x => Λ (a q x * a q x)
  have hQ0 : ∀ x, 0 ≤ Q x := fun x => hsq (a q x)
  have hQle : ∀ x, Q x ≤ q x ^ 2 := by
    intro x
    have h1 := hmono (a q x * a q x) ((q x ^ 2) • (1 : Ball q →ᵇ ℝ)) fun k => by
      rw [coe_mul, Pi.mul_apply, smul_one_apply, a_apply]
      have h2 := ev_le q k x
      have h3 := norm_nonneg (ev q k x)
      nlinarith
    rw [map_smul, hΛ1, smul_eq_mul, mul_one] at h1
    exact h1
  have hcross : ∀ x y, Λ (a q x * a q y) ≤ Real.sqrt (Q x) * Real.sqrt (Q y) := by
    intro x y
    have h1 := Real.abs_le_sqrt (hCS (a q x) (a q y))
    rw [Real.sqrt_mul (hQ0 x)] at h1
    exact (le_abs_self _).trans h1
  have hQadd : ∀ x y, Q (x + y) ≤ (Real.sqrt (Q x) + Real.sqrt (Q y)) ^ 2 := by
    intro x y
    have h1 := hmono (a q (x + y) * a q (x + y))
      (a q x * a q x + (2 : ℝ) • (a q x * a q y) + a q y * a q y) fun k => by
      simp only [coe_mul, coe_add, coe_smul, Pi.mul_apply, Pi.add_apply, smul_eq_mul, a_apply]
      have h2 : ‖ev q k (x + y)‖ ≤ ‖ev q k x‖ + ‖ev q k y‖ := by
        rw [map_add]; exact norm_add_le _ _
      have h3 := norm_nonneg (ev q k (x + y))
      nlinarith
    rw [map_add, map_add, map_smul, smul_eq_mul] at h1
    have h2 := hcross x y
    have h3 := Real.sq_sqrt (hQ0 x)
    have h4 := Real.sq_sqrt (hQ0 y)
    change Λ (a q (x + y) * a q (x + y)) ≤ _
    have h5 : Λ (a q x * a q x) = Q x := rfl
    have h6 : Λ (a q y * a q y) = Q y := rfl
    nlinarith
  have hQsmul : ∀ (c : ℂ) (x : E), Q (c • x) = ‖c‖ ^ 2 * Q x := by
    intro c x
    have e : a q (c • x) * a q (c • x) = (‖c‖ ^ 2) • (a q x * a q x) := by
      ext k
      simp only [coe_mul, coe_smul, Pi.mul_apply, smul_eq_mul, a_apply, map_smul, norm_mul]
      ring
    change Λ (a q (c • x) * a q (c • x)) = _
    rw [e, map_smul, smul_eq_mul]
  let h : Seminorm ℂ E := Seminorm.of (fun x => Real.sqrt (Q x))
    (fun x y => by
      rw [Real.sqrt_le_iff]
      exact ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), hQadd x y⟩)
    (fun c x => by
      rw [hQsmul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)])
  have hh : ∀ x, h x = Real.sqrt (Q x) := fun x => rfl
  have hh2 : ∀ x, h x ^ 2 = Q x := fun x => by rw [hh, Real.sq_sqrt (hQ0 x)]
  have hhq : ∀ x, h x ≤ q x := by
    intro x
    rw [hh, Real.sqrt_le_iff]
    exact ⟨apply_nonneg q x, hQle x⟩
  refine ⟨h, Seminorm.continuous_of_le hq hhq, ?_, hhq, ?_, ?_⟩
  · -- `p ≤ h`
    intro x
    have h1 := hΛψ [x]
    have e : ψ p q [x] = a q x - (p x) • (1 : Ball q →ᵇ ℝ) := by
      ext k
      simp [ψ_apply, a_apply]
    rw [e, map_sub, map_smul, hΛ1, smul_eq_mul, mul_one] at h1
    have h2 := hCS (a q x) 1
    rw [mul_one, mul_one, hΛ1, mul_one] at h2
    have h3 := Real.abs_le_sqrt h2
    rw [hh]
    have h4 := le_abs_self (Λ (a q x))
    linarith
  · -- parallelogram law
    intro x y
    rw [hh2, hh2, hh2, hh2]
    have e : a q (x + y) * a q (x + y) + a q (x - y) * a q (x - y) =
        (2 : ℝ) • (a q x * a q x) + (2 : ℝ) • (a q y * a q y) := by
      ext k
      simp only [coe_mul, coe_add, coe_smul, Pi.mul_apply, Pi.add_apply, smul_eq_mul, a_apply,
        map_add, map_sub]
      have := parallelogram_law_with_norm ℝ (ev q k x) (ev q k y)
      linarith
    have h1 := congrArg Λ e
    rw [map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h1
    exact h1
  · -- the 2-summing estimate
    intro n x c hyp
    have h1 := hmono (∑ i : Fin n, a q (x i) * a q (x i)) (c • (1 : Ball q →ᵇ ℝ)) fun k => by
      rw [smul_one_apply, coe_sum, Finset.sum_apply]
      have h2 := hyp (ev q k) (fun y => ev_le q k y)
      refine le_trans (le_of_eq ?_) h2
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [coe_mul, Pi.mul_apply, a_apply]
      ring
    rw [map_sum, map_smul, hΛ1, smul_eq_mul, mul_one] at h1
    refine le_trans (le_of_eq ?_) h1
    exact Finset.sum_congr rfl fun i _ => hh2 (x i)
