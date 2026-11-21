-- Prove2me | solution 1 for MasulloGRH.hilbertian_of_pietsch_state
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:48:04.710658+00:00
-- url     : https://prove2.me/submissions/e10e513d-95db-4d1d-ba46-b8c1708b0da9

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open MasulloGRH

universe u

theorem solution (E : Type u)
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (hE : IsHLCS E)
    (p q : Seminorm ℂ E) (hp : Continuous p) (hq : Continuous q)
    (Λ : (StrongDual ℂ E → ℝ) → ℝ)
    (hadd : ∀ φ ψ : StrongDual ℂ E → ℝ,
        (∃ M : ℝ, ∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → |φ f| ≤ M) →
        (∃ M : ℝ, ∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → |ψ f| ≤ M) →
        Λ (φ + ψ) = Λ φ + Λ ψ)
    (hsmul : ∀ (r : ℝ) (φ : StrongDual ℂ E → ℝ),
        (∃ M : ℝ, ∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → |φ f| ≤ M) →
        Λ (r • φ) = r * Λ φ)
    (hmono : ∀ φ ψ : StrongDual ℂ E → ℝ,
        (∃ M : ℝ, ∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → |φ f| ≤ M) →
        (∃ M : ℝ, ∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → |ψ f| ≤ M) →
        (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → φ f ≤ ψ f) → Λ φ ≤ Λ ψ)
    (hone : Λ (fun _ => 1) = 1)
    (hdom : ∀ x : E, p x ≤ Λ (fun f => ‖f x‖)) :
    ∃ h : Seminorm ℂ E, Continuous h ∧ (∀ x, p x ≤ h x) ∧ (∀ x, h x ≤ q x) ∧
      (∀ x y, h (x + y) ^ 2 + h (x - y) ^ 2 = 2 * h x ^ 2 + 2 * h y ^ 2) ∧
      ∀ (n : ℕ) (x : Fin n → E) (c : ℝ),
        (∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → ∑ i, ‖f (x i)‖ ^ 2 ≤ c) →
        ∑ i, h (x i) ^ 2 ≤ c := by
  classical
  -- functions bounded on the `q`-polar
  let Bd : (StrongDual ℂ E → ℝ) → Prop := fun φ =>
    ∃ M : ℝ, ∀ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ q y) → |φ f| ≤ M
  have bd_const : ∀ c : ℝ, Bd (fun _ => c) := fun c => ⟨|c|, fun _ _ => le_rfl⟩
  have bd_add : ∀ φ ψ, Bd φ → Bd ψ → Bd (φ + ψ) := by
    rintro φ ψ ⟨M, hM⟩ ⟨N, hN⟩
    exact ⟨M + N, fun f hf => (abs_add_le _ _).trans (add_le_add (hM f hf) (hN f hf))⟩
  have bd_smul : ∀ (r : ℝ) φ, Bd φ → Bd (r • φ) := by
    rintro r φ ⟨M, hM⟩
    refine ⟨|r| * M, fun f hf => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM f hf) (abs_nonneg r)
  have Λconst : ∀ c : ℝ, Λ (fun _ => c) = c := by
    intro c
    have : (fun _ : StrongDual ℂ E => c) = c • (fun _ => (1 : ℝ)) := by
      funext f; simp
    rw [this, hsmul c _ (bd_const 1), hone, mul_one]
  -- the basic quantities
  have bd_sq : ∀ x : E, Bd (fun f => ‖f x‖ ^ 2) := fun x =>
    ⟨q x ^ 2, fun f hf => by
      rw [abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hf x) 2⟩
  have bd_norm : ∀ x : E, Bd (fun f => ‖f x‖) := fun x =>
    ⟨q x, fun f hf => by rw [abs_of_nonneg (norm_nonneg _)]; exact hf x⟩
  have bd_re : ∀ x y : E, Bd (fun f => (f x * (starRingEnd ℂ) (f y)).re) := fun x y =>
    ⟨q x * q y, fun f hf => by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, RCLike.norm_conj]
      exact mul_le_mul (hf x) (hf y) (norm_nonneg _) (apply_nonneg q x)⟩
  let S : E → ℝ := fun x => Λ (fun f => ‖f x‖ ^ 2)
  let A : E → E → ℝ := fun x y => Λ (fun f => (f x * (starRingEnd ℂ) (f y)).re)
  have S_nonneg : ∀ x, 0 ≤ S x := by
    intro x
    have h0 := hmono (fun _ => (0 : ℝ)) _ (bd_const 0) (bd_sq x) (fun f _ => by positivity)
    rwa [Λconst] at h0
  have S_le : ∀ x, S x ≤ q x ^ 2 := by
    intro x
    have h0 := hmono _ (fun _ => q x ^ 2) (bd_sq x) (bd_const _) fun f hf =>
      pow_le_pow_left₀ (norm_nonneg _) (hf x) 2
    rwa [Λconst] at h0
  -- expansion of `S (x + t y)` for real `t`
  have S_expand : ∀ (x y : E) (t : ℝ), S (x + (t : ℂ) • y) = S x + 2 * t * A x y + t ^ 2 * S y := by
    intro x y t
    have hfun : (fun f : StrongDual ℂ E => ‖f (x + (t : ℂ) • y)‖ ^ 2) =
        ((fun f => ‖f x‖ ^ 2) + (2 * t) • (fun f => (f x * (starRingEnd ℂ) (f y)).re)) +
          (t ^ 2) • (fun f => ‖f y‖ ^ 2) := by
      funext f
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_smul, smul_eq_mul]
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
        Complex.normSq_add, Complex.normSq_mul, Complex.normSq_ofReal, map_mul, Complex.conj_ofReal]
      have : (f x * ((t : ℂ) * (starRingEnd ℂ) (f y))).re = t * (f x * (starRingEnd ℂ) (f y)).re := by
        rw [show f x * ((t : ℂ) * (starRingEnd ℂ) (f y)) = (t : ℂ) * (f x * (starRingEnd ℂ) (f y)) by ring,
          Complex.re_ofReal_mul]
      rw [this]
      ring
    show Λ _ = _
    rw [hfun, hadd _ _ (bd_add _ _ (bd_sq x) (bd_smul _ _ (bd_re x y))) (bd_smul _ _ (bd_sq y)),
      hadd _ _ (bd_sq x) (bd_smul _ _ (bd_re x y)), hsmul _ _ (bd_re x y), hsmul _ _ (bd_sq y)]
  -- Cauchy–Schwarz for the positive functional
  have CS : ∀ x y : E, A x y ^ 2 ≤ S x * S y := by
    intro x y
    have hq : ∀ t : ℝ, 0 ≤ S y * (t * t) + 2 * A x y * t + S x := by
      intro t
      have := S_nonneg (x + (t : ℂ) • y)
      rw [S_expand] at this
      nlinarith [this]
    have hd := discrim_le_zero hq
    unfold discrim at hd
    nlinarith [hd]
  have A_le : ∀ x y : E, A x y ≤ Real.sqrt (S x) * Real.sqrt (S y) := by
    intro x y
    rw [← Real.sqrt_mul (S_nonneg x)]
    exact Real.le_sqrt_of_sq_le (CS x y)
  -- homogeneity
  have S_smul : ∀ (c : ℂ) (x : E), S (c • x) = ‖c‖ ^ 2 * S x := by
    intro c x
    have hfun : (fun f : StrongDual ℂ E => ‖f (c • x)‖ ^ 2) = (‖c‖ ^ 2) • (fun f => ‖f x‖ ^ 2) := by
      funext f
      simp [map_smul, norm_mul, mul_pow]
    show Λ _ = _
    rw [hfun, hsmul _ _ (bd_sq x)]
  -- the Hilbertian seminorm
  let h : Seminorm ℂ E := Seminorm.of (fun x => Real.sqrt (S x))
    (fun x y => by
      have h1 := S_expand x y 1
      simp only [Complex.ofReal_one, one_smul, mul_one, one_pow, one_mul] at h1
      refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
      rw [h1]
      have hx := Real.sq_sqrt (S_nonneg x)
      have hy := Real.sq_sqrt (S_nonneg y)
      nlinarith [A_le x y, Real.sqrt_nonneg (S x), Real.sqrt_nonneg (S y)])
    (fun c x => by
      rw [S_smul, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg c)])
  have h_apply : ∀ x, h x = Real.sqrt (S x) := fun x => rfl
  have h_sq : ∀ x, h x ^ 2 = S x := fun x => by rw [h_apply, Real.sq_sqrt (S_nonneg x)]
  have h_le_q : ∀ x, h x ≤ q x := by
    intro x
    rw [h_apply]
    calc Real.sqrt (S x) ≤ Real.sqrt (q x ^ 2) := Real.sqrt_le_sqrt (S_le x)
      _ = q x := Real.sqrt_sq (apply_nonneg q x)
  refine ⟨h, ?_, ?_, h_le_q, ?_, ?_⟩
  · -- continuity: dominated by the continuous seminorm `q`
    obtain ⟨⟨ι, _, P, hP⟩, _⟩ := hE
    have : IsTopologicalAddGroup E := hP.topologicalAddGroup
    exact Seminorm.continuous_of_le hq (fun x => h_le_q x)
  · -- `p ≤ h`: Jensen for the state
    intro x
    have hq2 : ∀ t : ℝ, 0 ≤ 1 * (t * t) + (-2 * Λ (fun f => ‖f x‖)) * t + S x := by
      intro t
      have hfun : (fun f : StrongDual ℂ E => (‖f x‖ - t) ^ 2) =
          ((fun f => ‖f x‖ ^ 2) + (-2 * t) • (fun f => ‖f x‖)) + (fun _ => t ^ 2) := by
        funext f; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      have hb : Bd (fun f : StrongDual ℂ E => (‖f x‖ - t) ^ 2) := by
        rw [hfun]
        exact bd_add _ _ (bd_add _ _ (bd_sq x) (bd_smul _ _ (bd_norm x))) (bd_const _)
      have hpos := hmono (fun _ => (0 : ℝ)) (fun f => (‖f x‖ - t) ^ 2) (bd_const 0) hb
        (fun f _ => by positivity)
      rw [Λconst, hfun, hadd _ _ (bd_add _ _ (bd_sq x) (bd_smul _ _ (bd_norm x))) (bd_const _),
        hadd _ _ (bd_sq x) (bd_smul _ _ (bd_norm x)), hsmul _ _ (bd_norm x), Λconst] at hpos
      show 0 ≤ 1 * (t * t) + -2 * Λ (fun f => ‖f x‖) * t + S x
      nlinarith [hpos]
    have hd := discrim_le_zero hq2
    unfold discrim at hd
    have hJ : Λ (fun f => ‖f x‖) ^ 2 ≤ S x := by nlinarith [hd]
    rw [h_apply]
    exact (hdom x).trans (Real.le_sqrt_of_sq_le hJ)
  · -- parallelogram law
    intro x y
    have h1 := S_expand x y 1
    have h2 := S_expand x y (-1)
    simp only [Complex.ofReal_one, one_smul, mul_one, one_pow, one_mul] at h1
    simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_smul, one_smul, ← sub_eq_add_neg] at h2
    rw [h_sq, h_sq, h_sq, h_sq, h1, h2]
    ring
  · -- 2-summing with constant one
    intro n x c hc
    have hsum : ∀ s : Finset (Fin n),
        Bd (fun f => ∑ i ∈ s, ‖f (x i)‖ ^ 2) ∧
          Λ (fun f => ∑ i ∈ s, ‖f (x i)‖ ^ 2) = ∑ i ∈ s, S (x i) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        refine ⟨by simpa using bd_const 0, ?_⟩
        simpa using Λconst 0
      | insert i s hi ih =>
        obtain ⟨hb, he⟩ := ih
        have hfun : (fun f : StrongDual ℂ E => ∑ j ∈ insert i s, ‖f (x j)‖ ^ 2) =
            (fun f => ‖f (x i)‖ ^ 2) + (fun f => ∑ j ∈ s, ‖f (x j)‖ ^ 2) := by
          funext f; simp [Finset.sum_insert hi]
        refine ⟨by rw [hfun]; exact bd_add _ _ (bd_sq _) hb, ?_⟩
        rw [hfun, hadd _ _ (bd_sq _) hb, he, Finset.sum_insert hi]
    obtain ⟨hb, he⟩ := hsum Finset.univ
    have hle := hmono _ (fun _ => c) hb (bd_const c) (fun f hf => hc f hf)
    rw [Λconst, he] at hle
    simpa only [h_sq] using hle
