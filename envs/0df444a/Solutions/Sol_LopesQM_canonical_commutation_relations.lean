-- Prove2me | solution 1 for LopesQM.canonical_commutation_relations
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T00:12:24.666631+00:00
-- url     : https://prove2.me/submissions/2af2ebff-ac55-4ca0-b314-cf15800ffded

import Mathlib
import Definitions.Def_LopesQM_Defs
open MeasureTheory


namespace LopesQM

theorem pos_symm {n : ℕ} (j : Fin n) (ψ φ : WaveFn n) :
    l2Inner (positionOp j ψ) φ = l2Inner ψ (positionOp j φ) := by
  unfold l2Inner positionOp
  congr 1
  funext x
  simp only [map_mul, Complex.conj_ofReal]
  ring

/-- derivative of `y ↦ (y j : ℂ) * ψ y` -/
lemma fderiv_coord_mul {n : ℕ} (j : Fin n) (ψ : WaveFn n) (x : Rn n)
    (hψ : DifferentiableAt ℝ ψ x) (v : Rn n) :
    fderiv ℝ (positionOp j ψ) x v =
      ((v j : ℝ) : ℂ) * ψ x + ((x j : ℝ) : ℂ) * fderiv ℝ ψ x v := by
  have hc : HasFDerivAt (fun y : Rn n => ((y j : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (EuclideanSpace.proj j)) x :=
    (Complex.ofRealCLM.comp (EuclideanSpace.proj j)).hasFDerivAt
  have h := hc.mul hψ.hasFDerivAt
  rw [show positionOp j ψ = (fun y : Rn n => ((y j : ℝ) : ℂ)) * ψ from rfl, h.fderiv]
  simp [smul_eq_mul]
  ring

/-- derivative of `y ↦ c * fderiv ψ y w` -/
lemma fderiv_momentum {n : ℕ} (hbar : ℝ) (j : Fin n) (ψ : WaveFn n) (x : Rn n)
    (hψ : DifferentiableAt ℝ (fderiv ℝ ψ) x) (v : Rn n) :
    fderiv ℝ (momentumOp hbar j ψ) x v = -(Complex.I * (hbar : ℂ)) *
      fderiv ℝ (fderiv ℝ ψ) x v (EuclideanSpace.single j 1) := by
  set c : ℂ := -(Complex.I * (hbar : ℂ))
  set w : Rn n := EuclideanSpace.single j 1
  rw [show momentumOp hbar j ψ = fun y => c * fderiv ℝ ψ y w from rfl]
  have h1 : HasFDerivAt (fun y => fderiv ℝ ψ y w)
      ((ContinuousLinearMap.apply ℝ ℂ w).comp (fderiv ℝ (fderiv ℝ ψ) x)) x :=
    (ContinuousLinearMap.apply ℝ ℂ w).hasFDerivAt.comp x hψ.hasFDerivAt
  have h2 := h1.const_mul c
  rw [h2.fderiv]
  simp

theorem ccr {n : ℕ} (hbar : ℝ) (hhbar : 0 < hbar) (j k : Fin n) :
    (∀ ψ : WaveFn n, ∀ x : Rn n,
        commutator (positionOp k) (positionOp j) ψ x = 0) ∧
    (∀ ψ : WaveFn n, ContDiff ℝ 2 ψ → ∀ x : Rn n,
        commutator (momentumOp hbar k) (momentumOp hbar j) ψ x = 0) ∧
    (∀ ψ : WaveFn n, Differentiable ℝ ψ → ∀ x : Rn n,
        Complex.I / (hbar : ℂ) * commutator (momentumOp hbar j) (positionOp j) ψ x = ψ x) ∧
    (j ≠ k → ∀ ψ : WaveFn n, Differentiable ℝ ψ → ∀ x : Rn n,
        Complex.I / (hbar : ℂ) * commutator (momentumOp hbar j) (positionOp k) ψ x = 0) := by
  have hb : (hbar : ℂ) ≠ 0 := by exact_mod_cast hhbar.ne'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ψ x
    simp only [commutator, positionOp, Pi.sub_apply]
    ring
  · intro ψ hψ x
    have hd : DifferentiableAt ℝ (fderiv ℝ ψ) x :=
      ((hψ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
    have hsymm := (hψ.contDiffAt (x := x)).isSymmSndFDerivAt (by simp [minSmoothness])
    simp only [commutator, momentumOp, Pi.sub_apply]
    rw [fderiv_momentum hbar j ψ x hd, fderiv_momentum hbar k ψ x hd,
      hsymm (EuclideanSpace.single k 1) (EuclideanSpace.single j 1)]
    ring
  · intro ψ hψ x
    simp only [commutator, momentumOp, positionOp, Pi.sub_apply]
    rw [fderiv_coord_mul j ψ x (hψ x)]
    simp
    field_simp
    ring_nf
    simp [Complex.I_sq]
  · intro hjk ψ hψ x
    simp only [commutator, momentumOp, positionOp, Pi.sub_apply]
    rw [fderiv_coord_mul k ψ x (hψ x)]
    have : (EuclideanSpace.single j (1 : ℝ) : Rn n) k = 0 := by
      simp [EuclideanSpace.single_apply, Ne.symm hjk]
    rw [this]
    simp only [Complex.ofReal_zero, zero_mul, zero_add]
    ring


lemma l2Inner_self {n : ℕ} (ψ : WaveFn n) : l2Inner ψ ψ = ((∫ x, ‖ψ x‖ ^ 2 : ℝ) : ℂ) := by
  unfold l2Inner
  have e : (fun x => ψ x * (starRingEnd ℂ) (ψ x)) = fun x => (((‖ψ x‖ ^ 2 : ℝ)) : ℂ) := by
    funext x
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [e]
  exact integral_ofReal

lemma l2Norm_eq_zero_iff {n : ℕ} (g : WaveFn n) (hg : MemLp g 2) :
    l2Norm g = 0 ↔ g =ᵐ[volume] 0 := by
  have hint : Integrable (fun x => ‖g x‖ ^ 2) := by
    have := hg.integrable_norm_pow (p := 2) (by norm_num)
    simpa using this
  have hnn : 0 ≤ ∫ x, ‖g x‖ ^ 2 := integral_nonneg fun x => by positivity
  unfold l2Norm
  rw [Real.sqrt_eq_zero hnn, integral_eq_zero_iff_of_nonneg (fun x => by positivity) hint]
  constructor
  · intro h
    filter_upwards [h] with x hx
    simpa using hx
  · intro h
    filter_upwards [h] with x hx
    simp [hx]

theorem disp {n : ℕ} (A : Op n) (ψ : WaveFn n)
    (hψ : MemLp ψ 2) (hAψ : MemLp (A ψ) 2) (hne : l2Norm ψ ≠ 0) :
    dispersion A ψ = 0 ↔ ∃ α : ℂ, A ψ =ᵐ[volume] fun x => α * ψ x := by
  have hmem : ∀ α : ℂ, MemLp (fun x => A ψ x - α * ψ x) 2 := fun α =>
    hAψ.sub (hψ.const_mul α)
  unfold dispersion
  constructor
  · intro h
    refine ⟨expectation A ψ, ?_⟩
    have := (l2Norm_eq_zero_iff _ (hmem _)).mp h
    filter_upwards [this] with x hx
    simpa [sub_eq_zero] using hx
  · rintro ⟨α, hα⟩
    have hself : l2Inner ψ ψ ≠ 0 := by
      rw [l2Inner_self]
      intro h0
      apply hne
      unfold l2Norm
      have : (∫ x, ‖ψ x‖ ^ 2 : ℝ) = 0 := by exact_mod_cast h0
      rw [this, Real.sqrt_zero]
    have hE : expectation A ψ = α := by
      unfold expectation
      have : l2Inner (A ψ) ψ = α * l2Inner ψ ψ := by
        unfold l2Inner
        rw [← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [hα] with x hx
        rw [hx]; ring
      rw [this, mul_div_assoc, div_self hself, mul_one]
    rw [hE]
    refine (l2Norm_eq_zero_iff _ (hmem α)).mpr ?_
    filter_upwards [hα] with x hx
    simp [hx]

set_option maxHeartbeats 2000000 in
theorem mom_symm {n : ℕ} (hbar : ℝ) (j : Fin n) (ψ φ : WaveFn n)
    (hψ : InMomentumDomain ψ) (hφ : InMomentumDomain φ) :
    l2Inner (momentumOp hbar j ψ) φ = l2Inner ψ (momentumOp hbar j φ) := by
  obtain ⟨hψc, hψs⟩ := hψ
  obtain ⟨hφc, hφs⟩ := hφ
  set v : Rn n := EuclideanSpace.single j 1
  set c : ℂ := -(Complex.I * (hbar : ℂ))
  set φb : WaveFn n := fun x => (starRingEnd ℂ) (φ x) with hφb
  have hφbc : ContDiff ℝ 1 φb := Complex.conjCLE.contDiff.comp hφc
  have hφbs : HasCompactSupport φb := hφs.comp_left (by simp)
  have hdφb : ∀ x, fderiv ℝ φb x v = (starRingEnd ℂ) (fderiv ℝ φ x v) := by
    intro x
    have h := Complex.conjCLE.hasFDerivAt.comp x ((hφc.differentiable one_ne_zero) x).hasFDerivAt
    rw [show φb = Complex.conjCLE ∘ φ from rfl, h.fderiv]
    simp
  have hcont_dψ : Continuous fun x => fderiv ℝ ψ x v :=
    (hψc.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcont_dφb : Continuous fun x => fderiv ℝ φb x v :=
    (hφbc.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hsupp_dψ : HasCompactSupport fun x => fderiv ℝ ψ x v := by
    have := hψs.fderiv (𝕜 := ℝ)
    exact this.comp_left (g := fun L => L v) (by simp)
  have hsupp_dφb : HasCompactSupport fun x => fderiv ℝ φb x v := by
    have := hφbs.fderiv (𝕜 := ℝ)
    exact this.comp_left (g := fun L => L v) (by simp)
  have i1 : Integrable (fun x => fderiv ℝ ψ x v * φb x) :=
    (hcont_dψ.mul hφbc.continuous).integrable_of_hasCompactSupport (hsupp_dψ.mul_right)
  have i2 : Integrable (fun x => ψ x * fderiv ℝ φb x v) :=
    (hψc.continuous.mul hcont_dφb).integrable_of_hasCompactSupport (hsupp_dφb.mul_left)
  have i3 : Integrable (fun x => ψ x * φb x) :=
    (hψc.continuous.mul hφbc.continuous).integrable_of_hasCompactSupport (hφbs.mul_left)
  have ibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) i1 i2 i3
    (fun x _ => (hψc.differentiable one_ne_zero) x) (fun x _ => (hφbc.differentiable one_ne_zero) x)
  unfold l2Inner momentumOp
  have lhs : ∫ x, c * fderiv ℝ ψ x v * (starRingEnd ℂ) (φ x) =
      c * ∫ x, fderiv ℝ ψ x v * φb x := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hφb]; ring
  have rhs : ∫ x, ψ x * (starRingEnd ℂ) (c * fderiv ℝ φ x v) =
      (starRingEnd ℂ) c * ∫ x, ψ x * fderiv ℝ φb x v := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hdφb, map_mul]; ring
  change ∫ x, c * fderiv ℝ ψ x v * (starRingEnd ℂ) (φ x) =
    ∫ x, ψ x * (starRingEnd ℂ) (c * fderiv ℝ φ x v)
  rw [lhs, rhs, ibp]
  have hc : (starRingEnd ℂ) c = -c := by simp [c, Complex.conj_ofReal]
  rw [hc]; ring

end LopesQM

open LopesQM

theorem solution {n : ℕ} (hbar : ℝ) (hhbar : 0 < hbar) (j k : Fin n) :
    (∀ ψ : WaveFn n, ∀ x : Rn n,
        commutator (positionOp k) (positionOp j) ψ x = 0) ∧
    (∀ ψ : WaveFn n, ContDiff ℝ 2 ψ → ∀ x : Rn n,
        commutator (momentumOp hbar k) (momentumOp hbar j) ψ x = 0) ∧
    (∀ ψ : WaveFn n, Differentiable ℝ ψ → ∀ x : Rn n,
        Complex.I / (hbar : ℂ) * commutator (momentumOp hbar j) (positionOp j) ψ x = ψ x) ∧
    (j ≠ k → ∀ ψ : WaveFn n, Differentiable ℝ ψ → ∀ x : Rn n,
        Complex.I / (hbar : ℂ) * commutator (momentumOp hbar j) (positionOp k) ψ x = 0) := by
  exact ccr hbar hhbar j k
