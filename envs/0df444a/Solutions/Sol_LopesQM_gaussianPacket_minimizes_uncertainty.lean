-- Prove2me | solution 1 for LopesQM.gaussianPacket_minimizes_uncertainty
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T00:30:23.718438+00:00
-- url     : https://prove2.me/submissions/00a502fc-02b1-4f54-9ac3-c0a09af412b1

import Mathlib
import Definitions.Def_LopesQM_Defs
open MeasureTheory
open ProbabilityTheory

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


/-- Cauchy–Schwarz for the book's inner product. -/
lemma norm_l2Inner_le {n : ℕ} (u w : WaveFn n) (hu : Continuous u) (hus : HasCompactSupport u)
    (hw : Continuous w) (hws : HasCompactSupport w) :
    ‖l2Inner u w‖ ≤ l2Norm u * l2Norm w := by
  unfold l2Inner l2Norm
  have hmu : MemLp (fun x => ‖u x‖) (ENNReal.ofReal 2) :=
    (hu.norm.memLp_of_hasCompactSupport hus.norm)
  have hmw : MemLp (fun x => ‖w x‖) (ENNReal.ofReal 2) :=
    (hw.norm.memLp_of_hasCompactSupport hws.norm)
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun x => norm_nonneg (u x))
    (Filter.Eventually.of_forall fun x => norm_nonneg (w x)) hmu hmw
  calc ‖∫ x, u x * (starRingEnd ℂ) (w x)‖ ≤ ∫ x, ‖u x * (starRingEnd ℂ) (w x)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ x, ‖u x‖ * ‖w x‖ := by congr 1; funext x; rw [norm_mul, Complex.norm_conj]
    _ ≤ (∫ x, ‖u x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) * (∫ x, ‖w x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := hH
    _ = Real.sqrt (∫ x, ‖u x‖ ^ 2) * Real.sqrt (∫ x, ‖w x‖ ^ 2) := by
        simp only [Real.rpow_two, Real.sqrt_eq_rpow, one_div]

set_option maxHeartbeats 4000000 in
theorem heis {n : ℕ} (hbar : ℝ) (hhbar : 0 < hbar) (j : Fin n)
    (ψ : WaveFn n) (hX : InPositionDomain j ψ) (hP : InMomentumDomain ψ)
    (hnorm : l2Norm ψ = 1) :
    dispersion (positionOp j) ψ * dispersion (momentumOp hbar j) ψ ≥ hbar / 2 := by
  obtain ⟨hψc, hψs⟩ := hP
  have hψcont : Continuous ψ := hψc.continuous
  have hψd : Differentiable ℝ ψ := hψc.differentiable one_ne_zero
  set v : Rn n := EuclideanSpace.single j 1 with hv
  set c : ℂ := -(Complex.I * (hbar : ℂ)) with hc
  -- normalisation
  have h1 : ∫ x, ‖ψ x‖ ^ 2 = 1 := Real.sqrt_eq_one.mp hnorm
  have hself : l2Inner ψ ψ = 1 := by rw [l2Inner_self, h1]; simp
  -- the coordinate function and continuity facts
  set xc : Rn n → ℝ := fun x => x j with hxc
  have hxcc : Continuous xc := (EuclideanSpace.proj j).continuous
  set a : ℝ := ∫ x, xc x * ‖ψ x‖ ^ 2 with ha
  have hα : expectation (positionOp j) ψ = (a : ℂ) := by
    unfold expectation
    rw [hself, div_one]
    unfold l2Inner positionOp
    have e : (fun x => ((x j : ℝ) : ℂ) * ψ x * (starRingEnd ℂ) (ψ x)) =
        fun x => ((xc x * ‖ψ x‖ ^ 2 : ℝ) : ℂ) := by
      funext x
      rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast; ring
    rw [e]
    exact integral_ofReal
  set β := expectation (momentumOp hbar j) ψ
  set u : WaveFn n := fun x => positionOp j ψ x - (a : ℂ) * ψ x with hu
  set w : WaveFn n := fun x => momentumOp hbar j ψ x - β * ψ x with hw
  have hdX : dispersion (positionOp j) ψ = l2Norm u := by
    unfold dispersion; rw [hα]
  have hdP : dispersion (momentumOp hbar j) ψ = l2Norm w := rfl
  -- regularity of u and w
  have hdψc : Continuous fun x => fderiv ℝ ψ x v :=
    (hψc.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdψs : HasCompactSupport fun x => fderiv ℝ ψ x v := by
    have := hψs.fderiv (𝕜 := ℝ)
    exact this.comp_left (g := fun L => L v) (by simp)
  have hu_eq : u = fun x => (((xc x - a : ℝ)) : ℂ) * ψ x := by
    funext x; simp only [hu, positionOp, hxc]; push_cast; ring
  have hxac : Continuous fun x : Rn n => (((xc x - a : ℝ)) : ℂ) :=
    Complex.continuous_ofReal.comp (hxcc.sub continuous_const)
  have huc : Continuous u := by rw [hu_eq]; exact hxac.mul hψcont
  have hus : HasCompactSupport u := by rw [hu_eq]; exact hψs.mul_left
  have hwc : Continuous w :=
    (continuous_const.mul hdψc).sub (continuous_const.mul hψcont)
  have hws : HasCompactSupport w := by
    have h1 : HasCompactSupport (momentumOp hbar j ψ) := hdψs.mul_left
    have h2 : HasCompactSupport fun x => β * ψ x := hψs.mul_left
    exact h1.sub h2
  -- the key identity via integration by parts
  set φb : WaveFn n := fun x => (starRingEnd ℂ) (ψ x) with hφb
  have hφbd : Differentiable ℝ φb :=
    Complex.conjCLE.differentiable.comp hψd
  have hdφb : ∀ x, fderiv ℝ φb x v = (starRingEnd ℂ) (fderiv ℝ ψ x v) := by
    intro x
    have h := Complex.conjCLE.hasFDerivAt.comp x (hψd x).hasFDerivAt
    rw [show φb = Complex.conjCLE ∘ ψ from rfl, h.fderiv]
    simp
  set F : Rn n → ℂ := fun x => (((xc x - a : ℝ)) : ℂ) with hF
  set G : Rn n → ℂ := fun x => ψ x * φb x with hG
  have hFd : ∀ x, HasFDerivAt F (Complex.ofRealCLM.comp (EuclideanSpace.proj j)) x := by
    intro x
    have h := ((Complex.ofRealCLM.comp (EuclideanSpace.proj j)).hasFDerivAt (x := x)).sub_const
      ((a : ℝ) : ℂ)
    have eF : F = fun y => (Complex.ofRealCLM.comp (EuclideanSpace.proj j)) y - ((a : ℝ) : ℂ) := by
      funext y; simp [hF, hxc]
    rw [eF]; exact h
  have hdF : ∀ x, fderiv ℝ F x v = 1 := by
    intro x; rw [(hFd x).fderiv]; simp [hv]
  have hdG : ∀ x, fderiv ℝ G x v = fderiv ℝ ψ x v * φb x + ψ x * fderiv ℝ φb x v := by
    intro x
    have h := (hψd x).hasFDerivAt.mul (hφbd x).hasFDerivAt
    rw [show G = ψ * φb from rfl, h.fderiv]
    simp [smul_eq_mul]; ring
  have hGc : Continuous G := hψcont.mul (Complex.continuous_conj.comp hψcont)
  have hGs : HasCompactSupport G := hψs.mul_right
  have hdGc : Continuous fun x => fderiv ℝ G x v := by
    have : (fun x => fderiv ℝ G x v) =
        fun x => fderiv ℝ ψ x v * φb x + ψ x * (starRingEnd ℂ) (fderiv ℝ ψ x v) := by
      funext x; rw [hdG, hdφb]
    rw [this]
    exact (hdψc.mul (Complex.continuous_conj.comp hψcont)).add
      (hψcont.mul (Complex.continuous_conj.comp hdψc))
  have hdGs : HasCompactSupport fun x => fderiv ℝ G x v := by
    have := hGs.fderiv (𝕜 := ℝ)
    exact this.comp_left (g := fun L => L v) (by simp)
  have hFc : Continuous F := hxac
  have i1 : Integrable (fun x => fderiv ℝ F x v * G x) := by
    have : (fun x => fderiv ℝ F x v * G x) = G := by funext x; rw [hdF, one_mul]
    rw [this]; exact hGc.integrable_of_hasCompactSupport hGs
  have i2 : Integrable (fun x => F x * fderiv ℝ G x v) :=
    (hFc.mul hdGc).integrable_of_hasCompactSupport hdGs.mul_left
  have i3 : Integrable (fun x => F x * G x) :=
    (hFc.mul hGc).integrable_of_hasCompactSupport hGs.mul_left
  have ibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) i1 i2 i3
    (fun x _ => (hFd x).differentiableAt) (fun x _ => (hψd x).mul (hφbd x))
  have hGint : ∫ x, G x = 1 := by
    rw [← hself]; rfl
  have hibp' : ∫ x, F x * fderiv ℝ G x v = -1 := by
    rw [ibp]
    have : (fun x => fderiv ℝ F x v * G x) = G := by funext x; rw [hdF, one_mul]
    rw [this, hGint]
  -- I1 := ∫ F ψ conj(∂ψ)
  set I1 : ℂ := ∫ x, F x * ψ x * (starRingEnd ℂ) (fderiv ℝ ψ x v) with hI1
  have hA_int : Integrable fun x => F x * ψ x * (starRingEnd ℂ) (fderiv ℝ ψ x v) :=
    ((hFc.mul hψcont).mul (Complex.continuous_conj.comp hdψc)).integrable_of_hasCompactSupport
      (hψs.mul_left.mul_right)
  have hB_int : Integrable fun x => F x * (fderiv ℝ ψ x v * φb x) :=
    (hFc.mul (hdψc.mul (Complex.continuous_conj.comp hψcont))).integrable_of_hasCompactSupport
      ((hdψs.mul_right).mul_left)
  have hconjI1 : ∫ x, F x * (fderiv ℝ ψ x v * φb x) = (starRingEnd ℂ) I1 := by
    rw [hI1, ← integral_conj]
    congr 1; funext x
    simp only [hF, hφb, map_mul, Complex.conj_ofReal, Complex.conj_conj]
    ring
  have hsum : I1 + (starRingEnd ℂ) I1 = -1 := by
    rw [← hibp', ← hconjI1, hI1, ← integral_add hA_int hB_int]
    congr 1; funext x
    rw [hdG, hdφb]; ring
  have hre : I1.re = -1 / 2 := by
    have := congrArg Complex.re hsum
    simp at this
    linarith
  -- ⟨u, w⟩ = conj c * I1
  have hJ : ∫ x, F x * ψ x * (starRingEnd ℂ) (ψ x) = 0 := by
    have e : (fun x => F x * ψ x * (starRingEnd ℂ) (ψ x)) =
        fun x => (((xc x * ‖ψ x‖ ^ 2 - a * ‖ψ x‖ ^ 2 : ℝ)) : ℂ) := by
      funext x
      simp only [hF]
      rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast; ring
    have hre0 : (∫ x, (((xc x * ‖ψ x‖ ^ 2 - a * ‖ψ x‖ ^ 2 : ℝ)) : ℂ)) =
        (((∫ x, (xc x * ‖ψ x‖ ^ 2 - a * ‖ψ x‖ ^ 2)) : ℝ) : ℂ) := integral_ofReal
    rw [e, hre0]
    have hN : HasCompactSupport fun x => ‖ψ x‖ ^ 2 :=
      hψs.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
    have hi1 : Integrable fun x => xc x * ‖ψ x‖ ^ 2 :=
      (hxcc.mul (hψcont.norm.pow 2)).integrable_of_hasCompactSupport
        hN.mul_left
    have hi2 : Integrable fun x => a * ‖ψ x‖ ^ 2 :=
      (continuous_const.mul (hψcont.norm.pow 2)).integrable_of_hasCompactSupport
        hN.mul_left
    rw [integral_sub hi1 hi2, integral_const_mul, h1, ← ha]
    simp
  have hinner : l2Inner u w = (starRingEnd ℂ) c * I1 := by
    have hJint : Integrable fun x => F x * ψ x * (starRingEnd ℂ) (ψ x) :=
      ((hFc.mul hψcont).mul (Complex.continuous_conj.comp hψcont)).integrable_of_hasCompactSupport
        (hψs.mul_left.mul_right)
    have e : (fun x => u x * (starRingEnd ℂ) (w x)) = fun x =>
        (starRingEnd ℂ) c * (F x * ψ x * (starRingEnd ℂ) (fderiv ℝ ψ x v)) -
          (starRingEnd ℂ) β * (F x * ψ x * (starRingEnd ℂ) (ψ x)) := by
      funext x
      rw [hu_eq]
      simp only [hw, momentumOp, hF, map_sub, map_mul]
      ring
    unfold l2Inner
    rw [e, integral_sub (hA_int.const_mul _) (hJint.const_mul _), integral_const_mul,
      integral_const_mul, hJ, ← hI1]
    ring
  have hlow : hbar / 2 ≤ ‖l2Inner u w‖ := by
    rw [hinner, norm_mul, Complex.norm_conj, hc, norm_neg, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_of_nonneg hhbar.le]
    have : |I1.re| ≤ ‖I1‖ := Complex.abs_re_le_norm I1
    rw [hre] at this
    norm_num at this
    nlinarith
  have hup := norm_l2Inner_le u w huc hus hwc hws
  rw [hdX, hdP]
  linarith


lemma int_prod {n : ℕ} (h : Fin n → ℝ → ℂ) :
    ∫ x : Rn n, ∏ i, h i (x i) = ∏ i, ∫ t, h i t := by
  have e := (PiLp.volume_preserving_toLp (Fin n)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding (fun x : Rn n => ∏ i, h i (x i))
  rw [← e]
  simp only [PiLp.toLp_apply]
  exact integral_fintype_prod_eq_prod (fun i t => h i t)

/-- `∫ g(x_j) ∏ᵢ ρᵢ(xᵢ) = ∫ g ρⱼ` when every `ρᵢ` integrates to one. -/
lemma int_single {n : ℕ} (ρ : Fin n → ℝ → ℂ) (hρ : ∀ i, ∫ t, ρ i t = 1) (j : Fin n)
    (g : ℝ → ℂ) :
    ∫ x : Rn n, g (x j) * ∏ i, ρ i (x i) = ∫ t, g t * ρ j t := by
  classical
  set h : Fin n → ℝ → ℂ := Function.update ρ j (fun t => g t * ρ j t) with hh
  have e : ∀ x : Rn n, g (x j) * ∏ i, ρ i (x i) = ∏ i, h i (x i) := by
    intro x
    rw [← Finset.mul_prod_erase Finset.univ (fun i => ρ i (x i)) (Finset.mem_univ j),
      ← Finset.mul_prod_erase Finset.univ (fun i => h i (x i)) (Finset.mem_univ j)]
    simp only [hh, Function.update_self]
    rw [mul_assoc]
    congr 2
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  simp_rw [e]
  rw [int_prod, ← Finset.mul_prod_erase Finset.univ (fun i => ∫ t, h i t) (Finset.mem_univ j)]
  simp only [hh, Function.update_self]
  rw [Finset.prod_eq_one, mul_one]
  intro i hi
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi), hρ]


section Packet

variable {n : ℕ} (hbar a : ℝ) (x0 p0 : Rn n)

/-- `‖ψ x‖²` of the Gaussian packet factorizes into one-dimensional Gaussian densities. -/
lemma packet_normSq (ha : 0 < a) (x : Rn n) :
    ‖gaussianPacket hbar a x0 p0 x‖ ^ 2 =
      ∏ i, gaussianPDFReal (x0 i) (a ^ 2).toNNReal (x i) := by
  have hb : 0 < 2 * Real.pi * a ^ 2 := by positivity
  unfold gaussianPacket
  rw [norm_mul, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one, Complex.norm_exp_ofReal,
    Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  simp only [gaussianPDFReal, Real.coe_toNNReal _ (sq_nonneg a)]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum]
  have hsum : ∑ i : Fin n, -(x i - x0 i) ^ 2 / (2 * a ^ 2) = -(‖x - x0‖ ^ 2) / (2 * a ^ 2) := by
    have e : ‖x - x0‖ ^ 2 = ∑ i : Fin n, (x i - x0 i) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]; simp [Real.norm_eq_abs, sq_abs]
    rw [e]
    simp only [neg_div, Finset.sum_div, Finset.sum_neg_distrib]
  rw [hsum, mul_pow, ← Real.exp_nat_mul]
  have hexp : ((2 : ℕ) : ℝ) * (-(‖x - x0‖ ^ 2) / (4 * a ^ 2)) = -(‖x - x0‖ ^ 2) / (2 * a ^ 2) := by
    field_simp; ring
  rw [hexp]
  congr 1
  have key : ∀ b : ℝ, 0 < b → ((b ^ ((n : ℝ) / 4))⁻¹) ^ 2 = ((Real.sqrt b)⁻¹) ^ n := by
    intro b hb
    rw [inv_pow, inv_pow, ← Real.rpow_natCast (b ^ ((n : ℝ) / 4)) 2, ← Real.rpow_mul hb.le,
      Real.sqrt_eq_rpow, ← Real.rpow_natCast (b ^ (1 / 2 : ℝ)) n, ← Real.rpow_mul hb.le]
    congr 2
    push_cast; ring
  exact key _ hb

/-- The complex density `ψ · conj ψ` as a product of one-dimensional densities. -/
lemma packet_mul_conj (ha : 0 < a) (x : Rn n) :
    gaussianPacket hbar a x0 p0 x * (starRingEnd ℂ) (gaussianPacket hbar a x0 p0 x) =
      ∏ i, ((gaussianPDFReal (x0 i) (a ^ 2).toNNReal (x i) : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, packet_normSq hbar a x0 p0 ha]
  push_cast; rfl

lemma rho_int (ha : 0 < a) (i : Fin n) :
    ∫ t, ((gaussianPDFReal (x0 i) (a ^ 2).toNNReal t : ℝ) : ℂ) = 1 := by
  have hv : (a ^ 2).toNNReal ≠ 0 := by
    rw [ne_eq, Real.toNNReal_eq_zero, not_le]; positivity
  have h := integral_gaussianPDFReal_eq_one (x0 i) hv
  calc ∫ t, ((gaussianPDFReal (x0 i) (a ^ 2).toNNReal t : ℝ) : ℂ)
      = ((∫ t, gaussianPDFReal (x0 i) (a ^ 2).toNNReal t : ℝ) : ℂ) := integral_ofReal
    _ = 1 := by rw [h]; simp

/-- One-dimensional integrals against the density reduce to Gaussian expectations. -/
lemma int_one_dim (ha : 0 < a) (j : Fin n) (g : ℝ → ℂ) :
    ∫ x : Rn n, g (x j) * (gaussianPacket hbar a x0 p0 x *
        (starRingEnd ℂ) (gaussianPacket hbar a x0 p0 x)) =
      ∫ t, g t ∂(gaussianReal (x0 j) (a ^ 2).toNNReal) := by
  have hv : (a ^ 2).toNNReal ≠ 0 := by
    rw [ne_eq, Real.toNNReal_eq_zero, not_le]; positivity
  simp_rw [packet_mul_conj hbar a x0 p0 ha]
  rw [int_single _ (rho_int a x0 ha) j g, integral_gaussianReal_eq_integral_smul hv]
  congr 1; funext t
  rw [Complex.real_smul]; ring


lemma packet_deriv (ha : 0 < a) (j : Fin n) (x : Rn n) :
    fderiv ℝ (gaussianPacket hbar a x0 p0) x (EuclideanSpace.single j 1) =
      gaussianPacket hbar a x0 p0 x *
        (((-(x j - x0 j) / (2 * a ^ 2) : ℝ) : ℂ) + Complex.I * ((p0 j / hbar : ℝ) : ℂ)) := by
  set C : ℂ := ((((2 * Real.pi * a ^ 2) ^ ((n : ℝ) / 4))⁻¹ : ℝ) : ℂ)
  set A : Rn n → ℝ := fun y => -(‖y - x0‖ ^ 2) / (4 * a ^ 2) with hAdef
  set B : Rn n → ℝ := fun y => inner ℝ p0 y / hbar with hBdef
  have hψ : gaussianPacket hbar a x0 p0 =
      fun y => C * Complex.exp ((A y : ℝ) : ℂ) * Complex.exp (Complex.I * ((B y : ℝ) : ℂ)) := rfl
  have hN := ((hasFDerivAt_id x).sub_const x0).norm_sq
  have hA : HasFDerivAt A ((-(1 / (4 * a ^ 2))) •
      (2 • (innerSL ℝ (id x - x0)).comp (ContinuousLinearMap.id ℝ (Rn n)))) x := by
    have := hN.const_smul (-(1 / (4 * a ^ 2)))
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    simp only [hAdef, Pi.smul_apply, smul_eq_mul, id]
    ring
  have hB : HasFDerivAt B ((1 / hbar) • innerSL ℝ p0) x := by
    have := ((innerSL ℝ p0).hasFDerivAt (x := x)).const_smul (1 / hbar)
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    simp only [hBdef, Pi.smul_apply, smul_eq_mul, innerSL_apply_apply]
    ring
  have hE1 := (Complex.ofRealCLM.hasFDerivAt.comp x hA).cexp
  have hE2 := ((Complex.ofRealCLM.hasFDerivAt.comp x hB).const_mul Complex.I).cexp
  have hfull := (hE1.const_mul C).mul hE2
  rw [hψ, show (fun y => C * Complex.exp ((A y : ℝ) : ℂ) * Complex.exp (Complex.I * ((B y : ℝ) : ℂ)))
      = ((fun y => C * Complex.exp ((⇑Complex.ofRealCLM ∘ A) y)) *
          fun y => Complex.exp (Complex.I * (⇑Complex.ofRealCLM ∘ B) y)) from rfl, hfull.fderiv]
  simp [smul_eq_mul, innerSL_apply_apply, EuclideanSpace.inner_single_right, hAdef, hBdef]
  ring

end Packet

theorem gp_main {n : ℕ} (hbar : ℝ) (hhbar : 0 < hbar)
    (a : ℝ) (ha : 0 < a) (x0 p0 : Rn n) (j : Fin n) :
    l2Norm (gaussianPacket hbar a x0 p0) = 1 ∧
    expectation (positionOp j) (gaussianPacket hbar a x0 p0) = ((x0 j : ℝ) : ℂ) ∧
    expectation (momentumOp hbar j) (gaussianPacket hbar a x0 p0) = ((p0 j : ℝ) : ℂ) ∧
    dispersion (positionOp j) (gaussianPacket hbar a x0 p0) = a ∧
    dispersion (positionOp j) (gaussianPacket hbar a x0 p0) *
      dispersion (momentumOp hbar j) (gaussianPacket hbar a x0 p0) = hbar / 2 := by
  set ψ := gaussianPacket hbar a x0 p0 with hψdef
  set γ := gaussianReal (x0 j) (a ^ 2).toNNReal with hγ
  have hv : ((a ^ 2).toNNReal : ℝ) = a ^ 2 := Real.coe_toNNReal _ (sq_nonneg a)
  have hvne : (a ^ 2).toNNReal ≠ 0 := by
    rw [ne_eq, Real.toNNReal_eq_zero, not_le]; positivity
  have hb : (hbar : ℂ) ≠ 0 := by exact_mod_cast hhbar.ne'
  have ha2 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  -- basic Gaussian moments (complex-valued)
  have hint1 : Integrable (fun t : ℝ => ((t : ℝ) : ℂ)) γ :=
    ((memLp_id_gaussianReal (μ := x0 j) (v := (a ^ 2).toNNReal) 1).integrable le_rfl).ofReal
  have m0 : ∫ t, (1 : ℂ) ∂γ = 1 := by simp
  have m1 : ∫ t : ℝ, ((t : ℝ) : ℂ) ∂γ = ((x0 j : ℝ) : ℂ) := by
    calc ∫ t : ℝ, ((t : ℝ) : ℂ) ∂γ = ((∫ t, t ∂γ : ℝ) : ℂ) := integral_ofReal
      _ = _ := by rw [hγ, integral_id_gaussianReal]
  have m2 : ∫ t, (((t - x0 j) ^ 2 : ℝ) : ℂ) ∂γ = ((a ^ 2 : ℝ) : ℂ) := by
    rw [show (∫ t, (((t - x0 j) ^ 2 : ℝ) : ℂ) ∂γ) = ((∫ t, (t - x0 j) ^ 2 ∂γ : ℝ) : ℂ) from
      integral_ofReal]
    have := variance_id_gaussianReal (μ := x0 j) (v := (a ^ 2).toNNReal)
    rw [variance_eq_integral measurable_id.aemeasurable] at this
    simp only [id] at this
    rw [integral_id_gaussianReal] at this
    rw [hγ, this, hv]
  -- real integrals against the density
  have hreal : ∀ g : ℝ → ℝ, ∫ x : Rn n, g (x j) * ‖ψ x‖ ^ 2 = ∫ t, g t ∂γ := by
    intro g
    have h := int_one_dim hbar a x0 p0 ha j (fun t => ((g t : ℝ) : ℂ))
    have e : (fun x : Rn n => ((g (x j) : ℝ) : ℂ) * (ψ x * (starRingEnd ℂ) (ψ x))) =
        fun x => (((g (x j) * ‖ψ x‖ ^ 2) : ℝ) : ℂ) := by
      funext x; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    rw [e] at h
    have h2 : (((∫ x : Rn n, g (x j) * ‖ψ x‖ ^ 2) : ℝ) : ℂ) = (((∫ t, g t ∂γ) : ℝ) : ℂ) := by
      calc (((∫ x : Rn n, g (x j) * ‖ψ x‖ ^ 2) : ℝ) : ℂ)
          = ∫ x : Rn n, (((g (x j) * ‖ψ x‖ ^ 2) : ℝ) : ℂ) := integral_ofReal.symm
        _ = ∫ t, ((g t : ℝ) : ℂ) ∂γ := h
        _ = _ := integral_ofReal
    exact_mod_cast h2
  have hn1 : ∫ x : Rn n, ‖ψ x‖ ^ 2 = 1 := by
    have := hreal (fun _ => 1)
    simp only [one_mul] at this
    rw [this]; simp
  have hself : l2Inner ψ ψ = 1 := by rw [l2Inner_self, hn1]; simp
  -- momentum operator on the packet
  set κ : ℝ → ℂ := fun t => Complex.I * ((hbar / (2 * a ^ 2) : ℝ) : ℂ) * ((t - x0 j : ℝ) : ℂ)
    with hκ
  have hP : ∀ x, momentumOp hbar j ψ x = ψ x * (κ (x j) + ((p0 j : ℝ) : ℂ)) := by
    intro x
    unfold momentumOp
    rw [hψdef, packet_deriv hbar a x0 p0 ha j x]
    simp only [hκ]
    push_cast
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold l2Norm; rw [hn1, Real.sqrt_one]
  · unfold expectation
    rw [hself, div_one]
    unfold l2Inner positionOp
    have := int_one_dim hbar a x0 p0 ha j (fun t : ℝ => ((t : ℝ) : ℂ))
    simp only [mul_assoc] at this ⊢
    rw [this, m1]
  · unfold expectation
    rw [hself, div_one]
    unfold l2Inner
    have e : (fun x => momentumOp hbar j ψ x * (starRingEnd ℂ) (ψ x)) =
        fun x => (κ (x j) + ((p0 j : ℝ) : ℂ)) * (ψ x * (starRingEnd ℂ) (ψ x)) := by
      funext x; rw [hP]; ring
    rw [e, int_one_dim hbar a x0 p0 ha j (fun t => κ t + ((p0 j : ℝ) : ℂ))]
    have hκint : Integrable (fun t => κ t) γ := by
      simp only [hκ]
      have : Integrable (fun t : ℝ => ((t : ℝ) : ℂ) - ((x0 j : ℝ) : ℂ)) γ :=
        hint1.sub (integrable_const _)
      refine (this.const_mul (Complex.I * ((hbar / (2 * a ^ 2) : ℝ) : ℂ))).congr
        (Filter.Eventually.of_forall fun t => ?_)
      push_cast; ring
    rw [integral_add hκint (integrable_const _)]
    have : ∫ t, κ t ∂γ = 0 := by
      simp only [hκ]
      rw [integral_const_mul]
      have e2 : (fun t : ℝ => (((t - x0 j) : ℝ) : ℂ)) = fun t : ℝ => ((t : ℝ) : ℂ) - ((x0 j : ℝ) : ℂ) := by
        funext t; push_cast; ring
      rw [e2, integral_sub hint1 (integrable_const _), m1]
      simp
    rw [this]; simp
  · -- dispersion of X
    unfold dispersion
    have hEX : expectation (positionOp j) ψ = ((x0 j : ℝ) : ℂ) := by
      unfold expectation
      rw [hself, div_one]
      unfold l2Inner positionOp
      have := int_one_dim hbar a x0 p0 ha j (fun t : ℝ => ((t : ℝ) : ℂ))
      simp only [mul_assoc] at this ⊢
      rw [this, m1]
    rw [hEX]
    unfold l2Norm
    have e : (fun x : Rn n => ‖positionOp j ψ x - ((x0 j : ℝ) : ℂ) * ψ x‖ ^ 2) =
        fun x => (x j - x0 j) ^ 2 * ‖ψ x‖ ^ 2 := by
      funext x
      simp only [positionOp]
      rw [← sub_mul, norm_mul, mul_pow, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        sq_abs]
    rw [e, hreal (fun t => (t - x0 j) ^ 2)]
    have : ∫ t, (t - x0 j) ^ 2 ∂γ = a ^ 2 := by exact_mod_cast m2
    rw [this, Real.sqrt_sq ha.le]
  · -- product of dispersions
    unfold dispersion
    have hEX : expectation (positionOp j) ψ = ((x0 j : ℝ) : ℂ) := by
      unfold expectation
      rw [hself, div_one]
      unfold l2Inner positionOp
      have := int_one_dim hbar a x0 p0 ha j (fun t : ℝ => ((t : ℝ) : ℂ))
      simp only [mul_assoc] at this ⊢
      rw [this, m1]
    have hEP : expectation (momentumOp hbar j) ψ = ((p0 j : ℝ) : ℂ) := by
      unfold expectation
      rw [hself, div_one]
      unfold l2Inner
      have e : (fun x => momentumOp hbar j ψ x * (starRingEnd ℂ) (ψ x)) =
          fun x => (κ (x j) + ((p0 j : ℝ) : ℂ)) * (ψ x * (starRingEnd ℂ) (ψ x)) := by
        funext x; rw [hP]; ring
      rw [e, int_one_dim hbar a x0 p0 ha j (fun t => κ t + ((p0 j : ℝ) : ℂ))]
      have hκint : Integrable (fun t => κ t) γ := by
        simp only [hκ]
        have : Integrable (fun t : ℝ => ((t : ℝ) : ℂ) - ((x0 j : ℝ) : ℂ)) γ :=
          hint1.sub (integrable_const _)
        refine (this.const_mul (Complex.I * ((hbar / (2 * a ^ 2) : ℝ) : ℂ))).congr
          (Filter.Eventually.of_forall fun t => ?_)
        push_cast; ring
      rw [integral_add hκint (integrable_const _)]
      have : ∫ t, κ t ∂γ = 0 := by
        simp only [hκ]
        rw [integral_const_mul]
        have e2 : (fun t : ℝ => (((t - x0 j) : ℝ) : ℂ)) =
            fun t : ℝ => ((t : ℝ) : ℂ) - ((x0 j : ℝ) : ℂ) := by
          funext t; push_cast; ring
        rw [e2, integral_sub hint1 (integrable_const _), m1]
        simp
      rw [this]; simp
    rw [hEX, hEP]
    unfold l2Norm
    have e1 : (fun x : Rn n => ‖positionOp j ψ x - ((x0 j : ℝ) : ℂ) * ψ x‖ ^ 2) =
        fun x => (x j - x0 j) ^ 2 * ‖ψ x‖ ^ 2 := by
      funext x
      simp only [positionOp]
      rw [← sub_mul, norm_mul, mul_pow, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        sq_abs]
    have e2 : (fun x : Rn n => ‖momentumOp hbar j ψ x - ((p0 j : ℝ) : ℂ) * ψ x‖ ^ 2) =
        fun x => ((hbar / (2 * a ^ 2)) ^ 2 * (x j - x0 j) ^ 2) * ‖ψ x‖ ^ 2 := by
      funext x
      rw [hP]
      have : ψ x * (κ (x j) + ((p0 j : ℝ) : ℂ)) - ((p0 j : ℝ) : ℂ) * ψ x =
          (Complex.I * (((hbar / (2 * a ^ 2)) * (x j - x0 j) : ℝ) : ℂ)) * ψ x := by
        simp only [hκ]; push_cast; ring
      rw [this, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        mul_pow, sq_abs]
      ring
    rw [e1, e2, hreal (fun t => (t - x0 j) ^ 2),
      hreal (fun t => (hbar / (2 * a ^ 2)) ^ 2 * (t - x0 j) ^ 2)]
    have h2 : ∫ t, (t - x0 j) ^ 2 ∂γ = a ^ 2 := by exact_mod_cast m2
    rw [integral_const_mul, h2, Real.sqrt_sq ha.le]
    have : (hbar / (2 * a ^ 2)) ^ 2 * a ^ 2 = (hbar / (2 * a)) ^ 2 := by
      field_simp
    rw [this, Real.sqrt_sq (by positivity)]
    field_simp

end LopesQM

open LopesQM

theorem solution {n : ℕ} (hbar : ℝ) (hhbar : 0 < hbar)
    (a : ℝ) (ha : 0 < a) (x0 p0 : Rn n) (j : Fin n) :
    l2Norm (gaussianPacket hbar a x0 p0) = 1 ∧
    expectation (positionOp j) (gaussianPacket hbar a x0 p0) = ((x0 j : ℝ) : ℂ) ∧
    expectation (momentumOp hbar j) (gaussianPacket hbar a x0 p0) = ((p0 j : ℝ) : ℂ) ∧
    dispersion (positionOp j) (gaussianPacket hbar a x0 p0) = a ∧
    dispersion (positionOp j) (gaussianPacket hbar a x0 p0) *
      dispersion (momentumOp hbar j) (gaussianPacket hbar a x0 p0) = hbar / 2 := by
  exact gp_main hbar hhbar a ha x0 p0 j
