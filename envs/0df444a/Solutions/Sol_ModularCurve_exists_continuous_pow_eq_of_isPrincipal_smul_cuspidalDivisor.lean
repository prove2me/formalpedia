-- Prove2me | solution 1 for ModularCurve.exists_continuous_pow_eq_of_isPrincipal_smul_cuspidalDivisor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/3638a053-5071-5b38-8bf6-e2044f199927

import Definitions.Def_ModularCurve_EtaQuotient
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_NumberTheory_DedekindSum
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Complex.Polynomial.Basic
import Theorems.Thm_ModularForm_logEta_specialLinearGroup_smul
import Theorems.Thm_ModularForm_exp_logEta
import Theorems.Thm_ModularForm_continuous_logEta
import Theorems.Thm_ModularForm_logEta_add_intCast
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero
import Theorems.Thm_ModularCurve_smul_cuspidalDivisor_apply_eq_ord
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq
import Theorems.Thm_ModularCurve_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_hasSum_jq_qParam
import Theorems.Thm_ModularCurve_hasSum_qParam_mul_laurent
import Theorems.Thm_ModularCurve_hasSum_modularUnitSeries_qParam
import Theorems.Thm_ModularCurve_laurent_qParam_coeff_unique
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_E4_cube_div_discriminant_smul
import Theorems.Thm_ModularCurve_exists_sl2_heckeDiagMatrix_smul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_continuous_pow_eq_of_isPrincipal_smul_cuspidalDivisor
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false

noncomputable section

open Complex ModularGroup Filter

p2m_open "UpperHalfPlane~I"

open scoped ModularForm MatrixGroups Real Topology Manifold

local notation "𝕢" => Function.Periodic.qParam

namespace EtaBranch

def logEta (z : ℂ) : ℂ := π * I * z / 12 + ∑' n : ℕ, log (1 - ModularForm.eta_q n z)

private theorem _root_.EtaBranch.exp_logEta (z : ℍ) : exp (logEta z) = η (z : ℂ) := ModularForm.exp_logEta z

p2m_export "EtaBranch" "exp_logEta"
private theorem _root_.EtaBranch.continuous_logEta : Continuous fun τ : ℍ => logEta τ := ModularForm.continuous_logEta

p2m_export "EtaBranch" "continuous_logEta"
theorem logEta_add_int (z : ℂ) (m : ℤ) : logEta (z + m) = logEta z + π * I * m / 12 :=
  ModularForm.logEta_add_intCast z m

def phi (γ : SL(2, ℤ)) : ℚ :=
  ((γ 0 0 + γ 1 1 : ℤ) : ℚ) / (((γ 1 0).toNat : ℕ) : ℚ) - 12 * dedekindSum (γ 1 1) (γ 1 0).toNat

theorem logEta_smul (γ : SL(2, ℤ)) (hc : 0 < (γ 1 0 : ℤ)) (z : ℍ) :
    logEta ((γ • z : ℍ) : ℂ) = logEta z + log (-I * ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ))) / 2
      + π * I / 12 * (phi γ : ℂ) :=
  ModularForm.logEta_specialLinearGroup_smul γ hc z

lemma norm_eta_q (n : ℕ) (z : ℂ) : ‖ModularForm.eta_q n z‖ = Real.exp (-(2 * π * (n + 1) * z.im)) := by
  rw [ModularForm.eta_q_eq_cexp, norm_exp]
  congr 1
  simp [mul_re, mul_im]

lemma norm_eta_q_lt_one (n : ℕ) {z : ℂ} (hz : 0 < z.im) : ‖ModularForm.eta_q n z‖ < 1 := by
  rw [norm_eta_q, Real.exp_lt_one_iff]
  have : 0 < 2 * π * (n + 1) * z.im := by positivity
  linarith

lemma one_sub_eta_q_mem_slitPlane (n : ℕ) {z : ℂ} (hz : 0 < z.im) :
    1 - ModularForm.eta_q n z ∈ slitPlane := by
  rw [sub_eq_add_neg]
  exact mem_slitPlane_of_norm_lt_one (by rw [norm_neg]; exact norm_eta_q_lt_one n hz)

lemma differentiableOn_logEta {δ : ℝ} (hδ : 0 < δ) : DifferentiableOn ℂ logEta {z : ℂ | δ < z.im} := by
  have hopen : IsOpen {z : ℂ | δ < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hlin : Differentiable ℂ fun z : ℂ => π * I * z / 12 := by fun_prop
  refine hlin.differentiableOn.add ?_
  set r : ℝ := Real.exp (-(2 * π * δ)) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by rw [hr, Real.exp_lt_one_iff]; have := Real.pi_pos; nlinarith
  have hq : ∀ (n : ℕ) (z : ℂ), δ < z.im → ‖ModularForm.eta_q n z‖ ≤ r ^ (n + 1) := by
    intro n z hz
    rw [norm_eta_q, hr, ← Real.exp_nat_mul, Real.exp_le_exp]
    push_cast
    have : 0 < 2 * π * (n + 1) := by positivity
    nlinarith
  set C : ℝ := r * (1 - r)⁻¹ / 2 + 1 with hC
  have hC0 : 0 ≤ C := by
    have : 0 ≤ (1 - r)⁻¹ := inv_nonneg.2 (by linarith)
    positivity
  refine differentiableOn_tsum_of_summable_norm (u := fun n : ℕ => C * r ^ (n + 1)) ?_ (fun n => ?_)
    hopen ?_
  · exact (summable_geometric_of_lt_one hr0.le hr1).mul_left C |>.comp_injective (add_left_injective 1)
      |>.congr fun n => by simp [Function.comp, pow_succ]
  · have h1 : DifferentiableOn ℂ (fun z : ℂ => 1 - ModularForm.eta_q n z) {z : ℂ | δ < z.im} := by
      apply Differentiable.differentiableOn
      simp only [ModularForm.eta_q_eq_cexp]
      fun_prop
    exact h1.clog fun z hz => one_sub_eta_q_mem_slitPlane n (hδ.trans hz)
  · intro n z hz
    have hx1 : ‖ModularForm.eta_q n z‖ < 1 := norm_eta_q_lt_one n (hδ.trans hz)
    have hxr : ‖ModularForm.eta_q n z‖ ≤ r := by
      refine (hq n z hz).trans ?_
      calc r ^ (n + 1) ≤ r ^ 1 := pow_le_pow_of_le_one hr0.le hr1.le (Nat.le_add_left 1 n)
        _ = r := pow_one r
    have h := Complex.norm_log_one_add_le (z := -ModularForm.eta_q n z) (by rwa [norm_neg])
    rw [norm_neg, ← sub_eq_add_neg] at h
    refine h.trans ?_
    set x := ‖ModularForm.eta_q n z‖ with hx
    have hx0 : 0 ≤ x := norm_nonneg _
    have h1r : 0 < 1 - r := by linarith
    have hinv : (1 - x)⁻¹ ≤ (1 - r)⁻¹ := inv_anti₀ h1r (by linarith)
    calc x ^ 2 * (1 - x)⁻¹ / 2 + x ≤ x * r * (1 - r)⁻¹ / 2 + x := by
          have : x ^ 2 * (1 - x)⁻¹ ≤ x * r * (1 - r)⁻¹ := by
            rw [sq]
            exact mul_le_mul (mul_le_mul_of_nonneg_left hxr hx0) hinv (inv_nonneg.2 (by linarith))
              (by positivity)
          linarith
      _ = C * x := by rw [hC]; ring
      _ ≤ C * r ^ (n + 1) := mul_le_mul_of_nonneg_left (hq n z hz) hC0

lemma differentiableAt_logEta {z : ℂ} (hz : 0 < z.im) : DifferentiableAt ℂ logEta z := by
  have hδ : 0 < z.im / 2 := half_pos hz
  have hopen : IsOpen {w : ℂ | z.im / 2 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  exact (differentiableOn_logEta hδ).differentiableAt (hopen.mem_nhds (by show z.im / 2 < z.im; linarith))

section Branch

variable (ℓ : ℕ) [NeZero ℓ]

lemma coe_D_smul (τ : ℍ) : ((ModularForm.heckeDiagMatrix ℓ • τ : ℍ) : ℂ) = (ℓ : ℂ) * τ :=
  ModularForm.coe_heckeDiagMatrix_smul (NeZero.ne ℓ) τ

def Lg (τ : ℍ) : ℂ := logEta τ - logEta ((ModularForm.heckeDiagMatrix ℓ • τ : ℍ) : ℂ)

omit [NeZero ℓ] in
lemma continuous_Lg : Continuous (Lg ℓ) :=
  continuous_logEta.sub (continuous_logEta.comp (continuous_const_smul _))

lemma exp_Lg (τ : ℍ) : exp (Lg ℓ τ) = η (τ : ℂ) / η ((ℓ : ℂ) * τ) := by
  rw [Lg, exp_sub, exp_logEta, exp_logEta, coe_D_smul]

lemma disc_div_disc (τ : ℍ) :
    ModularForm.discriminant τ / ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ) =
      exp (24 * Lg ℓ τ) := by
  rw [show (24 : ℂ) * Lg ℓ τ = ((24 : ℕ) : ℂ) * Lg ℓ τ by push_cast; ring, Complex.exp_nat_mul, exp_Lg,
    div_pow, ModularForm.discriminant, ModularForm.discriminant, coe_D_smul]

lemma mdifferentiable_Lg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Lg ℓ) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  have hℓ : (0 : ℝ) < ℓ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ)
  have hz' : 0 < ((ℓ : ℂ) * z).im := by
    rw [show ((ℓ : ℂ) * z).im = ℓ * z.im by simp]; exact mul_pos hℓ hz
  have h1 : DifferentiableAt ℂ logEta z := differentiableAt_logEta hz
  have h2 : DifferentiableAt ℂ (fun w : ℂ => logEta ((ℓ : ℂ) * w)) z :=
    (differentiableAt_logEta hz').comp z (differentiableAt_id.const_mul _)
  refine ((h1.sub h2).differentiableWithinAt).congr (fun w hw => ?_) ?_
  · show Lg ℓ (ofComplex w) = logEta w - logEta ((ℓ : ℂ) * w)
    rw [Lg, coe_D_smul, ofComplex_apply_of_im_pos hw]
  · show Lg ℓ (ofComplex z) = logEta z - logEta ((ℓ : ℂ) * z)
    rw [Lg, coe_D_smul, ofComplex_apply_of_im_pos hz]

variable (c : ℂ)

def Hc (τ : ℍ) : ℂ := exp (c * Lg ℓ τ)

omit [NeZero ℓ] in
lemma continuous_Hc : Continuous (Hc ℓ c) :=
  continuous_exp.comp (continuous_const.mul (continuous_Lg ℓ))

omit [NeZero ℓ] in
lemma mdifferentiable_Hc [NeZero ℓ] : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Hc ℓ c) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have h := (UpperHalfPlane.mdifferentiable_iff).1 (mdifferentiable_Lg ℓ)
  exact ((h.const_mul c).cexp).congr fun z _ => rfl

omit [NeZero ℓ] in
lemma Hc_ne_zero (τ : ℍ) : Hc ℓ c τ ≠ 0 := exp_ne_zero _

lemma Hc_pow_eq (N m : ℕ) (hc : (N : ℂ) * c = 24 * m) (τ : ℍ) :
    Hc ℓ c τ ^ N = (ModularForm.discriminant τ / ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ)) ^ m := by
  rw [Hc, ← Complex.exp_nat_mul, ← mul_assoc, hc, disc_div_disc, ← Complex.exp_nat_mul]
  congr 1; ring

lemma det_eq (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have h := γ.2; rw [Matrix.det_fin_two] at h; linear_combination h

lemma companion (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 ℓ) :
    ∃ γ' : SL(2, ℤ), (γ' 0 0 : ℤ) = γ 0 0 ∧ (γ' 1 1 : ℤ) = γ 1 1 ∧ (γ' 1 0 : ℤ) * ℓ = γ 1 0 ∧
      ∀ τ : ℍ, (ModularForm.heckeDiagMatrix ℓ • (γ • τ) : ℍ) = γ' • (ModularForm.heckeDiagMatrix ℓ • τ) := by
  have hdvd : (ℓ : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (CongruenceSubgroup.Gamma0_mem.1 hγ)
  obtain ⟨c', hc'⟩ := hdvd
  have hdet := det_eq γ
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ
  refine ⟨⟨!![γ 0 0, ℓ * γ 0 1; c', γ 1 1], ?_⟩, rfl, rfl, ?_, fun τ => ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet + (γ 0 1) * hc'
  · show c' * (ℓ : ℤ) = γ 1 0
    rw [hc']; ring
  · apply UpperHalfPlane.ext
    rw [coe_D_smul, coe_specialLinearGroup_apply, coe_specialLinearGroup_apply, coe_D_smul]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, eq_intCast]
    have hden : ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
      simpa [ModularGroup.denom_apply] using UpperHalfPlane.denom_ne_zero (γ : GL (Fin 2) ℝ) τ
    have hden' : ((c' : ℤ) : ℂ) * ((ℓ : ℂ) * (τ : ℂ)) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
      rw [hc'] at hden; push_cast at hden; rw [← mul_assoc, mul_comm ((c' : ℤ) : ℂ)]; exact hden
    push_cast
    have hc'' : ((γ 1 0 : ℤ) : ℂ) = (ℓ : ℂ) * (c' : ℂ) := by rw [hc']; push_cast; ring
    rw [mul_div_assoc', div_eq_div_iff hden hden']
    linear_combination (-(ℓ : ℂ) * (((γ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 0 1 : ℤ) : ℂ)) * (τ : ℂ)) * hc''

theorem Lg_smul_of_pos (γ γ' : SL(2, ℤ)) (hc : 0 < (γ 1 0 : ℤ)) (h11 : (γ' 1 1 : ℤ) = γ 1 1)
    (h10 : (γ' 1 0 : ℤ) * ℓ = γ 1 0)
    (hact : ∀ τ : ℍ, (ModularForm.heckeDiagMatrix ℓ • (γ • τ) : ℍ) = γ' • (ModularForm.heckeDiagMatrix ℓ • τ))
    (τ : ℍ) : Lg ℓ (γ • τ) = Lg ℓ τ + π * I / 12 * ((phi γ : ℂ) - (phi γ' : ℂ)) := by
  have hℓpos : (0 : ℤ) < ℓ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ)
  have hc'pos : 0 < (γ' 1 0 : ℤ) := by
    by_contra h; push Not at h
    have : (γ' 1 0 : ℤ) * ℓ ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg h hℓpos.le
    linarith
  have L1 := logEta_smul γ hc τ
  have L2 := logEta_smul γ' hc'pos (ModularForm.heckeDiagMatrix ℓ • τ)
  rw [Lg, Lg, hact, L1, L2, coe_D_smul, h11]
  have hS : log (-I * (((γ' 1 0 : ℤ) : ℂ) * ((ℓ : ℂ) * (τ : ℂ)) + ((γ 1 1 : ℤ) : ℂ)))
      = log (-I * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ))) := by
    rw [← h10]; push_cast; ring_nf
  rw [hS]
  ring

theorem Lg_T_zpow_smul (b : ℤ) (τ : ℍ) :
    Lg ℓ (ModularGroup.T ^ b • τ) = Lg ℓ τ + π * I * b * (1 - (ℓ : ℂ)) / 12 := by
  have h1 : ((ModularGroup.T ^ b • τ : ℍ) : ℂ) = (τ : ℂ) + b := by
    rw [UpperHalfPlane.modular_T_zpow_smul]; simp [add_comm]
  have h2 : ((ModularForm.heckeDiagMatrix ℓ • (ModularGroup.T ^ b • τ) : ℍ) : ℂ)
      = ((ModularForm.heckeDiagMatrix ℓ • τ : ℍ) : ℂ) + ((ℓ * b : ℤ) : ℂ) := by
    rw [coe_D_smul, coe_D_smul, h1]; push_cast; ring
  rw [Lg, Lg, h1, h2, logEta_add_int, logEta_add_int]
  push_cast; ring

theorem exists_Lg_smul_eq_add (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 ℓ) :
    ∃ ω : ℂ, ∀ τ : ℍ, Lg ℓ (γ • τ) = Lg ℓ τ + ω := by

  suffices key : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 ℓ → 0 ≤ (γ 1 0 : ℤ) →
      ∃ ω : ℂ, ∀ τ : ℍ, Lg ℓ (γ • τ) = Lg ℓ τ + ω by
    rcases le_or_gt 0 (γ 1 0 : ℤ) with h | h
    · exact key γ hγ h
    · have hneg : -γ ∈ CongruenceSubgroup.Gamma0 ℓ := by
        rw [CongruenceSubgroup.Gamma0_mem] at hγ ⊢
        rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, hγ, neg_zero]
      have hc : 0 ≤ ((-γ : SL(2, ℤ)) 1 0 : ℤ) := by
        rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]; linarith
      obtain ⟨ω, hω⟩ := key (-γ) hneg hc
      exact ⟨ω, fun τ => by rw [← hω τ, ModularGroup.SL_neg_smul]⟩
  intro γ hγ hc0
  rcases hc0.lt_or_eq with hc | hc
  · obtain ⟨γ', -, h11, h10, hact⟩ := companion ℓ γ hγ
    exact ⟨_, fun τ => Lg_smul_of_pos ℓ γ γ' hc h11 h10 hact τ⟩
  ·
    have hdet := det_eq γ
    rw [← hc, mul_zero, sub_zero] at hdet
    have had : (γ 0 0 : ℤ) = γ 1 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet with h | h <;>
        [skip; skip] <;> nlinarith [Int.eq_one_or_neg_one_of_mul_eq_one' hdet]
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet with ha | ha
    ·
      have hd : (γ 1 1 : ℤ) = 1 := by rw [← had, ha]
      have hγT : γ = ModularGroup.T ^ (γ 0 1 : ℤ) := by
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [ModularGroup.coe_T_zpow, ha, hd, ← hc]
      refine ⟨π * I * (γ 0 1 : ℤ) * (1 - (ℓ : ℂ)) / 12, fun τ => ?_⟩
      conv_lhs => rw [hγT]
      exact Lg_T_zpow_smul ℓ _ τ
    ·
      have hd : (γ 1 1 : ℤ) = -1 := by rw [← had, ha]
      have hγT : γ = -(ModularGroup.T ^ (-(γ 0 1 : ℤ))) := by
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [ModularGroup.coe_T_zpow, ha, hd, ← hc]
      refine ⟨π * I * (-(γ 0 1 : ℤ) : ℤ) * (1 - (ℓ : ℂ)) / 12, fun τ => ?_⟩
      conv_lhs => rw [hγT, ModularGroup.SL_neg_smul]
      exact Lg_T_zpow_smul ℓ _ τ

theorem exists_Hc_smul_eq_mul (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 ℓ) :
    ∃ ω : ℂ, ∀ τ : ℍ, Hc ℓ c (γ • τ) = ω * Hc ℓ c τ := by
  obtain ⟨ω, hω⟩ := exists_Lg_smul_eq_add ℓ γ hγ
  exact ⟨exp (c * ω), fun τ => by rw [Hc, Hc, hω, mul_add, exp_add, mul_comm]⟩

end Branch

def HP : Set ℂ := {z : ℂ | 0 < z.im}

lemma isOpen_HP : IsOpen HP := isOpen_lt continuous_const Complex.continuous_im

lemma isPreconnected_HP : IsPreconnected HP := (convex_halfSpace_im_gt 0).isPreconnected

def Hol (F : ℍ → ℂ) : Prop := DifferentiableOn ℂ (F ∘ ofComplex) HP

namespace Hol

variable {F G : ℍ → ℂ}

lemma const (a : ℂ) : Hol fun _ => a := differentiableOn_const a

lemma add (hF : Hol F) (hG : Hol G) : Hol (F + G) := DifferentiableOn.add hF hG

lemma neg (hF : Hol F) : Hol (-F) := DifferentiableOn.neg hF

lemma mul (hF : Hol F) (hG : Hol G) : Hol (F * G) := DifferentiableOn.mul hF hG

lemma pow (hF : Hol F) (n : ℕ) : Hol (F ^ n) := DifferentiableOn.pow hF n

lemma smul (a : ℂ) (hF : Hol F) : Hol (fun τ => a * F τ) := DifferentiableOn.const_mul hF a

lemma congr {F' : ℍ → ℂ} (hF : Hol F) (h : ∀ τ, F τ = F' τ) : Hol F' :=
  DifferentiableOn.congr hF fun z _ => by simp [Function.comp, h]

lemma of_mdifferentiable (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) : Hol F :=
  UpperHalfPlane.mdifferentiable_iff.1 hF

lemma comp_D (ℓ : ℕ) [NeZero ℓ] (hF : Hol F) : Hol fun τ => F (ModularForm.heckeDiagMatrix ℓ • τ) := by
  have hℓ : (0 : ℝ) < ℓ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ)
  have hmaps : Set.MapsTo (fun z : ℂ => (ℓ : ℂ) * z) HP HP := fun z hz => by
    show 0 < ((ℓ : ℂ) * z).im
    rw [show ((ℓ : ℂ) * z).im = ℓ * z.im by simp]; exact mul_pos hℓ hz
  have h : DifferentiableOn ℂ ((F ∘ ofComplex) ∘ fun z : ℂ => (ℓ : ℂ) * z) HP :=
    hF.comp (differentiable_id.const_mul _).differentiableOn hmaps
  refine h.congr fun z hz => ?_
  show F (ModularForm.heckeDiagMatrix ℓ • ofComplex z) = F (ofComplex ((ℓ : ℂ) * z))
  congr 1
  apply UpperHalfPlane.ext
  rw [coe_D_smul, ofComplex_apply_of_im_pos hz, ofComplex_apply_of_im_pos (hmaps hz)]

end Hol

theorem exists_eqOn_zero_of_prod_eq_zero {ι : Type*} (s : Finset ι) (g : ι → ℂ → ℂ)
    (hg : ∀ i ∈ s, DifferentiableOn ℂ (g i) HP) (h : ∀ z ∈ HP, ∏ i ∈ s, g i z = 0) :
    ∃ i ∈ s, ∀ z ∈ HP, g i z = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exfalso
    have hI : Complex.I ∈ HP := by show 0 < Complex.I.im; simp
    simpa using h Complex.I hI
  | insert a s ha ih =>
    have hI : Complex.I ∈ HP := by show 0 < Complex.I.im; simp
    have hga : AnalyticOnNhd ℂ (g a) HP := (hg a (Finset.mem_insert_self a s)).analyticOnNhd isOpen_HP
    have hgs : ∀ i ∈ s, DifferentiableOn ℂ (g i) HP := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hprod : DifferentiableOn ℂ (fun z => ∏ i ∈ s, g i z) HP := by
      have := DifferentiableOn.finsetProd hgs
      refine this.congr fun z _ => ?_
      simp [Finset.prod_apply]
    have hps : AnalyticOnNhd ℂ (fun z => ∏ i ∈ s, g i z) HP := hprod.analyticOnNhd isOpen_HP
    rcases (hga Complex.I hI).eventually_eq_zero_or_eventually_ne_zero with hz | hnz
    ·
      refine ⟨a, Finset.mem_insert_self a s, fun z hz' => ?_⟩
      have hfr : ∃ᶠ w in 𝓝[≠] Complex.I, g a w = 0 := (hz.filter_mono nhdsWithin_le_nhds).frequently
      exact hga.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_HP hI hfr hz'
    ·
      have hmem : ∀ᶠ w in 𝓝[≠] Complex.I, w ∈ HP :=
        mem_nhdsWithin_of_mem_nhds (isOpen_HP.mem_nhds hI)
      have hev : ∀ᶠ w in 𝓝[≠] Complex.I, (∏ i ∈ s, g i w) = 0 := by
        filter_upwards [hnz, hmem] with w hw1 hw2
        have := h w hw2
        rw [Finset.prod_insert ha] at this
        exact (mul_eq_zero.1 this).resolve_left hw1
      have hzero := hps.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_HP hI hev.frequently
      obtain ⟨i, hi, hiz⟩ := ih hgs fun z hz => hzero hz
      exact ⟨i, Finset.mem_insert_of_mem hi, hiz⟩

def RealL (A : LaurentSeries ℂ) (F : ℍ → ℂ) : Prop :=
  ∀ τ : ℍ, HasSum (fun m : ℤ => A.coeff m * 𝕢 1 (τ : ℂ) ^ m) (F τ)

namespace RealL

variable {A B : LaurentSeries ℂ} {F G : ℍ → ℂ}

lemma add (hA : RealL A F) (hB : RealL B G) : RealL (A + B) (F + G) := fun τ => by
  simpa [add_mul] using (hA τ).add (hB τ)

lemma neg (hA : RealL A F) : RealL (-A) (-F) := fun τ => by
  simpa [neg_mul] using (hA τ).neg

lemma mul (hA : RealL A F) (hB : RealL B G) : RealL (A * B) (F * G) := fun τ =>
  ModularCurve.hasSum_qParam_mul_laurent 1 one_pos A B F G hA hB τ

lemma C (a : ℂ) : RealL (HahnSeries.C a) (fun _ => a) := fun τ => by
  refine (hasSum_ite_eq (0 : ℤ) a).congr_fun fun m => ?_
  by_cases hm : m = 0
  · subst hm; simp
  · simp [hm]

lemma one : RealL 1 1 := by first | exact C 1 | simpa [Pi.one_def] using C 1

lemma congr {A' : LaurentSeries ℂ} {F' : ℍ → ℂ} (hA : RealL A F) (h1 : A = A') (h2 : ∀ τ, F τ = F' τ) :
    RealL A' F' := fun τ => by rw [← h1, ← h2]; exact hA τ

lemma pow (hA : RealL A F) : ∀ n : ℕ, RealL (A ^ n) (F ^ n)
  | 0 => by simpa using one
  | n + 1 => by simpa [pow_succ] using (pow hA n).mul hA

lemma unique (hA : RealL A F) (hB : RealL A G) (τ : ℍ) : F τ = G τ := (hA τ).unique (hB τ)

lemma eq_zero (hA : RealL A fun _ => 0) : A = 0 :=
  ModularCurve.laurent_qParam_coeff_unique 1 one_pos (fun _ => 0) A 0 hA (fun τ => by
    simp)

lemma qParam_D_smul (ℓ : ℕ) [NeZero ℓ] (τ : ℍ) :
    𝕢 1 ((ModularForm.heckeDiagMatrix ℓ • τ : ℍ) : ℂ) = 𝕢 1 (τ : ℂ) ^ ℓ := by
  rw [coe_D_smul]
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
  rw [← Complex.exp_nat_mul]; congr 1; ring

lemma qExpand (ℓ : ℕ) [NeZero ℓ] (hA : RealL A F) :
    RealL (ModularCurve.qExpand ℂ ℓ A) (fun τ => F (ModularForm.heckeDiagMatrix ℓ • τ)) := by
  intro τ
  have hinj : Function.Injective (fun n : ℤ => (ℓ : ℤ) * n) :=
    mul_right_injective₀ (by exact_mod_cast NeZero.ne ℓ)
  rw [← hinj.hasSum_iff]
  · have h := hA (ModularForm.heckeDiagMatrix ℓ • τ)
    rw [qParam_D_smul] at h
    refine h.congr_fun fun n => ?_
    simp only [Function.comp_apply, ModularCurve.qExpand_coeff_mul]
    rw [zpow_mul, zpow_natCast]
  · intro m hm
    rw [ModularCurve.qExpand_coeff_of_not_dvd ℓ _ (fun ⟨n, hn⟩ => hm ⟨n, hn.symm⟩), zero_mul]

end RealL

def jt (τ : ℍ) : ℂ := ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ

lemma hol_jt : Hol jt := by
  have hE : DifferentiableOn ℂ (⇑ModularForm.E₄ ∘ ofComplex) HP :=
    UpperHalfPlane.mdifferentiable_iff.1 ModularForm.E₄.holo'
  have hD : DifferentiableOn ℂ (ModularForm.discriminant ∘ ofComplex) HP := by
    refine DifferentiableOn.congr (f := fun z => ModularForm.eta z ^ 24) ?_ ?_
    · exact fun z hz => ((ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hz).pow 24).differentiableWithinAt
    · intro z hz
      simp [ModularForm.discriminant, ofComplex_apply_of_im_pos hz]
  have hD0 : ∀ z ∈ HP, (ModularForm.discriminant ∘ ofComplex) z ≠ 0 := fun z _ =>
    ModularForm.discriminant_ne_zero _
  exact (hE.pow 3).div hD hD0

lemma realL_jt : RealL (ModularCurve.jqModC ℂ) jt := by
  intro τ
  have h := ModularCurve.hasSum_jq_qParam τ
  refine h.congr_fun fun m => ?_
  congr 1
  rw [← ModularCurve.jqModC_rat, ← ModularCurve.map_jqModC (Rat.castHom ℂ), HahnSeries.map_coeff]
  rfl

lemma jt_smul (γ : SL(2, ℤ)) (τ : ℍ) : jt (γ • τ) = jt τ := ModularCurve.E4_cube_div_discriminant_smul γ τ

lemma jt_D_smul (ℓ : ℕ) [NeZero ℓ] (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 ℓ) (τ : ℍ) :
    jt (ModularForm.heckeDiagMatrix ℓ • γ • τ) = jt (ModularForm.heckeDiagMatrix ℓ • τ) := by
  obtain ⟨γ', hγ', -⟩ := ModularCurve.exists_sl2_heckeDiagMatrix_smul_eq ℓ γ hγ
  rw [hγ' τ]
  exact jt_smul γ' _

section Good

variable (K : Type*) [Field K] (σ : K →+* ℂ) (ℓ : ℕ) [Fact (Nat.Prime ℓ)]

def Good (x : LaurentSeries K) : Prop :=
  ∃ F : ℍ → ℂ, RealL (ModularCurve.coeffMap σ x) F ∧ Hol F ∧
    ∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : ℍ, F (γ • τ) = F τ

variable {K σ ℓ}

omit [Fact (Nat.Prime ℓ)] in
lemma Good.add {x y : LaurentSeries K} (hx : Good K σ ℓ x) (hy : Good K σ ℓ y) : Good K σ ℓ (x + y) := by
  obtain ⟨F, h1, h2, h3⟩ := hx; obtain ⟨G, g1, g2, g3⟩ := hy
  refine ⟨F + G, ?_, h2.add g2, fun γ hγ τ => ?_⟩
  · rw [map_add]; exact h1.add g1
  · show F (γ • τ) + G (γ • τ) = F τ + G τ
    rw [h3 γ hγ τ, g3 γ hγ τ]

omit [Fact (Nat.Prime ℓ)] in
lemma Good.mul {x y : LaurentSeries K} (hx : Good K σ ℓ x) (hy : Good K σ ℓ y) : Good K σ ℓ (x * y) := by
  obtain ⟨F, h1, h2, h3⟩ := hx; obtain ⟨G, g1, g2, g3⟩ := hy
  refine ⟨F * G, ?_, h2.mul g2, fun γ hγ τ => ?_⟩
  · rw [map_mul]; exact h1.mul g1
  · show F (γ • τ) * G (γ • τ) = F τ * G τ
    rw [h3 γ hγ τ, g3 γ hγ τ]

omit [Fact (Nat.Prime ℓ)] in
lemma Good.const (a : K) : Good K σ ℓ (algebraMap K (LaurentSeries K) a) := by
  refine ⟨fun _ => σ a, ?_, Hol.const _, fun _ _ _ => rfl⟩
  have : ModularCurve.coeffMap σ (algebraMap K (LaurentSeries K) a) = HahnSeries.C (σ a) := by
    ext k
    rw [ModularCurve.coeffMap_coeff]
    simp [HahnSeries.algebraMap_apply', HahnSeries.coeff_single, apply_ite σ]
  rw [this]; exact RealL.C _

variable [Algebra ℚ K] (hσK : ∀ q : ℚ, σ (algebraMap ℚ K q) = (q : ℂ))

omit [Fact (Nat.Prime ℓ)] in
include hσK in
lemma coeffMap_sigma_coeffEmb (x : LaurentSeries ℚ) :
    ModularCurve.coeffMap σ (ModularCurve.coeffEmb K x) = ModularCurve.coeffMap (Rat.castHom ℂ) x := by
  ext m
  rw [ModularCurve.coeffMap_coeff, ModularCurve.coeffEmb_coeff, ModularCurve.coeffMap_coeff, hσK]
  rfl

omit [Fact (Nat.Prime ℓ)] [Algebra ℚ K] in
lemma coeffMap_sigma_jqModC : ModularCurve.coeffMap σ (ModularCurve.jqModC K) = ModularCurve.jqModC ℂ := by
  show (ModularCurve.jqModC K).map σ = _
  exact ModularCurve.map_jqModC σ

omit [Fact (Nat.Prime ℓ)] [Algebra ℚ K] in

lemma Good.jqModC : Good K σ ℓ (ModularCurve.jqModC K) :=
  ⟨jt, by rw [coeffMap_sigma_jqModC]; exact realL_jt, hol_jt, fun γ _ τ => jt_smul γ τ⟩

omit [Algebra ℚ K] in

lemma Good.jqNModC : Good K σ ℓ (ModularCurve.jqNModC K ℓ) := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hser : ModularCurve.coeffMap σ (ModularCurve.jqNModC K ℓ) = ModularCurve.qExpand ℂ ℓ (ModularCurve.jqModC ℂ) := by
    have h1 : ModularCurve.jqNModC K ℓ = ModularCurve.qExpand K ℓ (ModularCurve.jqModC K) := rfl
    rw [h1, ModularCurve.coeffMap_qExpand, coeffMap_sigma_jqModC]
  have hR : RealL (ModularCurve.coeffMap σ (ModularCurve.jqNModC K ℓ))
      (fun τ => jt (ModularForm.heckeDiagMatrix ℓ • τ)) := by
    rw [hser]; exact realL_jt.qExpand ℓ
  have hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : ℍ,
      jt (ModularForm.heckeDiagMatrix ℓ • γ • τ) = jt (ModularForm.heckeDiagMatrix ℓ • τ) :=
    fun γ hγ τ => jt_D_smul ℓ γ hγ τ
  exact ⟨fun τ => jt (ModularForm.heckeDiagMatrix ℓ • τ), hR, hol_jt.comp_D ℓ, hinv⟩

omit [Algebra ℚ K] in

theorem Good.of_mem_adjoin {x : LaurentSeries K}
    (hx : x ∈ Algebra.adjoin K {x : LaurentSeries K | ∃ (d : ℕ) (_ : NeZero d), d ∣ ℓ ∧ x = ModularCurve.jqNModC K d}) :
    Good K σ ℓ x := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨d, hd, hdvd, rfl⟩ := hx
    rcases (Nat.dvd_prime (Fact.out : ℓ.Prime)).1 hdvd with h1 | h2
    · subst h1
      rw [ModularCurve.jqNModC_one]
      exact Good.jqModC
    · subst h2
      exact Good.jqNModC
  | algebraMap a => exact Good.const a
  | add x y _ _ hx hy => exact hx.add hy
  | mul x y _ _ hx hy => exact hx.mul hy

end Good

section Assembly

open ModularCurve AlgebraicCurve

variable (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]

local notation "ℚ̄" => AlgebraicClosure ℚ

def sigmaC : (AlgebraicClosure ℚ) →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := AlgebraicClosure ℚ)).toRingHom

lemma sigmaC_rat (q : ℚ) : sigmaC (algebraMap ℚ ℚ̄ q) = (q : ℂ) := by
  rw [sigmaC, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]; rfl

theorem exists_realized_identity (m : ℕ)
    (hP : Divisor.IsPrincipal ((m : ℤ) • cuspidalDivisor ℓ)) :
    ∃ (Y Z : ℍ → ℂ) (κ : ℂ), κ ≠ 0 ∧ Hol Y ∧ Hol Z ∧
      (∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : ℍ, Y (γ • τ) = Y τ) ∧
      (∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : ℍ, Z (γ • τ) = Z τ) ∧
      (∃ τ₀ : ℍ, Z τ₀ ≠ 0) ∧
      ∀ τ : ℍ, Y τ ^ (ℓ - 1) = κ * (ModularForm.discriminant τ /
        ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ)) ^ m * Z τ ^ (ℓ - 1) := by
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩

  set Fb := modularFunctionFieldBar ℓ with hFb
  have hmem := modularUnitSeries_mem_modularFunctionFieldFull ℓ
  set ub : modularFunctionFieldBar ℓ :=
    ⟨coeffEmb ℚ̄ (modularUnitSeries ℓ), coeffEmb_mem_laurentBaseChange ℚ̄ hmem⟩ with hub
  obtain ⟨f, hf0, hf⟩ := hP
  have hDU : ∀ v : Place ℚ̄ (modularFunctionFieldBar ℓ),
      (((ℓ : ℤ) - 1) • cuspidalDivisor ℓ) v = v.ord ub := smul_cuspidalDivisor_apply_eq_ord ℓ hmem

  have hσu : ModularCurve.coeffMap sigmaC (coeffEmb ℚ̄ (modularUnitSeries ℓ))
      = ModularCurve.coeffMap (Rat.castHom ℂ) (modularUnitSeries ℓ) :=
    coeffMap_sigma_coeffEmb (K := AlgebraicClosure ℚ) (σ := sigmaC) (sigmaC_rat) _
  have hRu : RealL (ModularCurve.coeffMap sigmaC (coeffEmb ℚ̄ (modularUnitSeries ℓ)))
      (fun τ => ModularForm.discriminant τ / ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ)) := by
    rw [hσu]; intro τ; exact hasSum_modularUnitSeries_qParam ℓ τ
  have hub0 : ub ≠ 0 := by
    intro h
    have h' : coeffEmb ℚ̄ (modularUnitSeries ℓ) = 0 := by
      have := congrArg Subtype.val h; simpa [hub] using this
    have h0 : RealL (ModularCurve.coeffMap sigmaC (coeffEmb ℚ̄ (modularUnitSeries ℓ))) (fun _ => 0) := by
      rw [h', map_zero]; intro τ; simp
    have := RealL.unique hRu h0 UpperHalfPlane.I
    exact div_ne_zero (ModularForm.discriminant_ne_zero _) (ModularForm.discriminant_ne_zero _) this

  set N : ℕ := ℓ - 1 with hN
  set g : modularFunctionFieldBar ℓ := f ^ N * (ub ^ m)⁻¹ with hg
  have hfN0 : f ^ N ≠ 0 := pow_ne_zero _ hf0
  have hubm0 : ub ^ m ≠ 0 := pow_ne_zero _ hub0
  have hg0 : g ≠ 0 := mul_ne_zero hfN0 (inv_ne_zero hubm0)
  have hNcast : ((ℓ : ℤ) - 1) = (N : ℤ) := by
    rw [hN]; push_cast [Nat.cast_sub hℓ.out.one_le]; ring
  have hord : ∀ v : Place ℚ̄ (modularFunctionFieldBar ℓ), v.ord g = 0 := by
    intro v
    have h1 := hf v
    have h2 := hDU v
    rw [Finsupp.smul_apply, smul_eq_mul] at h1 h2
    have e1 : v.ord g = v.ord (f ^ N) + v.ord ((ub ^ m)⁻¹) := v.ord_mul hfN0 (inv_ne_zero hubm0)
    have e2 : v.ord ((ub ^ m)⁻¹) = -v.ord (ub ^ m) := v.ord_inv _
    have e3 : v.ord (f ^ N) = (N : ℤ) * v.ord f := by rw [← zpow_natCast, v.ord_zpow]
    have e4 : v.ord (ub ^ m) = (m : ℤ) * v.ord ub := by rw [← zpow_natCast, v.ord_zpow]
    rw [e1, e2, e3, e4, ← h1, ← h2, hNcast]
    ring

  haveI := finiteDimensional_adjoin_coeffEmb_jq ℓ
  have hj : Transcendental ℚ̄ (⟨coeffEmb ℚ̄ jq, coeffEmb_mem_laurentBaseChange ℚ̄ (jq_mem_full ℓ)⟩ :
      modularFunctionFieldBar ℓ) := transcendental_coeffEmb_jq ℚ̄ ℓ
  obtain ⟨lam, hlam⟩ := Place.mem_range_algebraMap_of_forall_ord_eq_zero (K := AlgebraicClosure ℚ) _ hj hord
  have hlam0 : lam ≠ 0 := by rintro rfl; exact hg0 (by rw [← hlam, map_zero])

  have hfK : ((f : modularFunctionFieldBar ℓ) : LaurentSeries ℚ̄) ^ N
      = algebraMap ℚ̄ (LaurentSeries ℚ̄) lam * (coeffEmb ℚ̄ (modularUnitSeries ℓ)) ^ m := by
    have h1 : (g : LaurentSeries ℚ̄) = algebraMap ℚ̄ (LaurentSeries ℚ̄) lam := by
      rw [← hlam]; rfl
    have h2 : (g : LaurentSeries ℚ̄) * (coeffEmb ℚ̄ (modularUnitSeries ℓ)) ^ m = (f : LaurentSeries ℚ̄) ^ N := by
      have hu' : ((ub ^ m : modularFunctionFieldBar ℓ) : LaurentSeries ℚ̄) = (coeffEmb ℚ̄ (modularUnitSeries ℓ)) ^ m := by
        simp [hub]
      have hne : ((ub ^ m : modularFunctionFieldBar ℓ) : LaurentSeries ℚ̄) ≠ 0 := by
        intro h; apply hubm0; exact_mod_cast h
      rw [hg]; push_cast
      rw [← hu', inv_mul_cancel_right₀ hne]
    rw [← h2, h1]

  have hfmem : ((f : modularFunctionFieldBar ℓ) : LaurentSeries ℚ̄) ∈
      IntermediateField.adjoin ℚ̄ {x : LaurentSeries ℚ̄ | ∃ (d : ℕ) (_ : NeZero d), d ∣ ℓ ∧ x = jqNModC ℚ̄ d} := by
    rw [← laurentBaseChange_modularFunctionFieldFull ℚ̄ ℓ]; exact f.2
  obtain ⟨y, hy, z, hz, hyz⟩ := IntermediateField.mem_adjoin_iff_div.1 hfmem
  have hz0 : z ≠ 0 := by
    intro h; rw [h, div_zero] at hyz; exact hf0 (by exact_mod_cast hyz)
  obtain ⟨Y, hY1, hY2, hY3⟩ := Good.of_mem_adjoin (K := AlgebraicClosure ℚ) (σ := sigmaC) (ℓ := ℓ) hy
  obtain ⟨Z, hZ1, hZ2, hZ3⟩ := Good.of_mem_adjoin (K := AlgebraicClosure ℚ) (σ := sigmaC) (ℓ := ℓ) hz

  have hyN : y ^ N = algebraMap ℚ̄ (LaurentSeries ℚ̄) lam * (coeffEmb ℚ̄ (modularUnitSeries ℓ)) ^ m * z ^ N := by
    have : y = (f : LaurentSeries ℚ̄) * z := by rw [hyz, div_mul_cancel₀ _ hz0]
    rw [this, mul_pow, hfK]

  set u : ℍ → ℂ := fun τ => ModularForm.discriminant τ / ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ)
  have hR1 : RealL (ModularCurve.coeffMap sigmaC (y ^ N)) (Y ^ N) := by rw [map_pow]; exact hY1.pow N
  have hR2 : RealL (ModularCurve.coeffMap sigmaC (y ^ N)) ((fun _ => sigmaC lam) * u ^ m * Z ^ N) := by
    rw [hyN, map_mul, map_mul, map_pow, map_pow]
    refine ((?_ : RealL _ _).mul (hRu.pow m)).mul (hZ1.pow N)
    have : ModularCurve.coeffMap sigmaC (algebraMap ℚ̄ (LaurentSeries ℚ̄) lam) = HahnSeries.C (sigmaC lam) := by
      ext k
      rw [ModularCurve.coeffMap_coeff]
      simp [HahnSeries.algebraMap_apply', HahnSeries.coeff_single, apply_ite sigmaC]
    rw [this]; exact RealL.C _
  refine ⟨Y, Z, sigmaC lam, (map_ne_zero sigmaC).2 hlam0, hY2, hZ2, hY3, hZ3, ?_, fun τ => ?_⟩
  · by_contra hno
    push Not at hno
    have hZ0 : RealL (ModularCurve.coeffMap sigmaC z) (fun _ => 0) := hZ1.congr rfl hno
    have := RealL.eq_zero hZ0
    exact hz0 ((map_eq_zero_iff _ (fun a b h => by
      ext k; have := congrArg (fun s => HahnSeries.coeff s k) h
      exact sigmaC.injective (by simpa [ModularCurve.coeffMap_coeff] using this))).1 this)
  · have := RealL.unique hR1 hR2 τ
    simpa [u, mul_assoc] using this

theorem exists_continuous_pow_eq_of_isPrincipal_smul_cuspidalDivisor (m : ℕ) (hm : 0 < m)
    (hP : Divisor.IsPrincipal ((m : ℤ) • cuspidalDivisor ℓ)) :
    ∃ H : ℍ → ℂ, Continuous H ∧
      (∀ τ : ℍ, H τ ^ (ℓ - 1) = (ModularForm.discriminant τ /
        ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ)) ^ m) ∧
      ∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : ℍ, H (γ • τ) = H τ := by
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  have _hm : m ≠ 0 := hm.ne'
  obtain ⟨Y, Z, κ, hκ, hY, hZ, hYi, hZi, ⟨τ₀, hτ₀⟩, hid⟩ := exists_realized_identity ℓ m hP
  set N : ℕ := ℓ - 1 with hN
  have hNpos : 0 < N := by have := hℓ.out.two_le; omega
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'

  set c : ℂ := 24 * (m : ℂ) / N with hc
  have hcN : (N : ℂ) * c = 24 * m := by rw [hc]; field_simp
  set H := Hc ℓ c with hH
  have hHpow : ∀ τ : ℍ, H τ ^ N = (ModularForm.discriminant τ /
      ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ)) ^ m := fun τ => Hc_pow_eq ℓ c N m hcN τ
  refine ⟨H, continuous_Hc ℓ c, hHpow, fun γ hγ => ?_⟩

  obtain ⟨ν, hν⟩ := IsAlgClosed.exists_pow_nat_eq κ hNpos
  have hν0 : ν ≠ 0 := by rintro rfl; rw [zero_pow hNpos.ne'] at hν; exact hκ hν.symm
  have hζ := Complex.isPrimitiveRoot_exp N hNpos.ne'
  set ζ := Complex.exp (2 * π * Complex.I / N) with hζdef
  have hprod : ∀ τ : ℍ, ∏ μ ∈ Polynomial.nthRootsFinset N (1 : ℂ), (Y τ - μ * (ν * H τ * Z τ)) = 0 := by
    intro τ
    rw [← hζ.pow_sub_pow_eq_prod_sub_mul (Y τ) (ν * H τ * Z τ) hNpos, hid τ, ← hHpow τ, mul_pow, mul_pow, hν]
    ring

  have hHhol : Hol H := Hol.of_mdifferentiable (mdifferentiable_Hc ℓ c)
  obtain ⟨μ, hμ, hμz⟩ := exists_eqOn_zero_of_prod_eq_zero (Polynomial.nthRootsFinset N (1 : ℂ))
    (fun μ z => (Y (ofComplex z) - μ * (ν * H (ofComplex z) * Z (ofComplex z))))
    (fun μ _ => (hY.sub ((hHhol.mul hZ).const_mul ν |>.const_mul μ)).congr (fun z _ => by
      simp [Function.comp, mul_assoc]))
    (fun z hz => by simpa using hprod (ofComplex z))
  have hYeq : ∀ τ : ℍ, Y τ = μ * (ν * H τ * Z τ) := fun τ => by
    have := hμz (τ : ℂ) τ.im_pos
    rw [ofComplex_apply] at this
    exact sub_eq_zero.1 this
  have hμ0 : μ ≠ 0 := by
    rw [Polynomial.mem_nthRootsFinset hNpos] at hμ
    rintro rfl; rw [zero_pow hNpos.ne'] at hμ; exact zero_ne_one hμ

  obtain ⟨ω, hω⟩ := exists_Hc_smul_eq_mul ℓ c γ hγ
  have hω' : ∀ τ : ℍ, H (γ • τ) = ω * H τ := hω
  have key : (ω - 1) * (μ * ν * H τ₀ * Z τ₀) = 0 := by
    have h1 := hYeq (γ • τ₀)
    rw [hYi γ hγ, hZi γ hγ, hω', hYeq τ₀] at h1
    linear_combination -h1
  have hω1 : ω = 1 := by
    have hne : μ * ν * H τ₀ * Z τ₀ ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero hμ0 hν0) (Hc_ne_zero ℓ c τ₀)) hτ₀
    exact sub_eq_zero.1 ((mul_eq_zero.1 key).resolve_right hne)
  intro τ
  rw [hω' τ, hω1, one_mul]

end Assembly

end EtaBranch

end

theorem solution (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (m : ℕ) (hm : 0 < m) (hP : AlgebraicCurve.Divisor.IsPrincipal ((m : ℤ) • ModularCurve.cuspidalDivisor ℓ)) : ∃ H : UpperHalfPlane → ℂ, Continuous H ∧ (∀ τ : UpperHalfPlane, H τ ^ (ℓ - 1) = (ModularForm.discriminant τ / ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ)) ^ m) ∧ ∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : UpperHalfPlane, H (γ • τ) = H τ :=
  EtaBranch.exists_continuous_pow_eq_of_isPrincipal_smul_cuspidalDivisor ℓ m hm hP

end S_ModularCurve_exists_continuous_pow_eq_of_isPrincipal_smul_cuspidalDivisor
end P2MW
export P2MW.S_ModularCurve_exists_continuous_pow_eq_of_isPrincipal_smul_cuspidalDivisor (solution)
