-- Prove2me | solution 1 for Malliavin.smoothElementaryNaturalItoDuality_pastCylinder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:48:52.224707+00:00
-- url     : https://prove2.me/submissions/d3171fc4-ffd2-435a-aa7d-d024d3687c0f

import Definitions.Def_Malliavin_KernelIdentification
import Definitions.Def_Malliavin_NaturalClarkOcone
import Theorems.Thm_Malliavin_iocIndicator_eq_intervalIndicator_sub
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_bestNaturalItoIntegrand_centeredNaturalItoIntegral
import Theorems.Thm_Malliavin_centeredNaturalItoEquiv_apply
import Theorems.Thm_Malliavin_centeredNaturalItoIntegralIsometry_apply
import Theorems.Thm_Malliavin_centeredPartL2_coe
import Theorems.Thm_Malliavin_centeredWienerIntegral_coe
import Theorems.Thm_Malliavin_coeFn_smulLp
import Theorems.Thm_Malliavin_elementaryBrownianValueLinear_apply
import Theorems.Thm_Malliavin_elementaryPredictable_coeLp
import Theorems.Thm_Malliavin_expectationL2_wienerIntegral
import Theorems.Thm_Malliavin_inner_predictableProjection_sub
import Theorems.Thm_Malliavin_integral_eq_inner_const
import Theorems.Thm_Malliavin_mderiv_cylindrical
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
import Theorems.Thm_Malliavin_timeDerivative_smulLp
import Theorems.Thm_Malliavin_wienerIntegralEquiv_symm_ofDual
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.bestNaturalItoIntegrand_centeredNaturalItoIntegral
attribute [local simp] Malliavin.centeredNaturalItoEquiv_apply
attribute [local simp] Malliavin.centeredNaturalItoIntegralIsometry_apply
attribute [local simp] Malliavin.centeredPartL2_coe
attribute [local simp] Malliavin.centeredWienerIntegral_coe
attribute [local simp] Malliavin.elementaryBrownianValueLinear_apply
attribute [local simp] Malliavin.expectationL2_wienerIntegral
attribute [local simp] Malliavin.mem_symmetricSubmodule



set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
namespace Malliavin
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (G : W → ℝ) (hG : IsSmoothBounded G)
    {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (hb : ∃ C, ∀ y, |f y| ≤ C)
    (hb' : ∃ C, ∀ y, ‖fderiv ℝ f y‖ ≤ C)
    (t : Fin n → ℝ≥0) (a b : ℝ≥0) (hab : a ≤ b)
    (ht : ∀ i, t i ≤ a) :
    let Z := pastCylinderLpMeas hB coordinate coordinate_apply hsm hnat
      f hf hb hb' t a ht
    inner ℝ (hG.toLp P - expectationL2 (hG.toLp P))
        (elementaryBrownianValue hB hsm hnat hab Z) =
      inner ℝ
        (predictableProjection 𝓅
          (Malliavin.timeDerivative hB coordinate coordinate_apply generated
            (hG.mderivLp P)))
        (elementaryPredictable 𝓅 a b Z) := by
  let hZ := isSmoothBounded_cylinder coordinate coordinate_apply f hf hb hb' t
  let Z := pastCylinderLpMeas hB coordinate coordinate_apply hsm hnat
    f hf hb hb' t a ht
  let h : CameronMartin.Space P :=
    CameronMartin.ofDual P (coordinate b) - CameronMartin.ofDual P (coordinate a)
  change inner ℝ (hG.toLp P - expectationL2 (hG.toLp P))
      (elementaryBrownianValue hB hsm hnat hab Z) =
    inner ℝ
      (predictableProjection 𝓅
        (Malliavin.timeDerivative hB coordinate coordinate_apply generated
          (hG.mderivLp P)))
      (elementaryPredictable 𝓅 a b Z)
  have hhLp : (h : RandomL2 P) = brownianLp hB b - brownianLp hB a := by
    dsimp [h]
    have hbLp : CameronMartin.centeredDualToLp P (coordinate b) = brownianLp hB b :=
      (brownianLp_eq_ofDual hB coordinate coordinate_apply b).symm
    have haLp : CameronMartin.centeredDualToLp P (coordinate a) = brownianLp hB a :=
      (brownianLp_eq_ofDual hB coordinate coordinate_apply a).symm
    rw [hbLp, haLp]
  have hhKernel :
      (wienerIntegralEquiv hB).symm
          (LinearIsometryEquiv.ofEq _ _
            (space_eq_firstChaos hB coordinate coordinate_apply generated) h) =
        iocIndicator a b := by
    dsimp [h]
    simp only [map_sub]
    rw [
      wienerIntegralEquiv_symm_ofDual hB coordinate coordinate_apply generated b,
      wienerIntegralEquiv_symm_ofDual hB coordinate coordinate_apply generated a,
      iocIndicator_eq_intervalIndicator_sub hB hab]
  have horth (i : Fin n) :
      inner ℝ (CameronMartin.ofDual P (coordinate (t i))) h = 0 := by
    dsimp [h]
    have htiLp : CameronMartin.centeredDualToLp P (coordinate (t i)) =
        brownianLp hB (t i) :=
      (brownianLp_eq_ofDual hB coordinate coordinate_apply (t i)).symm
    have hbLp : CameronMartin.centeredDualToLp P (coordinate b) = brownianLp hB b :=
      (brownianLp_eq_ofDual hB coordinate coordinate_apply b).symm
    have haLp : CameronMartin.centeredDualToLp P (coordinate a) = brownianLp hB a :=
      (brownianLp_eq_ofDual hB coordinate coordinate_apply a).symm
    rw [inner_sub_right, htiLp, hbLp, haLp,
      inner_brownianLp, inner_brownianLp,
      min_eq_left (by exact_mod_cast (ht i).trans hab),
      min_eq_left (by exact_mod_cast ht i), sub_self]
  have hcontract (w : W) :
      inner ℝ
          (mderiv P (fun y ↦ f (fun i ↦ B (t i) y)) w) h = 0 := by
    have hfun : (fun y ↦ f (fun i ↦ B (t i) y)) =
        fun y ↦ f (fun i ↦ coordinate (t i) y) := by
      funext y
      simp only [coordinate_apply]
    rw [hfun, mderiv_cylindrical P f (fun i ↦ coordinate (t i)) w
      ((hf.differentiable one_ne_zero) _), Submodule.coe_inner,
      Submodule.coe_sum, sum_inner]
    simp only [Submodule.coe_smul, real_inner_smul_left,
      ← Submodule.coe_inner, horth, mul_zero, Finset.sum_const_zero]
  have hsmul :
      hZ.smulLp P h = Malliavin.smulLp h (hZ.toLp P) := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (hZ.memLp_smul P h 2),
      coeFn_smulLp h (hZ.toLp P), MemLp.coeFn_toLp (hZ.memLp P 2)]
      with w hleft hright hcoeff
    change ((hZ.memLp_smul P h 2).toLp
        (fun x ↦ f (fun i ↦ B (t i) x) • h)) w =
      (Malliavin.smulLp h (hZ.toLp P)) w
    rw [hleft, hright]
    exact congrArg (fun c : ℝ ↦ c • h) hcoeff.symm
  have htime :
      Malliavin.timeDerivative hB coordinate coordinate_apply generated
          (hZ.smulLp P h) =
        (elementaryPredictable 𝓅 a b Z : TimeProcessL2 P) := by
    rw [hsmul, timeDerivative_smulLp hB coordinate coordinate_apply generated,
      hhKernel, elementaryPredictable_coeLp]
    rfl
  have hhCoeFn : ((h : RandomL2 P) : W → ℝ) =ᵐ[P]
      fun w ↦ B b w - B a w := by
    rw [hhLp]
    filter_upwards [Lp.coeFn_sub (brownianLp hB b) (brownianLp hB a),
      coeFn_brownianLp hB b, coeFn_brownianLp hB a]
      with w hsub hbrow harow
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [hbrow, harow]
  have hZCoeFn : ((Z : RandomL2 P) : W → ℝ) =ᵐ[P]
      fun w ↦ f (fun i ↦ B (t i) w) := by
    change ((hZ.toLp P : W → ℝ) =ᵐ[P]
      fun w ↦ f (fun i ↦ B (t i) w))
    exact MemLp.coeFn_toLp (hZ.memLp P 2)
  have hdiv : hZ.divergenceLp P h =
      elementaryBrownianValue hB hsm hnat hab Z := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (hZ.memLp_divergence P h),
      coeFn_elementaryBrownianValue hB hsm hnat hab Z,
      hZCoeFn, hhCoeFn]
      with w hleft hright hcoeff hinc
    change ((hZ.memLp_divergence P h).toLp
        (fun x ↦ f (fun i ↦ B (t i) x) * (h : RandomL2 P) x -
          inner ℝ (mderiv P (fun y ↦ f (fun i ↦ B (t i) y)) x) h)) w =
      (elementaryBrownianValue hB hsm hnat hab Z) w
    rw [hleft, hright, hcoeff, hinc, hcontract]
    ring
  have hcentered :
      ∫ w, elementaryBrownianValue hB hsm hnat hab Z w ∂P = 0 :=
    integral_elementaryBrownianValue hB hsm hnat hab Z
  have hconst (c : ℝ) :
      Lp.const 2 P c = c • Lp.const 2 P (1 : ℝ) := by
    change (Lp.constL 2 P ℝ) c = c • (Lp.constL 2 P ℝ) 1
    rw [← map_smul]
    simp only [smul_eq_mul, mul_one]
  have hone : inner ℝ (Lp.const 2 P (1 : ℝ))
      (elementaryBrownianValue hB hsm hnat hab Z) = 0 := by
    rw [real_inner_comm, ← integral_eq_inner_const, hcentered]
  have hexpect : inner ℝ (expectationL2 (hG.toLp P))
      (elementaryBrownianValue hB hsm hnat hab Z) = 0 := by
    rw [expectationL2, hconst, real_inner_smul_left, hone, mul_zero]
  have hmain : inner ℝ (hG.toLp P)
      (elementaryBrownianValue hB hsm hnat hab Z) =
        inner ℝ (hG.mderivLp P) (hZ.smulLp P h) := by
    rw [← hdiv]
    exact (inner_mderivLp_smulLp P hG hZ h).symm
  let D := Malliavin.timeDerivative hB coordinate coordinate_apply generated
    (hG.mderivLp P)
  let V := elementaryPredictable 𝓅 a b Z
  have hproj :
      inner ℝ ((predictableProjection 𝓅 D : PredictableProcessL2 𝓅 P) : TimeProcessL2 P)
          (V : TimeProcessL2 P) =
        inner ℝ D (V : TimeProcessL2 P) := by
    have hp := inner_predictableProjection_sub (𝓕 := 𝓅) D V
    rw [inner_sub_left] at hp
    exact sub_eq_zero.mp hp
  calc
    inner ℝ (hG.toLp P - expectationL2 (hG.toLp P))
        (elementaryBrownianValue hB hsm hnat hab Z) =
        inner ℝ (hG.toLp P)
          (elementaryBrownianValue hB hsm hnat hab Z) := by
      rw [inner_sub_left, hexpect, sub_zero]
    _ = inner ℝ (hG.mderivLp P) (hZ.smulLp P h) := hmain
    _ = inner ℝ D
        (Malliavin.timeDerivative hB coordinate coordinate_apply generated
          (hZ.smulLp P h)) :=
      by
        dsimp only [D]
        exact (LinearIsometry.inner_map_map (𝕜 := ℝ)
          (Malliavin.timeDerivative hB coordinate coordinate_apply generated)
          (hG.mderivLp P) (hZ.smulLp P h)).symm
    _ = inner ℝ D (V : TimeProcessL2 P) := by rw [htime]
    _ = inner ℝ
        ((predictableProjection 𝓅 D : PredictableProcessL2 𝓅 P) : TimeProcessL2 P)
        (V : TimeProcessL2 P) := hproj.symm
    _ = inner ℝ (predictableProjection 𝓅 D) V := rfl
end Malliavin
