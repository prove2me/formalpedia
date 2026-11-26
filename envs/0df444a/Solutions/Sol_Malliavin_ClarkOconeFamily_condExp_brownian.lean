-- Prove2me | solution 1 for Malliavin.ClarkOconeFamily.condExp_brownian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:08.446343+00:00
-- url     : https://prove2.me/submissions/8e883ead-0f04-4e79-971a-bebcd9bb46a8

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_Malliavin_PointwiseCondExp
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_IsWienerGenerated_measurable
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.mem_symmetricSubmodule



set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
variable {B : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
variable {B : ℝ≥0 → W → ℝ}
namespace Malliavin
namespace _root_.Malliavin.ClarkOconeFamily
theorem _root_.solution
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    {a b : ℝ≥0} (hab : a ≤ b) :
    P[B b | 𝓕 a] =ᵐ[P] B a := by
  have hBb : MemLp (B b) 2 P :=
    (C.isPreBrownian.isGaussianProcess.hasGaussianLaw_eval b).memLp_two
  have hBa : MemLp (B a) 2 P :=
    (C.isPreBrownian.isGaussianProcess.hasGaussianLaw_eval a).memLp_two
  -- the increment is independent of `𝓕 a`
  have hshift := C.isPreBrownian.indepFun_shift a
  have heval : Measurable (fun x : ℝ≥0 → ℝ ↦ x (b - a)) := measurable_pi_apply _
  have hfuturePast := hshift.comp heval measurable_id
  have hfuturePast' : IndepFun (fun w ↦ B b w - B a w)
      (fun w (t : Set.Iic a) ↦ B t w) P := by
    convert hfuturePast using 1
    · funext w
      change B b w - B a w = B (a + (b - a)) w - B a w
      rw [add_comm, tsub_add_cancel_of_le hab]
    · rfl
  have hind := (IndepFun_iff_Indep _ _ _).mp hfuturePast'
  have hnat : 𝓕 a =
      MeasurableSpace.comap (fun w (t : Set.Iic a) ↦ B t w) inferInstance := by
    rw [C.naturalFiltration, Filtration.natural_eq_comap]
  rw [← hnat] at hind
  -- conditional expectation of the increment vanishes
  have hmeas_incr : Measurable fun w ↦ B b w - B a w :=
    (C.stronglyMeasurable b).measurable.sub (C.stronglyMeasurable a).measurable
  have hincr : P[(fun w ↦ B b w - B a w) | 𝓕 a] =ᵐ[P] fun _ ↦ 0 := by
    have h := condExp_indep_eq (μ := P)
      (m₁ := MeasurableSpace.comap (fun w ↦ B b w - B a w) inferInstance)
      (m₂ := 𝓕 a) hmeas_incr.comap_le (𝓕.le a)
      (Measurable.stronglyMeasurable (measurable_iff_comap_le.mpr le_rfl)) hind
    refine h.trans ?_
    have hzero : ∫ w, (B b w - B a w) ∂P = 0 := by
      rw [integral_sub (hBb.integrable one_le_two) (hBa.integrable one_le_two),
        C.isPreBrownian.integral_eval b, C.isPreBrownian.integral_eval a, sub_zero]
    filter_upwards with w
    rw [hzero]
  -- `B a` is `𝓕 a`-measurable
  have hcomap_le : MeasurableSpace.comap (B a) inferInstance ≤ 𝓕 a := by
    rw [C.naturalFiltration]
    exact le_iSup₂ (f := fun (j : ℝ≥0) (_ : j ≤ a) ↦
      MeasurableSpace.comap (B j) inferInstance) a le_rfl
  have hBa_meas : StronglyMeasurable[𝓕 a] (B a) :=
    (Measurable.mono (measurable_iff_comap_le.mpr le_rfl) hcomap_le le_rfl).stronglyMeasurable
  -- assemble
  have hsplit : B b = fun w ↦ (B b w - B a w) + B a w := by
    funext w
    ring
  calc P[B b | 𝓕 a]
      = P[(fun w ↦ (B b w - B a w) + B a w) | 𝓕 a] := by rw [← hsplit]
    _ =ᵐ[P] P[(fun w ↦ B b w - B a w) | 𝓕 a] + P[B a | 𝓕 a] :=
        condExp_add ((hBb.integrable one_le_two).sub (hBa.integrable one_le_two))
          (hBa.integrable one_le_two) _
    _ =ᵐ[P] (fun _ ↦ (0 : ℝ)) + B a := by
        refine Filter.EventuallyEq.add hincr ?_
        exact condExp_of_stronglyMeasurable (𝓕.le a) hBa_meas (hBa.integrable one_le_two)
          |>.symm ▸ Filter.EventuallyEq.rfl
    _ =ᵐ[P] B a := by
        filter_upwards with w
        simp only [Pi.add_apply, zero_add]
end _root_.Malliavin.ClarkOconeFamily
end Malliavin
