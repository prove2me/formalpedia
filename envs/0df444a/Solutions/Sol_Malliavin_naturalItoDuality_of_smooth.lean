-- Prove2me | solution 1 for Malliavin.naturalItoDuality_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:44:51.272913+00:00
-- url     : https://prove2.me/submissions/2bf6648c-f871-4033-8415-c0bc7f1a9c20

import Definitions.Def_Malliavin_KernelIdentification
import Definitions.Def_Malliavin_NaturalClarkOcone

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
    (hCore : SmoothNaturalItoDuality
      hB coordinate coordinate_apply generated hsm hnat)
    (F : D12 P) (U : PredictableProcessL2 𝓅 P) :
    inner ℝ (F.1 - expectationL2 F.1) (naturalItoIntegral hB hsm hnat U) =
      inner ℝ
        (predictableProjection 𝓅
          (Malliavin.timeDerivative hB coordinate coordinate_apply generated
            (mderivD12 P F))) U := by
  obtain ⟨G, hG, hDG⟩ := inGraphClosure_mderivClosure P F.2
  let R : Lp (CameronMartin.Space P) 2 P →L[ℝ] PredictableProcessL2 𝓅 P :=
    (predictableProjection 𝓅).comp
      (Malliavin.timeDerivative hB coordinate coordinate_apply generated
        ).toContinuousLinearMap
  have heq (n : ℕ) :
      inner ℝ (centeredPartCLM ((G n).2.toLp P))
          (naturalItoIntegral hB hsm hnat U) =
        inner ℝ (R ((G n).2.mderivLp P)) U := by
    rw [centeredPartCLM_apply]
    exact hCore (G n).1 (G n).2 U
  have hcenter :
      Tendsto (fun n ↦ centeredPartCLM ((G n).2.toLp P)) atTop
        (𝓝 (centeredPartCLM F.1)) :=
    ((centeredPartCLM (P := P)).continuous.tendsto F.1).comp hG
  have hleft :
      Tendsto
        (fun n ↦ inner ℝ (centeredPartCLM ((G n).2.toLp P))
          (naturalItoIntegral hB hsm hnat U)) atTop
        (𝓝 (inner ℝ (centeredPartCLM F.1)
          (naturalItoIntegral hB hsm hnat U))) :=
    hcenter.inner tendsto_const_nhds
  have hrightProcess :
      Tendsto (fun n ↦ R ((G n).2.mderivLp P)) atTop
        (𝓝 (R (mderivClosure P F.1))) :=
    (R.continuous.tendsto (mderivClosure P F.1)).comp hDG
  have hright :
      Tendsto (fun n ↦ inner ℝ (R ((G n).2.mderivLp P)) U) atTop
        (𝓝 (inner ℝ (R (mderivClosure P F.1)) U)) :=
    hrightProcess.inner tendsto_const_nhds
  rw [show (fun n ↦ inner ℝ (centeredPartCLM ((G n).2.toLp P))
      (naturalItoIntegral hB hsm hnat U)) =
      fun n ↦ inner ℝ (R ((G n).2.mderivLp P)) U by
        funext n
        exact heq n] at hleft
  have hlimit :
      inner ℝ (centeredPartCLM F.1) (naturalItoIntegral hB hsm hnat U) =
        inner ℝ (R (mderivClosure P F.1)) U :=
    tendsto_nhds_unique hleft hright
  rw [centeredPartCLM_apply] at hlimit
  change inner ℝ (F.1 - expectationL2 F.1)
      (naturalItoIntegral hB hsm hnat U) =
    inner ℝ
      (predictableProjection 𝓅
        (Malliavin.timeDerivative hB coordinate coordinate_apply generated
          (mderivD12 P F))) U at hlimit
  exact hlimit
end Malliavin
