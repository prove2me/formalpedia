-- Prove2me | solution 1 for GlobalTheory.JR.MeasTransport.map_selfDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:01:26.078945+00:00
-- url     : https://prove2.me/submissions/7b9b5a57-a6ab-4b0d-8e79-12815b3da0fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulMatMemUnitaryGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MapIsIsomSelfDualMeasureKerLEqPiHaar
import Theorems.Thm_GlobalTheory_JR_MeasTransport_trForm_apply
import Theorems.Thm_GlobalTheory_JR_MeasTransport_kerL_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.MeasTransport
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.MeasTransport
theorem _root_.solution [hU : Unram F E] [MeasurableSpace E] [BorelSpace E] (A : Et F E) (ψ : AddChar F ℂ) {r : ℕ}
    {x : A.K} {j : A.L ≃ₗ[E] (Fin r → E)} (hx : A.IsIsom x j) (μ : Measure A.L) (hμ : SelfDual μ (A.kerL ψ x)) :
    SelfDual (Measure.map j μ) (fun a b => ψ (trForm (F := F) r a b)) := by
  haveI : IsUltrametricDist E := hU.ultraE
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : LocallyCompactSpace E := hU.lcE
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  haveI : IsModuleTopology F E := isModuleTopologyOfFiniteDimensional
  haveI : IsModuleTopology F (Fin r → E) := IsModuleTopology.instPi

  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L
  haveI : ContinuousSMul F A.L := IsModuleTopology.toContinuousSMul F A.L
  let jF : A.L ≃ₗ[F] (Fin r → E) := j.restrictScalars F
  have hc : Continuous jF := IsModuleTopology.continuous_of_linearMap jF.toLinearMap
  have hcs : Continuous jF.symm := IsModuleTopology.continuous_of_linearMap jF.symm.toLinearMap
  let jC : A.L ≃L[F] (Fin r → E) := { jF with continuous_toFun := hc, continuous_invFun := hcs }
  have hcoe : (⇑jC : A.L → Fin r → E) = ⇑j := rfl
  have hme : MeasurableEmbedding (⇑j) := by rw [← hcoe]; exact jC.toHomeomorph.measurableEmbedding
  haveI := hμ.1
  have hfour : ∀ (g : (Fin r → E) → ℂ) (y : A.L),
      fourB (Measure.map j μ) (fun a b => ψ (trForm (F := F) r a b)) g (j y) = fourB μ (A.kerL ψ x) (g ∘ j) y := by
    intro g y
    unfold fourB
    rw [hme.integral_map]
    simp only [Function.comp, kerL_eq A ψ hx, trForm_apply]
  refine ⟨by rw [← hcoe]; exact jC.isAddHaarMeasure_map μ, fun f hf v => ?_⟩
  obtain ⟨y, rfl⟩ := j.surjective v
  have hfj : IsTest (f ∘ j) := by
    refine ⟨hf.1.comp_continuous (by rw [← hcoe]; exact jC.continuous), ?_⟩
    rw [← hcoe]; exact hf.2.comp_homeomorph jC.toHomeomorph
  rw [hfour]
  have h2 : (fourB (Measure.map j μ) (fun a b => ψ (trForm (F := F) r a b)) f) ∘ j = fourB μ (A.kerL ψ x) (f ∘ j) :=
    funext fun y => hfour f y
  rw [h2, hμ.2 _ hfj y]
  simp [map_neg]
end GlobalTheory.JR.MeasTransport
