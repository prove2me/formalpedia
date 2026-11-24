-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HInv.map_tuple_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:51:44.136074+00:00
-- url     : https://prove2.me/submissions/3f56994a-885a-4819-8652-6cfb22649c5a

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraProperties
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MapMulVecEqSmul
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MapMulEqOfNormOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitaryActionPreservesHaarLocal
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ModDet_map_mulVec_eq_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_NormOneHaar_map_mul_eq_of_norm_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HInv
namespace GlobalTheory.CompanionTheory.SW.HInv
theorem _root_.solution {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [LocallyCompactSpace K] [SecondCountableTopology K] [T2Space K] [MeasurableSpace K]
    [BorelSpace K] [IsArtinianRing K] [IsReduced K] (τ : K →+* K) (hc : Continuous τ)
    (hi : ∀ y, τ (τ y) = y) {M n : ℕ} (A : Matrix (Fin M) (Fin M) K)
    (hA : A.det * τ A.det = 1) (μ : Measure (Fin n → Fin M → K)) [μ.IsAddHaarMeasure] :
    μ.map (fun X a => A *ᵥ X a) = μ := by
  let lam : Measure K := Measure.addHaar
  have hl : lam.map (fun y => A.det * y) = lam :=
    NormOneHaar.map_mul_eq_of_norm_one K τ hc hi lam _ hA
  let μ0 : Measure (Fin M → K) := Measure.pi fun _ => lam
  have hdet : IsUnit A.det := IsUnit.of_mul_eq_one _ hA
  have h0 : μ0.map (fun x => A *ᵥ x) = μ0 := by
    have := ModDet.map_mulVec_eq_smul K (Fin M) μ0 lam A hdet 1 (by simpa using hl)
    simpa using this
  let P : Measure (Fin n → Fin M → K) := Measure.pi fun _ => μ0
  have hmeas : Measurable (fun x : Fin M → K => A *ᵥ x) :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  haveI hs : SigmaFinite (μ0.map (fun x => A *ᵥ x)) := by
    rw [h0]; infer_instance
  have hP : P.map (fun X a => A *ᵥ X a) = P := by
    have := Measure.pi_map_pi (μ := fun _ : Fin n => μ0) (f := fun _ x => A *ᵥ x)
      (fun _ => hmeas.aemeasurable)
    simpa only [h0] using this
  have e := Measure.isAddLeftInvariant_eq_smul μ P
  rw [e, Measure.map_smul, hP]
end GlobalTheory.CompanionTheory.SW.HInv
