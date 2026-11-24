-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Transv.map_toMatrix_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:16:57.688798+00:00
-- url     : https://prove2.me/submissions/783b27bf-4b86-4b20-9550-f6e32f81dde5

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarInvariantUnderTransvection
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Transv_measurePreserving_pi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Transv
namespace GlobalTheory.CompanionTheory.SW.Transv
theorem _root_.solution (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [LocallyCompactSpace K] [SecondCountableTopology K] [T2Space K] [MeasurableSpace K]
    [BorelSpace K] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : Measure (ι → K))
    [μ.IsAddHaarMeasure] (t : Matrix.TransvectionStruct ι K) :
    μ.map (fun x => t.toMatrix *ᵥ x) = μ := by
  let ν : Measure K := Measure.addHaar
  let P : Measure (ι → K) := Measure.pi fun _ : ι => ν
  haveI : P.IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hμ : μ = Measure.addHaarScalarFactor μ P • P := Measure.isAddLeftInvariant_eq_smul μ P
  have hP : P.map (fun x => t.toMatrix *ᵥ x) = P := (measurePreserving_pi ν t).map_eq
  generalize Measure.addHaarScalarFactor μ P = c at hμ
  rw [hμ, Measure.map_smul, hP]
end GlobalTheory.CompanionTheory.SW.Transv
