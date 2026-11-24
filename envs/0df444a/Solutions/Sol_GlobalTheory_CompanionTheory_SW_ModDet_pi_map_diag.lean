-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ModDet.pi_map_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:49:21.827899+00:00
-- url     : https://prove2.me/submissions/feebed8a-2fc1-4405-ace2-53f1987f44a0

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixTransvectionDiagonalDecompositionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarInvariantUnderTransvectionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MapMulVecEqSmul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ModDet_map_mul_unit
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ModDet_pi_smul_const

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ModDet
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  [LocallyCompactSpace K] [SecondCountableTopology K] [T2Space K] [MeasurableSpace K] [BorelSpace K]
namespace GlobalTheory.CompanionTheory.SW.ModDet
theorem _root_.solution {ι : Type} [Fintype ι] (lam : Measure K) [lam.IsAddHaarMeasure] (D : ι → Kˣ) :
    (Measure.pi fun _ : ι => lam).map (fun x i => (D i : K) * x i) =
      (∏ i, (distribHaarChar K (D i))⁻¹) • Measure.pi fun _ : ι => lam := by
  have hm : ∀ i, Measurable (fun y : K => (D i : K) * y) := fun i =>
    (continuous_const.mul continuous_id).measurable
  have hs : ∀ i, SigmaFinite (lam.map (fun y : K => (D i : K) * y)) := fun i => by
    rw [map_mul_unit]; infer_instance
  rw [Measure.pi_map_pi (fun i => (hm i).aemeasurable)]
  simp_rw [map_mul_unit]
  exact pi_smul_const lam _
end GlobalTheory.CompanionTheory.SW.ModDet
