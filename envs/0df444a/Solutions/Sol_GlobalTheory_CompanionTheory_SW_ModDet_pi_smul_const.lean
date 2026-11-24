-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ModDet.pi_smul_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:29:03.582634+00:00
-- url     : https://prove2.me/submissions/391eea69-03e5-4743-939a-f34b8fa97449

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixTransvectionDiagonalDecompositionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarInvariantUnderTransvectionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MapMulVecEqSmul

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
theorem _root_.solution {ι : Type} [Fintype ι] (lam : Measure K) [SigmaFinite lam] (c : ι → ℝ≥0) :
    Measure.pi (fun i => c i • lam) = (∏ i, c i) • Measure.pi (fun _ : ι => lam) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib,
    ENNReal.coe_finset_prod]
end GlobalTheory.CompanionTheory.SW.ModDet
