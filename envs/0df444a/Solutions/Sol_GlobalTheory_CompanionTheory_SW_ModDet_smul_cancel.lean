-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ModDet.smul_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:29:27.018071+00:00
-- url     : https://prove2.me/submissions/8cbfb7f8-2d07-4185-b491-c43b6b30684f

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
theorem _root_.solution (lam : Measure K) [lam.IsAddHaarMeasure] {a b : ℝ≥0}
    (h : a • lam = b • lam) : a = b := by
  obtain ⟨C, hC, hn⟩ := exists_compact_mem_nhds (0 : K)
  have h0 : lam C ≠ 0 := (Measure.measure_pos_of_mem_nhds lam hn).ne'
  have h1 : lam C ≠ ∞ := hC.measure_lt_top.ne
  have e := congrArg (fun m : Measure K => m C) h
  simp only [Measure.smul_apply, Measure.nnreal_smul_coe_apply] at e
  exact ENNReal.coe_injective ((ENNReal.mul_left_inj h0 h1).1 e)
end GlobalTheory.CompanionTheory.SW.ModDet
