-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegLoc.Scaled.unit_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:38:52.829865+00:00
-- url     : https://prove2.me/submissions/74f89e87-7963-4969-b49a-5ee12b8506d8

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SumCompSurj
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardRangeMulQuotientBoundedLevel
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_mem_lev_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegLoc GlobalTheory.CompanionTheory.SiegLoc.Scaled
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.SiegLoc.Scaled
theorem _root_.solution {ϖ x : R} (hϖ : ¬ IsUnit ϖ) (hx : IsUnit x) : x ∉ lev ϖ 1 := by
  intro h
  obtain ⟨t, rfl⟩ := mem_lev_iff.1 h
  exact hϖ (by simpa using isUnit_of_mul_isUnit_left hx)
end GlobalTheory.CompanionTheory.SiegLoc.Scaled
