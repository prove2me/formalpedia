-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LocInv.iUnion_valBall_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:35:19.062431+00:00
-- url     : https://prove2.me/submissions/1cd419c7-f8fb-463a-ba8a-344143ff1232

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalFieldSelfdualMeasureExists
import Theorems.Thm_GroundTheory_LocalField_valBall_antitone


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LocInv
open GroundTheory.LocalField ValuativeRel MeasureTheory Topology Filter
open scoped NNReal ENNReal
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]
namespace GlobalTheory.CompanionTheory.SW.LocInv
theorem _root_.solution (n : ℤ) : ⋃ k : ℕ, (valBall K (n - (k : ℤ)) : Set K) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨m, hm⟩ := exists_mem_valBall_neg_nat x
  refine Set.mem_iUnion.mpr ⟨(n + m).toNat, ?_⟩
  exact valBall_antitone (by omega) hm
end GlobalTheory.CompanionTheory.SW.LocInv
