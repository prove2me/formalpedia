-- Prove2me | solution 1 for GlobalTheory.SW.ind_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:11:48.159007+00:00
-- url     : https://prove2.me/submissions/f9e6abd6-f8ee-42f5-9280-897c6b3e4e4f

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TestFunctionWitness

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex
open GlobalTheory GlobalTheory.SW
open Classical
namespace GlobalTheory.SW
theorem _root_.solution {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι] :
    (fun x : Matrix κ ι K => if IntM x then (1:ℂ) else 0) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  rw [if_pos (show IntM (0 : Matrix κ ι K) from fun k i => by simpa using isIntegral_zero)] at h0
  exact one_ne_zero h0
end GlobalTheory.SW
