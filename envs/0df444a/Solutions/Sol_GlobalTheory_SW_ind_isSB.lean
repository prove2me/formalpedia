-- Prove2me | solution 1 for GlobalTheory.SW.ind_isSB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:11:43.161077+00:00
-- url     : https://prove2.me/submissions/63c54ac3-b30d-4ee2-997d-4025504889f0

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TestFunctionWitness
import Theorems.Thm_GlobalTheory_SW_ind_sb

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
    IsSB (fun x : Matrix κ ι K => if IntM x then (1:ℂ) else 0) := ⟨1, one_pos, ind_sb⟩
end GlobalTheory.SW
