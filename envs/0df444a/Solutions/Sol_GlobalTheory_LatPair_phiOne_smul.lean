-- Prove2me | solution 1 for GlobalTheory.LatPair.phiOne_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:54:41.568517+00:00
-- url     : https://prove2.me/submissions/334bca5e-42cf-48f5-983f-2924a21b8d2a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Theorems.Thm_GlobalTheory_LatPair_maps_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable [Fintype n']
variable {P : Pair k n'} {Q : Pair k n} {x : Matrix n n' k}
variable [DecidableEq n'] [Fintype n] [DecidableEq n]
namespace GlobalTheory.LatPair
theorem _root_.solution (g : GL n' k) (h : GL n k) :
    phiOne (g • P) (h • Q) x = phiOne P Q ((h⁻¹ : GL n k).val * x * g.val) := by
  classical
  exact if_congr (maps_smul g h) rfl rfl
end GlobalTheory.LatPair
