-- Prove2me | solution 1 for GlobalTheory.LatPair.Pair.smul_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:00:27.75777+00:00
-- url     : https://prove2.me/submissions/e86c56e1-1418-4d16-b79f-dd8c9c564a81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Theorems.Thm_GlobalTheory_LatPair_Pair_HasVal_gl_smul

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
variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
variable {n n' : Type*}
variable [Fintype n] [DecidableEq n]
open GlobalTheory.LatPair.Pair
namespace GlobalTheory.LatPair.Pair
theorem _root_.solution {g : GL n k} {P : Pair k n} {e : n → k} (he : P.HasVal e 1) :
    g • P = P ↔ g • P.ker = P.ker ∧ g • e - e ∈ P.ker := by
  rw [← hasVal_one_iff he]
  exact ⟨fun h => ⟨by rw [← smul_ker, h], by simpa [h] using he.gl_smul g⟩,
    fun h => ext_ker ((smul_ker g P).trans h.1) (he.gl_smul g) h.2⟩
end GlobalTheory.LatPair.Pair
