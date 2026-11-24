-- Prove2me | solution 1 for GlobalTheory.LatPair.sumOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:32.834602+00:00
-- url     : https://prove2.me/submissions/a654741e-43a3-4b90-a00a-c5abcad3b553

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift

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
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (φ : Form k n M)
namespace GlobalTheory.LatPair
theorem _root_.solution (S : Pair k n → Finset (Pair k n)) (w : Pair k n → Pair k n → ℂ) (P : Pair k n) :
    sumOp S w φ P = ∑ Q ∈ S P, w P Q • φ Q := rfl
end GlobalTheory.LatPair
