-- Prove2me | solution 1 for GlobalTheory.LatPair.up_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:59:51.106945+00:00
-- url     : https://prove2.me/submissions/562d1e51-73d0-450b-8c36-7150c8f83035

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Theorems.Thm_GlobalTheory_LatPair_eq_glue_iff

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
variable (L : Submodule 𝒪[k] (n → k)) [hL : L.IsLattice k]
variable (q : Unif k)
namespace GlobalTheory.LatPair
theorem _root_.solution {y : L} (hy : Red.mk L y ≠ 0) : up L q ⟨_, hy⟩ = glue (isGlue_inv_smul L q hy) :=
  (eq_glue_iff _).2 ⟨up_ker _ _ _, (up_hasVal_iff _ _ _ _).2 rfl⟩
end GlobalTheory.LatPair
