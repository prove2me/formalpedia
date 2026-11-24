-- Prove2me | solution 1 for GlobalTheory.LatPair.Pair.lat_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:53:22.885915+00:00
-- url     : https://prove2.me/submissions/c367caff-5cee-47d6-a48b-9b1f9b2a8c7a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Theorems.Thm_GlobalTheory_LatPair_Pair_ker_le

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
open GlobalTheory.LatPair.Pair
variable {P Q : Pair k n} {x y e : n → k} {a b : 𝓀[k]}
namespace GlobalTheory.LatPair.Pair
theorem _root_.solution (he : P.HasVal e 1) : P.lat = P.ker ⊔ Submodule.span 𝒪[k] {e} := by
  refine le_antisymm (fun x hx => ?_) (sup_le P.ker_le ((Submodule.span_singleton_le_iff_mem _ _).2 he.mem))
  obtain ⟨s, -, h⟩ := (hasVal_iff he).1 (P.hasVal_fn ⟨x, hx⟩)
  have := Submodule.add_mem_sup h (Submodule.smul_mem _ s (Submodule.mem_span_singleton_self e))
  simpa using this
end GlobalTheory.LatPair.Pair
