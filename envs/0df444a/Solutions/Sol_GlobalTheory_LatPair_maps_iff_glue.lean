-- Prove2me | solution 1 for GlobalTheory.LatPair.maps_iff_glue
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:48.167745+00:00
-- url     : https://prove2.me/submissions/79350027-15b5-42ec-bcd3-10953ca0c14e

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
variable [Fintype n']
variable {P : Pair k n'} {Q : Pair k n} {x : Matrix n n' k}
namespace GlobalTheory.LatPair
theorem _root_.solution {e : n' → k} {e' : n → k} (he : P.HasVal e 1) (he' : Q.HasVal e' 1) :
    Maps P Q x ↔ (∀ y ∈ P.ker, x *ᵥ y ∈ Q.ker) ∧ x *ᵥ e - e' ∈ Q.ker := by
  rw [maps_iff_hasVal, ← Pair.hasVal_one_iff he']
  refine ⟨fun h => ⟨fun y hy => Pair.mem_ker.2 (h _ _ (Pair.mem_ker.1 hy)), h _ _ he⟩, fun h y a hy => ?_⟩
  obtain ⟨s, rfl, hs⟩ := (Pair.hasVal_iff he).1 hy
  refine (Pair.hasVal_iff h.2).2 ⟨s, rfl, ?_⟩
  simpa only [mulVec_sub, mulVec_smul] using h.1 _ hs
end GlobalTheory.LatPair
