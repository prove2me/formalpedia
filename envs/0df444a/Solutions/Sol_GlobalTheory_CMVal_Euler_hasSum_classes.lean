-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.hasSum_classes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:24:14.663803+00:00
-- url     : https://prove2.me/submissions/8f82e620-a309-4ceb-b479-b23697886372

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallLocInShift
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler
variable {G : Type} [CommGroup G] (U : Subgroup G) (ω : G →* ℂ)
variable {U ω}
namespace GlobalTheory.CMVal.Euler
theorem _root_.solution {M : Set G} (hM : Stable U M) (hs : Summable (cs U ω M)) :
    HasSum (fun z : {z : G ⧸ U // ∃ y : G, (QuotientGroup.mk y : G ⧸ U) = z ∧ y ∈ M} => ω z.1.out) (∑' z, cs U ω M z) := by
  classical
  have h1 : cs U ω M = Set.indicator {z : G ⧸ U | ∃ y : G, (QuotientGroup.mk y : G ⧸ U) = z ∧ y ∈ M} fun z => ω z.out := by
    funext z
    have : z.out ∈ M ↔ ∃ y : G, (QuotientGroup.mk y : G ⧸ U) = z ∧ y ∈ M := by
      refine ⟨fun h => ⟨_, QuotientGroup.out_eq' z, h⟩, ?_⟩
      rintro ⟨y, rfl, hy⟩
      obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U y
      rw [hu]; exact (hM u u.2 y).2 hy
    simp only [cs, Set.indicator_apply, Set.mem_setOf_eq, this]
  have h2 := hs.hasSum
  rw [h1] at h2
  rw [h1]
  exact hasSum_subtype_iff_indicator.2 h2
end GlobalTheory.CMVal.Euler
