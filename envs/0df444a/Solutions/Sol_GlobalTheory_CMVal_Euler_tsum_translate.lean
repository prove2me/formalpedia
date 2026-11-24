-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.tsum_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:41:40.1558+00:00
-- url     : https://prove2.me/submissions/8ec97f7f-7c51-48b8-99c2-fe1677a16bf6

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallLocInShift
import Theorems.Thm_GlobalTheory_CMVal_Euler_cs_mk
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
theorem _root_.solution (hω : ∀ u ∈ U, ω u = 1) {M : Set G} (hM : Stable U M) (π : G) :
    ∑' z, cs U ω {y | π⁻¹ * y ∈ M} z = ω π * ∑' z, cs U ω M z := by
  classical
  have hM' : Stable U {y | π⁻¹ * y ∈ M} := fun u hu y => by
    simp only [Set.mem_setOf_eq, ← mul_assoc]; exact hM u hu _
  rw [← (Equiv.mulLeft (QuotientGroup.mk π : G ⧸ U)).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun z => ?_
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
  show cs U ω _ (QuotientGroup.mk (π * y)) = _
  rw [cs_mk hω hM', cs_mk hω hM, Set.indicator_apply, Set.indicator_apply]
  simp
end GlobalTheory.CMVal.Euler
