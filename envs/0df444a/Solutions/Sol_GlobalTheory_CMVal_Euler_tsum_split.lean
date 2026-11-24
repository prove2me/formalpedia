-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.tsum_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:02:52.041001+00:00
-- url     : https://prove2.me/submissions/262d4826-1744-44f8-82a0-c099bc866bdc

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallLocInShift
import Theorems.Thm_GlobalTheory_CMVal_Euler_tsum_translate
import Theorems.Thm_GlobalTheory_CMVal_Euler_summable_mono
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
theorem _root_.solution (hω : ∀ u ∈ U, ω u = 1) {B M M₁ M' : Set G} (hB : Summable (cs U ω B)) (h : M ⊆ B) (h₁ : M₁ ⊆ M)
    (hM' : Stable U M') (π : G) (hπ : ∀ y, π⁻¹ * y ∈ M' ↔ y ∈ M ∧ y ∉ M₁) :
    ∑' z, cs U ω M z = ∑' z, cs U ω M₁ z + ω π * ∑' z, cs U ω M' z := by
  classical
  rw [← tsum_translate hω hM', ← (summable_mono hB (h₁.trans h)).tsum_add
    (summable_mono (M := {y | π⁻¹ * y ∈ M'}) hB (fun y hy => h ((hπ y).1 hy).1))]
  refine tsum_congr fun z => ?_
  simp only [cs, Set.indicator_apply, Set.mem_setOf_eq, hπ]
  by_cases a : z.out ∈ M₁
  · simp [a, h₁ a]
  · simp [a]
end GlobalTheory.CMVal.Euler
