-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.tsum_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:02:50.967073+00:00
-- url     : https://prove2.me/submissions/250f8fc5-bd49-4532-bda4-edeeec5e9aa9

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
theorem _root_.solution (hω : ∀ u ∈ U, ω u = 1) {B M M' : Set G} (hB : Summable (cs U ω B)) (h : M' ⊆ B) (hM : Stable U M)
    {ι : Type} (R : Finset ι) (g : ι → G) (hg : ∀ r ∈ R, ω (g r) = 1)
    (h1 : ∀ y ∈ M', ∃! r, r ∈ R ∧ (g r)⁻¹ * y ∈ M) (h2 : ∀ r ∈ R, ∀ y, (g r)⁻¹ * y ∈ M → y ∈ M') :
    ∑' z, cs U ω M' z = R.card * ∑' z, cs U ω M z := by
  classical
  have h3 : ∑ r ∈ R, ∑' z, cs U ω {y | (g r)⁻¹ * y ∈ M} z = R.card * ∑' z, cs U ω M z := by
    rw [Finset.sum_congr rfl fun r hr => (tsum_translate hω hM (g r)).trans (by rw [hg r hr, one_mul])]
    simp
  rw [← h3, ← Summable.tsum_finsetSum fun r hr =>
    summable_mono (M := {y | (g r)⁻¹ * y ∈ M}) hB (fun y hy => h (h2 r hr y hy))]
  refine tsum_congr fun z => ?_
  simp only [cs, Set.indicator_apply, Set.mem_setOf_eq]
  by_cases a : z.out ∈ M'
  · obtain ⟨r, ⟨hr, hr'⟩, hu⟩ := h1 _ a
    rw [if_pos a, Finset.sum_eq_single r, if_pos hr']
    · intro b hb hne
      exact if_neg fun hh => hne (hu b ⟨hb, hh⟩)
    · exact fun hh => absurd hr hh
  · rw [if_neg a]
    exact (Finset.sum_eq_zero fun r hr => if_neg fun hh => a (h2 r hr _ hh)).symm
end GlobalTheory.CMVal.Euler
