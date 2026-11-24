-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.tendsto_tsum_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:22:40.043347+00:00
-- url     : https://prove2.me/submissions/92b949cc-ad24-4d2f-a2fc-a090049440df

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallLocInShift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler
variable {G : Type} [CommGroup G] (U : Subgroup G) (ω : G →* ℂ)
variable {U ω}
namespace GlobalTheory.CMVal.Euler
theorem _root_.solution (hω : ∀ u ∈ U, ω u = 1) {B : Set G} (hB : Summable (cs U ω B)) {ι : Type} (l : Filter ι)
    (M : ι → Set G) (h : ∀ s, M s ⊆ B) (h1 : ∀ y ∈ U, ∀ s, y ∈ M s) (h2 : ∀ y ∉ U, ∀ᶠ s in l, y ∉ M s) :
    Tendsto (fun s => ∑' z, cs U ω (M s) z) l (𝓝 1) := by
  classical
  have h0 : ∑' z : G ⧸ U, (if z = 1 then (1 : ℂ) else 0) = 1 := tsum_ite_eq _ _
  rw [← h0]
  refine tendsto_tsum_of_dominated_convergence hB.norm (fun z => ?_)
    (Eventually.of_forall fun s z => norm_indicator_le_of_subset (h s) _ _)
  have h4 : z.out ∈ U ↔ z = 1 := by rw [← QuotientGroup.eq_one_iff, QuotientGroup.out_eq']
  by_cases a : z = 1
  · rw [if_pos a]
    refine tendsto_const_nhds.congr fun s => ?_
    rw [cs, Set.indicator_of_mem (h1 _ (h4.2 a) s), hω _ (h4.2 a)]
  · rw [if_neg a]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [h2 _ (fun hh => a (h4.1 hh))] with s hs
    rw [cs, Set.indicator_of_notMem hs]
end GlobalTheory.CMVal.Euler
