-- Prove2me | solution 1 for GlobalTheory.PDivGroup.TateOver.exists_p_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:02:54.329422+00:00
-- url     : https://prove2.me/submissions/c819b644-e0e8-4429-a727-d4f140aee655

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsCounitEqOneMulEqZeroOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvEqOneOfForallPairing
import Theorems.Thm_GlobalTheory_PDivGroup_ptsMap_res_mulP
import Theorems.Thm_GlobalTheory_PDivGroup_pointsMap_mulP_res_eq_pow
import Theorems.Thm_GlobalTheory_PDivGroup_TateOver_conv_succ_pow
import Theorems.Thm_GlobalTheory_PDivGroup_exists_comp_res_iff
import Theorems.Thm_ReciprocityTheory_PGsh_IsPtDer_map_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module
open GlobalTheory
open GlobalTheory.PDivGroup
open PDiv TateFree
variable {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O)
variable {B : Type} [CommRing B] [Algebra O B]
variable [Fact p.Prime] {G}
namespace GlobalTheory.PDivGroup
namespace TateOver
theorem _root_.solution (t : G.TateOver B) (n : ℕ) (ht : t.conv (n + 1) = 1) :
    ∃ s : G.TateOver B, s.conv n = 1 ∧ (p : ℤ_[p]) • s = t := by
  have h1 : ∀ k, t.conv (k + 1) = 1 → t.conv 1 = 1 := fun k => by
    induction k with
    | zero => exact id
    | succ k ih => exact fun h => ih (by rw [← t.compat_conv, h, map_one])
  have h2 : ∀ k, t.conv (k + 1) ^ p ^ k = 1 := fun k => by
    induction k with
    | zero => rw [pow_zero, pow_one]; exact h1 n ht
    | succ k ih => rw [pow_succ', pow_mul, t.conv_succ_pow, ← map_pow, ih, map_one]
  choose s hs using fun k => (G.exists_comp_res_iff k (t.pt (k + 1))).2 (h2 k)
  have hs' : ∀ k, pointsMap B (G.res k) (toConv (s k)) = t.conv (k + 1) := fun k =>
    congrArg toConv (hs k)
  refine ⟨⟨s, fun k => congrArg ofConv (G.ptsMap_res_injective k
    (a₁ := pointsMap B (G.mulP k) (toConv (s (k + 1)))) (a₂ := toConv (s k)) ?_)⟩,
    G.ptsMap_res_injective n (((hs' n).trans ht).trans (map_one _).symm),
    TateOver.ext_conv fun k => ?_⟩
  · rw [ptsMap_res_mulP, ← pointsMap_mulP_res_eq_pow, hs', hs', t.compat_conv]
  · rw [TateOver.p_smul_conv, ← pointsMap_mulP_res_eq_pow, ← t.compat_conv, ← hs']
end TateOver
end GlobalTheory.PDivGroup
