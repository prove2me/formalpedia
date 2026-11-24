-- Prove2me | solution 1 for GlobalTheory.Ex.RecPeriods.cubN_mul_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:44:17.721605+00:00
-- url     : https://prove2.me/submissions/8f24676a-7591-4feb-b5a4-974063ebf627

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIsoOnG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_N_split


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.RecPeriods
namespace GlobalTheory.Ex.RecPeriods
theorem _root_.solution {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ) (a b : ℕ) (y x : A) :
    cubN θ (b * a) 1 y x = cubN θ a 1 (y ^ b) x * cubN θ b 1 y x ^ a := by
  induction a with
  | zero => simp [cubN]
  | succ a ih =>
    have s := h.N_split b (y ^ (b * a)) y x
    have e : cubN θ (b * (a + 1)) 1 y x = cubN θ (b * a) 1 y x * cubN θ b (y ^ (b * a)) y x := by
      simp only [cubN, mul_add, mul_one, Finset.prod_range_add, one_mul, pow_add]
    have f : cubN θ (a + 1) 1 (y ^ b) x = cubN θ a 1 (y ^ b) x * θ (y ^ (b * a)) (y ^ b) x := by
      simp only [cubN, Finset.prod_range_succ, one_mul, pow_mul]
    rw [e, f, ih, s, pow_succ]
    ac_rfl
end GlobalTheory.Ex.RecPeriods
