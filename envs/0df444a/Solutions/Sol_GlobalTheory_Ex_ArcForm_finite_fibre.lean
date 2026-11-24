-- Prove2me | solution 1 for GlobalTheory.Ex.ArcForm.finite_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:44:37.950734+00:00
-- url     : https://prove2.me/submissions/ca6ceaa7-11e2-4e2c-91ee-c07008995eed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AevalArcTxEqZero
import Theorems.Thm_GlobalTheory_ClassMin_finite_sublevel
import Theorems.Thm_GlobalTheory_ClassMin_realExtension_ofIntBilin_posDef
import Theorems.Thm_GlobalTheory_Conv_coe_expandConv
import Theorems.Thm_GlobalTheory_Conv_coe_expandConvLaurent
import Theorems.Thm_GlobalTheory_Conv_expandConv_u
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Conv.coe_expandConv
attribute [local simp] GlobalTheory.Conv.coe_expandConvLaurent
attribute [local simp] GlobalTheory.Conv.expandConv_u



set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators Topology
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.ArcForm
namespace GlobalTheory.Ex.ArcForm
theorem _root_.solution {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) {m : ℕ} (hm : m ≠ 0)
    (y : N.X) (n : ℤ) : {χ : N.X | β.be (y + m • χ) (y + m • χ) / (2 * m ^ 2) = n}.Finite := by
  have h := GlobalTheory.ClassMin.finite_sublevel
    (GlobalTheory.ClassMin.realExtension_ofIntBilin_posDef β.symm β.pos) (((n + 1) * (2 * m ^ 2) : ℤ) / 2 : ℝ)
  have hinj : Function.Injective fun χ : N.X => y + m • χ := fun a b hab =>
    smul_right_injective N.X (Int.natCast_ne_zero.2 hm) (by
      simpa only [natCast_zsmul] using add_left_cancel hab)
  refine (h.preimage hinj.injOn).subset fun χ hχ => ?_
  have hχ' : β.be (y + m • χ) (y + m • χ) / (2 * m ^ 2) = n := hχ
  have hpos : (0 : ℤ) < 2 * m ^ 2 := by positivity
  have h2 := Int.lt_ediv_add_one_mul_self (β.be (y + m • χ) (y + m • χ)) hpos
  rw [hχ'] at h2
  simp only [Set.mem_preimage, Set.mem_setOf_eq, GlobalTheory.ClassMin.ofIntBilin_apply]
  have h3 : ((β.be (y + m • χ) (y + m • χ) : ℤ) : ℝ) ≤ (((n + 1) * (2 * m ^ 2) : ℤ) : ℝ) := by
    exact_mod_cast h2.le
  linarith
end GlobalTheory.Ex.ArcForm
