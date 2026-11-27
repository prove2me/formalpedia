-- Prove2me | solution 1 for GlobalTheory.SeparatingSeq.ge_pow_pow_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T06:19:40.124807+00:00
-- url     : https://prove2.me/submissions/c3a9ddb4-d355-4f54-9e74-eced09bf0368

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntSOfMulEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsEmbeddingCongrIntegralCharacter
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsLadicSeparatingSequenceEmbeddings
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_l_inv_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_l_ne_zero
import Theorems.Thm_GlobalTheory_TeichSeq_ge_l_pow
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



set_option autoImplicit false
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.SeparatingSeq
open TeichSeq
variable {C : Type} [Field C] {V : VF C}
namespace GlobalTheory.SeparatingSeq
theorem _root_.solution {t c : C} (ht : V.Ge 0 t) (hc : V.Ge 0 c) (h : V.Ge 1 (t - c)) (n : ℕ) :
    V.Ge n (t ^ V.l ^ n - c ^ V.l ^ n) := by
  have hq : V.Ge 0 ((V.l : C)⁻¹ * (t - c)) := by simpa using h.l_inv_mul
  have hd : (V.l : intRing V) ∣ (⟨t, ht⟩ : intRing V) - ⟨c, hc⟩ :=
    ⟨⟨_, hq⟩, Subtype.ext (by
      show t - c = ((V.l : intRing V) : C) * ((V.l : C)⁻¹ * (t - c))
      rw [SubringClass.coe_natCast, mul_inv_cancel_left₀ VF.l_ne_zero])⟩
  obtain ⟨z, hz⟩ := (pow_dvd_pow _ (Nat.le_succ n)).trans (dvd_sub_pow_of_dvd_sub hd n)
  have hz' : t ^ V.l ^ n - c ^ V.l ^ n = (z : C) * (V.l : C) ^ n := by
    have := congrArg Subtype.val hz
    simpa [mul_comm] using this
  rw [hz']
  exact VF.Ge.mul_int z.2 (ge_l_pow V n)
end GlobalTheory.SeparatingSeq
