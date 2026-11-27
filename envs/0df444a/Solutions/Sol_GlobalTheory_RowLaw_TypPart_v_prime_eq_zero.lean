-- Prove2me | solution 1 for GlobalTheory.RowLaw.TypPart.v_prime_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T06:25:40.393312+00:00
-- url     : https://prove2.me/submissions/2007f72d-e4c4-4292-93be-a5ac658b96cc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugedFormalGroupCurveLogarithmsAddSubgroupRescaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugedCurveLogarithmsClosedUnderTadicLimits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CurveLogarithmsInvNatCastSmulMemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowExponentPartMemGaugedCurveLogarithms
import Theorems.Thm_GlobalTheory_RowLaw_TypPart_ge_intCast
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_ge_natCast
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
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
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
noncomputable section
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.TypPart
variable {C : Type} [Field C]
namespace GlobalTheory.RowLaw.TypPart
theorem _root_.solution (V : VF C) {p : ℕ} (hp : p.Prime) (hpl : p ≠ V.l) : V.v (p : C) = 0 := by
  have hc : IsCoprime (p : ℤ) (V.l : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp V.l_prime).2 hpl)
  obtain ⟨a, b, hab⟩ := hc
  have h1 : (a : C) * (p : C) + (b : C) * (V.l : C) = 1 := by
    have := congrArg (fun z : ℤ => (z : C)) hab
    simpa using this
  have h0 : (0 : WithTop ℝ) ≤ V.v (p : C) := by simpa [VF.Ge] using VF.ge_natCast (V := V) p
  have ha : (0 : WithTop ℝ) ≤ V.v (a : C) := by simpa [VF.Ge] using ge_intCast V a
  have hb : (0 : WithTop ℝ) ≤ V.v (b : C) := by simpa [VF.Ge] using ge_intCast V b
  by_contra hne
  have hpos : (0 : WithTop ℝ) < V.v (p : C) := lt_of_le_of_ne h0 (Ne.symm hne)
  have e1 : (0 : WithTop ℝ) < V.v ((a : C) * (p : C)) := by
    rw [V.v.map_mul]; exact lt_of_lt_of_le hpos (le_add_of_nonneg_left ha)
  have e2 : (0 : WithTop ℝ) < V.v ((b : C) * (V.l : C)) := by
    rw [V.v.map_mul, V.v_l]; exact lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left hb)
  have := V.v.map_lt_add e1 e2
  rw [h1, V.v.map_one] at this
  exact lt_irrefl _ this
end GlobalTheory.RowLaw.TypPart
