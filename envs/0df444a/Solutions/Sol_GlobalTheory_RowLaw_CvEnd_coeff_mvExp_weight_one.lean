-- Prove2me | solution 1 for GlobalTheory.RowLaw.CvEnd.coeff_mvExp_weight_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T06:04:09.84626+00:00
-- url     : https://prove2.me/submissions/fedeb4b9-8474-489b-8a09-5d5521aee203

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AdjointEndPairMemGaugedCurveLogarithms
import Theorems.Thm_GlobalTheory_RowLaw_CvEnd_ordGe_pow
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
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.CvEnd
open MvPowerSeries
variable {C : Type} [Field C]
variable {σ τ : Type}
namespace GlobalTheory.RowLaw.CvEnd
theorem _root_.solution {w : τ → ℕ} {G : MvPowerSeries τ C} (hG : G ∈ ordGe C w 1) (e : τ →₀ ℕ)
    (he : Finsupp.weight w e = 1) : coeff e (mvExp G) = coeff e G := by
  classical
  have hne : e ≠ 0 := by
    rintro rfl
    simp at he
  show (∑ k ∈ Finset.range (e.degree + 1), coeff e (G ^ k) / (k.factorial : C)) = _
  rw [Finset.sum_eq_single 1]
  · simp
  · intro k _ hk
    by_cases h0 : k = 0
    · rw [h0, pow_zero, coeff_one, if_neg hne, zero_div]
    · rw [ordGe_pow hG k e (by omega), zero_div]
  · intro h
    exfalso
    apply h
    rw [Finset.mem_range]
    have : e.degree ≠ 0 := fun h => hne ((Finsupp.degree_eq_zero_iff e).1 h)
    omega
end GlobalTheory.RowLaw.CvEnd
