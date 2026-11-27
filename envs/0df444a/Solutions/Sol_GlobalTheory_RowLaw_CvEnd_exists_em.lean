-- Prove2me | solution 1 for GlobalTheory.RowLaw.CvEnd.exists_em
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T06:06:36.489229+00:00
-- url     : https://prove2.me/submissions/c3061d86-87bc-492e-9dda-3192c2fbd8fd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AdjointEndPairMemGaugedCurveLogarithms
import Theorems.Thm_GlobalTheory_RowLaw_CvEnd_emb_zero
import Theorems.Thm_GlobalTheory_RowLaw_CvEnd_emb_one
import Theorems.Thm_GlobalTheory_RowLaw_CvEnd_weight_wz
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_finsupp_deg_one
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
variable {κ : Type} [Fintype κ]
namespace GlobalTheory.RowLaw.CvEnd
theorem _root_.solution (e : Fin 2 × κ →₀ ℕ) (he : Finsupp.weight (wz κ) e = 1) : ∃ i μ, e = em i μ := by
  classical
  rw [weight_wz] at he
  obtain ⟨i, hi⟩ := finsupp_deg_one (Finsupp.equivFunOnFinite.symm fun x => e (1, x)) (by
    rw [Finsupp.degree_eq_sum]; simpa using he)
  refine ⟨i, Finsupp.equivFunOnFinite.symm fun x => e (0, x), ?_⟩
  ext ⟨g, x⟩
  have := DFunLike.congr_fun hi x
  fin_cases g
  · simp [em, emb_zero, Finsupp.single_apply]
  · simpa [em, emb_one, Finsupp.single_apply] using this
end GlobalTheory.RowLaw.CvEnd
