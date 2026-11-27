-- Prove2me | solution 1 for GlobalTheory.RowLaw.EndBlock.matrixEnd_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T06:25:30.621932+00:00
-- url     : https://prove2.me/submissions/89e32c38-76aa-4f90-ac3a-a191a2851a75

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntSOfMulEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugeAdjointEndPairElementaryBlock
import Theorems.Thm_P2M_GlobalTheory_RowLaw_EndBlock_subst_zero__6c228542d1c2
import Theorems.Thm_GlobalTheory_RowLaw_EndBlock_cc_lin
import Theorems.Thm_GlobalTheory_RowLaw_EndBlock_subst_inCol
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_GlobalTheory_RowVal_cc_subst
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
noncomputable section
open scoped BigOperators
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.EndBlock
open MvPowerSeries
variable {C : Type} [Field C]
variable {dd : ℕ}
variable {d d' : ℕ} {I I' : Fin 2 → Type} (X : RawChart C d I (Fin dd)) (Z : RawChart C d' I' (Fin 2 × Fin dd))
namespace GlobalTheory.RowLaw.EndBlock
theorem _root_.solution (hlg : ∀ x, Z.lg x = inCol x.1 (X.lg x.2)) (hex : ∀ x, Z.ex x = inCol x.1 (X.ex x.2))
    (hlg0 : ∀ i, constantCoeff (X.lg i) = 0) (hex0 : ∀ i, constantCoeff (X.ex i) = 0) (r s : Fin 2)
    (M : Matrix (Fin dd) (Fin dd) C) {τ : Type} {a : Fin 2 × Fin dd → MvPowerSeries τ C}
    (ha : ∀ i, constantCoeff (a i) = 0) (col : Fin 2) (i : Fin dd) :
    endP Z (Matrix.of fun x y : Fin 2 × Fin dd => if x.1 = r ∧ y.1 = s then M x.2 y.2 else 0) a (col, i) =
      if col = r then endP X M (fun k => a (s, k)) i else 0 := by
  have hZ : ∀ x, constantCoeff (Z.lg x) = 0 := fun x => by
    rw [hlg, inCol, cc_subst (fun _ => constantCoeff_X _), hlg0]
  unfold endP
  rw [hex, subst_inCol (cc_lin Z hZ _ ha)]
  split_ifs with hc
  · congr 1
    funext k
    rw [Fintype.sum_prod_type, Finset.sum_eq_single s]
    · refine Finset.sum_congr rfl fun y _ => ?_
      rw [hlg, subst_inCol ha]
      simp [hc]
    · intro t _ ht
      simp [ht]
    · simp
  · simp only [Matrix.of_apply, hc, false_and, if_false, zero_smul, Finset.sum_const_zero]
    exact subst_zero' (hex0 i)
end GlobalTheory.RowLaw.EndBlock
