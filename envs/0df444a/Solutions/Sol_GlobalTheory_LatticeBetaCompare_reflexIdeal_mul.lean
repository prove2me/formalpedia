-- Prove2me | solution 1 for GlobalTheory.LatticeBetaCompare.reflexIdeal_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:54:32.322696+00:00
-- url     : https://prove2.me/submissions/0ae36d86-4148-4c40-a307-012703c1ba68

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ReflexNormIndexIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsMulMemOfMemSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoeEqSpanDetOfIntVecLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MultAddMultConjugate
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_succ
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_consZero_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_succ
attribute [local simp] ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.consZero_zero



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LatticeBetaCompare
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.GenusLatCompare
open scoped nonZeroDivisors Pointwise
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
variable {H : Host E} (Dw : Datum H) {l : Level H} (c : Coeff l)
namespace GlobalTheory.LatticeBetaCompare
theorem _root_.solution (𝔞 𝔟 : Ideal (𝓞 E)) :
    reflexIdeal Dw c (𝔞 * 𝔟) = reflexIdeal Dw c 𝔞 * reflexIdeal Dw c 𝔟 := by
  simp only [reflexIdeal, Ideal.map_mul, mul_pow, Finset.prod_mul_distrib]
end GlobalTheory.LatticeBetaCompare
