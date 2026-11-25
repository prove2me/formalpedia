-- Prove2me | solution 1 for GroundTheory.PAdicHodge.seriesEval_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:50:13.031797+00:00
-- url     : https://prove2.me/submissions/66a843d5-3e07-4db7-8afb-f92834fd418d

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BdRSeries
import Theorems.Thm_GroundTheory_PAdicHodge_seriesEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.seriesEval_X

set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open PowerSeries
variable {B : Type*} [CommRing B] (I : Ideal B)
variable [Algebra ℚ B]
variable [IsAdicComplete I B]
variable {I}
namespace GroundTheory.PAdicHodge
theorem _root_.solution {z : B} (hz : z ∈ I) {g : ℚ⟦X⟧} (hg : constantCoeff g = 0) {w : B}
    (hw : w ∈ I) (hgw : seriesEval I z hz g = w) (f : ℚ⟦X⟧) :
    seriesEval I w hw f = seriesEval I z hz (f.subst g) := by
  have hS := HasSubst.of_constantCoeff_zero' hg
  have key : seriesEval I w hw = (seriesEval I z hz).comp (substAlgHom hS) := by
    refine IsAdicComplete.algHom_ext I fun n => ?_
    have hwn : (Ideal.Quotient.mkₐ ℚ (I ^ n) w) ^ n = 0 := pow_mk_eq_zero I hw n
    rw [truncEval_unique ((Ideal.Quotient.mkₐ ℚ (I ^ n)).comp (seriesEval I w hw)) _ hwn
      (by rw [AlgHom.comp_apply, seriesEval_X]),
      truncEval_unique ((Ideal.Quotient.mkₐ ℚ (I ^ n)).comp ((seriesEval I z hz).comp
        (substAlgHom hS))) _ hwn (by
        rw [AlgHom.comp_apply, AlgHom.comp_apply, coe_substAlgHom, subst_X hS, hgw])]
  rw [key, AlgHom.comp_apply, coe_substAlgHom]
end GroundTheory.PAdicHodge
