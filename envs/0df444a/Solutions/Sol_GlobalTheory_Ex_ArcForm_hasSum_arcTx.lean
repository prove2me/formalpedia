-- Prove2me | solution 1 for GlobalTheory.Ex.ArcForm.hasSum_arcTx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:48:30.736654+00:00
-- url     : https://prove2.me/submissions/7549ca8d-9a32-40bd-8b08-f76a1b90f4e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AevalArcTxEqZero
import Theorems.Thm_GlobalTheory_Ex_ArcForm_hasSum_regroup
import Theorems.Thm_GlobalTheory_Ex_ArcForm_finite_fibre
import Theorems.Thm_GlobalTheory_Ex_ArcForm_exponent_nonneg
import Theorems.Thm_GlobalTheory_Conv_coe_expandConv
import Theorems.Thm_GlobalTheory_Conv_coe_expandConvLaurent
import Theorems.Thm_GlobalTheory_Conv_expandConv_u
import Theorems.Thm_GlobalTheory_Ex_twist_terms
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
theorem _root_.solution (N : NumD ℂ) {k : ℕ} (β : N.Form k) {m : ℕ} (hm : m ^ 2 ∣ k) (ho : Odd m)
    (p : N.QT (m ^ 2)) (u : ℂˣ) (h : Summable fun χ => ‖(N.twist β u).txT m (N.twQ β u hm p) χ‖) :
    HasSum (fun n => PowerSeries.coeff n (N.arcTx β.be m p) * (u : ℂ) ^ n)
      ((N.twist β u).tx m (N.twQ β u hm p)) := by
  have h1 : HasSum (fun χ : N.X => (N.twist β u).txT m (N.twQ β u hm p) χ)
      ((N.twist β u).tx m (N.twQ β u hm p)) := h.of_norm.hasSum
  have h2 := hasSum_regroup _ (fun χ => exponent_nonneg β m (p.1.1.toAdd + m • χ))
    (finite_fibre β ho.pos.ne' p.1.1.toAdd) (N.txT m p) u _ (h1.congr_fun fun χ => by
      rw [(GlobalTheory.Ex.twist_terms ℂ N k β u m hm ho p χ).1, Units.val_zpow_eq_zpow_val])
  simpa only [NumD.arcTx, PowerSeries.coeff_mk] using h2
end GlobalTheory.Ex.ArcForm
