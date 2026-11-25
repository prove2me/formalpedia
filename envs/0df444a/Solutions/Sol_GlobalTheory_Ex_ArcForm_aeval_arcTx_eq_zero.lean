-- Prove2me | solution 1 for GlobalTheory.Ex.ArcForm.aeval_arcTx_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:44:51.706428+00:00
-- url     : https://prove2.me/submissions/0df3ad16-6564-4aa0-bb0d-e0f789f51579

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AevalArcTxEqZero
import Theorems.Thm_GlobalTheory_Ex_ArcForm_hasSum_arcTx
import Theorems.Thm_GlobalTheory_Ex_ArcForm_aeval_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators Topology
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.ArcForm
namespace GlobalTheory.Ex.ArcForm
theorem _root_.solution : ∀ (N : NumD ℂ) (k : ℕ) (β : N.Form k) (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∀ (ι : Type) (p : ι → N.QT (m ^ 2)) (F : MvPolynomial ι ℂ) (ε : ℝ), 0 < ε → (∀ u : ℂˣ, ‖(u : ℂ)‖ < ε → (∀ i, Summable fun χ => ‖(N.twist β u).txT m (N.twQ β u hm (p i)) χ‖) ∧ MvPolynomial.eval (fun i => (N.twist β u).tx m (N.twQ β u hm (p i))) F = 0) → MvPolynomial.aeval (fun i => N.arcTx β.be m (p i)) F = 0 :=
  fun N _ β m hm ho _ p F _ hε h =>
    aeval_eq_zero _ F hε (fun u i => (N.twist β u).tx m (N.twQ β u hm (p i)))
      (fun u hu i => hasSum_arcTx N β hm ho (p i) u ((h u hu).1 i)) fun u hu => (h u hu).2
end GlobalTheory.Ex.ArcForm
