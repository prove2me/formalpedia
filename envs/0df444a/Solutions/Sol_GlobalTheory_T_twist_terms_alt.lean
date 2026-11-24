-- Prove2me | solution 1 for GlobalTheory.T.twist_terms_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:24:48.639799+00:00
-- url     : https://prove2.me/submissions/6343cac4-79d2-4490-b7e1-d56db16f7111

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTerms
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTermsStatement
import Theorems.Thm_GlobalTheory_Ex_twist_terms


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (k : ℕ) (β : N.Form k) (u : Oˣ) (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∀ (p : N.QT (m ^ 2)) (χ : N.X), (N.twist β u).txT m (N.twQ β u hm p) χ = (u ^ (β.be (p.1.1.toAdd + m • χ) (p.1.1.toAdd + m • χ) / (2 * m ^ 2)) : Oˣ) * N.txT m p χ ∧ (∀ (j : ℕ) (hj : j ∣ k) (q : N.QT j), j ≠ 0 → (N.twist β u).evT m (N.twQ β u hm p) (N.twQ β u hj q).1.2 χ = (u ^ (β.be (p.1.1.toAdd + m • χ) (p.1.1.toAdd + m • χ) / (2 * m ^ 2) + β.be q.1.1.toAdd (p.1.1.toAdd + m • χ) / j) : Oˣ) * N.evT m p q.1.2 χ) ∧ ∀ (j : ℕ) (hj : j ∣ k) (q q' : N.QT j), (N.twist β u).wp (N.twQ β u hj q) (N.twQ β u hj q') = N.wp q q' ∧ N.twQ β u hj (q * q') = N.twQ β u hj q * N.twQ β u hj q' ∧ (N.QEq q q' ↔ (N.twist β u).QEq (N.twQ β u hj q) (N.twQ β u hj q')) := by
  first | exact @GlobalTheory.Ex.twist_terms | exact GlobalTheory.Ex.twist_terms | (intros; apply GlobalTheory.Ex.twist_terms <;> assumption)
end _root_.GlobalTheory.T
