-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.twist_wp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:30:07.444943+00:00
-- url     : https://prove2.me/submissions/87d31b73-5095-421f-a43c-b4da94ebede1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTerms

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
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.NumD
variable {O : Type} [CommRing O] (N : NumD O)
namespace GlobalTheory.Ex.NumD
theorem _root_.solution {k : ℕ} (β : N.Form k) (u : Oˣ) {j : ℕ} (hj : j ∣ k) (q q' : N.QT j) :
    (N.twist β u).wp (N.twQ β u hj q) (N.twQ β u hj q') = N.wp q q' := by
  show q.1.2.s q'.1.1.toAdd * u ^ (β.be q.1.1.toAdd q'.1.1.toAdd / j) * cubN N.θ j 1 q'.1.2.b q.1.2.b /
    (q'.1.2.s q.1.1.toAdd * u ^ (β.be q'.1.1.toAdd q.1.1.toAdd / j) * cubN N.θ j 1 q.1.2.b q'.1.2.b) =
    q.1.2.s q'.1.1.toAdd * cubN N.θ j 1 q'.1.2.b q.1.2.b / (q'.1.2.s q.1.1.toAdd * cubN N.θ j 1 q.1.2.b q'.1.2.b)
  rw [β.symm q'.1.1.toAdd]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]; abel
end GlobalTheory.Ex.NumD
