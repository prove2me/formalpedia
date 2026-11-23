-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.twist_wQ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:15.487274+00:00
-- url     : https://prove2.me/submissions/533fd682-d477-4dea-8c6b-23f86b87e237

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
theorem _root_.solution {k : ℕ} (β : N.Form k) (u : Oˣ) {j : ℕ} (hj : j ∣ k) (p : N.QT j) :
    (N.twist β u).wQ (N.twQ β u hj p) =
      u ^ (β.be p.1.1.toAdd p.1.1.toAdd / 2 - β.be p.1.1.toAdd p.1.1.toAdd / j * ((j - 1) / 2 : ℕ)) * N.wQ p := by
  show N.ψ p.1.1.toAdd * u ^ (β.be p.1.1.toAdd p.1.1.toAdd / 2) * mulq N.θ N.σ j p.1.2.b /
      (p.1.2.s p.1.1.toAdd * u ^ (β.be p.1.1.toAdd p.1.1.toAdd / j) * cubN N.θ j 1 p.1.2.b p.1.2.b /
        dbl N.θ N.σ p.1.2.b ^ j) ^ ((j - 1) / 2) = _ * (N.ψ p.1.1.toAdd * mulq N.θ N.σ j p.1.2.b /
      (p.1.2.s p.1.1.toAdd * cubN N.θ j 1 p.1.2.b p.1.2.b / dbl N.θ N.σ p.1.2.b ^ j) ^ ((j - 1) / 2))
  rw [zpow_sub, zpow_mul, zpow_natCast, mul_right_comm (p.1.2.s _), mul_div_right_comm _ (u ^ _), mul_pow]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_inv]; abel
end GlobalTheory.Ex.NumD
