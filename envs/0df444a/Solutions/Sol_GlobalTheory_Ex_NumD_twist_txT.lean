-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.twist_txT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:46.320504+00:00
-- url     : https://prove2.me/submissions/8c67b4d6-df64-4b42-8f87-8012d0a57ad7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTerms
import Theorems.Thm_GlobalTheory_Ex_NumD_Form_exp_count
import Theorems.Thm_GlobalTheory_Ex_NumD_twist_wQ
import Theorems.Thm_GlobalTheory_Ex_NumD_twist_vt

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
theorem _root_.solution {k : ℕ} (β : N.Form k) (u : Oˣ) (m : ℕ) (hm : m ^ 2 ∣ k) (ho : Odd m) (p : N.QT (m ^ 2)) (χ : N.X) :
    (N.twist β u).txT m (N.twQ β u hm p) χ =
      (u ^ (β.be (p.1.1.toAdd + m • χ) (p.1.1.toAdd + m • χ) / (2 * m ^ 2)) : Oˣ) * N.txT m p χ := by
  show (((N.twist β u).wQ (N.twQ β u hm p) / mulq N.θ N.σ m p.1.2.b : Oˣ) : O) *
    (N.twist β u).vt (N.twG β u p.1.2 _ (β.div_add hm p.1.1.toAdd) ^ m) χ =
      _ * (((N.wQ p / mulq N.θ N.σ m p.1.2.b : Oˣ) : O) * N.vt (p.1.2 ^ m) χ)
  rw [twist_wQ, twist_vt, β.exp_count hm ho, ← mul_assoc, ← mul_assoc, ← Units.val_mul, ← Units.val_mul]
  congr 2
  simp only [zpow_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]; abel
end GlobalTheory.Ex.NumD
