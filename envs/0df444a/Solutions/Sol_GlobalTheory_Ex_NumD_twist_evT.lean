-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.twist_evT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:09:48.064778+00:00
-- url     : https://prove2.me/submissions/7bf77232-2dd5-4ca2-866f-7b9d84b04642

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTerms
import Theorems.Thm_GlobalTheory_Ex_NumD_Form_div_nsmul
import Theorems.Thm_GlobalTheory_Ex_NumD_Form_exp_count
import Theorems.Thm_GlobalTheory_Ex_NumD_twist_wQ
import Theorems.Thm_GlobalTheory_Ex_NumD_twist_vt
import Theorems.Thm_GlobalTheory_Ex_NumD_twG_mul

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
theorem _root_.solution {k : ℕ} (β : N.Form k) (u : Oˣ) (m : ℕ) (hm : m ^ 2 ∣ k) (ho : Odd m) (p : N.QT (m ^ 2)) (χ : N.X)
    {j : ℕ} (hj : j ∣ k) (q : N.QT j) :
    (N.twist β u).evT m (N.twQ β u hm p) (N.twQ β u hj q).1.2 χ =
      (u ^ (β.be (p.1.1.toAdd + m • χ) (p.1.1.toAdd + m • χ) / (2 * m ^ 2) +
        β.be q.1.1.toAdd (p.1.1.toAdd + m • χ) / j) : Oˣ) * N.evT m p q.1.2 χ := by
  show ((q.1.2.s p.1.1.toAdd * u ^ (β.be q.1.1.toAdd p.1.1.toAdd / j) * cubN N.θ (m ^ 2) 1 p.1.2.b q.1.2.b *
    (N.twist β u).wQ (N.twQ β u hm p) / mulq N.θ N.σ m (q.1.2.b * p.1.2.b) : Oˣ) : O) *
    (N.twist β u).vt ((N.twG β u q.1.2 _ (β.div_add hj q.1.1.toAdd) *
      N.twG β u p.1.2 _ (β.div_add hm p.1.1.toAdd)) ^ m) χ =
      _ * (((q.1.2.s p.1.1.toAdd * cubN N.θ (m ^ 2) 1 p.1.2.b q.1.2.b *
        N.wQ p / mulq N.θ N.σ m (q.1.2.b * p.1.2.b) : Oˣ) : O) * N.vt ((q.1.2 * p.1.2) ^ m) χ)
  rw [twG_mul, twist_wQ, twist_vt, β.exp_count hm ho, β.div_add hj, β.div_nsmul hj, ← mul_assoc (_ : O), ← mul_assoc (_ : O),
    ← Units.val_mul, ← Units.val_mul]
  congr 2
  simp only [add_mul, zpow_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]; abel
end GlobalTheory.Ex.NumD
