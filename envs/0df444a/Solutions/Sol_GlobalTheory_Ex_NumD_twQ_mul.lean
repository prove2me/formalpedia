-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.twQ_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:51:23.175466+00:00
-- url     : https://prove2.me/submissions/dd84c66c-9670-455f-afc4-084fecbf656c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTerms
import Theorems.Thm_GlobalTheory_Ex_NumD_Form_div_add_left
import Theorems.Thm_GlobalTheory_Ex_NumD_twG_mul
import Theorems.Thm_GlobalTheory_Ex_NumD_twG_congr

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
    N.twQ β u hj (q * q') = N.twQ β u hj q * N.twQ β u hj q' := by
  refine Subtype.ext (Prod.ext rfl ?_)
  show N.twG β u (q.1.2 * q'.1.2) _ (β.div_add hj (q.1.1.toAdd + q'.1.1.toAdd)) =
    N.twG β u q.1.2 _ (β.div_add hj q.1.1.toAdd) * N.twG β u q'.1.2 _ (β.div_add hj q'.1.1.toAdd)
  rw [twG_mul]
  exact N.twG_congr β u _ _ _ _ _ fun z => β.div_add_left hj _ _ z
end GlobalTheory.Ex.NumD
