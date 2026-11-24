-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.twist_qEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:08:01.469608+00:00
-- url     : https://prove2.me/submissions/09d4cd98-4064-4c37-b047-75e494cd9443

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTerms
import Theorems.Thm_GlobalTheory_Ex_NumD_Form_div_add_nsmul
import Theorems.Thm_GlobalTheory_Ex_NumD_twG_mul
import Theorems.Thm_GlobalTheory_Ex_NumD_twG_congr
import Theorems.Thm_GlobalTheory_Ex_NumD_twG_inj
import Theorems.Thm_GlobalTheory_Ex_NumD_twist_io

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
    N.QEq q q' ↔ (N.twist β u).QEq (N.twQ β u hj q) (N.twQ β u hj q') := by
  refine exists_congr fun (z : N.X) => and_congr_right fun (h : q'.1.1.toAdd = q.1.1.toAdd + j • z) => ?_
  show _ ↔ N.twG β u q'.1.2 _ (β.div_add hj q'.1.1.toAdd) =
    N.twG β u q.1.2 _ (β.div_add hj q.1.1.toAdd) * (N.twist β u).io z
  rw [twist_io, twG_mul, ← N.twG_congr β u (q.1.2 * N.io z) (fun x => β.be q'.1.1.toAdd x / j)
    (fun x => β.be q.1.1.toAdd x / j + β.be z x) (β.div_add hj q'.1.1.toAdd) _
    fun x => by rw [h, β.div_add_nsmul hj]]
  exact ⟨fun e => by rw [e], N.twG_inj β u _ _ _ _⟩
end GlobalTheory.Ex.NumD
