-- Prove2me | solution 1 for GlobalTheory.Capelli.mixedOp_lie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:35:33.39687+00:00
-- url     : https://prove2.me/submissions/f2f7eb70-545e-4fcb-ae19-188e89d1bc71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CommuteRowOpRightMixedOp
import Theorems.Thm_GlobalTheory_Capelli_polar_apply
import Theorems.Thm_GlobalTheory_Capelli_colOp_lie
import Theorems.Thm_GlobalTheory_Capelli_commute_colOp_colOp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Capelli.polar_apply

set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.Capelli
variable {K σ : Type*} [CommRing K]
variable {I J I' J' : Type*}
namespace GlobalTheory.Capelli
theorem _root_.solution [Fintype I] [Fintype I'] [DecidableEq J] (z : I × J → σ)
    (hz : Function.Injective z) (y : I' × J → σ) (hy : Function.Injective y)
    (hzy : ∀ u w, z u ≠ y w) (i j k l : J) :
    mixedOp K z y i j * mixedOp K z y k l - mixedOp K z y k l * mixedOp K z y i j =
      (if j = k then mixedOp K z y i l else 0) - (if l = i then mixedOp K z y k j else 0) := by
  have h₁ := colOp_lie (K := K) z hz i j k l
  have h₂ := colOp_lie (K := K) y hy l k j i
  have h₃ := (commute_colOp_colOp (K := K) z y hzy i j l k).eq
  have h₄ := (commute_colOp_colOp (K := K) z y hzy k l j i).eq
  have h : mixedOp K z y i j * mixedOp K z y k l - mixedOp K z y k l * mixedOp K z y i j =
      (colOp K z i j * colOp K z k l - colOp K z k l * colOp K z i j) -
      (colOp K y l k * colOp K y j i - colOp K y j i * colOp K y l k) := by
    simp only [mixedOp, sub_mul, mul_sub, h₃, h₄]
    abel
  rw [h, h₁, h₂]
  simp only [mixedOp, eq_comm (a := k) (b := j), eq_comm (a := i) (b := l)]
  split_ifs <;> abel
end GlobalTheory.Capelli
