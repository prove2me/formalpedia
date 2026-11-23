-- Prove2me | solution 1 for GlobalTheory.RegBound.comp_succ_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:20:44.577605+00:00
-- url     : https://prove2.me/submissions/5a546dd5-08a5-456b-bd6a-6e42a87b575b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module MvPolynomial
open GlobalTheory GlobalTheory.RegBound
variable {σ K : Type} [Field K]
namespace GlobalTheory.RegBound
theorem _root_.solution {h : MvPolynomial σ K} (hh : h.IsHomogeneous 1) (e : ℕ)
    (B : MvPolynomial σ K) :
    homogeneousComponent (e + 1) (h * B) = h * homogeneousComponent e B := by
  induction B using MvPolynomial.induction_on' with
  | monomial d c =>
    have h1 := isHomogeneous_monomial (d := d) c rfl
    rw [homogeneousComponent_of_mem (hh.mul h1), homogeneousComponent_of_mem h1]
    by_cases he : e = d.degree
    · rw [if_pos he, if_pos (by omega)]
    · rw [if_neg he, if_neg (by omega), mul_zero]
  | add p q hp hq => simp [mul_add, hp, hq]
end GlobalTheory.RegBound
