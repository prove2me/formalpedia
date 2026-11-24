-- Prove2me | solution 1 for GlobalTheory.GramCount.prim_of_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:27:50.186508+00:00
-- url     : https://prove2.me/submissions/aae4c203-e011-4be8-9511-f618bc812fcb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Theorems.Thm_GlobalTheory_GramCount_prim_of_isUnit_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.GramCount
variable {A : Type} [CommRing A]
variable (c : A →+* A) {n : ℕ}
namespace GlobalTheory.GramCount
theorem _root_.solution (hc : ∀ u, c (c u) = u) (I : Ideal A) (hI : ∀ u ∈ I, IsUnit (1 + u))
    {m : ℕ} (x y : Fin m → Fin n → A)
    (h : ∀ a b, ip c (x a) (y b) - (if a = b then 1 else 0) ∈ I) : Prim c x := by

  apply prim_of_isUnit_det c hc x y
  have hone : (Ideal.Quotient.mk I).mapMatrix (Matrix.of fun a b => ip c (x a) (y b)) = 1 := by
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.one_apply]
    have hab := h a b
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at hab
    rw [hab]
    split_ifs <;> simp
  have key : (Matrix.of fun a b => ip c (x a) (y b)).det - 1 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, RingHom.map_det, hone,
      Matrix.det_one, sub_self]
  simpa using hI _ key
end GlobalTheory.GramCount
