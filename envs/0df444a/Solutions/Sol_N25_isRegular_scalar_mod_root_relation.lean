-- Prove2me | solution 1 for N25.isRegular_scalar_mod_root_relation
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:36:01.525904+00:00
-- url     : https://prove2.me/submissions/a88e111c-8399-4515-b631-0f06130e18a8

import Mathlib
import Theorems.Thm_N25_isRegular_algebraMap_adjoinRoot_of_monic
import Theorems.Thm_N25_isRegular_map_ringEquiv
import Theorems.Thm_N25_isRegular_quotient_swap
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

/-! Regularity in monic root extensions and two-element regular-sequence swaps. -/
noncomputable section

namespace N25

open Polynomial

/-- A regular cubic after scalar specialization lets that scalar survive the cubic quotient. -/
theorem _root_.solution
    {R : Type*} [CommRing R] [IsDomain R]
    (q c : Polynomial R) (D : R) (hq : q.Monic) (hD : D ≠ 0)
    (hc : IsRegular (AdjoinRoot.mk
      (q.map (Ideal.Quotient.mk (Ideal.span ({D} : Set R))))
      (c.map (Ideal.Quotient.mk (Ideal.span ({D} : Set R)))))) :
    IsRegular (Ideal.Quotient.mk
      (Ideal.span ({AdjoinRoot.mk q c} : Set (AdjoinRoot q)))
      (AdjoinRoot.of q D)) := by
  let I : Ideal R := Ideal.span {D}
  have hm : Ideal.map (AdjoinRoot.of q) I =
      Ideal.span ({AdjoinRoot.of q D} : Set (AdjoinRoot q)) := by
    rw [Ideal.map_span, Set.image_singleton]
  let e : (AdjoinRoot q ⧸ Ideal.span ({AdjoinRoot.of q D} : Set (AdjoinRoot q))) ≃+*
      AdjoinRoot (q.map (Ideal.Quotient.mk I)) :=
    (Ideal.quotEquivOfEq hm.symm).trans
      (AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot I q)
  have he : e (Ideal.Quotient.mk
        (Ideal.span ({AdjoinRoot.of q D} : Set (AdjoinRoot q)))
        (AdjoinRoot.mk q c)) =
      AdjoinRoot.mk (q.map (Ideal.Quotient.mk I)) (c.map (Ideal.Quotient.mk I)) := by
    change AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot I q
      (Ideal.Quotient.mk (Ideal.map (AdjoinRoot.of q) I) (AdjoinRoot.mk q c)) = _
    exact AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot_mk_of I q c
  have hback : IsRegular (Ideal.Quotient.mk
      (Ideal.span ({AdjoinRoot.of q D} : Set (AdjoinRoot q))) (AdjoinRoot.mk q c)) := by
    have hh := isRegular_map_ringEquiv e.symm (show IsRegular
      (AdjoinRoot.mk (q.map (Ideal.Quotient.mk I)) (c.map (Ideal.Quotient.mk I))) from hc)
    rw [← he] at hh
    simpa only [RingEquiv.symm_apply_apply] using hh
  exact isRegular_quotient_swap (isRegular_algebraMap_adjoinRoot_of_monic q hq hD) hback

end N25
