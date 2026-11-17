-- Prove2me | solution 1 for N25.isLeftRegular_quotient_swap
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:35:56.899322+00:00
-- url     : https://prove2.me/submissions/f944fc0e-6d92-412b-ad3f-dd4965898896

import Mathlib

/-! Regularity in monic root extensions and two-element regular-sequence swaps. -/
noncomputable section

namespace N25

open Polynomial

/-- If `D` is left-regular in a commutative ring and `c` is left-regular
modulo `(D)`, then `D` is left-regular modulo `(c)`.  This special
two-element swap needs no Noetherian, local, or Jacobson hypothesis. -/
theorem _root_.solution
    {B : Type*} [CommRing B] {D c : B}
    (hD : IsLeftRegular D)
    (hc : IsLeftRegular
      (Ideal.Quotient.mk (Ideal.span ({D} : Set B)) c)) :
    IsLeftRegular
      (Ideal.Quotient.mk (Ideal.span ({c} : Set B)) D) := by
  apply isLeftRegular_of_non_zero_divisor
  rintro ⟨f⟩ hf
  change Ideal.Quotient.mk (Ideal.span ({c} : Set B)) D *
      Ideal.Quotient.mk (Ideal.span ({c} : Set B)) f = 0 at hf
  change Ideal.Quotient.mk (Ideal.span ({c} : Set B)) f = 0
  have hDf0 :
      Ideal.Quotient.mk (Ideal.span ({c} : Set B)) (D * f) = 0 := by
    simpa only [map_mul] using hf
  have hcf : c ∣ D * f :=
    (Ideal.Quotient.eq_zero_iff_dvd c (D * f)).mp hDf0
  obtain ⟨g, hg⟩ := hcf
  have hcg0 :
      Ideal.Quotient.mk (Ideal.span ({D} : Set B)) (c * g) = 0 := by
    rw [← hg]
    simp only [map_mul, Ideal.Quotient.mk_singleton_self, zero_mul]
  have hg0 :
      Ideal.Quotient.mk (Ideal.span ({D} : Set B)) g = 0 := by
    apply hc
    simpa only [map_mul, mul_zero] using hcg0
  have hDg : D ∣ g :=
    (Ideal.Quotient.eq_zero_iff_dvd D g).mp hg0
  obtain ⟨h, hgh⟩ := hDg
  apply (Ideal.Quotient.eq_zero_iff_dvd c f).mpr
  refine ⟨h, ?_⟩
  apply hD
  calc
    D * f = c * g := hg
    _ = c * (D * h) := by rw [hgh]
    _ = D * (c * h) := by ac_rfl

end N25
