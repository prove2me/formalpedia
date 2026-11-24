-- Prove2me | solution 1 for GlobalTheory.NB.LT.poly_dvd_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:02:42.52015+00:00
-- url     : https://prove2.me/submissions/5b3538a5-35da-40ab-8caa-01fe06a5b5ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvdSubOfDvdSubX
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open PowerSeries
namespace GlobalTheory.NB.LT
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ}
open PowerSeries in
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ} in
private lemma subsingleton_of_isHausdorff_whole_ideal {I : Ideal R} [IsHausdorff I R] (h : I = ⊤) :
    Subsingleton R := by
  subst h
  refine ⟨fun x y => ?_⟩
  have key : ∀ z : R, z = 0 := fun z =>
    IsHausdorff.haus ‹_› z fun n => by simp [Ideal.top_pow, SModEq.top]
  rw [key x, key y]
open PowerSeries in
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ} in
private lemma order_map_toNat_eq_natDegree_of_isDistinguishedAt {I : Ideal R} {p : Polynomial R}
    (H : p.IsDistinguishedAt I) (hI : I ≠ ⊤) :
    ((map (Ideal.Quotient.mk I)) (p : R⟦X⟧)).order.toNat = p.natDegree := by
  have h1 : constantCoeff (1 : R⟦X⟧) ∉ I := by
    simpa [Ideal.eq_top_iff_one] using hI
  have := H.coe_natDegree_eq_order_map (p : R⟦X⟧) 1 h1 (by simp)
  rw [← this]
  simp
end GlobalTheory.NB.LT
end
end

set_option autoImplicit false
noncomputable section
open PowerSeries
open GlobalTheory GlobalTheory.NB GlobalTheory.NB.LT
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ}
open PowerSeries
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ}
namespace GlobalTheory.NB.LT
namespace _root_.GlobalTheory.NB.LT
theorem _root_.solution {I : Ideal R} [IsAdicComplete I R] {p : Polynomial R}
    (H : p.IsDistinguishedAt I) {r : Polynomial R} (h : (p : R⟦X⟧) ∣ (r : R⟦X⟧)) : p ∣ r := by
  by_cases hI : I = ⊤
  · have := subsingleton_of_isHausdorff_whole_ideal (I := I) hI
    rw [Subsingleton.elim r 0]
    exact dvd_zero p
  have hm := H.monic
  obtain ⟨h, hh⟩ := h
  have D := H.isWeierstrassDivisorAt' (I := I)
  have hdeg : (r %ₘ p).degree < ((map (Ideal.Quotient.mk I)) (p : R⟦X⟧)).order.toNat := by
    rw [order_map_toNat_eq_natDegree_of_isDistinguishedAt H hI]
    by_cases hs : Nontrivial R
    · exact (Polynomial.degree_modByMonic_lt r hm).trans_le Polynomial.degree_le_natDegree
    · rw [not_nontrivial_iff_subsingleton] at hs
      rw [Subsingleton.elim (r %ₘ p) 0]
      simp
  have hmul : (p : R⟦X⟧) * (h - ((r /ₘ p : Polynomial R) : R⟦X⟧)) = ((r %ₘ p : Polynomial R) : R⟦X⟧) := by
    have e := Polynomial.modByMonic_add_div r p
    have e' : ((r %ₘ p : Polynomial R) : R⟦X⟧) + (p : R⟦X⟧) * ((r /ₘ p : Polynomial R) : R⟦X⟧)
        = (r : R⟦X⟧) := by
      rw [← Polynomial.coe_mul, ← Polynomial.coe_add, e]
    rw [mul_sub, ← hh, ← e']
    ring
  have := (D.eq_zero_of_mul_eq hdeg hmul).2
  exact (Polynomial.modByMonic_eq_zero_iff_dvd hm).mp this
end _root_.GlobalTheory.NB.LT
end GlobalTheory.NB.LT
