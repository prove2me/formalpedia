-- Prove2me | solution 1 for GlobalTheory.NB.LT.exists_poly_mod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:05:15.953924+00:00
-- url     : https://prove2.me/submissions/ca490fa7-3e5d-4a1b-967e-220ec8f03046

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
theorem _root_.solution [Nontrivial R] {I : Ideal R} [IsAdicComplete I R] {p : Polynomial R}
    (H : p.IsDistinguishedAt I) (a : R⟦X⟧) :
    ∃ r : Polynomial R, r.degree < p.degree ∧ (p : R⟦X⟧) ∣ a - r := by
  have hI : I ≠ ⊤ := by
    intro h
    have := subsingleton_of_isHausdorff_whole_ideal (I := I) h
    exact not_subsingleton R this
  have D := H.isWeierstrassDivisorAt' (I := I)
  have hd := D.isWeierstrassDivisionAt_div_mod a
  refine ⟨D.mod a, ?_, D.div a, sub_eq_iff_eq_add.mpr hd.eq_mul_add⟩
  have hlt := hd.degree_lt
  rw [order_map_toNat_eq_natDegree_of_isDistinguishedAt H hI] at hlt
  rwa [Polynomial.degree_eq_natDegree (Polynomial.Monic.ne_zero H.monic)]
end _root_.GlobalTheory.NB.LT
end GlobalTheory.NB.LT
