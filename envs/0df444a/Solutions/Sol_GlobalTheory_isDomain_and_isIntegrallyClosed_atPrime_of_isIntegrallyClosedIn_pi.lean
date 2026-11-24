-- Prove2me | solution 1 for GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_isIntegrallyClosedIn_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:02:33.540121+00:00
-- url     : https://prove2.me/submissions/ade447cd-d5ed-46ee-9107-a25408c97f28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Theorems.Thm_GlobalTheory_isDomain_and_isIntegrallyClosed_atPrime_of_isLocalization
import Theorems.Thm_GlobalTheory_isDomain_and_isIntegrallyClosed_atPrime_of_isDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
universe u
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {B : Type*} [CommRing B]
    {ι : Type*} [Finite ι] (K : ι → Type*) [∀ i, Field (K i)] [Algebra B (Π i, K i)]
    [hB : IsIntegrallyClosedIn B (Π i, K i)] (p : Ideal B) [hp : p.IsPrime]
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp ∧ IsIntegrallyClosed Bp := by
  classical
  have := Fintype.ofFinite ι
  have hinj : Function.Injective (algebraMap B (Π i, K i)) := (isIntegrallyClosedIn_iff.mp hB).1
  let φ (i : ι) : B →+* K i := (Pi.evalRingHom K i).comp (algebraMap B (Π i, K i))
  have key (i : ι) (x : K i) (hx : (φ i).IsIntegralElem x) :
      ∃ b : B, algebraMap B (Π i, K i) b = Pi.single i x := by
    apply IsIntegrallyClosedIn.algebraMap_eq_of_integral
    obtain ⟨f, hf, hfx⟩ := hx
    refine ⟨Polynomial.X * f, Polynomial.monic_X.mul hf, ?_⟩
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_X]
    funext j
    by_cases hj : j = i
    · subst hj
      have : (Polynomial.eval₂ (algebraMap B (Π i, K i)) (Pi.single j x) f) j = 0 := by
        have := Polynomial.hom_eval₂ f (algebraMap B (Π i, K i)) (Pi.evalRingHom K j)
          (Pi.single j x)
        simpa [φ] using this.trans (by simpa [φ] using hfx)
      simp [this]
    · simp [hj]
  choose e he using fun i ↦ key i 1 (RingHom.isIntegralElem_one _)
  have hsum : ∑ i, e i = 1 := by
    apply hinj
    simp [he, Finset.univ_sum_single, ← Pi.one_def]
  obtain ⟨i, hi⟩ : ∃ i, e i ∉ p := by
    by_contra! H
    exact hp.ne_top ((Ideal.eq_top_iff_one _).mpr (hsum ▸ p.sum_mem fun i _ ↦ H i))
  let D := (φ i).range
  letI : Algebra B D := (φ i).rangeRestrict.toAlgebra
  have hsurj : Function.Surjective (algebraMap B D) := (φ i).rangeRestrict_surjective
  have hidem : IsIdempotentElem (e i) := by
    apply hinj
    simp [he, ← Pi.single_mul]
  have : IsLocalization.Away (e i) D := by
    refine IsLocalization.away_of_isIdempotentElem_of_mul hidem (fun x y ↦ ?_) hsurj
    rw [Subtype.ext_iff, ← hinj.eq_iff, map_mul, map_mul, he]
    change algebraMap B (Π i, K i) x i = algebraMap B (Π i, K i) y i ↔ _
    refine ⟨fun h ↦ funext fun j ↦ ?_, fun h ↦ by simpa using congrFun h i⟩
    by_cases hj : j = i
    · subst hj
      simp [h]
    · simp [hj]
  have : IsIntegrallyClosedIn D (K i) := by
    rw [Subring.isIntegrallyClosedIn_iff]
    intro x hx
    letI : Algebra B (K i) := (φ i).toAlgebra
    have : IsScalarTower B D (K i) := .of_algebraMap_eq fun _ ↦ rfl
    have : Algebra.IsIntegral B D := Algebra.isIntegral_of_surjective hsurj
    obtain ⟨b, hb⟩ := key i x (isIntegral_trans x hx)
    exact ⟨b, by simp [φ, hb]⟩
  have : IsIntegrallyClosed D := IsIntegrallyClosed.of_isIntegrallyClosedIn D (K i)
  refine isDomain_and_isIntegrallyClosed_atPrime_of_isLocalization (.powers (e i)) D p ?_
    (fun q _ ↦ isDomain_and_isIntegrallyClosed_atPrime_of_isDomain q _) Bp
  rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]
end GlobalTheory
