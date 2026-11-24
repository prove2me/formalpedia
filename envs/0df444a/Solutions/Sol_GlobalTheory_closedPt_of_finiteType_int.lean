-- Prove2me | solution 1 for GlobalTheory.closedPt_of_finiteType_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:16:06.79589+00:00
-- url     : https://prove2.me/submissions/1e7d2a17-dc4a-4da0-84ed-10cea406d598

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMaximalPrimeCharNotMemFiniteTypeInt
import Theorems.Thm_GlobalTheory_isJacobsonRing_integers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R] (f : R), f ≠ 0 → ∃ M : Ideal R, M.IsMaximal ∧ f ∉ M ∧ ∃ p : ℕ, p.Prime ∧ (p : R) ∈ M := by
  intro R _ _ _ f hf
  haveI := isJacobsonRing_integers
  let S := Localization.Away f
  have hinj : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  haveI : Nontrivial S := hinj.nontrivial
  haveI : Algebra.FiniteType R S := IsLocalization.finiteType_of_monoid_fg (Submonoid.powers f) S
  haveI : Algebra.FiniteType ℤ S := Algebra.FiniteType.trans (S := R) inferInstance inferInstance
  obtain ⟨n, hn⟩ := Ideal.exists_maximal S
  letI : Field (S ⧸ n) := Ideal.Quotient.field n
  haveI : Algebra.FiniteType ℤ (S ⧸ n) := inferInstance
  haveI hfin := finite_of_finite_type_of_isJacobsonRing ℤ (S ⧸ n)
  have hZ : (algebraMap ℤ (S ⧸ n)).IsIntegral := fun x => IsIntegral.of_finite ℤ x
  let ψ : R →+* S ⧸ n := (Ideal.Quotient.mk n).comp (algebraMap R S)
  have hcomp : ψ.comp (Int.castRingHom R) = algebraMap ℤ (S ⧸ n) := RingHom.ext_int _ _
  have hψ : ψ.IsIntegral := RingHom.IsIntegral.tower_top (Int.castRingHom R) ψ (hcomp ▸ hZ)
  haveI hbot : (⊥ : Ideal (S ⧸ n)).IsMaximal := Ideal.bot_isMaximal
  let M : Ideal R := (⊥ : Ideal (S ⧸ n)).comap ψ
  have hM : M.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' ψ hψ ⊥
  refine ⟨M, hM, ?_, ?_⟩
  · intro hfM
    have h0 : ψ f = 0 := by simpa [M] using hfM
    have hu : IsUnit (algebraMap R S f) := IsLocalization.Away.algebraMap_isUnit f
    have hu' : IsUnit (ψ f) := hu.map (Ideal.Quotient.mk n)
    rw [h0] at hu'
    exact not_isUnit_zero hu'
  · have hMZ : (M.comap (Int.castRingHom R)).IsMaximal := by
      have : M.comap (Int.castRingHom R) = (⊥ : Ideal (S ⧸ n)).comap (algebraMap ℤ (S ⧸ n)) := by
        rw [← hcomp, ← Ideal.comap_comap]
      rw [this]
      exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ hZ ⊥
    obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal (M.comap (Int.castRingHom R))
    change _ = Ideal.span {a} at ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [Ideal.span_singleton_eq_bot.2 rfl] at ha
      exact Ring.ne_bot_of_isMaximal_of_not_isField hMZ Int.not_isField ha
    have hpr : Prime a := by
      rw [← Ideal.span_singleton_prime ha0, ← ha]
      exact hMZ.isPrime
    refine ⟨a.natAbs, Int.prime_iff_natAbs_prime.1 hpr, ?_⟩
    have hmem : (a.natAbs : ℤ) ∈ M.comap (Int.castRingHom R) := by
      rw [ha, Ideal.mem_span_singleton]
      exact Int.dvd_natAbs.2 dvd_rfl
    have h2 := Ideal.mem_comap.1 hmem
    simpa only [eq_intCast, Int.cast_natCast] using h2
end GlobalTheory
