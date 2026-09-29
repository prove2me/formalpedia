-- Prove2me | solution 1 for ModularCurve.exists_ringHom_integralClosure_int_complex_apply_natCast_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/918fe4a7-d03d-5148-96cf-a9a558605011

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_ringHom_integralClosure_int_complex_apply_natCast_eq_zero

set_option autoImplicit false

namespace P2mIntegralClosureRedHom

open Polynomial

theorem nonempty_ringHom_of_charP_of_integral (F : Type*) [Field F] (K : Type*) [Field K]
    [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP F p] [CharP K p]
    (hint : ∀ x : F, ∃ f : ℤ[X], f.Monic ∧ f.eval₂ (Int.castRingHom F) x = 0) :
    Nonempty (F →+* K) := by
  letI algF : Algebra (ZMod p) F := ZMod.algebra F p
  letI algK : Algebra (ZMod p) K := ZMod.algebra K p
  haveI : Algebra.IsIntegral (ZMod p) F := by
    refine ⟨fun x => ?_⟩
    obtain ⟨f, hfm, hf⟩ := hint x
    refine ⟨f.map (Int.castRingHom (ZMod p)), hfm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap (ZMod p) F).comp (Int.castRingHom (ZMod p)) = Int.castRingHom F :=
      RingHom.ext_int _ _
    rw [hcomp, hf]
  let ψ : F →ₐ[ZMod p] K := IsAlgClosed.lift
  exact ⟨ψ.toRingHom⟩

theorem span_natCast_int_isMaximal (p : ℕ) [hp : Fact p.Prime] :
    (Ideal.span {(p : ℤ)}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp.out).irreducible

theorem ker_algebraMap_int_integralClosure_le (I : Ideal ℤ) :
    RingHom.ker (algebraMap ℤ ↥(integralClosure ℤ ℂ)) ≤ I := by
  intro n hn
  rw [RingHom.mem_ker] at hn
  have h1 : ((algebraMap ℤ ↥(integralClosure ℤ ℂ) n : ↥(integralClosure ℤ ℂ)) : ℂ) = 0 := by
    rw [hn]; rfl
  have h3 : ((algebraMap ℤ ↥(integralClosure ℤ ℂ) n : ↥(integralClosure ℤ ℂ)) : ℂ) = (n : ℂ) := by
    simp
  rw [h3] at h1
  have : n = 0 := by exact_mod_cast h1
  subst this
  exact I.zero_mem

theorem exists_isMaximal_comap_eq (p : ℕ) [Fact p.Prime] :
    ∃ Q : Ideal ↥(integralClosure ℤ ℂ), Q.IsMaximal ∧
      Q.comap (algebraMap ℤ ↥(integralClosure ℤ ℂ)) = Ideal.span {(p : ℤ)} := by
  haveI := span_natCast_int_isMaximal p
  exact Ideal.exists_ideal_over_maximal_of_isIntegral (S := ↥(integralClosure ℤ ℂ))
    (Ideal.span {(p : ℤ)}) (ker_algebraMap_int_integralClosure_le _)

theorem nonempty_ringHom (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [hp : Fact p.Prime]
    [CharP K p] : Nonempty (↥(integralClosure ℤ ℂ) →+* K) := by
  obtain ⟨Q, hQmax, hQ⟩ := exists_isMaximal_comap_eq p

  letI : Field (↥(integralClosure ℤ ℂ) ⧸ Q) := Ideal.Quotient.field Q

  have hpQ : ((p : ↥(integralClosure ℤ ℂ))) ∈ Q := by
    have h1 : (p : ℤ) ∈ Q.comap (algebraMap ℤ ↥(integralClosure ℤ ℂ)) := by
      rw [hQ]; exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap] at h1
    simpa using h1

  have hp0 : ((p : ↥(integralClosure ℤ ℂ) ⧸ Q)) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk Q) p]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hpQ
  haveI hchar : CharP (↥(integralClosure ℤ ℂ) ⧸ Q) p :=
    (CharP.charP_iff_prime_eq_zero hp.out).mpr hp0

  have hint : ∀ x : ↥(integralClosure ℤ ℂ) ⧸ Q, ∃ f : ℤ[X], f.Monic ∧
      f.eval₂ (Int.castRingHom (↥(integralClosure ℤ ℂ) ⧸ Q)) x = 0 := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hy : IsIntegral ℤ y := Algebra.IsIntegral.isIntegral y
    obtain ⟨f, hfm, hf⟩ := hy
    refine ⟨f, hfm, ?_⟩
    have hcomp : Int.castRingHom (↥(integralClosure ℤ ℂ) ⧸ Q)
        = (Ideal.Quotient.mk Q).comp (algebraMap ℤ ↥(integralClosure ℤ ℂ)) :=
      RingHom.ext_int _ _
    rw [hcomp, ← Polynomial.hom_eval₂, hf, map_zero]
  obtain ⟨ψ⟩ := nonempty_ringHom_of_charP_of_integral (↥(integralClosure ℤ ℂ) ⧸ Q) K p hint
  exact ⟨ψ.comp (Ideal.Quotient.mk Q)⟩

end P2mIntegralClosureRedHom

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    ∃ φ : ↥(integralClosure ℤ ℂ) →+* K, φ (p : ↥(integralClosure ℤ ℂ)) = 0 := by
  obtain ⟨φ⟩ := P2mIntegralClosureRedHom.nonempty_ringHom K p
  exact ⟨φ, by rw [map_natCast]; exact CharP.cast_eq_zero K p⟩

end S_ModularCurve_exists_ringHom_integralClosure_int_complex_apply_natCast_eq_zero
end P2MW
export P2MW.S_ModularCurve_exists_ringHom_integralClosure_int_complex_apply_natCast_eq_zero (solution)
