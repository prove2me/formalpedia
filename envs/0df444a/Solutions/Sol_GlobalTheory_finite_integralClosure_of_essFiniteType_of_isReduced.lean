-- Prove2me | solution 1 for GlobalTheory.finite_integralClosure_of_essFiniteType_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:02:14.424244+00:00
-- url     : https://prove2.me/submissions/928fd419-14ee-45f7-ad3d-503b050ebc3f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormsAlgebraicIndependentSmulSubSumMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SubalgebraEqBotOfIsIntegralOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial
variable (o R : Type*) [CommRing o] [IsDedekindDomain o] [CommRing R] [Algebra o R]
  [Algebra.FiniteType o R]
include o
namespace GlobalTheory
theorem _root_.solution (B : Type*) [CommRing B]
    [IsReduced B] [IsAddTorsionFree B] [Algebra R B] [Algebra.EssFiniteType R B] :
    Module.Finite R (integralClosure R B) := by
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing o R
  haveI : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing R B
  haveI : Finite (minimalPrimes B) := (minimalPrimes.finite_of_isNoetherianRing B).to_subtype
  haveI hp (p : minimalPrimes B) : p.1.IsPrime := Ideal.minimalPrimes_isPrime p.2
  haveI (p : minimalPrimes B) : CharZero p.1.ResidueField := charZero_of_inj_zero fun n hn => by
    by_contra h0
    rw [← map_natCast (algebraMap B _), Ideal.algebraMap_residueField_eq_zero] at hn
    refine notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hn p.2 ?_
    refine mem_nonZeroDivisors_iff_right.mpr fun x hx => ?_
    rw [mul_comm, ← nsmul_eq_mul] at hx
    exact (nsmul_eq_zero_iff.mp hx).resolve_right h0
  haveI (p : minimalPrimes B) : Algebra.EssFiniteType R p.1.ResidueField := .comp R B _
  haveI (p : minimalPrimes B) := finite_integralClosure_of_essFiniteType_field o R p.1.ResidueField
  refine finite_integralClosure_of_family
    (fun p : minimalPrimes B => IsScalarTower.toAlgHom R B p.1.ResidueField) fun b hb => ?_
  have h : b ∈ sInf (minimalPrimes B) := Submodule.mem_sInf.mpr fun p hp' =>
    haveI := hp ⟨p, hp'⟩
    Ideal.algebraMap_residueField_eq_zero.mp (hb ⟨p, hp'⟩)
  rw [minimalPrimes, Ideal.sInf_minimalPrimes] at h
  exact IsReduced.eq_zero b (mem_nilradical.mp h)
end GlobalTheory
