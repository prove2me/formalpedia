-- Prove2me | solution 1 for GlobalTheory.ringKrullDim_quotient_eq_trdeg_of_mem_minimalPrimes_natPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:20:42.715866+00:00
-- url     : https://prove2.me/submissions/0fa97455-c538-42d5-b3d2-d4ff4117b755

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrullDimQuotientMinimalPrimeOverL
import Theorems.Thm_GlobalTheory_trdeg_quotient_eq_of_mem_minimalPrimes_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution (A : Type) [CommRing A]
    [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A] (l : ℕ) [Fact l.Prime] (q : Ideal A)
    [q.IsPrime] (hq : q ∈ (Ideal.span {(l : A)}).minimalPrimes) (d : ℕ)
    (hd : Algebra.trdeg ℤ A = d) : ringKrullDim (A ⧸ q) = d := by
  have hk : Function.Surjective (algebraMap ℤ (ZMod l)) := ZMod.intCast_surjective
  have hker : RingHom.ker (algebraMap ℤ (ZMod l)) = Ideal.span {(l : ℤ)} := by
    rw [algebraMap_int_eq]; exact ZMod.ker_intCastRingHom l
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have : FaithfulSMul ℤ A := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (by rw [algebraMap_int_eq]; exact Int.cast_injective)
  have hq' : q ∈ (Ideal.span {algebraMap ℤ A (l : ℤ)}).minimalPrimes := by simpa using hq
  have hlq : (l : A) ∈ q := hq.1.2 (Ideal.mem_span_singleton_self _)
  have hle : RingHom.ker (algebraMap ℤ (ZMod l)) ≤ RingHom.ker (algebraMap ℤ (A ⧸ q)) := by
    rw [hker, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker,
      IsScalarTower.algebraMap_apply ℤ A (A ⧸ q), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem]
    simpa using hlq
  let := ((algebraMap ℤ (ZMod l)).liftOfSurjective hk ⟨_, hle⟩).toAlgebra
  have : IsScalarTower ℤ (ZMod l) (A ⧸ q) := IsScalarTower.of_algebraMap_eq fun x ↦
    (RingHom.liftOfSurjective_comp_apply _ hk ⟨_, hle⟩ x).symm
  have : Algebra.FiniteType (ZMod l) (A ⧸ q) := .of_restrictScalars_finiteType ℤ _ _
  refine ringKrullDim_eq_of_trdeg_eq (ZMod l) _ ?_
  rw [trdeg_quotient_eq_of_mem_minimalPrimes_span ℤ (ZMod l) hk hl0 hker hq', hd]
end GlobalTheory
