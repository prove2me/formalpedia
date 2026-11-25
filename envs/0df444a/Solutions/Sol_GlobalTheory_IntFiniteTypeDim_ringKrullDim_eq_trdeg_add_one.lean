-- Prove2me | solution 1 for GlobalTheory.IntFiniteTypeDim.ringKrullDim_eq_trdeg_add_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:58:48.797891+00:00
-- url     : https://prove2.me/submissions/93afec29-b773-4c62-832c-ea2f165ea867

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrullDimQuotientMinimalPrimeOverL
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RingKrullDimQuotientLeOfMinimalPrimes
import Theorems.Thm_GlobalTheory_IntFiniteTypeDim_exists_natPrime_mem_of_isMaximal
import Theorems.Thm_GlobalTheory_IntFiniteTypeDim_ringKrullDim_quotient_le_of_minimalPrimes
import Theorems.Thm_GlobalTheory_ringKrullDim_quotient_eq_trdeg_of_mem_minimalPrimes_natPrime


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntFiniteTypeDim
namespace GlobalTheory.IntFiniteTypeDim
theorem _root_.solution :
    ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A],
      Function.Injective (algebraMap ℤ A) →
        ringKrullDim A = ((Cardinal.toENat (Algebra.trdeg ℤ A) + 1 : ℕ∞) : WithBot ℕ∞) := by
  intro A _ _ _ hinj
  haveI : CharZero A := charZero_of_injective_algebraMap hinj
  haveI : FaithfulSMul ℤ A := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  obtain ⟨d, hd⟩ := Cardinal.lt_aleph0.mp (trdeg_lt_aleph0_of_finiteType (R := ℤ) (S := A))
  have hrhs : ((Cardinal.toENat (Algebra.trdeg ℤ A) + 1 : ℕ∞) : WithBot ℕ∞) =
      (d : WithBot ℕ∞) + 1 := by
    rw [hd, Cardinal.toENat_nat]; rfl
  rw [hrhs]
  apply le_antisymm
  · refine (ringKrullDim_le_iff_isMaximal_height_le _).mpr fun m hm => ?_
    obtain ⟨l, hl, hlm⟩ := exists_natPrime_mem_of_isMaximal A m
    haveI := Fact.mk hl
    refine (Ideal.height_le_ringKrullDim_quotient_add_one hlm).trans ?_
    gcongr
    refine ringKrullDim_quotient_le_of_minimalPrimes _ _ fun q hq => ?_
    haveI := hq.1.1
    exact (ringKrullDim_quotient_eq_trdeg_of_mem_minimalPrimes_natPrime A l q hq d hd).le
  · obtain ⟨m, hm⟩ := Ideal.exists_maximal A
    obtain ⟨l, hl, hlm⟩ := exists_natPrime_mem_of_isMaximal A m
    haveI := Fact.mk hl
    obtain ⟨q, hq, -⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {(l : A)}) (J := m)
      ((Ideal.span_singleton_le_iff_mem _).mpr hlm)
    haveI := hq.1.1
    rw [← ringKrullDim_quotient_eq_trdeg_of_mem_minimalPrimes_natPrime A l q hq d hd]
    have hlq : (l : A) ∈ q := hq.1.2 (Ideal.mem_span_singleton_self _)
    exact ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
      (r := (l : A)) (mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.mpr hl.ne_zero))
      (Ideal.Quotient.eq_zero_iff_mem.mpr hlq)
end GlobalTheory.IntFiniteTypeDim
