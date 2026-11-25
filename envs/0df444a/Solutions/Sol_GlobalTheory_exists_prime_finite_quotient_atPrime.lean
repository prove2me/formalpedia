-- Prove2me | solution 1 for GlobalTheory.exists_prime_finite_quotient_atPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:20:53.237134+00:00
-- url     : https://prove2.me/submissions/f2760264-e905-4bc1-b8c9-840a1d15c436

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimeEqBotOrMaximalIdealOfIsFieldAway
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Theorems.Thm_GlobalTheory_finite_of_forall_prime_mem
import Theorems.Thm_GlobalTheory_exists_prime_notMem_forall_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing TensorProduct
namespace GlobalTheory
theorem _root_.solution {R A : Type*} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [CommRing A] [IsNoetherianRing A] [Algebra R A]
    (m : Ideal A) [m.IsMaximal] [Finite (A ⧸ m)]
    (hm : (maximalIdeal R).map (algebraMap R A) ≤ m) {q : Ideal A} (hq : q.IsPrime) (hqm : q ≤ m)
    {ϖ : R} (hϖ : ϖ ∈ maximalIdeal R) {f : A} (hf : algebraMap R A ϖ * f ∉ q) :
    ∃ Q : Ideal (Localization.AtPrime m), Q.IsPrime ∧
      algebraMap A _ (algebraMap R A ϖ * f) ∉ Q ∧ Module.Finite R (Localization.AtPrime m ⧸ Q) := by
  set L := Localization.AtPrime m
  have hdis : Disjoint (m.primeCompl : Set A) (q : Set A) :=
    Set.disjoint_left.mpr fun x hx hxq => hx (hqm hxq)
  have hq' : (q.map (algebraMap A L)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl L q hq hdis
  have hf' : algebraMap A L (algebraMap R A ϖ * f) ∉ q.map (algebraMap A L) := by
    rw [← Ideal.mem_comap]
    have := IsLocalization.under_map_of_isPrime_disjoint m.primeCompl L hq hdis
    rw [Ideal.under_def] at this
    rwa [this]
  obtain ⟨Q, hQ, hfQ, H⟩ := exists_prime_notMem_forall_mem hq' hf'
  refine ⟨Q, hQ, hfQ, ?_⟩
  haveI : IsLocalRing (L ⧸ Q) :=
    .of_surjective' (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective
  haveI hloc : IsLocalHom (Ideal.Quotient.mk Q) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  haveI : Finite (ResidueField L) :=
    Finite.of_equiv _ (IsLocalization.AtPrime.equivQuotMaximalIdeal m L).toEquiv
  haveI : Finite ((L ⧸ Q) ⧸ maximalIdeal (L ⧸ Q)) := by
    refine Finite.of_surjective (ResidueField.map (Ideal.Quotient.mk Q)) fun x => ?_
    obtain ⟨x, rfl⟩ := residue_surjective x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨residue L x, rfl⟩
  have hf0 := mt Ideal.Quotient.eq_zero_iff_mem.mp hfQ
  refine finite_of_forall_prime_mem hf0 H (fun h => hf0 ?_) (fun h => ?_)
  · have h1 := Ideal.mem_map_of_mem (algebraMap R (L ⧸ Q)) hϖ
    rw [h, Ideal.mem_bot] at h1
    rw [map_mul, map_mul]
    exact mul_eq_zero_of_left h1 _
  · refine (maximalIdeal.isMaximal (L ⧸ Q)).ne_top (top_le_iff.mp (h ▸ ?_))
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    have h1 : algebraMap A L (algebraMap R A r) ∈ maximalIdeal L :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff L m _).mpr
        (hm (Ideal.mem_map_of_mem _ hr))
    exact map_nonunit (Ideal.Quotient.mk Q) _ h1
end GlobalTheory
