-- Prove2me | solution 1 for IsDiscreteValuationRing.exists_isAdicComplete_map_maximalIdeal_eq_forall_sub_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/fa61bed1-af7f-5a08-8fb2-38e6db5a62c0

import Mathlib
import Theorems.Thm_IsAdicComplete_exists_isDomain_isDiscreteValuationRing_of_span_singleton_isMaximal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_exists_isAdicComplete_map_maximalIdeal_eq_forall_sub_mem_maximalIdeal

set_option autoImplicit false

universe u

open AdicCompletion IsLocalRing

theorem solution
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] :
    ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (σ : A →+* W) (_ : IsLocalHom σ),
      Ideal.map σ (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal W ∧
      ∀ w : W, ∃ a : A, w - σ a ∈ IsLocalRing.maximalIdeal W := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  set I : Ideal A := maximalIdeal A with hI
  have hIϖ : I = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hIfg : I.FG := IsNoetherian.noetherian I
  let W := AdicCompletion I A
  let σ : A →+* W := algebraMap A W
  set ϖ' : W := σ ϖ with hϖ'

  have hmapI : I.map σ = Ideal.span {ϖ'} := by
    rw [congrArg (Ideal.map σ) hIϖ, Ideal.map_span, Set.image_singleton]

  have hker : ∀ x : W, evalₐ I 1 x = 0 ↔ x ∈ I.map σ := by
    intro x
    have h₁ : (I ^ 1 : Ideal A) ≤ I ^ 1 • ⊤ := by rw [Ideal.smul_eq_mul, Ideal.mul_top]
    have h₂ : (I ^ 1 • ⊤ : Ideal A) ≤ I ^ 1 := by rw [Ideal.smul_eq_mul, Ideal.mul_top]
    have hk : eval I A 1 x = 0 ↔ x ∈ I.map σ := by
      rw [← LinearMap.mem_ker, ← pow_smul_top_eq_ker_eval hIfg, Ideal.smul_top_eq_map,
        Submodule.restrictScalars_mem, congrArg (Ideal.map σ) (pow_one I)]
    rw [← hk]
    constructor
    · intro h
      rw [← factor_evalₐ_eq_eval I x h₁, h, _root_.map_zero]
    · intro h
      rw [← factor_eval_eq_evalₐ I x h₂, h, _root_.map_zero]

  have hsurj1 : Function.Surjective (evalₐ I 1) := surjective_evalₐ I 1
  haveI hImax : I.IsMaximal := maximalIdeal.isMaximal A
  have hmax' : (Ideal.span {ϖ'}).IsMaximal := by
    have hkeq : RingHom.ker (evalₐ I 1).toRingHom = Ideal.span {ϖ'} := by
      ext x
      rw [RingHom.mem_ker, ← hmapI]
      exact hker x
    rw [← hkeq]
    have hfield : IsField (A ⧸ I ^ 1) := by
      rw [pow_one]
      exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient I).mp hImax
    have hfieldW : IsField (W ⧸ RingHom.ker (evalₐ I 1).toRingHom) :=
      MulEquiv.isField hfield (RingHom.quotientKerEquivOfSurjective hsurj1).toMulEquiv
    exact Ideal.Quotient.maximal_of_isField _ hfieldW

  haveI : Module.Flat A W := flat_of_isNoetherian I
  have hreg : IsSMulRegular W ϖ :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)
  have hϖ'nzd : ϖ' ∈ nonZeroDivisors W := by
    refine mem_nonZeroDivisors_iff_right.mpr fun z hz => hreg ?_
    show ϖ • z = ϖ • (0 : W)
    rw [smul_zero, Algebra.smul_def, mul_comm]
    exact hz

  haveI : IsAdicComplete I W := AdicCompletion.isAdicComplete hIfg
  haveI hcomp : IsAdicComplete (Ideal.span {ϖ'}) W := by
    rw [← hmapI, IsAdicComplete.map_algebraMap_iff]
    infer_instance

  obtain ⟨hD, hDVR, hirr, hmaxW⟩ :=
    IsAdicComplete.exists_isDomain_isDiscreteValuationRing_of_span_singleton_isMaximal ϖ' hϖ'nzd

  have hlocal : IsLocalHom σ := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have haI : a ∈ I := (mem_maximalIdeal a).mpr hna
    have : σ a ∈ maximalIdeal W := by
      rw [hmaxW, ← hmapI]
      exact Ideal.mem_map_of_mem σ haI
    exact (mem_maximalIdeal _).mp this ha
  refine ⟨W, inferInstance, hD, hDVR, ?_, σ, hlocal, ?_, fun w => ?_⟩
  · rw [hmaxW]; exact hcomp
  · rw [hmaxW]; exact hmapI
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalₐ I 1 w)
    refine ⟨a, ?_⟩
    rw [hmaxW, ← hmapI, ← hker, map_sub, ← ha, AlgHom.commutes, Ideal.Quotient.algebraMap_eq, sub_self]

end S_IsDiscreteValuationRing_exists_isAdicComplete_map_maximalIdeal_eq_forall_sub_mem_maximalIdeal
end P2MW
export P2MW.S_IsDiscreteValuationRing_exists_isAdicComplete_map_maximalIdeal_eq_forall_sub_mem_maximalIdeal (solution)
