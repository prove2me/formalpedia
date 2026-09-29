-- Prove2me | solution 1 for NumberField.StandardAddChar.psiLocal_rat_eq_psiQ_adeleSingleAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/47282907-b801-5fca-9509-b6c483f67561

import Mathlib
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_StandardAddChar_psiLocal_rat_eq_psiQ_adeleSingleAt

set_option autoImplicit false

open NumberField NumberField.StandardAddChar IsDedekindDomain

namespace PSIBAux

open NumberField.AdelicTrace

theorem algebraMap_trace_ringOfIntegers_rat (a : 𝓞 ℚ) :
    algebraMap ℤ (𝓞 ℚ) (Algebra.trace ℤ (𝓞 ℚ) a) = a := by
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, algebraMap ℤ (𝓞 ℚ) n = a :=
    ⟨Rat.ringOfIntegersEquiv a, by
      apply Rat.ringOfIntegersEquiv.injective
      simp⟩
  rw [Algebra.trace_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self, one_smul]

theorem traceInt_rat : traceInt ℚ = AddMonoidHom.id _ := by
  symm
  refine eq_traceInt ℚ continuous_id (fun a => ?_)
  rw [traceInt_diag, AddMonoidHom.id_apply, algebraMap_trace_ringOfIntegers_rat]
  rfl

theorem traceFinHom_rat (y : FiniteAdeleRing (𝓞 ℚ) ℚ) : traceFinHom ℚ y = y := by
  obtain ⟨k, hk⟩ := NumberField.AdelicBox.exists_algebraMap_add_mem_integralFiniteAdeles (𝓞 ℚ) ℚ y

  set w : Π v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ :=
    fun v => ⟨(algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) k + y) v, hk v⟩ with hw
  have hsm : (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 ℚ) => v.adicCompletion ℚ)
      (fun v => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) Filter.cofinite w
        : FiniteAdeleRing (𝓞 ℚ) ℚ) = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) k + y :=
    RestrictedProduct.ext _ _ fun v => rfl
  have hz : traceFinHom ℚ (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) k + y)
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) k + y := by
    have h := traceFinHom_structureMap ℚ w
    rw [traceInt_rat, AddMonoidHom.id_apply, hsm] at h
    exact h
  have hk' : traceFinHom ℚ (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) k)
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) k := by
    rw [traceFinHom_algebraMap]
    congr 1
    exact trace_rat_apply k
  have hsplit : y = (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) k + y)
      - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) k := by ring
  conv_lhs => rw [hsplit]
  rw [map_sub, hz, hk', ← hsplit]

theorem stdAddChar_rat_zero_eq_psiQ (y : FiniteAdeleRing (𝓞 ℚ) ℚ) :
    stdAddChar ℚ ((0 : InfiniteAdeleRing ℚ), y) = psiQ ((0 : InfiniteAdeleRing ℚ), y) := by
  change (adelicTraceData ℚ).psiK ((0 : InfiniteAdeleRing ℚ), y) = _
  rw [AdelicTraceData.psiK_apply, AdelicTraceData.adelicTrace_apply]
  change psiQ ((adelicTraceData ℚ).traceInf 0, traceFinHom ℚ y) = _
  rw [map_zero, traceFinHom_rat]

end PSIBAux

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ)) (x : p.adicCompletion ℚ) :
    psiLocal ℚ p x = psiQ (adeleSingleAt ℚ p x) := by
  rw [psiLocal_apply, adeleSingleAt_apply, PSIBAux.stdAddChar_rat_zero_eq_psiQ]

end S_NumberField_StandardAddChar_psiLocal_rat_eq_psiQ_adeleSingleAt
end P2MW
export P2MW.S_NumberField_StandardAddChar_psiLocal_rat_eq_psiQ_adeleSingleAt (solution)
