-- Prove2me | solution 1 for IsLocalRing.exists_isLocalRing_adicCompletion_isAdicComplete_map_maximalIdeal_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/a4c5822f-7caa-576f-b912-e628beaaa904

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_isLocalRing_adicCompletion_isAdicComplete_map_maximalIdeal_eq

set_option autoImplicit false

universe u

open AdicCompletion IsLocalRing in
theorem solution
    (O : Type u) [CommRing O] [IsNoetherianRing O] [IsLocalRing O] :
    ∃ (_ : IsLocalRing (AdicCompletion (maximalIdeal O) O))
      (_ : IsLocalHom (algebraMap O (AdicCompletion (maximalIdeal O) O))),
      IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal O) O)) (AdicCompletion (maximalIdeal O) O) ∧
      Ideal.map (algebraMap O (AdicCompletion (maximalIdeal O) O)) (maximalIdeal O) =
        maximalIdeal (AdicCompletion (maximalIdeal O) O) ∧
      ∀ x : AdicCompletion (maximalIdeal O) O, ∃ o : O,
        x - algebraMap O (AdicCompletion (maximalIdeal O) O) o ∈ maximalIdeal (AdicCompletion (maximalIdeal O) O) := by
  classical
  set I : Ideal O := maximalIdeal O with hI
  have hIfg : I.FG := IsNoetherian.noetherian I
  let W := AdicCompletion I O
  let σ : O →+* W := algebraMap O W

  have hker : ∀ x : W, evalₐ I 1 x = 0 ↔ x ∈ I.map σ := by
    intro x
    have h₁ : (I ^ 1 : Ideal O) ≤ I ^ 1 • ⊤ := by rw [Ideal.smul_eq_mul, Ideal.mul_top]
    have h₂ : (I ^ 1 • ⊤ : Ideal O) ≤ I ^ 1 := by rw [Ideal.smul_eq_mul, Ideal.mul_top]
    have hk : eval I O 1 x = 0 ↔ x ∈ I.map σ := by
      rw [← LinearMap.mem_ker, ← pow_smul_top_eq_ker_eval hIfg, Ideal.smul_top_eq_map,
        Submodule.restrictScalars_mem, congrArg (Ideal.map σ) (pow_one I)]
    rw [← hk]
    constructor
    · intro h
      rw [← factor_evalₐ_eq_eval I x h₁, h, _root_.map_zero]
    · intro h
      rw [← factor_eval_eq_evalₐ I x h₂, h, _root_.map_zero]
  have hsurj1 : Function.Surjective (evalₐ I 1) := surjective_evalₐ I 1
  haveI hImax : I.IsMaximal := maximalIdeal.isMaximal O
  haveI hmax' : (I.map σ).IsMaximal := by
    have hkeq : RingHom.ker (evalₐ I 1).toRingHom = I.map σ := by
      ext x
      rw [RingHom.mem_ker]
      exact hker x
    rw [← hkeq]
    have hfield : IsField (O ⧸ I ^ 1) := by
      rw [pow_one]
      exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient I).mp hImax
    exact Ideal.Quotient.maximal_of_isField _
      (MulEquiv.isField hfield (RingHom.quotientKerEquivOfSurjective hsurj1).toMulEquiv)
  haveI : IsAdicComplete I W := AdicCompletion.isAdicComplete hIfg
  haveI hcomp : IsAdicComplete (I.map σ) W := by
    rw [IsAdicComplete.map_algebraMap_iff]
    infer_instance
  haveI : IsLocalRing W := isLocalRing_of_isAdicComplete_maximal (I.map σ)
  have hmaxW : maximalIdeal W = I.map σ := (eq_maximalIdeal hmax').symm
  have hlocal : IsLocalHom σ := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have haI : a ∈ I := (mem_maximalIdeal a).mpr hna
    have : σ a ∈ maximalIdeal W := by
      rw [hmaxW]
      exact Ideal.mem_map_of_mem σ haI
    exact (mem_maximalIdeal _).mp this ha
  refine ⟨inferInstance, hlocal, ?_, hmaxW.symm, fun w => ?_⟩
  · rw [hmaxW]; exact hcomp
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalₐ I 1 w)
    refine ⟨a, ?_⟩
    rw [hmaxW, ← hker, map_sub, ← ha, AlgHom.commutes, Ideal.Quotient.algebraMap_eq, sub_self]

end S_IsLocalRing_exists_isLocalRing_adicCompletion_isAdicComplete_map_maximalIdeal_eq
end P2MW
export P2MW.S_IsLocalRing_exists_isLocalRing_adicCompletion_isAdicComplete_map_maximalIdeal_eq (solution)
