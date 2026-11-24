-- Prove2me | solution 1 for GlobalTheory.UnRep.finite_primes_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:59:02.7439+00:00
-- url     : https://prove2.me/submissions/c0c9c202-cbef-48b8-94dc-46ba32168e1a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormOneInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_AdelicUnitaryScalingUnit
import Theorems.Thm_GlobalTheory_UnRep_adEval_surjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep
namespace GlobalTheory.UnRep
theorem _root_.solution (F : Type) [Field F] [NumberField F] (e : FiniteAdeleRing (𝓞 F) F)
    (he : {v | e v ≠ 0}.Finite) :
    {P : Ideal (FiniteAdeleRing (𝓞 F) F) | P.IsPrime ∧ 1 - e ∈ P}.Finite := by
  refine (he.image fun v => RingHom.ker (adEval F v)).subset ?_
  rintro P ⟨hP, h⟩
  have hle : he.toFinset.inf (fun v => RingHom.ker (adEval F v)) ≤ P := by
    intro a ha
    have h0 : a * e = 0 := by
      refine FiniteAdeleRing.ext F fun v => ?_
      change a v * e v = 0
      by_cases hv : e v = 0
      · rw [hv, mul_zero]
      · have h1 : a ∈ RingHom.ker (adEval F v) :=
          (Finset.inf_le (f := fun v => RingHom.ker (adEval F v)) (he.mem_toFinset.2 hv)) ha
        have h2 : a v = 0 := h1
        rw [h2, zero_mul]
    have : a = a * (1 - e) := by rw [mul_sub, h0, mul_one, sub_zero]
    rw [this]
    exact P.mul_mem_left _ h
  obtain ⟨v, hv, hvP⟩ := (Ideal.IsPrime.inf_le' hP).1 hle
  exact ⟨v, he.mem_toFinset.1 hv,
    (RingHom.ker_isMaximal_of_surjective _ (adEval_surjective F v)).eq_of_le hP.ne_top hvP⟩
end GlobalTheory.UnRep
