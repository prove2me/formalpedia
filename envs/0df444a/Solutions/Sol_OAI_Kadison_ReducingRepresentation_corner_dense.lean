-- Prove2me | solution 1 for OAI.Kadison.ReducingRepresentation.corner_dense
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:19:08.611439+00:00
-- url     : https://prove2.me/submissions/5c3b01c9-5ec2-4ab9-9ffe-60ded9e0db51

import Mathlib
import Definitions.Def_OAIQ039C004

section
-- module Solutions.OAIQ039_CM.Commutator_CornerCyclicImplementation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.ReducingRepresentation

open MatrixCornerHilbert

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma corner_dense_oai (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) {p : A} (hp : IsStarProjection p)
    (Ω : H) (hΩ : DenseRange (fun a : A => σ a Ω)) (hpΩ : σ p Ω=Ω) :
    DenseRange (fun a : Corner hp => corner σ hp a
      (⟨Ω,(mem_fixedSpace _ _).mpr hpΩ⟩ : fixedSpace (σ p))) := by
  have hs : Function.Surjective (cornerProjection σ hp) := fun x => ⟨(x:H),cornerProjection_fixed σ hp x⟩
  have hd := hs.denseRange.comp hΩ (cornerProjection σ hp).continuous
  intro x
  apply (closure_mono ?_) (hd x)
  rintro _ ⟨a,rfl⟩
  let b : Corner hp := ⟨p*a*p,by rw [←mul_assoc,←mul_assoc,hp.isIdempotentElem.eq],
    by rw [mul_assoc _ p p,hp.isIdempotentElem.eq]⟩
  refine ⟨b,?_⟩
  apply Subtype.ext
  change σ (p*a*p) Ω=σ p (σ a Ω)
  simp only [map_mul,mul_apply_eq_comp,hpΩ]

end Kadison.ReducingRepresentation

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.ReducingRepresentation.corner_dense_oai.{u_1, u_2} := @OAI.Kadison.ReducingRepresentation.corner_dense_oai.{u_1, u_2}
