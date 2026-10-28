-- Prove2me | solution 1 for OAI.Kadison.BiprodLinkColumn.component_intertwines
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:21:23.824813+00:00
-- url     : https://prove2.me/submissions/318c847a-cd9e-4c59-b3e0-8c853675370f

import Mathlib
import Definitions.Def_OAIQ039C020

section
-- module Solutions.OAIQ039_CM.Commutator_BiprodLinkColumn
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

open Filter

namespace Kadison.BiprodLinkColumn

open HilbertBiprod PartialIsometryOrder HilbertFiniteMaps

variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

variable (N : VonNeumannAlgebra (Space H G))

variable (S : Set (Intertwiner N)) (hS : OrthogonalLinks N right left S)

include hS

omit hS

lemma component_intertwines_oai {A : Type*} [CStarAlgebra A]
    (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : A →⋆ₐ[ℂ] (G →L[ℂ] G))
    (v : Intertwiner N) (a : A)
    (hv : block (φ a) (ψ a)*star v.val=star v.val*block (φ a) (ψ a)) :
    (component N v).comp (φ a)=(ψ a).comp (component N v) := by
  ext x
  have h := congrArg (fun T : Space H G →L[ℂ] Space H G => (T (inlL x)).ofLp.2) hv
  simpa only [component,ContinuousLinearMap.comp_apply,adjoint_inrL,WithLp.sndL_apply,
    mul_apply_eq_comp,ContinuousLinearMap.star_eq_adjoint,block_apply,
    inlL_apply,WithLp.ofLp_toLp,WithLp.snd,map_zero] using h.symm

end Kadison.BiprodLinkColumn

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Kadison.BiprodLinkColumn.component_intertwines_oai.{u_1, u_2, u_3} := @OAI.Kadison.BiprodLinkColumn.component_intertwines_oai.{u_1, u_2, u_3}
