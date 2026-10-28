-- Prove2me | solution 1 for OAI.Kadison.TracialGNS.left_faithful
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:08:16.684089+00:00
-- url     : https://prove2.me/submissions/a1320c09-c910-4076-a678-14c63d0279f2

import Mathlib
import Definitions.Def_OAIQ039C003

section
-- module Solutions.OAIQ039_CM.Commutator_TracialDevelopment
attribute [-instance] _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion

namespace Kadison

namespace TracialGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))

lemma coe_preGNS_eq_zero_iff
    (hfaith : ∀ a : A, τ (star a * a) = 0 → a = 0) (a : A) :
    (τ.toPreGNS a : τ.GNS) = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply hfaith a
    have hn : ‖τ.toPreGNS a‖ = 0 := by
      rw [← Completion.norm_coe, h, norm_zero]
    have := τ.preGNS_norm_sq (τ.toPreGNS a)
    simpa [hn] using this.symm
  · rintro rfl
    simp [Completion.coe_zero]

lemma left_faithful_oai (hfaith : ∀ a : A, τ (star a * a) = 0 → a = 0) :
    Function.Injective τ.gnsStarAlgHom := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  apply (coe_preGNS_eq_zero_iff τ hfaith a).mp
  rw [← left_vacuum τ a, ha, zero_apply]

end TracialGNS

end Kadison
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.TracialGNS.left_faithful_oai.{u_1} := @OAI.Kadison.TracialGNS.left_faithful_oai.{u_1}
