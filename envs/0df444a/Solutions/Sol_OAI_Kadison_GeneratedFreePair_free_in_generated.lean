-- Prove2me | solution 1 for OAI.Kadison.GeneratedFreePair.free_in_generated
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:36:47.875522+00:00
-- url     : https://prove2.me/submissions/b2bdbec5-2efc-4c20-b6b2-2ae9e4bdc223

import Mathlib
import Definitions.Def_OAIQ039C060

section
-- module Solutions.OAIQ039_CM.Commutator_FreeMomentsTransport
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.FreeMoments

variable {A B : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
  [Ring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (U : ι → StarSubalgebra ℂ B)
  (τ : A →ₗ[ℂ] ℂ) (ρ : B →ₗ[ℂ] ℂ)
  (j : A →⋆ₐ[ℂ] B) (htrace : ∀ a,ρ (j a)=τ a)
  (hSU : ∀ i a,a∈S i → j a∈U i)

lemma word_transport (w : List (Letter S τ)) :
    word (w.map (Letter.transport S U τ ρ j htrace hSU))=j (word w) := by
  induction w with
  | nil => simp
  | cons a w ih => simp only [List.map_cons,word_cons,Letter.transport,ih,map_mul]

include htrace hSU in
theorem free_of_map (hfree : Free U ρ) : Free S τ := by
  intro w hw hne
  let F := Letter.transport S U τ ρ j htrace hSU
  have hr : Reduced (w.map F) := by
    simpa only [Reduced,List.isChain_map,F,Letter.transport] using hw
  have hn : w.map F≠[] := fun h => hne (List.map_eq_nil_iff.mp h)
  have hz := hfree (w.map F) hr hn
  rw [word_transport,htrace] at hz
  exact hz

end Kadison.FreeMoments

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_GeneratedFreePair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder InnerProductSpace

namespace Kadison.GeneratedFreePair

open FreeMoments

variable {H A : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [CStarAlgebra A]

variable (D : VonNeumannAlgebra H) (k : A →⋆ₐ[ℂ] (H →L[ℂ] H))

include D k in
theorem free_in_generated_oai (ξ : H)
    (hfree : Free (ambient D k) (VectorFunctional.functional ξ).toLinearMap) :
    Free (factors D k) (VectorGNS.subalgebraTrace (algebra D k) ξ).toLinearMap := by
  apply free_of_map (factors D k) (ambient D k)
    (VectorGNS.subalgebraTrace (algebra D k) ξ).toLinearMap
    (VectorFunctional.functional ξ).toLinearMap (algebra D k).toStarSubalgebra.subtype
    (fun _ => rfl) (fun _ _ ha => ha) hfree

end Kadison.GeneratedFreePair

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.GeneratedFreePair.free_in_generated_oai := @OAI.Kadison.GeneratedFreePair.free_in_generated_oai
