-- Prove2me | solution 1 for OAI.Saxl.intertwiningLiftSubrep_injective
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-15T21:32:11.961079+00:00
-- url     : https://prove2.me/submissions/38b48153-d3cd-4215-bbf3-577c9c6a37a0

import Mathlib
import Definitions.Def_OAIQ259US000

section
-- module Solutions.OAIQ259_US.Saxl_CyclicTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uX uY

namespace Saxl

lemma intertwiningLiftSubrep_injective_oai {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (f : Representation.IntertwiningMap ρ σ) (hf : Function.Injective f)
    (S : Subrepresentation σ) (hS : S ≤ f.range) :
    Function.Injective (intertwiningLiftSubrep f hf S hS) := by
  intro x y h
  apply Subtype.ext
  unfold intertwiningLiftSubrep at h
  have hh := (intertwiningRangeEquiv f hf).symm.injective h
  exact congrArg (fun z : f.range => (z : Y)) hh

end Saxl

end

end OAI
end

theorem solution.{uG, uX, uY} : type_of% @OAI.Saxl.intertwiningLiftSubrep_injective_oai.{uG, uX, uY} := @OAI.Saxl.intertwiningLiftSubrep_injective_oai.{uG, uX, uY}
