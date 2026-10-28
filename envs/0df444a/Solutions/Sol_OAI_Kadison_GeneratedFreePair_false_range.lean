-- Prove2me | solution 1 for OAI.Kadison.GeneratedFreePair.false_range
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:36:24.724414+00:00
-- url     : https://prove2.me/submissions/73d816b6-e50d-41af-a5f3-7c1f74670080

import Mathlib
import Definitions.Def_OAIQ039C060

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

lemma false_range_oai : factors D k false=(leftHom D k).range := by
  ext a
  change (a:H →L[ℂ] H)∈D ↔ ∃ d : D,leftHom D k d=a
  constructor
  · intro ha
    exact ⟨⟨a,ha⟩,Subtype.ext rfl⟩
  · rintro ⟨d,rfl⟩
    exact d.property

end Kadison.GeneratedFreePair

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.GeneratedFreePair.false_range_oai := @OAI.Kadison.GeneratedFreePair.false_range_oai
