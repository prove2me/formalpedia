-- Prove2me | solution 1 for OAI.Kadison.EquivariantBicommutant.bicommutant_range
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:04:45.597145+00:00
-- url     : https://prove2.me/submissions/b7bb8a5b-31bd-462a-b055-8aed7a68944c

import Mathlib
import Definitions.Def_OAIQ039C008

section
-- module Solutions.OAIQ039_CM.Commutator_EquivariantBicommutant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.EquivariantBicommutant

variable {A B : Type*} [Monoid A] [Monoid B]

lemma bicommutant_range_oai {C : Type*} (e : A ≃* B) (f : C → A)
    (hf : Set.centralizer (Set.centralizer (Set.range f))=Set.range f) :
    Set.centralizer (Set.centralizer (Set.range (e ∘ f)))=Set.range (e ∘ f) := by
  rw [Set.range_comp,bicommutant_image,hf]

end Kadison.EquivariantBicommutant

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Kadison.EquivariantBicommutant.bicommutant_range_oai.{u_1, u_2, u_3} := @OAI.Kadison.EquivariantBicommutant.bicommutant_range_oai.{u_1, u_2, u_3}
