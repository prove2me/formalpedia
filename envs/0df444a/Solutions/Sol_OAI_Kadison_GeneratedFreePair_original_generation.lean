-- Prove2me | solution 1 for OAI.Kadison.GeneratedFreePair.original_generation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:37:53.419827+00:00
-- url     : https://prove2.me/submissions/b2edc16b-01bf-46c0-acbc-9e7f36a9c4a7

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

lemma right_factor (a : A) : rightHom D k a∈factors D k true := by
  change k a∈k.range
  exact ⟨a,rfl⟩

lemma original_generation_oai (a : algebra D k) : (a:H →L[ℂ] H)∈Set.centralizer
    (Set.centralizer (((iSup (factors D k)).map (algebra D k).toStarSubalgebra.subtype) : Set _)) := by
  have hj : D.toStarSubalgebra⊔k.range≤
      (iSup (factors D k)).map (algebra D k).toStarSubalgebra.subtype := by
    apply sup_le
    · intro d hd
      exact ⟨leftHom D k ⟨d,hd⟩,(le_iSup (factors D k) false) hd,rfl⟩
    · rintro b ⟨x,rfl⟩
      exact ⟨rightHom D k x,(le_iSup (factors D k) true) (right_factor D k x),rfl⟩
  have hb := (NormalGNS.mem_bicommutant _ _).mp a.property
  intro T hT
  apply hb T
  intro x hx
  exact hT x (hj hx)

end Kadison.GeneratedFreePair

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.GeneratedFreePair.original_generation_oai := @OAI.Kadison.GeneratedFreePair.original_generation_oai
