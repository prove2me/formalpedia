-- Prove2me | solution 1 for OAI.Kadison.GeneratedMatrixBicommutant.in_represented
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:38:15.709717+00:00
-- url     : https://prove2.me/submissions/379a3b03-4b50-4bd8-bd59-b2de3a0285f2

import Mathlib
import Definitions.Def_OAIQ039C060
import Definitions.Def_OAIQ039C061

section
-- module Solutions.OAIQ039_CM.Commutator_GeneratedMatrixBicommutant
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder Matrix.Norms.L2Operator

namespace Kadison.GeneratedMatrixBicommutant

variable {H A : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [CStarAlgebra A]

variable (size : ℕ → ℕ)

variable (stage : ∀ n,Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ →⋆ₐ[ℂ] A)

variable (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H))

lemma representedStages_eq : NormalGNS.representedStages (algebra size stage φ)
    (fun n => Fin (size n+1)) (stageHom size stage φ)=stages size stage φ := by
  apply iSup_congr
  intro n
  rfl

lemma in_represented_oai (a : algebra size stage φ) :
    (a:H →L[ℂ] H)∈Set.centralizer (Set.centralizer
      (NormalGNS.representedStages (algebra size stage φ) (fun n => Fin (size n+1))
        (stageHom size stage φ) : Set (H →L[ℂ] H))) := by
  rw [representedStages_eq]
  exact (NormalGNS.mem_bicommutant _ _).mp a.property

end Kadison.GeneratedMatrixBicommutant

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.GeneratedMatrixBicommutant.in_represented_oai := @OAI.Kadison.GeneratedMatrixBicommutant.in_represented_oai
