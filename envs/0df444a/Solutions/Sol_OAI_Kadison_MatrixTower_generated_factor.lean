-- Prove2me | solution 1 for OAI.Kadison.MatrixTower.generated_factor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:21:30.654119+00:00
-- url     : https://prove2.me/submissions/7a4f1988-697f-4bca-9dae-4b047a085a89

import Mathlib
import Definitions.Def_OAIQ039C073

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixTowerClosure
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators

namespace Kadison.MatrixTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (F : ℕ → Stage M)

variable (hirr : ∀ a : M,(∀ n b,(F n).hom b*a=a*(F n).hom b) → ∃ z : ℂ,a=z • (1:M))

include hirr in
lemma generated_irreducible (a : H →L[ℂ] H) (ha : a∈M)
    (hc : a∈Set.centralizer (generated M F : Set (H →L[ℂ] H))) :
    ∃ z : ℂ,a=z • (1:H →L[ℂ] H) := by
  obtain ⟨z,hz⟩ := hirr ⟨a,ha⟩ (fun n b => Subtype.ext (hc _ (stage_mem M F n b)))
  exact ⟨z,congrArg Subtype.val hz⟩

include hirr in
lemma generated_factor_oai : FactorCorner.IsFactor (generated M F) := by
  intro a ha hc
  exact generated_irreducible M F hirr a (generated_le M F ha) hc

end Kadison.MatrixTower

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.MatrixTower.generated_factor_oai.{u_1} := @OAI.Kadison.MatrixTower.generated_factor_oai.{u_1}
