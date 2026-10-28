-- Prove2me | solution 1 for OAI.Kadison.GeneratedMatrixBicommutant.le_vonNeumann
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:15:04.481604+00:00
-- url     : https://prove2.me/submissions/03fe665a-a229-433a-a92f-073162d8a973

import Mathlib
import Definitions.Def_OAIQ039C026

section
-- module Solutions.OAIQ039_CM.Commutator_EquivariantBicommutant
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

lemma bicommutant_mono {s t : Set A} (h : s⊆t) :
    Set.centralizer (Set.centralizer s)⊆Set.centralizer (Set.centralizer t) := by
  intro x hx y hy
  exact hx y (fun z hz => hy z (h hz))

end Kadison.EquivariantBicommutant

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_GeneratedMatrixBicommutant
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
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

lemma le_vonNeumann_oai (N : VonNeumannAlgebra H)
    (hstage : ∀ n a,φ (stage n a)∈N) : algebra size stage φ≤N := by
  have hle : stages size stage φ≤N.toStarSubalgebra := by
    apply iSup_le
    intro n
    rintro a ⟨b,rfl⟩
    exact hstage n b
  intro a ha
  have hd := EquivariantBicommutant.bicommutant_mono hle ((NormalGNS.mem_bicommutant _ _).mp ha)
  change a∈N.carrier
  rw [←N.centralizer_centralizer']
  exact hd

end Kadison.GeneratedMatrixBicommutant

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.GeneratedMatrixBicommutant.le_vonNeumann_oai := @OAI.Kadison.GeneratedMatrixBicommutant.le_vonNeumann_oai
