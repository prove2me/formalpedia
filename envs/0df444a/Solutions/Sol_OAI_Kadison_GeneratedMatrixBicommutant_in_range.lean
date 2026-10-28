-- Prove2me | solution 1 for OAI.Kadison.GeneratedMatrixBicommutant.in_range
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:14:41.985986+00:00
-- url     : https://prove2.me/submissions/1f448e2a-932f-4d72-8615-e467601b6c6b

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

lemma in_range_oai (hφ : Set.centralizer (Set.centralizer (Set.range φ))=Set.range φ)
    (a : algebra size stage φ) : (a:H →L[ℂ] H)∈Set.range φ := by
  have hle : stages size stage φ≤φ.range := by
    apply iSup_le
    intro n
    rintro a ⟨b,rfl⟩
    exact ⟨stage n b,rfl⟩
  have hd := EquivariantBicommutant.bicommutant_mono hle ((NormalGNS.mem_bicommutant _ _).mp a.property)
  rw [show (φ.range : Set (H →L[ℂ] H))=Set.range φ from rfl,hφ] at hd
  exact hd

end Kadison.GeneratedMatrixBicommutant

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.GeneratedMatrixBicommutant.in_range_oai := @OAI.Kadison.GeneratedMatrixBicommutant.in_range_oai
