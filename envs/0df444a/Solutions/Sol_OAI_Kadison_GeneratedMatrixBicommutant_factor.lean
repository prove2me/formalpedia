-- Prove2me | solution 1 for OAI.Kadison.GeneratedMatrixBicommutant.factor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T07:23:23.103879+00:00
-- url     : https://prove2.me/submissions/22a55965-ad48-43bc-a5c8-0cb5fa5fadae

import Mathlib
import Definitions.Def_OAIQ039C037
import Theorems.Thm_OAI_Kadison_GeneratedMatrixBicommutant_in_range

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

lemma factor_oai (hφ : Set.centralizer (Set.centralizer (Set.range φ))=Set.range φ)
    (hinj : Function.Injective φ)
    (hirr : ∀ b : A,(∀ n (a : Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ),
      stage n a*b=b*stage n a) → ∃ c : ℂ,b=algebraMap ℂ A c) :
    FactorCorner.IsFactor (algebra size stage φ) := by
  intro z hz hcentral
  obtain ⟨b,hb⟩ := in_range size stage φ hφ ⟨z,hz⟩
  change φ b=z at hb
  obtain ⟨c,hc⟩ := hirr b (by
    intro n a
    apply hinj
    simp only [map_mul,hb]
    exact hcentral _ (stage_mem size stage φ n a))
  refine ⟨c,?_⟩
  rw [←hb,hc,Algebra.algebraMap_eq_smul_one,map_smul,map_one]

end Kadison.GeneratedMatrixBicommutant

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.GeneratedMatrixBicommutant.factor_oai := @OAI.Kadison.GeneratedMatrixBicommutant.factor_oai
