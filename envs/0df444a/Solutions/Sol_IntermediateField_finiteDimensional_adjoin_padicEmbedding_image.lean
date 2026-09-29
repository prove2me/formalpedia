-- Prove2me | solution 1 for IntermediateField.finiteDimensional_adjoin_padicEmbedding_image
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/11b1f491-b4a0-59a3-b489-ef08e9a1da35

import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_finiteDimensional_adjoin_padicEmbedding_image

set_option autoImplicit false
open scoped IntermediateField
open Polynomial
open scoped Pointwise

theorem solution
    (q : ℕ) [Fact q.Prime]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] :
    FiniteDimensional ℚ_[q]
      (IntermediateField.adjoin ℚ_[q] (padicEmbedding q '' (F : Set (AlgebraicClosure ℚ)))) := by
  classical
  let bF := Module.finBasis ℚ F
  let T : Set (PadicAlgCl q) := Set.range fun i => padicEmbedding q (bF i)
  haveI : FiniteDimensional ℚ_[q] (IntermediateField.adjoin ℚ_[q] T) :=
    IntermediateField.finiteDimensional_adjoin
      (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[q]) x).isIntegral)
  have hle : IntermediateField.adjoin ℚ_[q] (padicEmbedding q '' (F : Set (AlgebraicClosure ℚ))) ≤
      IntermediateField.adjoin ℚ_[q] T := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : AlgebraicClosure ℚ) = F.val.toLinearMap (⟨x, hx⟩ : F) := rfl
    rw [hx', ← bF.sum_repr (⟨x, hx⟩ : F), map_sum]
    change (padicEmbedding q).toLinearMap _ ∈ _
    rw [map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_smul, map_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply ℚ ℚ_[q] (PadicAlgCl q)]
    exact mul_mem (IntermediateField.algebraMap_mem _ _)
      (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion_injective hle)

end S_IntermediateField_finiteDimensional_adjoin_padicEmbedding_image
end P2MW
export P2MW.S_IntermediateField_finiteDimensional_adjoin_padicEmbedding_image (solution)
