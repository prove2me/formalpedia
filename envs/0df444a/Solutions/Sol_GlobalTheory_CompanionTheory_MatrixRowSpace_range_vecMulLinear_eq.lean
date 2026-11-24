-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MatrixRowSpace.range_vecMulLinear_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:52:43.088937+00:00
-- url     : https://prove2.me/submissions/ef614453-e76f-4db9-a483-4ea79bccafa0

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RangeVecMulLinearEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.MatrixRowSpace
variable {K : Type} [Field K]
namespace GlobalTheory.CompanionTheory.MatrixRowSpace
theorem _root_.solution {n r : ℕ} (c : Matrix (Fin r) (Fin n) K) :
    LinearMap.range c.vecMulLinear = Submodule.span K (Set.range c) := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    rw [Matrix.vecMulLinear_apply, Matrix.vecMul_eq_sum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    ext j
    simp [Matrix.vecMul, dotProduct, Pi.single_apply]
end GlobalTheory.CompanionTheory.MatrixRowSpace
