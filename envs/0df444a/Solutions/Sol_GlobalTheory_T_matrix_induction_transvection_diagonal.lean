-- Prove2me | solution 1 for GlobalTheory.T.matrix_induction_transvection_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:18:23.130884+00:00
-- url     : https://prove2.me/submissions/41f24801-2e85-4308-971a-596a5d615fe8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixInductionTransvectionDiagonal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixInductionTransvectionDiagonalStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_StableRangeOne_matrix_induction


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R], (∀ a b : R, IsCoprime a b → ∃ t, IsUnit (a + t * b)) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (p : Matrix ι ι R → Prop), (∀ (i j : ι) (c : R), i ≠ j → p (Matrix.transvection i j c)) → (∀ D : ι → R, (∀ i, IsUnit (D i)) → p (Matrix.diagonal D)) → (∀ A B, IsUnit A.det → IsUnit B.det → p A → p B → p (A * B)) → ∀ A : Matrix ι ι R, IsUnit A.det → p A := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.StableRangeOne.matrix_induction | exact GlobalTheory.CompanionTheory.Adelic.StableRangeOne.matrix_induction | (intros; apply GlobalTheory.CompanionTheory.Adelic.StableRangeOne.matrix_induction <;> assumption)
end _root_.GlobalTheory.T
