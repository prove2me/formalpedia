-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Adelic.StableRangeOne.mem_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:49:51.008042+00:00
-- url     : https://prove2.me/submissions/299d094a-4c80-417e-b26a-ac700859dcf7

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixInductionTransvectionDiagonal
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_StableRangeOne_mem_of_mul_left
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_StableRangeOne_isUnit_det_of_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_StableRangeOne_rowOp_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_StableRangeOne_mem_of_unit_pivot
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_StableRangeOne_exists_unit_pivot

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Adelic GlobalTheory.CompanionTheory.Adelic.StableRangeOne
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.Adelic.StableRangeOne
theorem _root_.solution (hR : ∀ a b : R, IsCoprime a b → ∃ t, IsUnit (a + t * b))
    (s : Finset ι) : ∀ A : Matrix ι ι R, IsUnit A.det → Fixed s A → A ∈ elem R ι := by
  induction s using Finset.induction_on with
  | empty =>
    intro A _ hF
    have : A = 1 := by
      ext i j
      exact hF i j (Or.inl (by simp))
    rw [this]
    exact one_mem _
  | insert k s hk ih =>
    intro A hA hF
    obtain ⟨w, hw0, hwF, hwu⟩ := exists_unit_pivot hR hA hF hk
    have hm := rowOp_mem k w hw0
    have hdet : IsUnit (rowOp k w * A).det := by
      rw [Matrix.det_mul]
      exact (isUnit_det_of_mem hm).mul hA
    exact mem_of_mul_left hm (mem_of_unit_pivot ih hdet hwF hk hwu)
end GlobalTheory.CompanionTheory.Adelic.StableRangeOne
