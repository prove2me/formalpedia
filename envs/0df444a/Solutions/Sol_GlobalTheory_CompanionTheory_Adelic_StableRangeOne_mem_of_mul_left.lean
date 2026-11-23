-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Adelic.StableRangeOne.mem_of_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:36.836016+00:00
-- url     : https://prove2.me/submissions/0afa116a-17a8-406d-a0d6-f66579246761

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixInductionTransvectionDiagonal
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_StableRangeOne_exists_left_inv

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
theorem _root_.solution {T A : Matrix ι ι R} (hT : T ∈ elem R ι) (h : T * A ∈ elem R ι) :
    A ∈ elem R ι := by
  obtain ⟨B, hB, hBT⟩ := exists_left_inv hT
  have : A = B * (T * A) := by rw [← mul_assoc, hBT, one_mul]
  rw [this]
  exact mul_mem hB h
end GlobalTheory.CompanionTheory.Adelic.StableRangeOne
