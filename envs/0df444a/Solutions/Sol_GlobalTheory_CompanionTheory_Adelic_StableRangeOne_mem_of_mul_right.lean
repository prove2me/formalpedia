-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Adelic.StableRangeOne.mem_of_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:17:18.014804+00:00
-- url     : https://prove2.me/submissions/6db3cf56-5c6b-43cb-adba-21163f77d9f1

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
theorem _root_.solution {T A : Matrix ι ι R} (hT : T ∈ elem R ι) (h : A * T ∈ elem R ι) :
    A ∈ elem R ι := by
  obtain ⟨B, hB, hBT⟩ := exists_left_inv hT
  have hTB : T * B = 1 := mul_eq_one_comm.mp hBT
  have : A = (A * T) * B := by rw [mul_assoc, hTB, mul_one]
  rw [this]
  exact mul_mem h hB
end GlobalTheory.CompanionTheory.Adelic.StableRangeOne
