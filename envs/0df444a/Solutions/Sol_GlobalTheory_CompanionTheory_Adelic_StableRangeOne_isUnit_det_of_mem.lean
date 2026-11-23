-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Adelic.StableRangeOne.isUnit_det_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:35.844288+00:00
-- url     : https://prove2.me/submissions/58c8f68a-416e-48d4-ae72-fabfa831b1f9

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
theorem _root_.solution {A : Matrix ι ι R} (hA : A ∈ elem R ι) : IsUnit A.det := by
  obtain ⟨B, _, hBA⟩ := exists_left_inv hA
  have : B.det * A.det = 1 := by rw [← Matrix.det_mul, hBA, Matrix.det_one]
  exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact this)
end GlobalTheory.CompanionTheory.Adelic.StableRangeOne
