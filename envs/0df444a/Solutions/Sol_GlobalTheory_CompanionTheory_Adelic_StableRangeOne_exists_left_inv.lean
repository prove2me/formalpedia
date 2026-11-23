-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Adelic.StableRangeOne.exists_left_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:14.888479+00:00
-- url     : https://prove2.me/submissions/a480b5bf-25f8-4d34-9301-046556e3b465

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixInductionTransvectionDiagonal
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_StableRangeOne_transvection_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_StableRangeOne_diagonal_mem

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
theorem _root_.solution {A : Matrix ι ι R} (hA : A ∈ elem R ι) :
    ∃ B ∈ elem R ι, B * A = 1 := by
  induction hA using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with ⟨i, j, c, h, rfl⟩ | ⟨D, hD, rfl⟩
    · refine ⟨Matrix.transvection i j (-c), transvection_mem h _, ?_⟩
      rw [Matrix.transvection_mul_transvection_same _ _ h]
      simp
    · refine ⟨Matrix.diagonal (fun i => (((hD i).unit⁻¹ : Rˣ) : R)),
        diagonal_mem (fun i => Units.isUnit _), ?_⟩
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact (hD i).val_inv_mul
  | one => exact ⟨1, one_mem _, one_mul _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, ha'⟩ := hx
    obtain ⟨b, hb, hb'⟩ := hy
    exact ⟨b * a, mul_mem hb ha, by rw [mul_assoc, ← mul_assoc a, ha', one_mul, hb']⟩
end GlobalTheory.CompanionTheory.Adelic.StableRangeOne
