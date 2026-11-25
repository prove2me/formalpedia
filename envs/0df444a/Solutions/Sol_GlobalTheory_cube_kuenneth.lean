-- Prove2me | solution 1 for GlobalTheory.cube_kuenneth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:59:52.803619+00:00
-- url     : https://prove2.me/submissions/5b9843bb-1d7c-4c7d-8d83-94aede374035

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe
import Theorems.Thm_GlobalTheory_nonempty_cubeHomology_extTensor_equiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex TensorProduct
universe v u
open GlobalTheory
open GlobalTheory.Cube Finset.HasAntidiagonal Module
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] [Finite ι] [Finite κ] {K : Type u} [Field K]
namespace GlobalTheory
theorem _root_.solution (A : Cube.{v} ι K) (B : Cube.{v} κ K)
    (hA : ∀ p, Module.Finite K ((cubeComplex A).homology p))
    (hB : ∀ q, Module.Finite K ((cubeComplex B).homology q)) (n : ℕ) :
    Module.Finite K ((cubeComplex (extTensor A B)).homology n) ∧
      finrank K ((cubeComplex (extTensor A B)).homology n) = ∑ x ∈ antidiagonal n,
        finrank K ((cubeComplex A).homology x.1) * finrank K ((cubeComplex B).homology x.2) := by
  obtain ⟨E⟩ := nonempty_cubeHomology_extTensor_equiv A B n
  refine ⟨Module.Finite.equiv E.symm, ?_⟩
  rw [E.finrank_eq, Module.finrank_pi_fintype, ← Finset.sum_coe_sort (antidiagonal n)]
  exact Finset.sum_congr rfl fun x _ => Module.finrank_tensorProduct
end GlobalTheory
