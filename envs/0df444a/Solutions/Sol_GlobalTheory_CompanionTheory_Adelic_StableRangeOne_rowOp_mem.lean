-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Adelic.StableRangeOne.rowOp_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:23.963829+00:00
-- url     : https://prove2.me/submissions/10436a37-4b82-4da0-9531-f4dec058aec7

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixInductionTransvectionDiagonal
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_StableRangeOne_transvection_mem

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
theorem _root_.solution (k : ι) (c : ι → R) (hc : c k = 0) : rowOp k c ∈ elem R ι := by
  have key : ∀ t : Finset ι, k ∉ t → rowOp k (fun j => if j ∈ t then c j else 0) ∈ elem R ι := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      have : rowOp k (fun j => if j ∈ (∅ : Finset ι) then c j else 0) = (1 : Matrix ι ι R) := by
        ext a b
        simp [rowOp]
      rw [this]
      exact one_mem _
    | insert i t hi ih =>
      intro hk
      have hki : k ≠ i := fun h => hk (h ▸ Finset.mem_insert_self _ _)
      have hkt : k ∉ t := fun h => hk (Finset.mem_insert_of_mem h)
      have : rowOp k (fun j => if j ∈ insert i t then c j else 0) =
          rowOp k (fun j => if j ∈ t then c j else 0) * Matrix.transvection k i (c i) := by
        ext a b
        by_cases hb : b = i
        · subst hb
          rw [Matrix.mul_transvection_apply_same]
          by_cases ha : a = k
          · subst ha
            simp [rowOp, Matrix.one_apply, hi, hki, hkt]
          · simp [rowOp, Matrix.one_apply, ha]
        · rw [Matrix.mul_transvection_apply_of_ne _ _ _ _ hb]
          simp [rowOp, Finset.mem_insert, hb]
      rw [this]
      exact mul_mem (ih hkt) (transvection_mem hki _)
  have := key (Finset.univ.erase k) (by simp)
  convert this using 2
  funext j
  by_cases h : j = k
  · subst h; simp [hc]
  · simp [h]
end GlobalTheory.CompanionTheory.Adelic.StableRangeOne
