-- Prove2me | solution 1 for GlobalTheory.vecPoly_mem_span_values
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:23:54.058832+00:00
-- url     : https://prove2.me/submissions/cacaa36c-57dd-40cb-9a3c-9ba2b7a17bf5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_VecPolyMemSpanValues

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (Z : ℂ → V)
    (X : ℕ → V) (ν : Fin n → ℂ) (hν : Function.Injective ν)
    (hZ : ∀ s : ℂ, Z s = ∑ j ∈ Finset.range n, s ^ j • X j) :
    (∀ j, j < n → X j ∈ Submodule.span ℂ (Set.range fun i => Z (ν i))) ∧
      ∀ s : ℂ, Z s ∈ Submodule.span ℂ (Set.range fun i => Z (ν i)) := by
  classical
  set W := Submodule.span ℂ (Set.range fun i => Z (ν i)) with hW
  set M : Matrix (Fin n) (Fin n) ℂ := Matrix.vandermonde ν with hM
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hν)
  have hinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hunit
  have hZν : ∀ i, Z (ν i) = ∑ l : Fin n, M i l • X l := by
    intro i
    rw [hZ, ← Fin.sum_univ_eq_sum_range (fun j => ν i ^ j • X j) n]
    simp [hM, Matrix.vandermonde_apply]
  have hX : ∀ k : Fin n, X k ∈ W := by
    intro k
    have key : ∀ l, ∑ i, M⁻¹ k i * M i l = (1 : Matrix (Fin n) (Fin n) ℂ) k l := fun l => by
      rw [← hinv, Matrix.mul_apply]
    have hsum : ∑ i : Fin n, M⁻¹ k i • Z (ν i) = X k := by
      simp_rw [hZν, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul, key, Matrix.one_apply, ite_smul, one_smul, zero_smul]
      simp
    rw [← hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨fun j hj => hX ⟨j, hj⟩, fun s => ?_⟩
  rw [hZ]
  exact Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (hX ⟨j, Finset.mem_range.mp hj⟩)
end GlobalTheory
