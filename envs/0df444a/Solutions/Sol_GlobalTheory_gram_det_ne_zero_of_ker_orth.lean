-- Prove2me | solution 1 for GlobalTheory.gram_det_ne_zero_of_ker_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:59:06.940182+00:00
-- url     : https://prove2.me/submissions/a64255be-29be-42ad-92a9-0980d3d69ed8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GramDetNeZeroOfKerOrth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
namespace GlobalTheory
theorem _root_.solution {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι → Fin n → K) (hli : LinearIndependent K u) (hsp : Submodule.span K (Set.range u) = LinearMap.ker (Matrix.toLin' A)) (horth : ∀ x z, A *ᵥ x = 0 → ∑ k, σ ((A *ᵥ z) k) * x k = 0) (hdec : ∀ v, ∃ z y, A *ᵥ y = 0 ∧ v = A *ᵥ z + y) : (Matrix.of fun i j => ∑ k, σ (u i k) * u j k).det ≠ 0 := by
  intro hdet
  obtain ⟨c, hc0, hGc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set x : Fin n → K := ∑ j, c j • u j with hxdef
  have hx0 : x ≠ 0 := by
    intro hx
    apply hc0
    funext j
    exact Fintype.linearIndependent_iff.mp hli c hx j
  have hxspan : x ∈ Submodule.span K (Set.range u) :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hAx : A *ᵥ x = 0 := by
    rw [hsp, LinearMap.mem_ker, Matrix.toLin'_apply] at hxspan
    exact hxspan
  have hu : ∀ i, ∑ k, σ (u i k) * x k = 0 := by
    intro i
    have := congrFun hGc i
    rw [Matrix.mulVec, dotProduct] at this
    simp only [Matrix.of_apply, Pi.zero_apply] at this
    rw [← this]
    simp only [hxdef, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have hy : ∀ y ∈ LinearMap.ker (Matrix.toLin' A), ∑ k, σ (y k) * x k = 0 := by
    intro y hy
    rw [← hsp] at hy
    obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hy
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ i, ∑ k, σ (d i) * σ (u i k) * x k = σ (d i) * ∑ k, σ (u i k) * x k := by
      intro i; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    simp [this, hu]
  have hall : ∀ v : Fin n → K, ∑ k, σ (v k) * x k = 0 := by
    intro v
    obtain ⟨z, y, hAy, rfl⟩ := hdec v
    have h1 := horth x z hAx
    have h2 := hy y (by rw [LinearMap.mem_ker, Matrix.toLin'_apply]; exact hAy)
    simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib, h1, h2, add_zero]
  apply hx0
  funext k
  have := hall (Pi.single k 1)
  simpa [Pi.single_apply] using this
end GlobalTheory
