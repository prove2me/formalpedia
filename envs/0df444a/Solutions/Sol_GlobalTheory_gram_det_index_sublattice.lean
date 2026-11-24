-- Prove2me | solution 1 for GlobalTheory.gram_det_index_sublattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:59:05.785436+00:00
-- url     : https://prove2.me/submissions/8fa20f6b-0588-413a-96c2-bfb95847fcb8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GramDetIndexSublattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open NumberField IsDedekindDomain
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (U V ι κ : Type) [AddCommGroup U] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (φ : U →ₗ[ℤ] V) (u : ι → U) (v : κ → U) (hc : Fintype.card ι = Fintype.card κ)
    (hv : ∀ k, v k ∈ Submodule.span ℤ (Set.range u)) :
    ∃ m : ℕ, (Matrix.gram ℝ fun k => φ (v k)).det = (m : ℝ) ^ 2 * (Matrix.gram ℝ fun i => φ (u i)).det ∧
      ∀ i, (m : ℤ) • u i ∈ Submodule.span ℤ (Set.range v) := by
  let e : ι ≃ κ := Fintype.equivOfCardEq hc
  choose A hA using fun i => (Submodule.mem_span_range_iff_exists_fun ℤ).1 (hv (e i))
  let Am : Matrix ι ι ℤ := Matrix.of A
  have hAm : ∀ i j, Am i j = A i j := fun _ _ => rfl
  let Ar : Matrix ι ι ℝ := Am.map (Int.castRingHom ℝ)
  have hAr : ∀ i j, Ar i j = (A i j : ℝ) := fun _ _ => rfl
  have hphi : ∀ i, φ (v (e i)) = ∑ j, (A i j : ℝ) • φ (u j) := by
    intro i
    rw [← hA i, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, Int.cast_smul_eq_zsmul]
  have h1 : (Matrix.gram ℝ fun k => φ (v k)).submatrix e e
      = Ar * (Matrix.gram ℝ fun i => φ (u i)) * Arᵀ := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply, hAr]
    rw [hphi i, hphi j, inner_sum]
    simp only [sum_inner, real_inner_smul_left, real_inner_smul_right, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  have hdetA : Ar.det = (Am.det : ℝ) := by
    have := (Int.castRingHom ℝ).map_det Am
    simpa [Ar] using this.symm
  refine ⟨Am.det.natAbs, ?_, ?_⟩
  · have h2 := Matrix.det_submatrix_equiv_self e (Matrix.gram ℝ fun k => φ (v k))
    rw [← h2, h1, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdetA]
    have h3 : ((Am.det.natAbs : ℕ) : ℝ) ^ 2 = (Am.det : ℝ) ^ 2 := by
      rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
    rw [h3]; ring
  · intro i
    have hkey : Am.det • u i = ∑ k, Am.adjugate i k • v (e k) := by
      have h4 : ∀ j, (Am.adjugate * Am) i j = Am.det * (1 : Matrix ι ι ℤ) i j := by
        intro j
        rw [Matrix.adjugate_mul, Matrix.smul_apply, smul_eq_mul]
      calc Am.det • u i = ∑ j, (Am.det * (1 : Matrix ι ι ℤ) i j) • u j := by
            simp [Matrix.one_apply, ite_smul]
        _ = ∑ j, (∑ k, Am.adjugate i k * A k j) • u j := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← h4 j, Matrix.mul_apply]; rfl
        _ = ∑ k, Am.adjugate i k • v (e k) := by
            simp only [Finset.sum_smul, ← hA, Finset.smul_sum, mul_smul]
            exact Finset.sum_comm
    have hmem : Am.det • u i ∈ Submodule.span ℤ (Set.range v) := by
      rw [hkey]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨e k, rfl⟩)
    rcases Int.natAbs_eq Am.det with h | h
    · rw [← h]; exact hmem
    · have : ((Am.det.natAbs : ℕ) : ℤ) = -Am.det := by omega
      rw [this, neg_smul]
      exact Submodule.neg_mem _ hmem
end GlobalTheory
