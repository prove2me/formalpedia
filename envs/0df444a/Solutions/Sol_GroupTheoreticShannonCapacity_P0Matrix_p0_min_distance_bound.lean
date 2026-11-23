-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.P0Matrix.p0_min_distance_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:52:49.245313+00:00
-- url     : https://prove2.me/submissions/1ed12815-ff13-491f-8900-9d07a5a4112c

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_p0_sign_property
import Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_p0_add_scalar_invertible

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset
namespace GroupTheoreticShannonCapacity.P0Matrix
theorem _root_.solution (n : ℕ) [NeZero n] (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : IsP0Matrix n M) (q : ℝ) (hq : 0 < q) :
    Lattice.minDistance n (Lattice.latticeOfMatrix n (M + q • 1)) ≥ q := by
  -- Show that all nonzero vectors in the lattice have infinity norm ≥ q
  unfold Lattice.minDistance
  apply le_csInf
  · -- The set is nonempty (there exist nonzero lattice vectors)
    -- Take x = e_0 (first standard basis vector), then (M + qI) * x is nonzero
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    let x : Fin n → ℤ := fun j => if j = ⟨0, hn⟩ then 1 else 0
    let v := (M + q • 1).mulVec (fun i => (x i : ℝ))
    use Lattice.inftyNorm n v
    refine ⟨v, ⟨x, rfl⟩, ?_, rfl⟩
    -- Show v ≠ 0 using that M + qI is invertible
    intro hv_zero
    have hx_ne : (fun i => (x i : ℝ)) ≠ 0 := by
      intro hx_zero
      have h0 : (x ⟨0, hn⟩ : ℝ) = 0 := congr_fun hx_zero ⟨0, hn⟩
      simp only [x, ↓reduceIte, Int.cast_one] at h0
      exact one_ne_zero h0
    have hunit := p0_add_scalar_invertible n M hM q hq
    rw [Matrix.isUnit_iff_isUnit_det] at hunit
    have hdet_ne := isUnit_iff_ne_zero.mp hunit
    have hno_kernel : ¬∃ w, w ≠ 0 ∧ (M + q • 1).mulVec w = 0 := by
      rw [Matrix.exists_mulVec_eq_zero_iff]
      exact hdet_ne
    push_neg at hno_kernel
    exact hno_kernel (fun i => (x i : ℝ)) hx_ne hv_zero
  · -- For all d in the set, d ≥ q
    intro d ⟨v, hv_in, hv_ne, hd_eq⟩
    rw [hd_eq]
    -- v = (M + qI) * x for some x ∈ ℤⁿ
    obtain ⟨x, hv_eq⟩ := hv_in
    -- x ≠ 0 since v ≠ 0 and M + qI is invertible
    have hx_ne : (fun i => (x i : ℝ)) ≠ 0 := by
      intro hx_zero
      apply hv_ne
      rw [hv_eq, hx_zero]
      simp only [Matrix.mulVec_zero]
    -- Apply p0_sign_property to get i with x_i ≠ 0 and (Mx)_i * x_i ≥ 0
    obtain ⟨i, hi_ne, hi_sign⟩ := p0_sign_property n M hM _ hx_ne
    -- Compute v_i = (Mx)_i + q * x_i
    have hv_i : v i = (M.mulVec (fun j => (x j : ℝ))) i + q * x i := by
      rw [hv_eq]
      simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    -- |v_i| ≥ q * |x_i| ≥ q
    have hvi_bound : |v i| ≥ q := by
      rw [hv_i]
      -- From sign property: (Mx)_i * x_i ≥ 0 means (Mx)_i and x_i have same sign
      -- So |(Mx)_i + q * x_i| ≥ q * |x_i|
      have hx_int : |(x i : ℝ)| ≥ 1 := by
        have hx_ne_int : x i ≠ 0 := by
          intro hcontra
          simp only [hcontra, Int.cast_zero] at hi_ne
          exact hi_ne rfl
        calc |(x i : ℝ)| = |x i| := by simp only [Int.cast_abs]
          _ ≥ 1 := by exact_mod_cast Int.one_le_abs hx_ne_int
      -- Case split on sign of x_i
      by_cases hx_pos : (x i : ℝ) > 0
      · -- x_i > 0, so (Mx)_i ≥ 0
        have hMx_nonneg : (M.mulVec (fun j => (x j : ℝ))) i ≥ 0 := by
          by_contra hMx_neg
          push_neg at hMx_neg
          have : (M.mulVec (fun j => (x j : ℝ))) i * x i < 0 := mul_neg_of_neg_of_pos hMx_neg hx_pos
          linarith
        have hx_ge_one : (x i : ℝ) ≥ 1 := by
          rw [abs_of_pos hx_pos] at hx_int
          exact hx_int
        calc |((M.mulVec fun j => ↑(x j)) i) + q * ↑(x i)|
            = (M.mulVec (fun j => (x j : ℝ))) i + q * x i := by
              rw [abs_of_nonneg]; nlinarith
          _ ≥ q * x i := by linarith
          _ ≥ q * 1 := by nlinarith
          _ = q := by ring
      · push_neg at hx_pos
        have hx_neg : (x i : ℝ) < 0 := by
          rcases ne_iff_lt_or_gt.mp hi_ne with h | h
          · exact h
          · linarith
        -- x_i < 0, so (Mx)_i ≤ 0
        have hMx_nonpos : (M.mulVec (fun j => (x j : ℝ))) i ≤ 0 := by
          by_contra hMx_pos
          push_neg at hMx_pos
          have : (M.mulVec (fun j => (x j : ℝ))) i * x i < 0 := mul_neg_of_pos_of_neg hMx_pos hx_neg
          linarith
        have hx_le_neg_one : (x i : ℝ) ≤ -1 := by
          rw [abs_of_neg hx_neg] at hx_int
          linarith
        calc |((M.mulVec fun j => ↑(x j)) i) + q * ↑(x i)|
            = -((M.mulVec (fun j => (x j : ℝ))) i + q * x i) := by
              rw [abs_of_neg]; nlinarith
          _ = -(M.mulVec (fun j => (x j : ℝ))) i - q * x i := by ring
          _ ≥ -q * x i := by linarith
          _ ≥ q * 1 := by nlinarith
          _ = q := by ring
    -- inftyNorm v ≥ |v i| ≥ q
    unfold Lattice.inftyNorm
    have h_le : |v i| ≤ Finset.sup' Finset.univ Finset.univ_nonempty (fun j => |v j|) :=
      Finset.le_sup' (fun j => |v j|) (Finset.mem_univ i)
    linarith
end GroupTheoreticShannonCapacity.P0Matrix
