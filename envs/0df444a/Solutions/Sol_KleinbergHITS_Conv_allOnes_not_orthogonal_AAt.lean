-- Prove2me | solution 1 for KleinbergHITS.Conv.allOnes_not_orthogonal_AAt
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:18:56.248587+00:00
-- url     : https://prove2.me/submissions/7d4facaf-1272-4b5b-9792-0fa7b3d772b4

import Mathlib
import Definitions.Def_KleinbergHITS_Conv_Setting
set_option autoImplicit false
open Matrix KleinbergHITS.Conv

theorem VV_key {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosSemidef)
    (hnn : ∀ i j, 0 ≤ M i j) (l : ℝ) (hl : IsPrincipalEigenvalue M l) (hl0 : l ≠ 0)
    (ω : Fin n → ℝ) (hω : M *ᵥ ω = l • ω) (hω1 : ∑ i, ω i ^ 2 = 1) :
    ∑ i, ω i ≠ 0 := by
  obtain ⟨hev, hdim, hmax⟩ := hl
  -- eigenvalues of M are nonnegative
  have hnonneg : ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' M) μ → 0 ≤ μ := by
    intro μ hμ
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    have hMv : M *ᵥ v = μ • v := by
      have := hv.apply_eq_smul
      simpa [Matrix.toLin'_apply] using this
    have hvne : v ≠ 0 := hv.2
    have hpos : 0 < ∑ i, v i ^ 2 := by
      by_contra hcon
      push_neg at hcon
      apply hvne
      funext i
      have h0 : ∑ i, v i ^ 2 = 0 := le_antisymm hcon (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg (v _))).1 h0 i (Finset.mem_univ i)
      simpa using this
    have h1 := hM.dotProduct_mulVec_nonneg v
    rw [hMv] at h1
    simp only [star_trivial, dotProduct, Pi.smul_apply, smul_eq_mul] at h1
    have : ∑ i, v i * (μ * v i) = μ * ∑ i, v i ^ 2 := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [this] at h1
    exact nonneg_of_mul_nonneg_left h1 hpos
  have hlpos : 0 < l := lt_of_le_of_ne (hnonneg l hev) (Ne.symm hl0)
  have hle : ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' M) μ → μ ≤ l := by
    intro μ hμ
    by_cases h : μ = l
    · exact h.le
    · have := hmax μ hμ h
      rw [abs_of_nonneg (hnonneg μ hμ), abs_of_pos hlpos] at this
      exact this.le
  -- B = l I - M is positive semidefinite
  set B : Matrix (Fin n) (Fin n) ℝ := l • (1 : Matrix (Fin n) (Fin n) ℝ) - M with hB
  have hBherm : B.IsHermitian := by
    have h := hM.1
    unfold Matrix.IsHermitian at h ⊢
    rw [hB, conjTranspose_sub, conjTranspose_smul, conjTranspose_one, h]
    simp
  have hBpsd : B.PosSemidef := by
    rw [hBherm.posSemidef_iff_eigenvalues_nonneg]
    intro i
    show 0 ≤ hBherm.eigenvalues i
    set v : Fin n → ℝ := ⇑(hBherm.eigenvectorBasis i) with hv
    have hBv : B *ᵥ v = hBherm.eigenvalues i • v := hBherm.mulVec_eigenvectorBasis i
    have hMv : M *ᵥ v = (l - hBherm.eigenvalues i) • v := by
      have : B *ᵥ v = l • v - M *ᵥ v := by
        rw [hB, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
      rw [this] at hBv
      rw [sub_smul]
      rw [← hBv]; abel
    have hvne : v ≠ 0 := by
      intro h0
      have h1 := (hBherm.eigenvectorBasis).orthonormal.1 i
      have : (hBherm.eigenvectorBasis i) = 0 := by
        ext j
        exact congrFun h0 j
      rw [this] at h1
      simp at h1
    have hev2 : Module.End.HasEigenvalue (Matrix.toLin' M) (l - hBherm.eigenvalues i) := by
      apply Module.End.hasEigenvalue_of_hasEigenvector (x := v)
      refine ⟨?_, hvne⟩
      rw [Module.End.mem_eigenspace_iff]
      simpa [Matrix.toLin'_apply] using hMv
    have := hle _ hev2
    linarith
  -- u = |ω|
  set u : Fin n → ℝ := fun i => |ω i| with hu
  have hωMω : ω ⬝ᵥ (M *ᵥ ω) = l := by
    rw [hω]
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
    have : ∑ i, ω i * (l * ω i) = l * ∑ i, ω i ^ 2 := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [this, hω1, mul_one]
  have huu : ∑ i, u i ^ 2 = 1 := by
    rw [← hω1]; apply Finset.sum_congr rfl; intro i _; simp [hu, sq_abs]
  have hMu_ge : l ≤ u ⬝ᵥ (M *ᵥ u) := by
    rw [← hωMω]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    have h1 : ω i * ω j ≤ |ω i| * |ω j| := by
      rw [← abs_mul]; exact le_abs_self _
    calc ω i * (M i j * ω j) = M i j * (ω i * ω j) := by ring
      _ ≤ M i j * (|ω i| * |ω j|) := mul_le_mul_of_nonneg_left h1 (hnn i j)
      _ = u i * (M i j * u j) := by simp only [hu]; ring
  have huB : star u ⬝ᵥ (B *ᵥ u) = 0 := by
    apply le_antisymm
    · have : star u ⬝ᵥ (B *ᵥ u) = l * ∑ i, u i ^ 2 - u ⬝ᵥ (M *ᵥ u) := by
        rw [hB, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
        simp only [star_trivial, dotProduct_sub, dotProduct_smul, smul_eq_mul]
        have : u ⬝ᵥ u = ∑ i, u i ^ 2 := by simp [dotProduct, sq]
        rw [this]
      rw [this, huu]; linarith
    · exact hBpsd.dotProduct_mulVec_nonneg u
  have hBu : B *ᵥ u = 0 := (hBpsd.dotProduct_mulVec_zero_iff u).1 huB
  have hMu : M *ᵥ u = l • u := by
    have : B *ᵥ u = l • u - M *ᵥ u := by
      rw [hB, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [this] at hBu
    exact (sub_eq_zero.1 hBu).symm
  -- eigenspace is one-dimensional
  have hωne : ω ≠ 0 := by
    intro h0
    rw [h0] at hω1
    simp at hω1
  have hmemω : ω ∈ Module.End.eigenspace (Matrix.toLin' M) l := by
    rw [Module.End.mem_eigenspace_iff]; simpa [Matrix.toLin'_apply] using hω
  have hmemu : u ∈ Module.End.eigenspace (Matrix.toLin' M) l := by
    rw [Module.End.mem_eigenspace_iff]; simpa [Matrix.toLin'_apply] using hMu
  have hnz : (⟨ω, hmemω⟩ : Module.End.eigenspace (Matrix.toLin' M) l) ≠ 0 := by
    intro h0
    apply hωne
    exact congrArg Subtype.val h0
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hnz).1 hdim ⟨u, hmemu⟩
  have hcu : ∀ i, |ω i| = c * ω i := by
    intro i
    have := congrArg (fun w : Module.End.eigenspace (Matrix.toLin' M) l => (w : Fin n → ℝ) i) hc
    simpa [hu] using this.symm
  have hc2 : c ^ 2 = 1 := by
    have : ∑ i, u i ^ 2 = c ^ 2 * ∑ i, ω i ^ 2 := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
      show |ω i| ^ 2 = c ^ 2 * ω i ^ 2
      rw [hcu i]; ring
    rw [huu, hω1] at this; linarith
  have hex : ∃ i, ω i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    simp [hcon] at hω1
  obtain ⟨i0, hi0⟩ := hex
  have hpos : 0 < ∑ i, |ω i| :=
    Finset.sum_pos' (fun i _ => abs_nonneg _) ⟨i0, Finset.mem_univ _, abs_pos.2 hi0⟩
  have hc' : c = 1 ∨ c = -1 := by
    have : (c - 1) * (c + 1) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  rcases hc' with h | h
  · have : ∑ i, ω i = ∑ i, |ω i| := by
      apply Finset.sum_congr rfl; intro i _; rw [hcu i, h]; ring
    rw [this]; exact hpos.ne'
  · have : ∑ i, ω i = -∑ i, |ω i| := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro i _; rw [hcu i, h]; ring
    rw [this]; exact neg_ne_zero.2 hpos.ne'

theorem solution {n : ℕ} (E : Fin n → Fin n → Prop) [DecidableRel E]
    (hAAt : Dagger (adjMatrix E * (adjMatrix E)ᵀ)) :
    ∀ ω, IsPrincipalEigenvector (adjMatrix E * (adjMatrix E)ᵀ) ω → allOnes n ⬝ᵥ ω ≠ 0 := by
  intro ω ⟨l, hl, hω, hω1⟩
  obtain ⟨l', hl', hl'0⟩ := hAAt
  have hl0 : l ≠ 0 := by
    intro h0
    have h1 := hl.2.2 l' hl'.1 (by rw [h0]; exact hl'0)
    rw [h0] at h1
    simp at h1
    exact absurd h1 (not_lt.2 (abs_nonneg _))
  have hpsd : ((adjMatrix E) * (adjMatrix E)ᵀ).PosSemidef := by
    have := Matrix.posSemidef_self_mul_conjTranspose (adjMatrix E)
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hnn : ∀ i j, 0 ≤ ((adjMatrix E) * (adjMatrix E)ᵀ) i j := by
    intro i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, adjMatrix]
    apply Finset.sum_nonneg
    intro k _
    split_ifs <;> norm_num
  have := VV_key _ hpsd hnn l hl hl0 ω hω hω1
  simpa [dotProduct, allOnes] using this
