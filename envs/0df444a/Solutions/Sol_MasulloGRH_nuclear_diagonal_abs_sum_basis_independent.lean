-- Prove2me | solution 1 for MasulloGRH.nuclear_diagonal_abs_sum_basis_independent
-- status  : ACCEPTED   (disprove)
-- author  : @marozols
-- created : 2026-11-21T00:52:09.410645+00:00
-- url     : https://prove2.me/submissions/29327d62-53c2-423c-8611-3890fa5f6bb6

import Definitions.Def_MasulloGRH_HilbertNuclear

set_option autoImplicit false

open MasulloGRH

theorem solution : ¬ (∀ (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) (hT : IsNuclearOperator T)
    (ι₁ ι₂ : Type) (b₁ : HilbertBasis ι₁ ℂ H) (b₂ : HilbertBasis ι₂ ℂ H),
    ∑' i, ‖inner ℂ (b₁ i) (T (b₁ i))‖ = ∑' j, ‖inner ℂ (b₂ j) (T (b₂ j))‖) := by
  intro h
  -- the standard orthonormal basis of `ℂ²`
  obtain ⟨e, he⟩ : ∃ e : OrthonormalBasis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2)),
      ∀ i j, inner ℂ (e i) (e j) = if i = j then (1 : ℂ) else 0 :=
    ⟨EuclideanSpace.basisFun (Fin 2) ℂ,
      orthonormal_iff_ite.1 (EuclideanSpace.basisFun (Fin 2) ℂ).orthonormal⟩
  have h00 : inner ℂ (e 0) (e 0) = (1 : ℂ) := by rw [he]; simp
  have h11 : inner ℂ (e 1) (e 1) = (1 : ℂ) := by rw [he]; simp
  have h01 : inner ℂ (e 0) (e 1) = (0 : ℂ) := by rw [he]; simp
  have h10 : inner ℂ (e 1) (e 0) = (0 : ℂ) := by rw [he]; simp
  -- the nilpotent rank-one operator `T u = ⟨u, e₀⟩ e₁`
  obtain ⟨T, hTapp⟩ : ∃ T : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2),
      ∀ u, T u = inner ℂ (e 0) u • e 1 :=
    ⟨(innerSL ℂ (e 0)).smulRight (e 1), fun u => rfl⟩
  have hT : IsNuclearOperator T := by
    refine ⟨fun m => if m = 0 then e 0 else 0, fun m => if m = 0 then e 1 else 0, ?_,
      fun u => ?_⟩
    · refine summable_of_ne_finset_zero (s := {0}) fun m hm => ?_
      have hm' : m ≠ 0 := by simpa using hm
      simp [hm']
    · rw [hTapp]
      have h1 := hasSum_ite_eq (0 : ℕ) (inner ℂ (e 0) u • e 1)
      have e1 : (fun m : ℕ => inner ℂ (if m = 0 then e 0 else 0) u • (if m = 0 then e 1 else 0)) =
          fun m : ℕ => if m = 0 then inner ℂ (e 0) u • e 1 else 0 := by
        funext m
        split_ifs <;> simp
      rw [e1]
      exact h1
  -- in the standard basis all diagonal entries vanish
  have hdiag : ∀ i, inner ℂ (e i) (T (e i)) = 0 := by
    intro i
    rw [hTapp, inner_smul_right]
    fin_cases i
    · simp [h01]
    · simp [h01]
  have hs1 : ∑' i, ‖inner ℂ (e.toHilbertBasis i) (T (e.toHilbertBasis i))‖ = 0 := by
    have : ∀ i, ‖inner ℂ (e.toHilbertBasis i) (T (e.toHilbertBasis i))‖ = 0 := by
      intro i
      rw [OrthonormalBasis.coe_toHilbertBasis, hdiag, norm_zero]
    rw [tsum_congr this, tsum_zero]
  -- the unit vector `v = (e₀ + e₁)/√2`
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := ⟨_, rfl⟩
  have hcc : c * c = 1 / 2 := by
    rw [hc, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hconj : (starRingEnd ℂ) c = c := by rw [hc, Complex.conj_ofReal]
  obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℂ (Fin 2), v = c • (e 0 + e 1) := ⟨_, rfl⟩
  have hvv : inner ℂ v v = (1 : ℂ) := by
    rw [hv, inner_smul_left, inner_smul_right, inner_add_left, inner_add_right, inner_add_right,
      h00, h01, h10, h11, hconj]
    have : c * (c * (1 + 0 + (0 + 1))) = c * c * 2 := by ring
    rw [this, hcc]
    norm_num
  have hTv : inner ℂ v (T v) = 1 / 2 := by
    rw [hTapp, inner_smul_right]
    have h1 : inner ℂ (e 0) v = c := by
      rw [hv, inner_smul_right, inner_add_right, h00, h01]
      ring
    have h2 : inner ℂ v (e 1) = c := by
      rw [hv, inner_smul_left, inner_add_left, h01, h11, hconj]
      ring
    rw [h1, h2, hcc]
  -- an orthonormal basis containing `v`
  have hon : Orthonormal ℂ ((↑) : ({v} : Set (EuclideanSpace ℂ (Fin 2))) → EuclideanSpace ℂ (Fin 2)) := by
    classical
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    have hi' : i = v := hi
    have hj' : j = v := hj
    rw [if_pos (Subtype.ext (hi'.trans hj'.symm))]
    change inner ℂ i j = 1
    rw [hi', hj']
    exact hvv
  obtain ⟨u, b, hvu, hb⟩ := hon.exists_orthonormalBasis_extension
  have hvmem : v ∈ u := hvu rfl
  have hs2 : (1 : ℝ) / 2 ≤ ∑' j, ‖inner ℂ (b.toHilbertBasis j) (T (b.toHilbertBasis j))‖ := by
    rw [tsum_fintype]
    have h1 := Finset.single_le_sum
      (f := fun j : u => ‖inner ℂ (b.toHilbertBasis j) (T (b.toHilbertBasis j))‖)
      (fun j _ => norm_nonneg _) (Finset.mem_univ (⟨v, hvmem⟩ : u))
    refine le_trans (le_of_eq ?_) h1
    change (1 : ℝ) / 2 = ‖inner ℂ (b.toHilbertBasis ⟨v, hvmem⟩) (T (b.toHilbertBasis ⟨v, hvmem⟩))‖
    rw [OrthonormalBasis.coe_toHilbertBasis, hb, hTv]
    norm_num
  have hfinal := h (EuclideanSpace ℂ (Fin 2)) T hT (Fin 2) u e.toHilbertBasis b.toHilbertBasis
  rw [hs1] at hfinal
  linarith
