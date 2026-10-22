-- Prove2me | solution 1 for LenstraIP.Hyperplanes.few_hyperplanes_meet_ball
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T00:41:08.142317+00:00
-- url     : https://prove2.me/submissions/c0ee4b35-8fa8-440c-b0e4-32efebcfe627

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice
import Definitions.Def_LenstraIP_Hyperplanes_LatticeData

set_option autoImplicit false

open KannanLattice.Core
open InnerProductSpace

namespace LenstraFewHyp

/-- Nearest-plane covering bound: every point of the real span of `b₁, …, b_m` is within
`√(Σ |bᵢ|²) / 2` of an integer combination of the `bᵢ`. -/
theorem cover {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    ∀ (m : ℕ) (b : Fin m → E) (x : E), x ∈ Submodule.span ℝ (Set.range b) →
      ∃ y ∈ Submodule.span ℤ (Set.range b), ‖x - y‖ ^ 2 ≤ (∑ i, ‖b i‖ ^ 2) / 4 := by
  intro m
  induction m with
  | zero =>
    intro b x hx
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    have : Set.range b = ∅ := Set.range_eq_empty b
    rw [this, Submodule.span_empty, Submodule.mem_bot] at hx
    simp [hx]
  | succ m ih =>
    intro b x hx
    let b' : Fin m → E := b ∘ Fin.castSucc
    let K : Submodule ℝ E := Submodule.span ℝ (Set.range b')
    have : FiniteDimensional ℝ K := FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hx
    obtain ⟨w, hwK, v, hvK, hbl⟩ := K.exists_add_mem_mem_orthogonal (b (Fin.last m))
    have hx0 : (∑ i : Fin m, c (Fin.castSucc i) • b' i) ∈ K :=
      Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    have hxK : (∑ i : Fin m, c (Fin.castSucc i) • b' i)
        + (c (Fin.last m) - (round (c (Fin.last m)) : ℝ)) • w ∈ K :=
      K.add_mem hx0 (K.smul_mem _ hwK)
    obtain ⟨y', hy', hdist⟩ := ih b' _ hxK
    refine ⟨y' + round (c (Fin.last m)) • b (Fin.last m), ?_, ?_⟩
    · refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
      exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨_, rfl⟩) hy'
    · have hy'K : y' ∈ K := Submodule.span_subset_span ℤ ℝ _ hy'
      have hvK' : (c (Fin.last m) - (round (c (Fin.last m)) : ℝ)) • v ∈ Kᗮ :=
        Kᗮ.smul_mem _ hvK
      have horth : inner ℝ ((∑ i : Fin m, c (Fin.castSucc i) • b' i)
          + (c (Fin.last m) - (round (c (Fin.last m)) : ℝ)) • w - y')
          ((c (Fin.last m) - (round (c (Fin.last m)) : ℝ)) • v) = 0 :=
        K.inner_right_of_mem_orthogonal (K.sub_mem hxK hy'K) hvK'
      have hvb : ‖v‖ ^ 2 ≤ ‖b (Fin.last m)‖ ^ 2 := by
        have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero w v
          (K.inner_right_of_mem_orthogonal hwK hvK)
        rw [hbl]
        nlinarith [sq_nonneg ‖w‖, sq_nonneg ‖v‖, sq_nonneg ‖w + v‖]
      have hround : |c (Fin.last m) - (round (c (Fin.last m)) : ℝ)| ≤ 1 / 2 :=
        abs_sub_round _
      have heq : ∑ i, c i • b i - (y' + round (c (Fin.last m)) • b (Fin.last m))
          = ((∑ i : Fin m, c (Fin.castSucc i) • b' i)
            + (c (Fin.last m) - (round (c (Fin.last m)) : ℝ)) • w - y')
            + (c (Fin.last m) - (round (c (Fin.last m)) : ℝ)) • v := by
        rw [← Int.cast_smul_eq_zsmul ℝ, Fin.sum_univ_castSucc, hbl]
        simp only [b', Function.comp_apply]
        module
      have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
      rw [← sq, ← sq, ← sq] at hp
      rw [heq, hp, norm_smul, mul_pow, Real.norm_eq_abs, Fin.sum_univ_castSucc]
      have h1 : |c (Fin.last m) - (round (c (Fin.last m)) : ℝ)| ^ 2 ≤ 1 / 4 := by
        nlinarith [abs_nonneg (c (Fin.last m) - (round (c (Fin.last m)) : ℝ))]
      have hs : ∑ i : Fin m, ‖b (Fin.castSucc i)‖ ^ 2 = ∑ i, ‖b' i‖ ^ 2 := rfl
      rw [hs]
      have hv0 : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
      nlinarith [mul_le_mul h1 hvb hv0 (by norm_num)]

/-- Counting integers `j` with `|j s - a| ≤ R`. -/
theorem count (s a R : ℝ) (hs : 0 < |s|) (hR : 0 ≤ R) (S : Set ℤ)
    (hS : ∀ j ∈ S, |(j : ℝ) * s - a| ≤ R) :
    S.Finite ∧ (S.ncard : ℝ) - 1 ≤ 2 * R / |s| := by
  have hs0 : s ≠ 0 := abs_pos.1 hs
  have key : ∀ j ∈ S, |(j : ℝ) - a / s| ≤ R / |s| := by
    intro j hj
    rw [le_div_iff₀ hs, ← abs_mul, sub_mul, div_mul_cancel₀ _ hs0]
    exact hS j hj
  have hsub : S ⊆ ↑(Finset.Icc ⌈a / s - R / |s|⌉ ⌊a / s + R / |s|⌋) := by
    intro j hj
    have := abs_le.1 (key j hj)
    simp only [Finset.coe_Icc, Set.mem_Icc]
    exact ⟨Int.ceil_le.2 (by linarith), Int.le_floor.2 (by linarith)⟩
  refine ⟨(Finset.finite_toSet _).subset hsub, ?_⟩
  rcases S.eq_empty_or_nonempty with h | ⟨j, hj⟩
  · subst h
    simp only [Set.ncard_empty, Nat.cast_zero, zero_sub]
    have : 0 ≤ 2 * R / |s| := by positivity
    linarith
  · have hc := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset, Int.card_Icc] at hc
    have hj' := hsub hj
    simp only [Finset.coe_Icc, Set.mem_Icc] at hj'
    have hc' : (S.ncard : ℤ) ≤ ⌊a / s + R / |s|⌋ + 1 - ⌈a / s - R / |s|⌉ := by omega
    have hcR : (S.ncard : ℝ) ≤ (⌊a / s + R / |s|⌋ : ℝ) + 1 - (⌈a / s - R / |s|⌉ : ℝ) := by
      exact_mod_cast hc'
    have h1 : ((⌊a / s + R / |s|⌋ : ℤ) : ℝ) ≤ a / s + R / |s| := Int.floor_le _
    have h2 : a / s - R / |s| ≤ ((⌈a / s - R / |s|⌉ : ℤ) : ℝ) := Int.le_ceil _
    have : 2 * R / |s| = R / |s| + R / |s| := by ring
    linarith

end LenstraFewHyp

open KannanLattice.Core LenstraIP.Hyperplanes in
theorem solution (k : ℕ) (b : Fin (k + 1) → EuclideanSpace ℝ (Fin (k + 1)))
    (hb : LinearIndependent ℝ b) (c₁ c₂ : ℝ) (h7 : ∏ i, ‖b i‖ ≤ c₂ * latDet b)
    (hmax : ∀ i, ‖b i‖ ≤ ‖b (Fin.last k)‖)
    (X : Set (EuclideanSpace ℝ (Fin (k + 1)))) (p : EuclideanSpace ℝ (Fin (k + 1))) (r R : ℝ)
    (hr : 0 < r) (h3l : Metric.closedBall p r ⊆ X) (h3r : X ⊆ Metric.closedBall p R)
    (h4 : R / r ≤ c₁) :
    (∃ y ∈ lattice b, y ∈ X) ∨
      ((hitIndices b p R).Finite ∧
        ((hitIndices b p R).ncard : ℝ) - 1 < c₁ * c₂ * Real.sqrt ((k : ℝ) + 1)) := by
  classical
  by_cases hL : ∃ y ∈ lattice b, y ∈ X
  · exact Or.inl hL
  right
  have hne : ∀ i, b i ≠ 0 := fun i => hb.ne_zero i
  have hbn : 0 < ‖b (Fin.last k)‖ := norm_pos_iff.2 (hne _)
  -- r ≤ R
  have hrR : r ≤ R := by
    have hpt : p + (r / ‖b (Fin.last k)‖) • b (Fin.last k) ∈ Metric.closedBall p r := by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (div_pos hr hbn), div_mul_cancel₀ _ hbn.ne']
    have hx := h3r (h3l hpt)
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hr hbn), div_mul_cancel₀ _ hbn.ne'] at hx
    exact hx
  have hRc : R ≤ c₁ * r := (div_le_iff₀ hr).1 h4
  have hc₁ : 0 < c₁ := by
    by_contra h
    push Not at h
    nlinarith
  -- covering radius: no lattice point in B(p, r) forces 2r < √n |bₙ|
  have hspan : Submodule.span ℝ (Set.range b) = ⊤ :=
    hb.span_eq_top_of_card_eq_finrank' (by simp)
  obtain ⟨y, hy, hyd⟩ := LenstraFewHyp.cover (k + 1) b p (by rw [hspan]; trivial)
  have hfar : r < ‖p - y‖ := by
    by_contra h
    push Not at h
    exact hL ⟨y, hy, h3l (by rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]; exact h)⟩
  have hsumle : (∑ i, ‖b i‖ ^ 2) ≤ ((k : ℝ) + 1) * ‖b (Fin.last k)‖ ^ 2 := by
    calc (∑ i, ‖b i‖ ^ 2) ≤ ∑ _i : Fin (k + 1), ‖b (Fin.last k)‖ ^ 2 :=
          Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hmax i) 2)
      _ = ((k : ℝ) + 1) * ‖b (Fin.last k)‖ ^ 2 := by simp
  have h2r : 2 * r < Real.sqrt ((k : ℝ) + 1) * ‖b (Fin.last k)‖ := by
    have hrr : r ^ 2 < ‖p - y‖ ^ 2 := pow_lt_pow_left₀ hfar hr.le two_ne_zero
    have hsq : (2 * r) ^ 2 < ((k : ℝ) + 1) * ‖b (Fin.last k)‖ ^ 2 := by nlinarith
    rw [← Real.sqrt_sq hbn.le, ← Real.sqrt_mul (by positivity)]
    exact (Real.lt_sqrt (by positivity)).2 hsq
  -- Hadamard-type bound through the Gram-Schmidt orthonormal basis
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin (k + 1))) = Fintype.card (Fin (k + 1)) :=
    finrank_euclideanSpace
  let e := gramSchmidtOrthonormalBasis hdim b
  have hdetE : e.toBasis.det b = ∏ i, inner ℝ (e i) (b i) := gramSchmidtOrthonormalBasis_det hdim b
  let B := basisOfLinearIndependentOfCardEqFinrank hb hdim.symm
  have hB : ⇑B = b := coe_basisOfLinearIndependentOfCardEqFinrank hb hdim.symm
  have hlat : latDet b = |e.toBasis.det b| := by
    have h1 : (EuclideanSpace.basisFun (Fin (k + 1)) ℝ).toBasis.det b
        = Matrix.det (Matrix.of fun i j => b j i) := by
      rw [Module.Basis.det_apply]
      congr 1
    have h2 := Module.Basis.det_mul_det (EuclideanSpace.basisFun (Fin (k + 1)) ℝ).toBasis e.toBasis B
    rw [hB] at h2
    unfold latDet
    rw [← h1, ← h2, abs_mul]
    rcases (EuclideanSpace.basisFun (Fin (k + 1)) ℝ).det_to_matrix_orthonormalBasis_real e with
      h | h
    · rw [OrthonormalBasis.coe_toBasis, h]; simp
    · rw [OrthonormalBasis.coe_toBasis, h]; simp
  have horth : ∀ i : Fin k, inner ℝ (e (Fin.last k)) (b (Fin.castSucc i)) = 0 :=
    fun i => gramSchmidtOrthonormalBasis_inv_triangular hdim b (Fin.castSucc_lt_last i)
  have hunorm : ‖e (Fin.last k)‖ = 1 := e.orthonormal.1 _
  have hP' : 0 < ∏ i : Fin k, ‖b (Fin.castSucc i)‖ :=
    Finset.prod_pos (fun i _ => norm_pos_iff.2 (hne _))
  have hlatle : latDet b ≤ (∏ i : Fin k, ‖b (Fin.castSucc i)‖)
      * |inner ℝ (e (Fin.last k)) (b (Fin.last k))| := by
    rw [hlat, hdetE, Fin.prod_univ_castSucc, abs_mul, Finset.abs_prod]
    refine mul_le_mul_of_nonneg_right (Finset.prod_le_prod (fun i _ => abs_nonneg _) ?_)
      (abs_nonneg _)
    intro i _
    calc |inner ℝ (e (Fin.castSucc i)) (b (Fin.castSucc i))|
        ≤ ‖e (Fin.castSucc i)‖ * ‖b (Fin.castSucc i)‖ := abs_real_inner_le_norm _ _
      _ = ‖b (Fin.castSucc i)‖ := by rw [e.orthonormal.1, one_mul]
  have hprod : ∏ i, ‖b i‖ = (∏ i : Fin k, ‖b (Fin.castSucc i)‖) * ‖b (Fin.last k)‖ :=
    Fin.prod_univ_castSucc _
  have hlat0 : 0 ≤ latDet b := abs_nonneg _
  have hc₂ : 0 < c₂ := by
    by_contra h
    push Not at h
    have := mul_nonpos_of_nonpos_of_nonneg h hlat0
    nlinarith [mul_pos hP' hbn]
  have hbs : ‖b (Fin.last k)‖ ≤ c₂ * |inner ℝ (e (Fin.last k)) (b (Fin.last k))| := by
    have h' := mul_le_mul_of_nonneg_left hlatle hc₂.le
    have : (∏ i : Fin k, ‖b (Fin.castSucc i)‖) * ‖b (Fin.last k)‖
        ≤ (∏ i : Fin k, ‖b (Fin.castSucc i)‖)
          * (c₂ * |inner ℝ (e (Fin.last k)) (b (Fin.last k))|) := by nlinarith
    exact le_of_mul_le_mul_left this hP'
  have hs : 0 < |inner ℝ (e (Fin.last k)) (b (Fin.last k))| := by
    by_contra h
    push Not at h
    nlinarith [abs_nonneg (inner ℝ (e (Fin.last k)) (b (Fin.last k)))]
  -- every hit index satisfies |j s - ⟪u, p⟫| ≤ R
  have hmem : ∀ j ∈ hitIndices b p R,
      |(j : ℝ) * inner ℝ (e (Fin.last k)) (b (Fin.last k)) - inner ℝ (e (Fin.last k)) p| ≤ R := by
    intro j hj
    obtain ⟨x, hx, hxH⟩ := hj
    have h0 : inner ℝ (e (Fin.last k)) (x - (j : ℝ) • b (Fin.last k)) = 0 := by
      unfold hyperplane at hxH
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hxH
      rw [← hc, inner_sum]
      simp [inner_smul_right, horth]
    rw [inner_sub_right, inner_smul_right] at h0
    have : (j : ℝ) * inner ℝ (e (Fin.last k)) (b (Fin.last k)) - inner ℝ (e (Fin.last k)) p
        = inner ℝ (e (Fin.last k)) (x - p) := by
      rw [inner_sub_right]
      linarith
    rw [this]
    calc |inner ℝ (e (Fin.last k)) (x - p)| ≤ ‖e (Fin.last k)‖ * ‖x - p‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ R := by
          rw [hunorm, one_mul, ← dist_eq_norm]
          exact hx
  obtain ⟨hfin, hcnt⟩ := LenstraFewHyp.count _ _ R hs (le_trans hr.le hrR) _ hmem
  refine ⟨hfin, lt_of_le_of_lt hcnt ?_⟩
  rw [div_lt_iff₀ hs]
  have hsq0 : 0 ≤ Real.sqrt ((k : ℝ) + 1) := Real.sqrt_nonneg _
  calc 2 * R ≤ c₁ * (2 * r) := by nlinarith
    _ < c₁ * (Real.sqrt ((k : ℝ) + 1) * ‖b (Fin.last k)‖) := mul_lt_mul_of_pos_left h2r hc₁
    _ ≤ c₁ * (Real.sqrt ((k : ℝ) + 1)
          * (c₂ * |inner ℝ (e (Fin.last k)) (b (Fin.last k))|)) := by gcongr
    _ = c₁ * c₂ * Real.sqrt ((k : ℝ) + 1) * |inner ℝ (e (Fin.last k)) (b (Fin.last k))| := by
          ring
