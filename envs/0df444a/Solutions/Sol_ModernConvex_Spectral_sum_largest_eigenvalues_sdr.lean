-- Prove2me | solution 1 for ModernConvex.Spectral.sum_largest_eigenvalues_sdr
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:45:01.468175+00:00
-- url     : https://prove2.me/submissions/4f9c4c30-2537-4423-bbc5-6bc79c87fba5

import Mathlib
import Definitions.Def_ModernConvex_Spectral_SDR

open Matrix ModernConvex.Spectral

lemma g70mc1_qexp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type*}
    [Fintype ι] (b : OrthonormalBasis ι ℝ E) (T : E →ₗ[ℝ] E) (μ : ι → ℝ)
    (hb : ∀ j, T (b j) = μ j • b j) (x : E) :
    inner ℝ (T x) x = ∑ j, μ j * (inner ℝ (b j) x) ^ 2 := by
  have hx : T x = ∑ j, (μ j * inner ℝ (b j) x) • b j := by
    conv_lhs => rw [← b.sum_repr' x]
    simp only [map_sum, map_smul, hb, smul_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
  rw [hx, sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_smul_left]; ring

lemma g70mc1_nsq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type*}
    [Fintype ι] (b : OrthonormalBasis ι ℝ E) (x : E) :
    inner ℝ x x = ∑ j, (inner ℝ (b j) x) ^ 2 := by
  rw [← b.sum_inner_mul_inner x x]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_comm x (b j)]; ring

lemma g70mc1_weyl {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {N : ℕ} (hN : Module.finrank ℝ E = N) (T T' : E →ₗ[ℝ] E)
    (hT : T.IsSymmetric) (hT' : T'.IsSymmetric)
    (h : ∀ x, inner ℝ (T' x) x ≤ inner ℝ (T x) x) (i : Fin N) :
    hT'.eigenvalues hN i ≤ hT.eigenvalues hN i := by
  classical
  set b := hT.eigenvectorBasis hN
  set b' := hT'.eigenvectorBasis hN
  set μ := hT.eigenvalues hN
  set μ' := hT'.eigenvalues hN
  let L : E →ₗ[ℝ] ({j : Fin N // j ≠ i} → ℝ) :=
    LinearMap.pi (fun j => if (j : Fin N) < i then innerₛₗ ℝ (b j) else innerₛₗ ℝ (b' j))
  have hlt : Module.finrank ℝ ({j : Fin N // j ≠ i} → ℝ) < Module.finrank ℝ E := by
    rw [Module.finrank_fintype_fun_eq_card, hN, Fintype.card_subtype_compl, Fintype.card_fin,
      Fintype.card_unique]
    have := i.isLt; omega
  have hker := LinearMap.ker_ne_bot_of_finrank_lt hlt (f := L)
  obtain ⟨x, hxk, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  rw [LinearMap.mem_ker] at hxk
  have hc : ∀ j : Fin N, j < i → inner ℝ (b j) x = 0 := by
    intro j hj
    have := congrFun hxk ⟨j, ne_of_lt hj⟩
    simpa [L, hj] using this
  have hc' : ∀ j : Fin N, i < j → inner ℝ (b' j) x = 0 := by
    intro j hj
    have := congrFun hxk ⟨j, ne_of_gt hj⟩
    simpa [L, not_lt.2 hj.le] using this
  have hxx : 0 < inner ℝ x x := real_inner_self_pos.2 hx0
  have e1 := g70mc1_qexp b T μ (fun j => by
    rw [hT.apply_eigenvectorBasis hN j]; rfl) x
  have e2 := g70mc1_qexp b' T' μ' (fun j => by
    rw [hT'.apply_eigenvectorBasis hN j]; rfl) x
  have n1 := g70mc1_nsq b x
  have n2 := g70mc1_nsq b' x
  have hanti := hT.eigenvalues_antitone hN
  have hanti' := hT'.eigenvalues_antitone hN
  have up : inner ℝ (T x) x ≤ μ i * inner ℝ x x := by
    rw [e1, n1, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rcases lt_or_ge j i with hj | hj
    · rw [hc j hj]; simp
    · exact mul_le_mul_of_nonneg_right (hanti hj) (sq_nonneg _)
  have lo : μ' i * inner ℝ x x ≤ inner ℝ (T' x) x := by
    rw [e2, n2, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rcases lt_or_ge i j with hj | hj
    · rw [hc' j hj]; simp
    · exact mul_le_mul_of_nonneg_right (hanti' hj) (sq_nonneg _)
  have := (lo.trans (h x)).trans up
  exact le_of_mul_le_mul_right this hxx

lemma g70mc1_eigmono {m : ℕ} (X X' : Matrix (Fin m) (Fin m) ℝ) (hX : X.IsHermitian)
    (hX' : X'.IsHermitian) (h : (X - X').PosSemidef) :
    ∀ i : Fin m, eigVec X' i ≤ eigVec X i := by
  intro i
  unfold eigVec
  rw [dif_pos hX, dif_pos hX']
  unfold IsHermitian.eigenvalues₀
  apply g70mc1_weyl
  intro x
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  have := h.dotProduct_mulVec_nonneg (WithLp.ofLp x)
  simp only [star_trivial, sub_mulVec, dotProduct_sub] at this
  have e : ∀ Y : Matrix (Fin m) (Fin m) ℝ,
      WithLp.ofLp (Matrix.toEuclideanLin Y x) = Y *ᵥ WithLp.ofLp x := fun Y => rfl
  rw [e, e]; simp only [star_trivial]
  linarith

lemma g70mc1_inner_mat {m : ℕ} (Y : Matrix (Fin m) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (Matrix.toEuclideanLin Y x) x = WithLp.ofLp x ⬝ᵥ (Y *ᵥ WithLp.ofLp x) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  have e : WithLp.ofLp (Matrix.toEuclideanLin Y x) = Y *ᵥ WithLp.ofLp x := rfl
  rw [e, star_trivial]

lemma g70mc1_inner_vec {m : ℕ} (x y : EuclideanSpace ℝ (Fin m)) :
    inner ℝ x y = WithLp.ofLp x ⬝ᵥ WithLp.ofLp y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

lemma g70mc1_trace {m : ℕ} (Z : Matrix (Fin m) (Fin m) ℝ) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ (Fin m))) :
    Z.trace = ∑ i, inner ℝ (Matrix.toEuclideanLin Z (b i)) (b i) := by
  have h1 := LinearMap.trace_eq_sum_inner (Matrix.toEuclideanLin Z) b
  have h2 := LinearMap.trace_eq_sum_inner (Matrix.toEuclideanLin Z) (EuclideanSpace.basisFun (Fin m) ℝ)
  have h3 : ∑ i, inner ℝ (Matrix.toEuclideanLin Z (b i)) (b i) =
      ∑ i, inner ℝ (b i) (Matrix.toEuclideanLin Z (b i)) :=
    Finset.sum_congr rfl fun i _ => real_inner_comm _ _
  rw [h3, ← h1, h2]
  unfold Matrix.trace
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm, g70mc1_inner_mat]
  simp [EuclideanSpace.basisFun_apply, mulVec, dotProduct, Pi.single_apply]

/-- core statement over the eigenbasis indexing `Fin N` -/
lemma g70mc1_sdr_core {m N k : ℕ} (hNm : N = m) (hk : k ≤ m) (X : Matrix (Fin m) (Fin m) ℝ)
    (hN : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = N)
    (hT : (Matrix.toEuclideanLin X).IsSymmetric) (t : ℝ) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin N => (j : ℕ) < k), hT.eigenvalues hN j ≤ t ↔
      ∃ (s : ℝ) (Z : Matrix (Fin m) (Fin m) ℝ),
        0 ≤ t - (k : ℝ) * s - Z.trace ∧ Z.PosSemidef ∧
          (Z - X + s • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef := by
  classical
  set b := hT.eigenvectorBasis hN
  set μ := hT.eigenvalues hN
  set S := Finset.univ.filter (fun j : Fin N => (j : ℕ) < k)
  have hcard : S.card = k := by
    simp only [S]; rw [Fin.card_filter_val_lt]; omega
  have hb : ∀ j, Matrix.toEuclideanLin X (b j) = μ j • b j := by
    intro j; rw [hT.apply_eigenvectorBasis hN j]; rfl
  have hqX : ∀ x : EuclideanSpace ℝ (Fin m),
      WithLp.ofLp x ⬝ᵥ (X *ᵥ WithLp.ofLp x) = ∑ j, μ j * (inner ℝ (b j) x) ^ 2 := by
    intro x; rw [← g70mc1_inner_mat]; exact g70mc1_qexp b _ μ hb x
  have hnorm : ∀ x : EuclideanSpace ℝ (Fin m),
      WithLp.ofLp x ⬝ᵥ WithLp.ofLp x = ∑ j, (inner ℝ (b j) x) ^ 2 := by
    intro x; rw [← g70mc1_inner_vec]; exact g70mc1_nsq b x
  have hunit : ∀ j, WithLp.ofLp (b j) ⬝ᵥ WithLp.ofLp (b j) = 1 := by
    intro j; rw [← g70mc1_inner_vec, real_inner_self_eq_norm_sq, b.orthonormal.1 j]; norm_num
  have hanti := hT.eigenvalues_antitone hN
  constructor
  · intro hS
    by_cases hm : m = 0
    · subst hm
      have hN0 : N = 0 := hNm
      subst hN0
      refine ⟨0, 0, ?_, PosSemidef.zero, ?_⟩
      · simp only [S] at hS; simp at hS; simpa using hS
      · have : (0 - X + (0:ℝ) • (1 : Matrix (Fin 0) (Fin 0) ℝ)) = 0 := by ext i; exact i.elim0
        rw [this]; exact PosSemidef.zero
    have hNpos : 0 < N := by omega
    let j0 : Fin N := ⟨if k = 0 then 0 else k - 1, by split_ifs <;> omega⟩
    set s := μ j0
    have hsl : ∀ j ∈ S, s ≤ μ j := by
      intro j hj
      simp only [S, Finset.mem_filter] at hj
      apply hanti
      show (j : ℕ) ≤ (j0 : ℕ)
      simp only [j0]; split_ifs <;> omega
    have hsg : ∀ j ∉ S, μ j ≤ s := by
      intro j hj
      simp only [S, Finset.mem_filter, not_and, not_lt] at hj
      apply hanti
      show (j0 : ℕ) ≤ (j : ℕ)
      have := hj (Finset.mem_univ _)
      simp only [j0]; split_ifs <;> omega
    let Z : Matrix (Fin m) (Fin m) ℝ :=
      ∑ j ∈ S, (μ j - s) • vecMulVec (WithLp.ofLp (b j)) (WithLp.ofLp (b j))
    have hvm : ∀ (v y : Fin m → ℝ), y ⬝ᵥ (vecMulVec v v *ᵥ y) = (v ⬝ᵥ y) ^ 2 := by
      intro v y
      rw [vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, smul_eq_mul, dotProduct_comm y v, sq]
    have hqZ : ∀ x : EuclideanSpace ℝ (Fin m),
        WithLp.ofLp x ⬝ᵥ (Z *ᵥ WithLp.ofLp x) = ∑ j ∈ S, (μ j - s) * (inner ℝ (b j) x) ^ 2 := by
      intro x
      simp only [Z, sum_mulVec, dotProduct_sum, smul_mulVec, dotProduct_smul, smul_eq_mul, hvm,
        g70mc1_inner_vec]
    have hZh : Z.IsHermitian := by
      simp only [Z]
      unfold IsHermitian
      rw [conjTranspose_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [conjTranspose_smul, star_trivial, conjTranspose_eq_transpose_of_trivial,
        transpose_vecMulVec]
    have hX' : X.IsHermitian := Matrix.isSymmetric_toEuclideanLin_iff.1 hT
    refine ⟨s, Z, ?_, ?_, ?_⟩
    · have htr : Z.trace = ∑ j ∈ S, μ j - k * s := by
        simp only [Z, trace_sum, trace_smul, trace_vecMulVec, hunit, smul_eq_mul, mul_one,
          Finset.sum_sub_distrib, Finset.sum_const, hcard, nsmul_eq_mul]
      rw [htr]; linarith
    · refine PosSemidef.of_dotProduct_mulVec_nonneg hZh fun y => ?_
      rw [star_trivial]
      have := hqZ (WithLp.toLp 2 y)
      simp only at this
      rw [this]
      exact Finset.sum_nonneg fun j hj => mul_nonneg (by linarith [hsl j hj]) (sq_nonneg _)
    · refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun y => ?_
      · exact (hZh.sub hX').add (by
          unfold IsHermitian; rw [conjTranspose_smul, conjTranspose_one, star_trivial])
      rw [star_trivial]
      have h1 := hqZ (WithLp.toLp 2 y)
      have h2 := hqX (WithLp.toLp 2 y)
      have h3 := hnorm (WithLp.toLp 2 y)
      simp only at h1 h2 h3
      simp only [add_mulVec, sub_mulVec, dotProduct_add, dotProduct_sub, smul_mulVec, one_mulVec,
        dotProduct_smul, smul_eq_mul]
      rw [h1, h2, h3, Finset.mul_sum]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin N => (j : ℕ) < k)]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin N => (j : ℕ) < k)]
      have hA : ∑ j ∈ S, (μ j - s) * (inner ℝ (b j) (WithLp.toLp 2 y)) ^ 2
          - ∑ j ∈ S, μ j * (inner ℝ (b j) (WithLp.toLp 2 y)) ^ 2
          + ∑ j ∈ S, s * (inner ℝ (b j) (WithLp.toLp 2 y)) ^ 2 = 0 := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_eq_zero fun j _ => by ring
      have hB : 0 ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin N => ¬ (j : ℕ) < k),
          (s * (inner ℝ (b j) (WithLp.toLp 2 y)) ^ 2 - μ j * (inner ℝ (b j) (WithLp.toLp 2 y)) ^ 2) := by
        refine Finset.sum_nonneg fun j hj => ?_
        have : j ∉ S := by simp only [S, Finset.mem_filter] at hj ⊢; tauto
        nlinarith [hsg j this, sq_nonneg (inner ℝ (b j) (WithLp.toLp 2 y))]
      rw [Finset.sum_sub_distrib] at hB
      simp only [S] at hA
      linarith
  · rintro ⟨s, Z, hle, hZ, hW⟩
    have hj : ∀ j, μ j ≤ inner ℝ (Matrix.toEuclideanLin Z (b j)) (b j) + s := by
      intro j
      have := hW.dotProduct_mulVec_nonneg (WithLp.ofLp (b j))
      rw [star_trivial] at this
      simp only [add_mulVec, sub_mulVec, dotProduct_add, dotProduct_sub, smul_mulVec, one_mulVec,
        dotProduct_smul, smul_eq_mul, hunit] at this
      have e1 : WithLp.ofLp (b j) ⬝ᵥ (X *ᵥ WithLp.ofLp (b j)) = μ j := by
        rw [← g70mc1_inner_mat, hb, real_inner_smul_left, real_inner_self_eq_norm_sq,
          b.orthonormal.1 j]; ring
      rw [g70mc1_inner_mat]; linarith
    have hnn : ∀ j, 0 ≤ inner ℝ (Matrix.toEuclideanLin Z (b j)) (b j) := by
      intro j; rw [g70mc1_inner_mat]
      have := hZ.dotProduct_mulVec_nonneg (WithLp.ofLp (b j)); rwa [star_trivial] at this
    have h1 : ∑ j ∈ S, μ j ≤ ∑ j ∈ S, inner ℝ (Matrix.toEuclideanLin Z (b j)) (b j) + k * s := by
      have := Finset.sum_le_sum fun j (_ : j ∈ S) => hj j
      rw [Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul] at this
      exact this
    have h2 : ∑ j ∈ S, inner ℝ (Matrix.toEuclideanLin Z (b j)) (b j) ≤ Z.trace := by
      rw [g70mc1_trace Z b]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => hnn j
    linarith

theorem g70mc1_sdr {m k : ℕ} (hk : k ≤ m) (X : Matrix (Fin m) (Fin m) ℝ)
    (hX : X.IsHermitian) (t : ℝ) :
    sumLargestEig k X ≤ t ↔
      ∃ (s : ℝ) (Z : Matrix (Fin m) (Fin m) ℝ),
        0 ≤ t - (k : ℝ) * s - Z.trace ∧ Z.PosSemidef ∧ (Z - X + s • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef := by
  rw [← g70mc1_sdr_core (Fintype.card_fin m) hk X finrank_euclideanSpace
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hX) t]
  unfold sumLargestEig partialSum eigVec
  rw [dif_pos hX]
  unfold IsHermitian.eigenvalues₀
  have h := (Fintype.card_fin m)
  apply le_iff_le_of_cmp_eq_cmp
  congr 1
  refine Finset.sum_nbij' (fun i => Fin.cast h.symm i) (fun j => Fin.cast h j) ?_ ?_ ?_ ?_ ?_
  · intro i hi; simpa using hi
  · intro j hj; simpa using hj
  · intro i _; rfl
  · intro j _; rfl
  · intro i _; rfl

theorem solution {m k : ℕ} (hk : k ≤ m) (X : Matrix (Fin m) (Fin m) ℝ)
    (hX : X.IsHermitian) (t : ℝ) :
    sumLargestEig k X ≤ t ↔
      ∃ (s : ℝ) (Z : Matrix (Fin m) (Fin m) ℝ),
        0 ≤ t - (k : ℝ) * s - Z.trace ∧ Z.PosSemidef ∧ (Z - X + s • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef := by
  exact g70mc1_sdr hk X hX t

