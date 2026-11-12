-- Prove2me | solution 1 for LowRankDenoise432.OptimalProjector.theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:34:06.230876+00:00
-- url     : https://prove2.me/submissions/f81b22ee-7861-4e14-bfee-27bb6ef402c5

import Mathlib
import Definitions.Def_LowRankDenoise432_OptimalProjector_Model
import Theorems.Thm_Matrix_IsHermitian_sorted_eigenvalues_le_add_of_re_dotProduct_le
import Theorems.Thm_LowRankDenoise432_OptimalProjector_lemma_3_2

section
set_option autoImplicit false

open Matrix LowRankDenoise432.OptimalProjector

namespace LowRankDenoise432.Dev.Lin

theorem PP_exists {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) :
    ∃ (U : Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ),
      U * Uᵀ = 1 ∧ Uᵀ * U = 1 ∧ A = U * diagonal lam * Uᵀ ∧
      ∀ (M : Type) [AddCommMonoid M] (g : ℝ → M), ∑ i, g (lam i) = ∑ j, g (hA.eigenvalues₀ j) := by
  refine ⟨((hA.eigenvectorUnitary : Matrix.unitaryGroup (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ),
    hA.eigenvalues, ?_, ?_, ?_, ?_⟩
  · have := (hA.eigenvectorUnitary).2.2
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  · have := (hA.eigenvectorUnitary).2.1
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  · have h := hA.spectral_theorem
    conv_lhs => rw [h]
    simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  · intro M _ g
    unfold Matrix.IsHermitian.eigenvalues
    exact Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
      (fun j => g (hA.eigenvalues₀ j))


/-- the diagonal indicator -/
noncomputable def PP_ind {d : ℕ} (lam : Fin d → ℝ) : Fin d → ℝ := fun i => if 0 < lam i then 1 else 0

theorem PP_P_fix {d : ℕ} {A U : Matrix (Fin d) (Fin d) ℝ} {lam : Fin d → ℝ}
    (hU1 : U * Uᵀ = 1) (hU2 : Uᵀ * U = 1) (hAU : A = U * diagonal lam * Uᵀ)
    {w : Fin d → ℝ} {μ : ℝ} (hμ : 0 < μ) (hw : A *ᵥ w = μ • w) :
    (U * diagonal (PP_ind lam) * Uᵀ) *ᵥ w = w := by
  have hUU : ∀ x, Uᵀ *ᵥ (U *ᵥ x) = x := fun x => by rw [mulVec_mulVec, hU2, one_mulVec]
  have hUU' : ∀ x, U *ᵥ (Uᵀ *ᵥ x) = x := fun x => by rw [mulVec_mulVec, hU1, one_mulVec]
  set c := Uᵀ *ᵥ w with hc
  have h1 : diagonal lam *ᵥ c = μ • c := by
    have h0 : Uᵀ *ᵥ (A *ᵥ w) = Uᵀ *ᵥ (μ • w) := by rw [hw]
    have h3 : Uᵀ *ᵥ (A *ᵥ w) = diagonal lam *ᵥ c := by
      rw [hAU]
      simp only [← mulVec_mulVec]
      rw [hUU]
    rw [← h3, h0, mulVec_smul]
  have h2 : diagonal (PP_ind lam) *ᵥ c = c := by
    ext i
    have := congrFun h1 i
    simp only [mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at this ⊢
    unfold PP_ind
    split_ifs with h
    · simp
    · have : c i = 0 := by
        have h3 : (lam i - μ) * c i = 0 := by linarith
        rcases mul_eq_zero.mp h3 with h4 | h4
        · exfalso; push Not at h; linarith
        · exact h4
      simp [this]
  simp only [← mulVec_mulVec]
  rw [← hc, h2, hc, hUU']


theorem PP_posProj_eq {d : ℕ} {A U : Matrix (Fin d) (Fin d) ℝ} {lam : Fin d → ℝ}
    (hU1 : U * Uᵀ = 1) (hU2 : Uᵀ * U = 1) (hAU : A = U * diagonal lam * Uᵀ) :
    posProj A = U * diagonal (PP_ind lam) * Uᵀ := by
  set P := U * diagonal (PP_ind lam) * Uᵀ with hP
  have hPt : Pᵀ = P := by
    simp [hP, transpose_mul, Matrix.mul_assoc]
  have hin : ∀ a b : EuclideanSpace ℝ (Fin d), inner ℝ a b = WithLp.ofLp a ⬝ᵥ WithLp.ofLp b := by
    intro a b
    simp [PiLp.inner_apply, dotProduct, mul_comm]
  have hAUe : ∀ i, A *ᵥ (U *ᵥ Pi.single i 1) = lam i • (U *ᵥ Pi.single i 1) := by
    intro i
    have : A * U = U * diagonal lam := by
      rw [hAU, Matrix.mul_assoc, Matrix.mul_assoc, hU2, Matrix.mul_one]
    rw [mulVec_mulVec, this, ← mulVec_mulVec]
    simp [mulVec_single_one]
  have key : ∀ x : EuclideanSpace ℝ (Fin d),
      (eigSpanAbove A 0).starProjection x = WithLp.toLp 2 (P *ᵥ WithLp.ofLp x) := by
    intro x
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · have hdec : P *ᵥ WithLp.ofLp x = ∑ i, (PP_ind lam i * (Uᵀ *ᵥ WithLp.ofLp x) i) •
          (U *ᵥ Pi.single i 1) := by
        rw [hP, ← mulVec_mulVec, ← mulVec_mulVec]
        set c := Uᵀ *ᵥ WithLp.ofLp x
        have : diagonal (PP_ind lam) *ᵥ c = ∑ i, (PP_ind lam i * c i) • (Pi.single i 1 : Fin d → ℝ) := by
          ext k
          simp [mulVec_diagonal, Finset.sum_apply, Pi.single_apply]
        rw [this, mulVec_sum]
        simp [mulVec_smul]
      rw [hdec]
      have : WithLp.toLp 2 (∑ i, (PP_ind lam i * (Uᵀ *ᵥ WithLp.ofLp x) i) • (U *ᵥ Pi.single i 1))
          = ∑ i, (PP_ind lam i * (Uᵀ *ᵥ WithLp.ofLp x) i) •
              (WithLp.toLp 2 (U *ᵥ Pi.single i 1) : EuclideanSpace ℝ (Fin d)) := by
        ext k; simp
      rw [this]
      refine Submodule.sum_mem _ fun i _ => ?_
      by_cases h : 0 < lam i
      · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨lam i, h, ?_⟩)
        simpa using hAUe i
      · simp [PP_ind, h]
    · intro w hw
      have hfix : P *ᵥ WithLp.ofLp w = WithLp.ofLp w := by
        induction hw using Submodule.span_induction with
        | mem w hw =>
          obtain ⟨μ, hμ, hw⟩ := hw
          exact PP_P_fix hU1 hU2 hAU hμ hw
        | zero => simp
        | add a b _ _ ha hb => simp [mulVec_add, ha, hb]
        | smul r a _ ha => simp [mulVec_smul, ha]
      rw [hin, WithLp.ofLp_sub, sub_dotProduct]
      have : WithLp.ofLp (WithLp.toLp 2 (P *ᵥ WithLp.ofLp x)) ⬝ᵥ WithLp.ofLp w
          = WithLp.ofLp x ⬝ᵥ WithLp.ofLp w := by
        simp only [WithLp.ofLp_toLp]
        rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hPt, hfix, dotProduct_comm]
      rw [this]; simp
  ext i j
  simp only [posProj, orthProjMatrix, Matrix.of_apply]
  rw [key]
  simp [mulVec_single_one]


theorem PP_orth_mulVec {d : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) :
    orthProjMatrix W *ᵥ WithLp.ofLp x = WithLp.ofLp (W.starProjection x) := by
  have hx : x = ∑ j, x j • (EuclideanSpace.single j (1 : ℝ)) := by
    ext k; simp [Pi.single_apply]
  conv_rhs => rw [hx, map_sum]
  ext i
  simp [orthProjMatrix, mulVec, dotProduct, mul_comm, Finset.sum_apply]

theorem PP_orth_isOrth {d : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) :
    IsOrthProjector (orthProjMatrix W) := by
  have hcol : ∀ (N : Matrix (Fin d) (Fin d) ℝ) i j, (N *ᵥ Pi.single j 1) i = N i j := by
    intro N i j; simp
  constructor
  · ext i j
    simp only [transpose_apply, orthProjMatrix, Matrix.of_apply]
    have h1 : ∀ a b : Fin d, (W.starProjection (EuclideanSpace.single b (1:ℝ))) a
        = inner ℝ (EuclideanSpace.single a (1:ℝ)) (W.starProjection (EuclideanSpace.single b 1)) := by
      intro a b; simp [EuclideanSpace.inner_single_left]
    rw [h1, h1, real_inner_comm, ← Submodule.inner_starProjection_left_eq_right]
  · have hmm : ∀ y : EuclideanSpace ℝ (Fin d),
        (orthProjMatrix W * orthProjMatrix W) *ᵥ WithLp.ofLp y = orthProjMatrix W *ᵥ WithLp.ofLp y := by
      intro y
      rw [← mulVec_mulVec, PP_orth_mulVec W y, PP_orth_mulVec W (W.starProjection y)]
      rw [Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem W y)]
    ext i j
    have := congrFun (hmm (EuclideanSpace.single j 1)) i
    simpa using this


theorem posProj_isOrthProjector {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) :
    IsOrthProjector (posProj A) := PP_orth_isOrth _

theorem trace_posProj_mul {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) :
    trace (posProj A * A) = ∑ j, max (hA.eigenvalues₀ j) 0 := by
  obtain ⟨U, lam, hU1, hU2, hAU, hsum⟩ := PP_exists hA
  rw [PP_posProj_eq hU1 hU2 hAU, ← hsum ℝ (fun t => max t 0)]
  have : U * diagonal (PP_ind lam) * Uᵀ * A = U * (diagonal (PP_ind lam) * diagonal lam) * Uᵀ := by
    conv_lhs => rw [hAU]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᵀ U, hU2, Matrix.one_mul]
  rw [this, trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU2, Matrix.one_mul,
    diagonal_mul_diagonal, trace_diagonal]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold PP_ind
  split_ifs with h
  · simp [h.le]
  · push Not at h; simp [h]

theorem trace_mul_le {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian)
    {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : IsOrthProjector Q) :
    trace (Q * A) ≤ ∑ j, max (hA.eigenvalues₀ j) 0 := by
  obtain ⟨U, lam, hU1, hU2, hAU, hsum⟩ := PP_exists hA
  rw [← hsum ℝ (fun t => max t 0)]
  obtain ⟨hQt, hQQ⟩ := hQ
  set R := Uᵀ * Q * U with hR
  have hRt : Rᵀ = R := by simp [hR, transpose_mul, hQt, Matrix.mul_assoc]
  have hRR : R * R = R := by
    have : R * R = Uᵀ * (Q * (U * Uᵀ) * Q) * U := by simp only [hR, Matrix.mul_assoc]
    rw [this, hU1, Matrix.mul_one, hQQ]
  have htr : trace (Q * A) = ∑ i, R i i * lam i := by
    have : Q * A = Q * U * diagonal lam * Uᵀ := by
      conv_lhs => rw [hAU]
      simp only [Matrix.mul_assoc]
    rw [this, trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    show trace (R * diagonal lam) = _
    simp [trace, Matrix.mul_diagonal]
  have hdiag : ∀ i, 0 ≤ R i i ∧ R i i ≤ 1 := by
    intro i
    have h1 : R i i = ∑ k, R i k ^ 2 := by
      conv_lhs => rw [← hRR]
      simp only [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      have : R k i = R i k := by
        have := congrFun (congrFun hRt i) k
        simpa using this
      rw [this, sq]
    have h0 : 0 ≤ R i i := by rw [h1]; exact Finset.sum_nonneg fun k _ => sq_nonneg _
    have h2 : R i i ^ 2 ≤ R i i := by
      calc R i i ^ 2 ≤ ∑ k, R i k ^ 2 :=
            Finset.single_le_sum (f := fun k => R i k ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ i)
        _ = R i i := h1.symm
    refine ⟨h0, ?_⟩
    nlinarith
  rw [htr]
  refine Finset.sum_le_sum fun i _ => ?_
  obtain ⟨h0, h1⟩ := hdiag i
  rcases le_total 0 (lam i) with h | h
  · calc R i i * lam i ≤ 1 * lam i := by nlinarith
      _ = lam i := one_mul _
      _ ≤ max (lam i) 0 := le_max_left _ _
  · calc R i i * lam i ≤ 0 := by nlinarith
      _ ≤ max (lam i) 0 := le_max_right _ _

theorem rank_posProj {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) :
    (posProj A).rank = (Finset.univ.filter fun j => 0 < hA.eigenvalues₀ j).card := by
  classical
  obtain ⟨U, lam, hU1, hU2, hAU, hsum⟩ := PP_exists hA
  rw [PP_posProj_eq hU1 hU2 hAU]
  have hdet : IsUnit Uᵀ.det := by
    refine IsUnit.of_mul_eq_one U.det ?_
    rw [← det_mul, hU2, det_one]
  have hdet' : IsUnit U.det := by
    refine IsUnit.of_mul_eq_one Uᵀ.det ?_
    rw [← det_mul, hU1, det_one]
  rw [rank_mul_eq_left_of_isUnit_det _ _ hdet, rank_mul_eq_right_of_isUnit_det _ _ hdet',
    rank_diagonal, Fintype.card_subtype]
  have := hsum ℕ (fun t => if 0 < t then 1 else 0)
  rw [← Finset.card_filter, ← Finset.card_filter] at this
  rw [← this]
  congr 1
  ext i
  simp [PP_ind]

end LowRankDenoise432.Dev.Lin
end

section
set_option autoImplicit false

open Matrix LowRankDenoise432.OptimalProjector

namespace LowRankDenoise432.Dev.Lin

theorem KF_rank_eq_trace {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} (h : Q * Q = Q) :
    (Q.rank : ℝ) = Matrix.trace Q := by
  have hI : IsIdempotentElem (Matrix.toLin' Q) := by
    unfold IsIdempotentElem; rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, h]
  have := ((LinearMap.isProj_range_iff_isIdempotentElem _).2 hI).trace
  rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (Fin d)), LinearMap.toMatrix_eq_toMatrix'] at this
  simp only [LinearMap.toMatrix'_toLin'] at this
  rw [this]
  rfl

theorem KF_nonneg {d : ℕ} {Q : Matrix (Fin d) (Fin d) ℝ} (h : IsOrthProjector Q)
    (x : Fin d → ℝ) : 0 ≤ x ⬝ᵥ (Q *ᵥ x) := by
  obtain ⟨h1, h2⟩ := h
  have : x ⬝ᵥ (Q *ᵥ x) = (Q *ᵥ x) ⬝ᵥ (Q *ᵥ x) := by
    have e : x ⬝ᵥ (Q *ᵥ x) = x ⬝ᵥ (Qᵀ *ᵥ (Q *ᵥ x)) := by
      rw [h1, Matrix.mulVec_mulVec, h2]
    rw [e, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rw [this]
  exact dotProduct_self_star_nonneg (Q *ᵥ x) |>.trans_eq' rfl |>.trans_eq (by simp)

theorem KF_ineq {d : ℕ} (k : ℕ) (hk : k ≤ d) (μ w : Fin d → ℝ) (hμ : Antitone μ)
    (hw0 : ∀ j, 0 ≤ w j) (hw1 : ∀ j, w j ≤ 1) (hs : ∑ j, w j = k) :
    ∑ j, μ j * w j ≤ ∑ j, μ j * (if (j : ℕ) < k then 1 else 0) := by
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · have : ∀ j ∈ Finset.univ, w j = 0 := by
      refine (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hw0 j)).1 ?_
      simpa using hs
    simp [this]
  · set t : ℝ := μ ⟨k - 1, by omega⟩ with ht
    have hpt : ∀ j : Fin d, μ j * w j - μ j * (if (j : ℕ) < k then 1 else 0)
        ≤ t * (w j - (if (j : ℕ) < k then 1 else 0)) := by
      intro j
      by_cases hj : (j : ℕ) < k
      · have : t ≤ μ j := hμ (show j ≤ ⟨k - 1, by omega⟩ from by
          rw [Fin.le_def]; simp; omega)
        simp only [hj, if_true]
        nlinarith [hw1 j]
      · have : μ j ≤ t := hμ (show (⟨k - 1, by omega⟩ : Fin d) ≤ j from by
          rw [Fin.le_def]; simp; omega)
        simp only [hj, if_false]
        nlinarith [hw0 j]
    have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hpt j)
    have hind : ∑ j : Fin d, (if (j : ℕ) < k then (1:ℝ) else 0) = k := by
      rw [← Finset.sum_filter]
      simp [Fin.card_filter_val_lt, Nat.min_eq_right hk]
    have h0 : ∑ i : Fin d, (w i - (if (i : ℕ) < k then (1:ℝ) else 0)) = 0 := by
      rw [Finset.sum_sub_distrib, hs, hind, sub_self]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, h0, mul_zero] at hsum
    linarith

theorem KF_complete {d : ℕ} (u : Fin d → Fin d → ℝ)
    (hu : ∀ i j, u i ⬝ᵥ u j = if i = j then 1 else 0) :
    ∑ j, vecMulVec (u j) (u j) = 1 := by
  have h1 : Matrix.of u * (Matrix.of u)ᵀ = 1 := by
    ext i j
    simp [Matrix.mul_apply, Matrix.one_apply, ← hu i j, dotProduct]
  have h2 := mul_eq_one_comm.1 h1
  ext a b
  have := congrFun₂ h2 a b
  simp [Matrix.mul_apply, Matrix.one_apply] at this
  simp [Matrix.sum_apply, vecMulVec_apply, this, Matrix.one_apply]

theorem KF_trace {d : ℕ} (u : Fin d → Fin d → ℝ) (c : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) :
    Matrix.trace (Q * ∑ j, c j • vecMulVec (u j) (u j)) = ∑ j, c j * (u j ⬝ᵥ (Q *ᵥ u j)) := by
  rw [Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_smul, Matrix.mul_vecMulVec, Matrix.trace_smul, Matrix.trace_vecMulVec,
    smul_eq_mul, dotProduct_comm]

theorem KF_topProj_eq {d : ℕ} (u : Fin d → Fin d → ℝ) (k : ℕ) :
    topProj u k = ∑ j : Fin d, (if (j : ℕ) < k then (1:ℝ) else 0) • vecMulVec (u j) (u j) := by
  unfold topProj
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem KF_A {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ} (u : Fin d → Fin d → ℝ) (μ : Fin d → ℝ)
    (hu : ∀ i j, u i ⬝ᵥ u j = if i = j then 1 else 0)
    (hAu : ∀ j, A *ᵥ u j = μ j • u j) :
    A = ∑ j, μ j • vecMulVec (u j) (u j) := by
  calc A = A * 1 := (Matrix.mul_one A).symm
    _ = A * ∑ j, vecMulVec (u j) (u j) := by rw [KF_complete u hu]
    _ = _ := by
      rw [Matrix.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.mul_vecMulVec, hAu, smul_vecMulVec]

theorem topProj_spec {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ} (k : ℕ) (hk : k ≤ d)
    (u : Fin d → Fin d → ℝ) (μ : Fin d → ℝ)
    (hu : ∀ i j, u i ⬝ᵥ u j = if i = j then 1 else 0)
    (hAu : ∀ j, A *ᵥ u j = μ j • u j) (hμ : Antitone μ) :
    IsOrthProjector (topProj u k) ∧ (topProj u k).rank = k ∧
      ∀ Q : Matrix (Fin d) (Fin d) ℝ, IsOrthProjector Q → Q.rank = k →
        trace (Q * A) ≤ trace (topProj u k * A) := by
  have hind : ∑ j : Fin d, (if (j : ℕ) < k then (1:ℝ) else 0) = k := by
    rw [← Finset.sum_filter]
    simp [Fin.card_filter_val_lt, Nat.min_eq_right hk]
  have hP : IsOrthProjector (topProj u k) := by
    constructor
    · unfold topProj
      simp [Matrix.transpose_sum]
    · unfold topProj
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum, Matrix.vecMulVec_mul_vecMulVec, hu]
      refine Finset.sum_congr rfl fun i hi => ?_
      simp [Finset.mem_filter] at hi ⊢
      rw [Finset.sum_eq_single_of_mem i (by simp [hi])]
      · simp
      · intro x _ hx
        simp [Ne.symm hx]
  have htr : ∀ Q : Matrix (Fin d) (Fin d) ℝ, Matrix.trace Q = ∑ j, u j ⬝ᵥ (Q *ᵥ u j) := by
    intro Q
    have := KF_trace u (fun _ => 1) Q
    simp only [one_smul, one_mul, KF_complete u hu, Matrix.mul_one] at this
    exact this
  refine ⟨hP, ?_, ?_⟩
  · have h1 := KF_rank_eq_trace hP.2
    have h2 : Matrix.trace (topProj u k) = k := by
      have := KF_trace u (fun j => if (j : ℕ) < k then (1:ℝ) else 0) 1
      rw [← KF_topProj_eq, Matrix.one_mul] at this
      rw [this]
      simpa [hu] using hind
    rw [h2] at h1
    exact_mod_cast h1
  · intro Q hQ hrk
    have hw0 := fun j => KF_nonneg hQ (u j)
    have hw1 : ∀ j, u j ⬝ᵥ (Q *ᵥ u j) ≤ 1 := by
      intro j
      have h := KF_nonneg (Q := 1 - Q) ⟨by simp [hQ.1], by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one, hQ.2]; abel⟩ (u j)
      rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, hu j j] at h
      simp at h
      linarith
    have hs : ∑ j, u j ⬝ᵥ (Q *ᵥ u j) = k := by
      rw [← htr, ← KF_rank_eq_trace hQ.2, hrk]
    have e1 : Matrix.trace (Q * A) = ∑ j, μ j * (u j ⬝ᵥ (Q *ᵥ u j)) := by
      conv_lhs => rw [KF_A u μ hu hAu]
      exact KF_trace u μ Q
    have e2 : Matrix.trace (topProj u k * A) = ∑ j, μ j * (if (j : ℕ) < k then 1 else 0) := by
      rw [Matrix.trace_mul_comm]
      conv_lhs => rw [KF_topProj_eq]
      rw [KF_trace]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hAu, dotProduct_smul, hu j j]
      simp [mul_comm]
    rw [e1, e2]
    exact KF_ineq k hk μ _ hμ hw0 hw1 hs

theorem card_pos_mono {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (h : ∀ x : Fin d → ℝ, x ⬝ᵥ (A *ᵥ x) ≤ x ⬝ᵥ (B *ᵥ x)) :
    (Finset.univ.filter fun j => 0 < hA.eigenvalues₀ j).card ≤
      (Finset.univ.filter fun j => 0 < hB.eigenvalues₀ j).card := by
  have key : ∀ j, hA.eigenvalues₀ j ≤ hB.eigenvalues₀ j := by
    intro j
    have := Matrix.IsHermitian.sorted_eigenvalues_le_add_of_re_dotProduct_le hA hB 0
      (by intro x; simpa using h x) j
    simpa using this
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact lt_of_lt_of_le hj (key j)

end LowRankDenoise432.Dev.Lin
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Matrix LowRankDenoise432.OptimalProjector

namespace LowRankDenoise432.Dev.Prob

section PN

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d m : ℕ} (M : NoisyCostModel P d m)

lemma PN_le : MeasurableSpace.comap M.c inferInstance ≤ (inferInstance : MeasurableSpace Ω) :=
  M.c_meas.comap_le

lemma PN_eps_meas (r : Fin m) (a : Fin d) : Measurable (fun ω => M.ε r ω a) :=
  (measurable_pi_apply a).comp (M.ε_meas r)

lemma PN_prod_int (r s : Fin m) (a f : Fin d) :
    Integrable (fun ω => M.ε r ω a * M.ε s ω f) P := by
  refine Integrable.of_bound
    ((PN_eps_meas M r a).mul (PN_eps_meas M s f)).aestronglyMeasurable (M.b * M.b) ?_
  filter_upwards [M.ε_bdd r a, M.ε_bdd s f] with ω h1 h2
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)

lemma PN_cov (r s : Fin m) (a f : Fin d) :
    ∫ ω, M.ε r ω a * M.ε s ω f ∂P = if r = s then M.noiseVar a f else 0 := by
  have hG := PN_le M
  rw [← integral_condExp hG]
  by_cases h : (r, a) = (s, f)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    simp only [if_true]
    have h0 := M.cond_mean_zero r a
    have h1 : (fun ω => M.ε r ω a * M.ε r ω a) =ᵐ[P] fun ω => (M.ε r ω a - (P[fun ω => M.ε r ω a | MeasurableSpace.comap M.c inferInstance]) ω) ^ 2 := by
      filter_upwards [h0] with ω hω
      simp only [Pi.zero_apply] at hω
      rw [hω]; ring
    have h2 := condExp_congr_ae (m := MeasurableSpace.comap M.c inferInstance) h1
    have h3 : (P[fun ω => M.ε r ω a * M.ε r ω a | MeasurableSpace.comap M.c inferInstance]) =ᵐ[P]
        Var[fun ω => M.ε r ω a; P | MeasurableSpace.comap M.c inferInstance] := h2
    rw [integral_congr_ae h3]
    have h4 := integral_congr_ae (M.cond_var_common r ⟨0, M.m_pos⟩ a)
    rw [h4]
    simp [NoisyCostModel.noiseVar, Matrix.diagonal_apply_eq]
  · have h0 := M.cond_uncorr r s a f h
    rw [integral_congr_ae h0]
    have : ¬ (r = s ∧ a = f) := fun hh => h (by rw [hh.1, hh.2])
    by_cases hr : r = s
    · have : a ≠ f := fun ha => by tauto
      simp [hr, NoisyCostModel.noiseVar, Matrix.diagonal_apply_ne _ this]
    · simp [hr]

lemma PN_avg (a : Fin d) (ω : Ω) :
    M.noiseAvg ω a = (m : ℝ)⁻¹ * ∑ r, M.ε r ω a := by
  simp [NoisyCostModel.noiseAvg, Finset.sum_apply]

lemma PN_avg_cov (a f : Fin d) :
    ∫ ω, M.noiseAvg ω a * M.noiseAvg ω f ∂P = M.noiseVar a f / m := by
  have hm : (m : ℝ) ≠ 0 := by have := M.m_pos; positivity
  have : (fun ω => M.noiseAvg ω a * M.noiseAvg ω f) =
      fun ω => ((m : ℝ)⁻¹ * (m : ℝ)⁻¹) * ∑ r, ∑ s, M.ε r ω a * M.ε s ω f := by
    funext ω
    simp only [PN_avg, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  rw [this, integral_const_mul, integral_finsetSum _ (fun r _ =>
    integrable_finsetSum _ (fun s _ => PN_prod_int M r s a f))]
  simp_rw [integral_finsetSum _ (fun s _ => PN_prod_int M _ s a f), PN_cov]
  simp
  field_simp

lemma PN_avg_int (a f : Fin d) :
    Integrable (fun ω => M.noiseAvg ω a * M.noiseAvg ω f) P := by
  have : (fun ω => M.noiseAvg ω a * M.noiseAvg ω f) =
      fun ω => ((m : ℝ)⁻¹ * (m : ℝ)⁻¹) * ∑ r, ∑ s, M.ε r ω a * M.ε s ω f := by
    funext ω
    simp only [PN_avg, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  rw [this]
  exact (integrable_finsetSum _ fun r _ => integrable_finsetSum _ fun s _ =>
    PN_prod_int M r s a f).const_mul _

end PN

/-- noise part -/
theorem noise_part {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d m : ℕ} (M : NoisyCostModel P d m) (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : IsOrthProjector Q) :
    ∫ ω, sqNorm (Q *ᵥ M.noiseAvg ω) ∂P = trace (Q * M.noiseVar) / m := by
  have key : ∀ ω, sqNorm (Q *ᵥ M.noiseAvg ω) =
      ∑ e, ∑ a, ∑ f, (Q e a * Q e f) * (M.noiseAvg ω a * M.noiseAvg ω f) := by
    intro ω
    unfold sqNorm
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [Matrix.mulVec, dotProduct, sq, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun f _ => ?_
    ring
  simp_rw [key]
  rw [integral_finsetSum _ (fun e _ => integrable_finsetSum _ fun a _ =>
    integrable_finsetSum _ fun f _ => (PN_avg_int M a f).const_mul _)]
  simp_rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun f _ =>
    (PN_avg_int M a f).const_mul _),
    integral_finsetSum _ (fun f _ => (PN_avg_int M _ f).const_mul _),
    integral_const_mul, PN_avg_cov]
  have hsum : ∀ a, ∑ e, Q e a * Q e a = Q a a := by
    intro a
    have := congrFun (congrFun hQ.2 a) a
    simp only [Matrix.mul_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h1 : Q a e = Q e a := by
      have := congrFun (congrFun hQ.1 e) a
      simpa [Matrix.transpose_apply] using this
    rw [h1]
  simp only [NoisyCostModel.noiseVar, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, ite_div, zero_div]
  rw [Finset.sum_comm]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_mul, hsum a]
  ring

section PN2

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d m : ℕ} (M : NoisyCostModel P d m)

end PN2

end LowRankDenoise432.Dev.Prob
end

section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Matrix LowRankDenoise432.OptimalProjector

namespace LowRankDenoise432.Dev.Prob

theorem PB_integrand {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d m : ℕ} (M : NoisyCostModel P d m) (R : Matrix (Fin d) (Fin d) ℝ) (ω : Ω) :
    sqNorm (R *ᵥ (M.c ω - M.costMean)) =
      ∑ e, ∑ a, ∑ b, (R e a * R e b) *
        ((M.c ω a - ∫ x, M.c x a ∂P) * (M.c ω b - ∫ x, M.c x b ∂P)) := by
  unfold sqNorm
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [mulVec, dotProduct, Pi.sub_apply, NoisyCostModel.costMean, sq,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem PB_integrable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d m : ℕ} (M : NoisyCostModel P d m) (a b : Fin d) :
    Integrable (fun ω => (M.c ω a - ∫ x, M.c x a ∂P) * (M.c ω b - ∫ x, M.c x b ∂P)) P :=
  ((M.c_memLp a).sub (memLp_const _)).integrable_mul ((M.c_memLp b).sub (memLp_const _))

/-- bias part -/
theorem bias_part {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d m : ℕ} (M : NoisyCostModel P d m) (R : Matrix (Fin d) (Fin d) ℝ) (hR : IsOrthProjector R) :
    ∫ ω, sqNorm (R *ᵥ (M.c ω - M.costMean)) ∂P = trace (R * M.costCov) := by
  simp_rw [PB_integrand]
  rw [integral_finset_sum _ fun e _ => integrable_finset_sum _ fun a _ =>
    integrable_finset_sum _ fun b _ => (PB_integrable M a b).const_mul _]
  have h1 : ∀ e : Fin d, ∫ ω, ∑ a, ∑ b, (R e a * R e b) *
        ((M.c ω a - ∫ x, M.c x a ∂P) * (M.c ω b - ∫ x, M.c x b ∂P)) ∂P
      = ∑ a, ∑ b, (R e a * R e b) * M.costCov a b := by
    intro e
    rw [integral_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ =>
      (PB_integrable M a b).const_mul _]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finset_sum _ fun b _ => (PB_integrable M a b).const_mul _]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_const_mul]
    rfl
  simp_rw [h1]
  have hsym : ∀ a b, M.costCov a b = M.costCov b a := fun a b => by
    simp [NoisyCostModel.costCov, covariance_comm]
  have hRR : ∀ a b, ∑ e, R e a * R e b = R a b := by
    intro a b
    have := congrFun (congrFun hR.2 a) b
    simp only [Matrix.mul_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun e _ => ?_
    have := congrFun (congrFun hR.1 e) a
    simp only [transpose_apply] at this
    rw [this]
  rw [Finset.sum_comm]
  simp_rw [trace, diag, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.sum_mul, hRR, hsym a y]

/-- D has nonnegative diagonal -/
theorem noiseVar_psd {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d m : ℕ} (M : NoisyCostModel P d m) (e : Fin d) : 0 ≤ M.noiseVar e e := by
  unfold NoisyCostModel.noiseVar
  rw [Matrix.diagonal_apply_eq]
  refine integral_nonneg_of_ae ?_
  unfold ProbabilityTheory.condVar
  exact condExp_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)

end LowRankDenoise432.Dev.Prob
end

section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Matrix LowRankDenoise432.OptimalProjector

namespace LowRankDenoise432.Dev.Err

theorem PE_expand {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    sqNorm (Q *ᵥ v) = ∑ e, ∑ a, ∑ b, (Q e a * Q e b) * (v a * v b) := by
  unfold sqNorm
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [mulVec, dotProduct, sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem err_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d m : ℕ} (M : NoisyCostModel P d m) (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : IsOrthProjector Q) :
    M.err Q = trace (Q * M.noiseVar) / m + trace ((1 - Q) * M.costCov) := by
  have hR : IsOrthProjector (1 - Q) := by
    obtain ⟨hs, hi⟩ := hQ
    refine ⟨by rw [Matrix.transpose_sub, Matrix.transpose_one, hs], ?_⟩
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hi]; abel
  have i1 : Integrable (fun ω => sqNorm (Q *ᵥ M.noiseAvg ω)) P := by
    simp_rw [PE_expand]
    refine integrable_finsetSum _ fun e _ => integrable_finsetSum _ fun a _ =>
      integrable_finsetSum _ fun b _ => ?_
    exact (Dev.Prob.PN_avg_int M a b).const_mul _
  have i2 : Integrable (fun ω => sqNorm ((1 - Q) *ᵥ (M.c ω - M.costMean))) P := by
    simp_rw [Dev.Prob.PB_integrand]
    refine integrable_finsetSum _ fun e _ => integrable_finsetSum _ fun a _ =>
      integrable_finsetSum _ fun b _ => ?_
    exact (Dev.Prob.PB_integrable M a b).const_mul _
  unfold NoisyCostModel.err
  have : ∀ ω, sqNorm (projEstimate Q M.costMean (M.obsAvg ω) - M.c ω) =
      sqNorm (Q *ᵥ M.noiseAvg ω) + sqNorm ((1 - Q) *ᵥ (M.c ω - M.costMean)) :=
    fun ω => (lemma_3_2 Q hQ M.costMean (M.c ω) (M.noiseAvg ω)).2
  simp_rw [this]
  rw [integral_add i1 i2, Dev.Prob.noise_part M Q hQ, Dev.Prob.bias_part M _ hR]

end LowRankDenoise432.Dev.Err
end

section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Matrix LowRankDenoise432.OptimalProjector

namespace LowRankDenoise432.Dev.T33

theorem err_alt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d m : ℕ} (M : NoisyCostModel P d m) (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : IsOrthProjector Q) :
    M.err Q = trace M.costCov - trace (Q * M.adjCov m) := by
  rw [Dev.Err.err_eq M Q hQ]
  unfold NoisyCostModel.adjCov
  rw [Matrix.sub_mul, trace_sub, Matrix.mul_sub, trace_sub, Matrix.mul_smul, trace_smul]
  simp only [smul_eq_mul, div_eq_mul_inv, Matrix.one_mul]
  ring

theorem isOrth_zero {d : ℕ} : IsOrthProjector (0 : Matrix (Fin d) (Fin d) ℝ) := by
  simp [IsOrthProjector]

theorem isOrth_one {d : ℕ} : IsOrthProjector (1 : Matrix (Fin d) (Fin d) ℝ) := by
  simp [IsOrthProjector]

theorem eigSpan_shift {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) :
    eigSpanAbove (S - t • (1 : Matrix (Fin d) (Fin d) ℝ)) 0 =
      eigSpanAbove (S + t • (1 : Matrix (Fin d) (Fin d) ℝ)) (2 * t) := by
  unfold eigSpanAbove
  congr 1
  ext v
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨μ, hμ, h⟩
    refine ⟨μ + 2 * t, by linarith, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    have h' : S *ᵥ WithLp.ofLp v = (μ + t) • WithLp.ofLp v := by
      rw [add_smul]; rw [← h]; abel
    rw [h']; module
  · rintro ⟨μ, hμ, h⟩
    refine ⟨μ - 2 * t, by linarith, ?_⟩
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    have h' : S *ᵥ WithLp.ofLp v = (μ - t) • WithLp.ofLp v := by
      rw [sub_smul, eq_sub_iff_add_eq]; exact h
    rw [h']; module


end LowRankDenoise432.Dev.T33

namespace LowRankDenoise432.OptimalProjector

open LowRankDenoise432.Dev

theorem chk_theorem_3_3 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d m : ℕ} (M : NoisyCostModel P d m) :
    -- (1) equation (2)
    (∀ Q : Matrix (Fin d) (Fin d) ℝ, IsOrthProjector Q →
      M.err Q = trace (Q * M.noiseVar) / m + trace ((1 - Q) * M.costCov) ∧
      M.err Q = trace M.costCov - trace (Q * M.adjCov m)) ∧
    -- (2) global optimality of the positive-eigenspace projector
    (IsOrthProjector (posProj (M.adjCov m)) ∧
      ∀ Q : Matrix (Fin d) (Fin d) ℝ, IsOrthProjector Q →
        M.err (posProj (M.adjCov m)) ≤ M.err Q) ∧
    -- (3) the minimum value and its two upper bounds
    (M.err (posProj (M.adjCov m)) = trace M.costCov - ∑ j, max (M.eigs m j) 0 ∧
      M.err (posProj (M.adjCov m)) ≤ trace M.noiseVar / m ∧
      M.err (posProj (M.adjCov m)) ≤ trace M.costCov) ∧
    -- (4) rank-k optimality of every top-k eigenspace projector
    (∀ k : ℕ, k ≤ d → ∀ (u : Fin d → Fin d → ℝ) (μ : Fin d → ℝ),
      (∀ i j, u i ⬝ᵥ u j = if i = j then 1 else 0) →
      (∀ j, M.adjCov m *ᵥ u j = μ j • u j) → Antitone μ →
      IsOrthProjector (topProj u k) ∧ (topProj u k).rank = k ∧
        ∀ Q : Matrix (Fin d) (Fin d) ℝ, IsOrthProjector Q → Q.rank = k →
          M.err (topProj u k) ≤ M.err Q) ∧
    -- (5) the optimal rank k*(m)
    (M.optRank m = (posProj (M.adjCov m)).rank ∧
      ∀ m₁ m₂ : ℕ, 0 < m₁ → m₁ ≤ m₂ → M.optRank m₁ ≤ M.optRank m₂) ∧
    -- (6) the homoscedastic case D = σ² I
    (∀ σ : ℝ, M.noiseVar = σ ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ) →
      posProj (M.adjCov m) =
        orthProjMatrix (eigSpanAbove (M.costCov + (σ ^ 2 / m) • (1 : Matrix (Fin d) (Fin d) ℝ))
          (2 * σ ^ 2 / m))) := by
  have hA := M.adjCov_isHermitian m
  have hP : IsOrthProjector (posProj (M.adjCov m)) := Lin.posProj_isOrthProjector _
  have hopt : ∀ Q : Matrix (Fin d) (Fin d) ℝ, IsOrthProjector Q →
      M.err (posProj (M.adjCov m)) ≤ M.err Q := by
    intro Q hQ
    rw [T33.err_alt M _ hP, T33.err_alt M Q hQ, Lin.trace_posProj_mul hA]
    have := Lin.trace_mul_le hA hQ
    linarith
  refine ⟨fun Q hQ => ⟨Dev.Err.err_eq M Q hQ, T33.err_alt M Q hQ⟩, ⟨hP, hopt⟩, ⟨?_, ?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_⟩
  · rw [T33.err_alt M _ hP, Lin.trace_posProj_mul hA]; rfl
  · have := hopt 1 T33.isOrth_one
    rw [Dev.Err.err_eq M 1 T33.isOrth_one] at this
    simpa using this
  · have := hopt 0 T33.isOrth_zero
    rw [Dev.Err.err_eq M 0 T33.isOrth_zero] at this
    simpa using this
  · intro k hk u μ hu hAu hμ
    obtain ⟨h1, h2, h3⟩ := Lin.topProj_spec (A := M.adjCov m) k hk u μ hu hAu hμ
    refine ⟨h1, h2, fun Q hQ hrank => ?_⟩
    rw [T33.err_alt M _ h1, T33.err_alt M Q hQ]
    have := h3 Q hQ hrank
    linarith
  · exact Lin.rank_posProj hA ▸ rfl
  · intro m₁ m₂ h1 h12
    unfold NoisyCostModel.optRank NoisyCostModel.eigs
    refine Lin.card_pos_mono (M.adjCov_isHermitian m₁) (M.adjCov_isHermitian m₂) ?_
    intro x
    have hD : x ⬝ᵥ (M.adjCov m₂ *ᵥ x) - x ⬝ᵥ (M.adjCov m₁ *ᵥ x) =
        (((m₁ : ℝ)⁻¹ - (m₂ : ℝ)⁻¹)) * ∑ e, M.noiseVar e e * x e ^ 2 := by
      have hdiag : M.noiseVar = Matrix.diagonal (fun e => M.noiseVar e e) := by
        unfold NoisyCostModel.noiseVar
        ext i j
        by_cases h : i = j
        · subst h; simp
        · simp [Matrix.diagonal_apply_ne _ h]
      unfold NoisyCostModel.adjCov
      rw [hdiag]
      generalize (fun e => M.noiseVar e e) = dd
      simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul,
        smul_eq_mul, Matrix.mulVec_diagonal, dotProduct, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      simp only [Pi.sub_apply, Pi.smul_apply, Matrix.mulVec_diagonal, smul_eq_mul, Matrix.diagonal_apply_eq]
      ring
    have h0 : 0 ≤ (((m₁ : ℝ)⁻¹ - (m₂ : ℝ)⁻¹)) := by
      have : (0 : ℝ) < m₁ := by exact_mod_cast h1
      have : (m₁ : ℝ) ≤ m₂ := by exact_mod_cast h12
      rw [sub_nonneg]; exact inv_anti₀ (by positivity) this
    have h2 : 0 ≤ ∑ e, M.noiseVar e e * x e ^ 2 :=
      Finset.sum_nonneg fun e _ => mul_nonneg (Dev.Prob.noiseVar_psd M e) (sq_nonneg _)
    nlinarith [mul_nonneg h0 h2]
  · intro σ hσ
    unfold posProj
    congr 1
    have : M.adjCov m = M.costCov - ((σ ^ 2 / m) • (1 : Matrix (Fin d) (Fin d) ℝ)) := by
      unfold NoisyCostModel.adjCov; rw [hσ, smul_smul]; congr 2; field_simp
    rw [this, T33.eigSpan_shift]
    rw [mul_div_assoc]

end LowRankDenoise432.OptimalProjector
end

theorem solution : type_of% @LowRankDenoise432.OptimalProjector.chk_theorem_3_3 := @LowRankDenoise432.OptimalProjector.chk_theorem_3_3
