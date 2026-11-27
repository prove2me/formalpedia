-- Prove2me | solution 1 for LpSubspaceCoreset.SmallP.lemma_2_12
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-27T00:58:50.137029+00:00
-- url     : https://prove2.me/submissions/fe8eea4f-1372-4866-96f4-f096df5cfb7e

import Mathlib
import Definitions.Def_LpSubspaceCoreset_SmallP_Cost
import Definitions.Def_LpSubspaceCoreset_SmallP_Lewis

set_option autoImplicit false

open LpSubspaceCoreset
open LpSubspaceCoreset.SmallP

open scoped InnerProductSpace Matrix
set_option maxHeartbeats 600000

private theorem lewis_frame (p : ℝ) {N r : ℕ}
    (M : Matrix (Fin N) (Fin r) ℝ) (hM : M.rank = r) (w : Fin N → ℝ)
    (hw : IsLewisWeights p M w) :
    ∃ (J : Matrix (Fin r) (Fin r) ℝ) (y : Fin N → Fin r → ℝ),
      (∀ i, y i ⬝ᵥ y i ≤ 1) ∧
      (∀ i, M i = (w i) ^ (1 / p) • J.mulVec (y i)) ∧
      ∑ i, w i • Matrix.vecMulVec (y i) (y i) = 1 ∧
      ∑ i, w i = r := by
  classical
  let d (i : Fin N) := if M i = 0 then 1 else (w i) ^ ((1 : ℝ) / 2 - 1 / p)
  let Z := lewisReweight p w M
  let E := EuclideanSpace ℝ (Fin N)
  let L := Matrix.toEuclideanLin Z
  let W := LinearMap.range L
  have wpos (i : Fin N) (hi : M i ≠ 0) : 0 < w i := ((hw i).2 hi).1
  have dpos (i : Fin N) : 0 < d i := by
    dsimp [d]
    split_ifs with hi
    · norm_num
    · exact Real.rpow_pos_of_pos (wpos i hi) _
  have entry {i : Fin N} {j : Fin r} (hi : M i = 0) : M i j = 0 :=
    congrFun hi j
  have hZ : Z = Matrix.diagonal d * M := by
    ext i j
    by_cases hi : M i = 0
    · simp [Z, lewisReweight, Matrix.diagonal_mul, d, hi, entry hi]
    · simp [Z, lewisReweight, Matrix.diagonal_mul, d, hi]
  have rankZ : Z.rank = r := by
    rw [hZ, Matrix.rank_mul_eq_right_of_det_ne_zero _ _ ?_, hM]
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (dpos i).ne'
  have dim : Module.finrank ℝ W = r := by
    change Module.finrank ℝ (Matrix.toEuclideanLin Z).range = r
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, ← Matrix.rank_eq_finrank_range_toLin, rankZ]
  let b := (stdOrthonormalBasis ℝ W).reindex (finCongr dim)
  let Q : Matrix (Fin N) (Fin r) ℝ := Matrix.of fun i j => (b j : E) i
  have gram : Qᵀ * Q = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hh := orthonormal_iff_ite.mp b.orthonormal i j
    change ⟪(b i : E), (b j : E)⟫_ℝ = _ at hh
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at hh
    change (∑ k, Q k i * Q k j) = _
    calc
      _ = WithLp.ofLp (b j : E) ⬝ᵥ WithLp.ofLp (b i : E) :=
        Finset.sum_congr rfl fun k _ => mul_comm (Q k i) (Q k j)
      _ = _ := hh
  let R : Matrix (Fin r) (Fin r) ℝ := Matrix.of fun i j =>
    b.repr (L.rangeRestrict (EuclideanSpace.single j 1)) i
  have hQR : Q * R = Z := by
    ext i j
    rw [Matrix.mul_apply]
    have h : (∑ k : Fin r, b.repr (L.rangeRestrict (EuclideanSpace.single j 1)) k • (b k : E)) =
        L (EuclideanSpace.single j 1) := by
      have hh := congrArg (fun u : W => (u : E)) (b.sum_repr (L.rangeRestrict (EuclideanSpace.single j 1)))
      change (↑(∑ k, b.repr (L.rangeRestrict (EuclideanSpace.single j 1)) k • b k) : E) =
        L (EuclideanSpace.single j 1) at hh
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using hh
    have ej : (L (EuclideanSpace.single j 1)) i = Z i j := by
      change (Z *ᵥ WithLp.ofLp (EuclideanSpace.single j 1)) i = Z i j
      rw [PiLp.ofLp_single, Matrix.mulVec_single_one]
      rfl
    have he := congrArg (fun u : E => WithLp.ofLp u i) h
    change (WithLp.ofLp (∑ k : Fin r, b.repr (L.rangeRestrict (EuclideanSpace.single j 1)) k • (b k : E))) i = _ at he
    simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul] at he
    calc
      _ = ∑ k, b.repr (L.rangeRestrict (EuclideanSpace.single j 1)) k * (b k : E) i :=
        Finset.sum_congr rfl fun k _ => mul_comm (Q i k) (R k j)
      _ = (L (EuclideanSpace.single j 1)) i := he
      _ = _ := ej
  have Qzero (i : Fin N) (hi : M i = 0) (j : Fin r) : Q i j = 0 := by
    obtain ⟨v, hv⟩ := (b j).2
    have h := congrArg (fun u : E => u i) hv
    change (Z *ᵥ WithLp.ofLp v) i = Q i j at h
    rw [← h, hZ, Matrix.mulVec, dotProduct]
    simp only [Matrix.diagonal_mul, entry hi, mul_zero, zero_mul, Finset.sum_const_zero]
  have weights (i : Fin N) : w i = ∑ j, Q i j ^ 2 := by
    by_cases hi : M i = 0
    · simp [(hw i).1 hi, Qzero i hi]
    rw [((hw i).2 hi).2, leverage]
    change ‖W.orthogonalProjectionOnto (EuclideanSpace.single i 1)‖ ^ 2 = _
    rw [← b.repr.norm_map, EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    rw [OrthonormalBasis.repr_apply_apply, W.inner_orthogonalProjectionOnto_eq_of_mem_left]
    change ⟪(b j : E), EuclideanSpace.single i 1⟫_ℝ = Q i j
    rw [EuclideanSpace.inner_single_right]
    change 1 * (b j : E) i = (b j : E) i
    exact one_mul _
  let y (i : Fin N) (j : Fin r) := Q i j / Real.sqrt (w i)
  refine ⟨Rᵀ, y, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : M i = 0
    · simp [y, Qzero i hi, dotProduct]
    · unfold dotProduct
      simp only [y, ← pow_two, div_pow, Real.sq_sqrt (wpos i hi).le, ← Finset.sum_div, ← weights]
      rw [div_self (wpos i hi).ne']
  · intro i
    by_cases hi : M i = 0
    · have hy : y i = 0 := by funext j; simp [y, Qzero i hi]
      rw [hi, hy, Matrix.mulVec_zero, smul_zero]
    funext j
    have right : (Rᵀ *ᵥ y i) j = Z i j / Real.sqrt (w i) := by
      unfold Matrix.mulVec dotProduct
      simp only [y, Matrix.transpose_apply, ← mul_div_assoc, ← Finset.sum_div]
      congr 1
      rw [← hQR, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    change M i j = w i ^ (1 / p) * (Rᵀ *ᵥ y i) j
    rw [right]
    have hentry : Z i j = d i * M i j := by rw [hZ, Matrix.diagonal_mul]
    have combined : w i ^ (1 / p) * d i = Real.sqrt (w i) := by
      rw [show d i = w i ^ ((1 : ℝ) / 2 - 1 / p) by simp [d, hi], ← Real.rpow_add (wpos i hi), Real.sqrt_eq_rpow]
      congr 1
      ring
    have root : 0 < Real.sqrt (w i) := Real.sqrt_pos.2 (wpos i hi)
    rw [hentry, ← mul_div_assoc, ← mul_assoc, combined]
    field_simp [root.ne']
  · ext j l
    rw [← gram, Matrix.mul_apply]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : M i = 0
    · simp [(hw i).1 hi, Qzero i hi]
    · dsimp only [y]
      rw [div_mul_div_comm, Real.mul_self_sqrt (wpos i hi).le]
      field_simp [(wpos i hi).ne']
  · simp only [weights]
    rw [Finset.sum_comm]
    calc
      _ = ∑ j : Fin r, (Qᵀ * Q) j j := by simp [Matrix.mul_apply, pow_two]
      _ = _ := by simp [gram]

theorem solution (p : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2) {N r : ℕ}
    (M : Matrix (Fin N) (Fin r) ℝ) (hM : M.rank = r) (w : Fin N → ℝ)
    (hw : IsLewisWeights p M w) (s : ℕ) (hs : 1 ≤ s) (T : Matrix (Fin s) (Fin r) ℝ)
    (i : Fin N) :
    norm2 (T.mulVec (M i)) ^ p ≤ w i * ∑ j, norm2 (T.mulVec (M j)) ^ p := by
  classical
  let _ : Nonempty (Fin N) := ⟨i⟩
  obtain ⟨J, y, ynorm, row, frame, _⟩ := lewis_frame p M hM w hw
  have wp (j : Fin N) : 0 ≤ w j := by
    by_cases hj : M j = 0
    · rw [(hw j).1 hj]
    · exact ((hw j).2 hj).1.le
  let C := T * J
  let a (j : Fin N) := norm2 (C *ᵥ y j)
  let G : ℝ := ∑ l : Fin s, ∑ h : Fin r, C l h ^ 2
  have an (j : Fin N) : 0 ≤ a j := by unfold a norm2; positivity
  have asq (j : Fin N) : a j ^ 2 = ∑ l, (C *ᵥ y j) l ^ 2 := by
    exact EuclideanSpace.real_norm_sq_eq _
  have quadratic (l : Fin s) :
      (∑ j, w j * (C *ᵥ y j) l ^ 2) = ∑ h, C l h ^ 2 := by
    have fr (h h' : Fin r) : (∑ j, w j * (y j h * y j h')) = if h = h' then 1 else 0 := by
      have h := congrArg (fun A : Matrix (Fin r) (Fin r) ℝ => A h h') frame
      simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply, Matrix.one_apply] using h
    have expand (j : Fin N) : w j * (C *ᵥ y j) l ^ 2 =
        ∑ h, ∑ h', (C l h * C l h') * (w j * (y j h * y j h')) := by
      rw [Matrix.mulVec, dotProduct, pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun h' _ => by ring
    simp only [expand]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h _
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, fr, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, pow_two]
  have total : ∑ j, w j * a j ^ 2 = G := by
    simp only [asq, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => quadratic l
  have point (j : Fin N) : a j ^ 2 ≤ G := by
    rw [asq]
    apply Finset.sum_le_sum
    intro l _
    have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (C l) (y j)
    change (C *ᵥ y j) l ^ 2 ≤ (∑ h, C l h ^ 2) * (∑ h, y j h ^ 2) at cs
    have hy : (∑ h, y j h ^ 2) ≤ 1 := by simpa [dotProduct, pow_two] using ynorm j
    exact cs.trans (mul_le_of_le_one_right (Finset.sum_nonneg fun _ _ => sq_nonneg _) hy)
  have express (j : Fin N) : norm2 (T *ᵥ M j) ^ p = w j * a j ^ p := by
    rw [row j, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
    have hp' : p ≠ 0 := by linarith
    have hh : (w j ^ (1 / p)) ^ p = w j := by
      rw [← Real.rpow_mul (wp j), one_div_mul_cancel hp', Real.rpow_one]
    change ‖(WithLp.toLp 2 (w j ^ (1 / p) • (T * J) *ᵥ y j) : EuclideanSpace ℝ (Fin s))‖ ^ p =
      w j * ‖(WithLp.toLp 2 (C *ᵥ y j) : EuclideanSpace ℝ (Fin s))‖ ^ p
    rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (wp j) _), Real.mul_rpow (Real.rpow_nonneg (wp j) _) (norm_nonneg _), hh]
  simp only [express]
  apply mul_le_mul_of_nonneg_left _ (wp i)
  let B := sSup (Set.range a)
  have a_le (j : Fin N) : a j ≤ B := le_csSup (Set.finite_range a).bddAbove ⟨j, rfl⟩
  have Bn : 0 ≤ B := (an i).trans (a_le i)
  rcases Bn.eq_or_lt with hb | hb
  · have az (j : Fin N) : a j = 0 := le_antisymm ((a_le j).trans_eq hb.symm) (an j)
    simp [az, Real.zero_rpow (by linarith : p ≠ 0)]
  · obtain ⟨j, hj⟩ := (Set.range_nonempty (f := a)).csSup_mem (Set.finite_range a)
    change a j = B at hj
    have Bsq : B ^ 2 ≤ ∑ j, w j * a j ^ 2 := by
      rw [← hj, total]
      apply point
    have bound (j : Fin N) : a j ^ 2 ≤ B ^ (2 - p) * a j ^ p := by
      rcases (an j).eq_or_lt with hz | hz
      · simp [← hz, Real.zero_rpow (by linarith : p ≠ 0)]
      · calc
          _ = a j ^ ((2 - p) + p) := by rw [sub_add_cancel, Real.rpow_two]
          _ = a j ^ (2 - p) * a j ^ p := Real.rpow_add hz _ _
          _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (an j) (a_le j) (sub_nonneg.2 hp2))
            (Real.rpow_nonneg (an j) _)
    have sum_bound : (∑ j, w j * a j ^ 2) ≤ B ^ (2 - p) * ∑ j, w j * a j ^ p := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      rw [mul_left_comm]
      exact mul_le_mul_of_nonneg_left (bound j) (wp j)
    have h : B ^ p ≤ ∑ j, w j * a j ^ p := by
      apply le_of_mul_le_mul_left _ (Real.rpow_pos_of_pos hb (2 - p))
      rw [← Real.rpow_add hb, sub_add_cancel]
      norm_num only [Real.rpow_two]
      exact Bsq.trans sum_bound
    exact (Real.rpow_le_rpow (an i) (a_le i) (by linarith)).trans h
