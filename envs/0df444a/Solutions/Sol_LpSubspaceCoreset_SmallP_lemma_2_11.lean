-- Prove2me | solution 1 for LpSubspaceCoreset.SmallP.lemma_2_11
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-27T00:52:15.01529+00:00
-- url     : https://prove2.me/submissions/1f00e6f5-08b2-4a51-aed6-49bc0ccb46b1

import Mathlib
import Definitions.Def_LpSubspaceCoreset_SmallP_Lewis

set_option autoImplicit false

open LpSubspaceCoreset
open LpSubspaceCoreset.SmallP
open scoped InnerProductSpace Matrix
set_option maxHeartbeats 600000

theorem solution (p : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2) {N r : ℕ}
    (M : Matrix (Fin N) (Fin r) ℝ) (hM : M.rank = r) (hM0 : ∀ i, M i ≠ 0) (w : Fin N → ℝ)
    (hw : IsLewisWeights p M w) :
    ∃ (J : Matrix (Fin r) (Fin r) ℝ) (y : Fin N → Fin r → ℝ), IsUnit J.det ∧
      (∀ i, y i ⬝ᵥ y i = 1) ∧
      (∀ i, M i = (w i) ^ (1 / p) • J.mulVec (y i)) ∧
      ∑ i, w i • Matrix.vecMulVec (y i) (y i) = 1 ∧
      ∑ i, w i = r := by
  classical
  let d (i : Fin N) := (w i) ^ ((1 : ℝ) / 2 - 1 / p)
  let Z := lewisReweight p w M
  let E := EuclideanSpace ℝ (Fin N)
  let L := Matrix.toEuclideanLin Z
  let W := LinearMap.range L
  have wpos (i : Fin N) : 0 < w i := ((hw i).2 (hM0 i)).1
  have dpos (i : Fin N) : 0 < d i := Real.rpow_pos_of_pos (wpos i) _
  have hZ : Z = Matrix.diagonal d * M := by
    ext i j
    simp [Z, lewisReweight, Matrix.diagonal_mul, d]
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
  have rankR : R.rank = r := by
    apply le_antisymm (by simpa using (Matrix.rank_le_card_width R))
    calc
      r = Z.rank := rankZ.symm
      _ = (Q * R).rank := congrArg Matrix.rank hQR.symm
      _ ≤ R.rank := Matrix.rank_mul_le_right Q R
  have detR : R.det ≠ 0 := by
    have hker : LinearMap.ker R.mulVecLin = ⊥ := by
      apply Submodule.finrank_eq_zero.mp
      have h := R.mulVecLin.finrank_range_add_finrank_ker
      change R.rank + Module.finrank ℝ (LinearMap.ker R.mulVecLin) = _ at h
      rw [rankR, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
      omega
    rw [← LinearMap.det_toLin', ne_eq, LinearMap.det_eq_zero_iff_ker_ne_bot, not_ne_iff]
    exact hker
  have weights (i : Fin N) : w i = ∑ j, Q i j ^ 2 := by
    rw [((hw i).2 (hM0 i)).2, leverage]
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
  refine ⟨Rᵀ, y, isUnit_iff_ne_zero.mpr (by simpa using detR), ?_, ?_, ?_, ?_⟩
  · intro i
    unfold dotProduct
    simp only [y, ← pow_two, div_pow, Real.sq_sqrt (wpos i).le, ← Finset.sum_div, ← weights]
    exact div_self (wpos i).ne'
  · intro i
    funext j
    have right : (Rᵀ *ᵥ y i) j = Z i j / Real.sqrt (w i) := by
      unfold Matrix.mulVec dotProduct
      simp only [y, Matrix.transpose_apply, ← mul_div_assoc, ← Finset.sum_div]
      congr 1
      rw [← hQR, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    change M i j = w i ^ (1 / p) * (Rᵀ *ᵥ y i) j
    rw [right]
    have hentry : Z i j = d i * M i j := by rfl
    have combined : w i ^ (1 / p) * d i = Real.sqrt (w i) := by
      rw [show d i = w i ^ ((1 : ℝ) / 2 - 1 / p) from rfl, ← Real.rpow_add (wpos i), Real.sqrt_eq_rpow]
      congr 1
      ring
    have root : 0 < Real.sqrt (w i) := Real.sqrt_pos.2 (wpos i)
    rw [hentry, ← mul_div_assoc, ← mul_assoc, combined]
    field_simp [root.ne']
  · ext j l
    rw [← gram, Matrix.mul_apply]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [y]
    rw [div_mul_div_comm, Real.mul_self_sqrt (wpos i).le]
    field_simp [(wpos i).ne']
  · simp only [weights]
    rw [Finset.sum_comm]
    calc
      _ = ∑ j : Fin r, (Qᵀ * Q) j j := by simp [Matrix.mul_apply, pow_two]
      _ = _ := by simp [gram]
