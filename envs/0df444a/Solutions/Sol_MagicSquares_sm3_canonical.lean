-- Prove2me | solution 1 for MagicSquares.sm3_canonical
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-17T05:33:29.269288+00:00
-- url     : https://prove2.me/submissions/53ee298a-0046-4692-9f3d-2c0c3c0d95c7

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresSemiMagic3

set_option autoImplicit false
set_option maxHeartbeats 0

open scoped BigOperators

namespace MagicSquares

/-! ## Canonical decomposition of a 3x3 semi-magic square

Every semi-magic square is a nonnegative combination of the six permutation
matrices, uniquely so after normalizing `min (x,y,z) = 0`. -/

/-- The row-sum equations, expanded. -/
private lemma row0 (M : Square 3 ℕ) (t : ℕ) (hM : IsSemiMagic M t) :
    M 0 0 + M 0 1 + M 0 2 = t := by
  have h := hM.1 (0 : Fin 3)
  simpa [rowSum, Fin.sum_univ_three] using h

private lemma row1 (M : Square 3 ℕ) (t : ℕ) (hM : IsSemiMagic M t) :
    M 1 0 + M 1 1 + M 1 2 = t := by
  have h := hM.1 (1 : Fin 3)
  simpa [rowSum, Fin.sum_univ_three] using h

private lemma row2 (M : Square 3 ℕ) (t : ℕ) (hM : IsSemiMagic M t) :
    M 2 0 + M 2 1 + M 2 2 = t := by
  have h := hM.1 (2 : Fin 3)
  simpa [rowSum, Fin.sum_univ_three] using h

private lemma col0 (M : Square 3 ℕ) (t : ℕ) (hM : IsSemiMagic M t) :
    M 0 0 + M 1 0 + M 2 0 = t := by
  have h := hM.2 (0 : Fin 3)
  simpa [colSum, Fin.sum_univ_three] using h

private lemma col1 (M : Square 3 ℕ) (t : ℕ) (hM : IsSemiMagic M t) :
    M 0 1 + M 1 1 + M 2 1 = t := by
  have h := hM.2 (1 : Fin 3)
  simpa [colSum, Fin.sum_univ_three] using h

private lemma col2 (M : Square 3 ℕ) (t : ℕ) (hM : IsSemiMagic M t) :
    M 0 2 + M 1 2 + M 2 2 = t := by
  have h := hM.2 (2 : Fin 3)
  simpa [colSum, Fin.sum_univ_three] using h

/-- A semi-magic square whose three *even* transversals each have minimum `0`
is a combination of the three *odd* permutation matrices alone. -/
private lemma sm3_residual (M : Square 3 ℕ) (t : ℕ) (hM : IsSemiMagic M t)
    (hD : min (M 0 0) (min (M 1 1) (M 2 2)) = 0)
    (hE : min (M 0 1) (min (M 1 2) (M 2 0)) = 0)
    (hF : min (M 0 2) (min (M 1 0) (M 2 1)) = 0) :
    ∃ x y z : ℕ, M = sm3Of 0 0 0 x y z := by
  have hR0 := row0 M t hM
  have hR1 := row1 M t hM
  have hR2 := row2 M t hM
  have hC0 := col0 M t hM
  have hC1 := col1 M t hM
  have hC2 := col2 M t hM
  have h_eq : M 1 0 = M 0 1 ∧ M 1 2 = M 0 0 ∧ M 2 0 = M 0 2 ∧
      M 2 1 = M 0 0 ∧ M 2 2 = M 0 1 ∧ M 1 1 = M 0 2 := by
    omega
  refine ⟨M 0 0, M 0 2, M 0 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sm3Of, h_eq]

/-- The three even-transversal minima. -/
private def evenMin (M : Square 3 ℕ) : ℕ × ℕ × ℕ :=
  (min (M 0 0) (min (M 1 1) (M 2 2)),
    min (M 0 1) (min (M 1 2) (M 2 0)),
    min (M 0 2) (min (M 1 0) (M 2 1)))

/-- Subtracting `u D + v E + w F` from a semi-magic square. -/
private def subEven (M : Square 3 ℕ) (u v w : ℕ) : Square 3 ℕ :=
  ![![M 0 0 - u, M 0 1 - v, M 0 2 - w],
    ![M 1 0 - w, M 1 1 - u, M 1 2 - v],
    ![M 2 0 - v, M 2 1 - w, M 2 2 - u]]

/-- The residual is semi-magic, with line sum `t - u - v - w`. -/
private lemma subEven_semiMagic (M : Square 3 ℕ) (t u v w : ℕ) (hM : IsSemiMagic M t)
    (hu : u ≤ M 0 0) (hu1 : u ≤ M 1 1) (hu2 : u ≤ M 2 2)
    (hv : v ≤ M 0 1) (hv1 : v ≤ M 1 2) (hv2 : v ≤ M 2 0)
    (hw : w ≤ M 0 2) (hw1 : w ≤ M 1 0) (hw2 : w ≤ M 2 1) :
    IsSemiMagic (subEven M u v w) (t - u - v - w) := by
  have hR0 := row0 M t hM
  have hR1 := row1 M t hM
  have hR2 := row2 M t hM
  have hC0 := col0 M t hM
  have hC1 := col1 M t hM
  have hC2 := col2 M t hM
  constructor
  · intro i
    fin_cases i <;> simp [subEven, rowSum, Fin.sum_univ_three] <;> omega
  · intro j
    fin_cases j <;> simp [subEven, colSum, Fin.sum_univ_three] <;> omega

/-- Each even transversal of the residual has minimum `0`. -/
private lemma subEven_mins (M : Square 3 ℕ) (u v w : ℕ)
    (hu : u ≤ M 0 0) (hu1 : u ≤ M 1 1) (hu2 : u ≤ M 2 2)
    (hv : v ≤ M 0 1) (hv1 : v ≤ M 1 2) (hv2 : v ≤ M 2 0)
    (hw : w ≤ M 0 2) (hw1 : w ≤ M 1 0) (hw2 : w ≤ M 2 1)
    (hDu : min (M 0 0) (min (M 1 1) (M 2 2)) = u)
    (hEv : min (M 0 1) (min (M 1 2) (M 2 0)) = v)
    (hFw : min (M 0 2) (min (M 1 0) (M 2 1)) = w) :
    min ((subEven M u v w) 0 0) (min ((subEven M u v w) 1 1) ((subEven M u v w) 2 2)) = 0 ∧
      min ((subEven M u v w) 0 1) (min ((subEven M u v w) 1 2) ((subEven M u v w) 2 0)) = 0 ∧
        min ((subEven M u v w) 0 2) (min ((subEven M u v w) 1 0) ((subEven M u v w) 2 1)) = 0 := by
  simp [subEven]
  omega

/-- Existence: every semi-magic square admits a normalized representation. -/
private lemma sm3_canonical_exists (M : Square 3 ℕ) (t : ℕ) (hM : IsSemiMagic M t) :
    ∃ u v w x y z : ℕ,
      M = sm3Of u v w x y z ∧ u + v + w + x + y + z = t ∧ min x (min y z) = 0 := by
  let u := min (M 0 0) (min (M 1 1) (M 2 2))
  let v := min (M 0 1) (min (M 1 2) (M 2 0))
  let w := min (M 0 2) (min (M 1 0) (M 2 1))
  have hu : u ≤ M 0 0 := by dsimp [u]; omega
  have hu1 : u ≤ M 1 1 := by dsimp [u]; omega
  have hu2 : u ≤ M 2 2 := by dsimp [u]; omega
  have hv : v ≤ M 0 1 := by dsimp [v]; omega
  have hv1 : v ≤ M 1 2 := by dsimp [v]; omega
  have hv2 : v ≤ M 2 0 := by dsimp [v]; omega
  have hw : w ≤ M 0 2 := by dsimp [w]; omega
  have hw1 : w ≤ M 1 0 := by dsimp [w]; omega
  have hw2 : w ≤ M 2 1 := by dsimp [w]; omega
  let M' := subEven M u v w
  have hM' : IsSemiMagic M' (t - u - v - w) := by
    exact subEven_semiMagic M t u v w hM hu hu1 hu2 hv hv1 hv2 hw hw1 hw2
  have hmins := subEven_mins M u v w hu hu1 hu2 hv hv1 hv2 hw hw1 hw2
    (by rfl) (by rfl) (by rfl)
  rcases sm3_residual M' (t - u - v - w) hM' hmins.1 hmins.2.1 hmins.2.2 with ⟨x, y, z, hM'eq⟩
  have h00 : (subEven M u v w) 0 0 = x := by
    have := congr_fun (congr_fun hM'eq (0 : Fin 3)) (0 : Fin 3)
    simpa [M', sm3Of] using this
  have h01 : (subEven M u v w) 0 1 = z := by
    have := congr_fun (congr_fun hM'eq (0 : Fin 3)) (1 : Fin 3)
    simpa [M', sm3Of] using this
  have h02 : (subEven M u v w) 0 2 = y := by
    have := congr_fun (congr_fun hM'eq (0 : Fin 3)) (2 : Fin 3)
    simpa [M', sm3Of] using this
  have h10 : (subEven M u v w) 1 0 = z := by
    have := congr_fun (congr_fun hM'eq (1 : Fin 3)) (0 : Fin 3)
    simpa [M', sm3Of] using this
  have h11 : (subEven M u v w) 1 1 = y := by
    have := congr_fun (congr_fun hM'eq (1 : Fin 3)) (1 : Fin 3)
    simpa [M', sm3Of] using this
  have h12 : (subEven M u v w) 1 2 = x := by
    have := congr_fun (congr_fun hM'eq (1 : Fin 3)) (2 : Fin 3)
    simpa [M', sm3Of] using this
  have h20 : (subEven M u v w) 2 0 = y := by
    have := congr_fun (congr_fun hM'eq (2 : Fin 3)) (0 : Fin 3)
    simpa [M', sm3Of] using this
  have h21 : (subEven M u v w) 2 1 = x := by
    have := congr_fun (congr_fun hM'eq (2 : Fin 3)) (1 : Fin 3)
    simpa [M', sm3Of] using this
  have h22 : (subEven M u v w) 2 2 = z := by
    have := congr_fun (congr_fun hM'eq (2 : Fin 3)) (2 : Fin 3)
    simpa [M', sm3Of] using this
  simp [subEven] at h00 h01 h02 h10 h11 h12 h20 h21 h22
  refine ⟨u, v, w, x, y, z, ?_, ?_, ?_⟩
  · -- M is the sum of the even part and the residual
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sm3Of] <;> omega
  · -- the six multiplicities sum to the line sum
    have hR0 := row0 M t hM
    omega
  · -- the odd part is normalized
    by_contra hne
    have hxpos : 0 < x := by omega
    have hypos : 0 < y := by omega
    have hzpos : 0 < z := by omega
    have hu_def : u = min (M 0 0) (min (M 1 1) (M 2 2)) := rfl
    omega

/-- The $D$-transversal minimum of a *normalized* combination is the even
multiplicity `u`. -/
private lemma sm3Of_min_D (u v w x y z : ℕ) (hmin : min x (min y z) = 0) :
    min ((sm3Of u v w x y z) 0 0)
      (min ((sm3Of u v w x y z) 1 1) ((sm3Of u v w x y z) 2 2)) = u := by
  simp [sm3Of]
  omega

/-- Likewise for the $E$-transversal and `v`. -/
private lemma sm3Of_min_E (u v w x y z : ℕ) (hmin : min x (min y z) = 0) :
    min ((sm3Of u v w x y z) 0 1)
      (min ((sm3Of u v w x y z) 1 2) ((sm3Of u v w x y z) 2 0)) = v := by
  simp [sm3Of]
  omega

/-- Likewise for the $F$-transversal and `w`. -/
private lemma sm3Of_min_F (u v w x y z : ℕ) (hmin : min x (min y z) = 0) :
    min ((sm3Of u v w x y z) 0 2)
      (min ((sm3Of u v w x y z) 1 0) ((sm3Of u v w x y z) 2 1)) = w := by
  simp [sm3Of]
  omega

/-- Uniqueness: the normalized multiplicities are recovered from the square by
taking the three even-transversal minima and subtracting. -/
private lemma sm3_canonical_unique (M : Square 3 ℕ)
    (u v w x y z u' v' w' x' y' z' : ℕ)
    (hM : M = sm3Of u v w x y z) (hmin : min x (min y z) = 0)
    (hM' : M = sm3Of u' v' w' x' y' z') (hmin' : min x' (min y' z') = 0) :
    u' = u ∧ v' = v ∧ w' = w ∧ x' = x ∧ y' = y ∧ z' = z := by
  have hu : min (M 0 0) (min (M 1 1) (M 2 2)) = u := by
    rw [hM]
    exact sm3Of_min_D u v w x y z hmin
  have hu' : min (M 0 0) (min (M 1 1) (M 2 2)) = u' := by
    rw [hM']
    exact sm3Of_min_D u' v' w' x' y' z' hmin'
  have hv : min (M 0 1) (min (M 1 2) (M 2 0)) = v := by
    rw [hM]
    exact sm3Of_min_E u v w x y z hmin
  have hv' : min (M 0 1) (min (M 1 2) (M 2 0)) = v' := by
    rw [hM']
    exact sm3Of_min_E u' v' w' x' y' z' hmin'
  have hw : min (M 0 2) (min (M 1 0) (M 2 1)) = w := by
    rw [hM]
    exact sm3Of_min_F u v w x y z hmin
  have hw' : min (M 0 2) (min (M 1 0) (M 2 1)) = w' := by
    rw [hM']
    exact sm3Of_min_F u' v' w' x' y' z' hmin'
  have h_u : u' = u := by omega
  have h_v : v' = v := by omega
  have h_w : w' = w := by omega
  -- the odd multiplicities are then read off as differences
  have hx : x = M 0 0 - u := by
    have h00 : M 0 0 = u + x := by
      have := congr_fun (congr_fun hM (0 : Fin 3)) (0 : Fin 3)
      simpa [sm3Of] using this
    omega
  have hx' : x' = M 0 0 - u' := by
    have h00 : M 0 0 = u' + x' := by
      have := congr_fun (congr_fun hM' (0 : Fin 3)) (0 : Fin 3)
      simpa [sm3Of] using this
    omega
  have hy : y = M 1 1 - u := by
    have h11 : M 1 1 = u + y := by
      have := congr_fun (congr_fun hM (1 : Fin 3)) (1 : Fin 3)
      simpa [sm3Of] using this
    omega
  have hy' : y' = M 1 1 - u' := by
    have h11 : M 1 1 = u' + y' := by
      have := congr_fun (congr_fun hM' (1 : Fin 3)) (1 : Fin 3)
      simpa [sm3Of] using this
    omega
  have hz : z = M 2 2 - u := by
    have h22 : M 2 2 = u + z := by
      have := congr_fun (congr_fun hM (2 : Fin 3)) (2 : Fin 3)
      simpa [sm3Of] using this
    omega
  have hz' : z' = M 2 2 - u' := by
    have h22 : M 2 2 = u' + z' := by
      have := congr_fun (congr_fun hM' (2 : Fin 3)) (2 : Fin 3)
      simpa [sm3Of] using this
    omega
  omega

end MagicSquares

open MagicSquares

theorem solution (M : Square 3 ℕ) (t : ℕ) (hM : IsSemiMagic M t) :
    ∃ u v w x y z : ℕ,
      M = sm3Of u v w x y z ∧
        u + v + w + x + y + z = t ∧
          min x (min y z) = 0 ∧
            ∀ u' v' w' x' y' z' : ℕ,
              M = sm3Of u' v' w' x' y' z' →
                min x' (min y' z') = 0 →
                  u' = u ∧ v' = v ∧ w' = w ∧ x' = x ∧ y' = y ∧ z' = z := by
  rcases sm3_canonical_exists M t hM with ⟨u, v, w, x, y, z, hMeq, hsum, hmin⟩
  refine ⟨u, v, w, x, y, z, hMeq, hsum, hmin, ?_⟩
  intro u' v' w' x' y' z' hM' hmin'
  exact sm3_canonical_unique M u v w x y z u' v' w' x' y' z' hMeq hmin hM' hmin'
