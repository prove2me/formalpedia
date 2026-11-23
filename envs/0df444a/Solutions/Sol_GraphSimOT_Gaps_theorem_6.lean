-- Prove2me | solution 1 for GraphSimOT.Gaps.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:06:01.347846+00:00
-- url     : https://prove2.me/submissions/f1debcdf-dde7-4fd9-a7ab-bfb8176913a1

import Mathlib
import Definitions.Def_GraphSimOT_Gaps_Distances

open Matrix GraphSimOT.Gaps

namespace Theorem6Aux

lemma adj_zero_or_one {n : ℕ} (G : SimpleGraph (Fin n)) (v v' : Fin n) :
    adj G v v' = 0 ∨ adj G v v' = 1 := by
  unfold adj
  split_ifs <;> simp

lemma abs_sub_eq_sq_of_zero_one {a b : ℝ} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    |a - b| = a ^ 2 + b ^ 2 - 2 * a * b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

lemma mul_permMatrix_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (σ : Equiv.Perm (Fin n))
    (v w' : Fin n) :
    (A * σ.permMatrix ℝ) v w' = A v (σ.symm w') := by
  simp only [Matrix.mul_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (σ.symm w')]
  · simp
  · intro x _ hx
    have hx' : σ x ≠ w' := fun h => hx (σ.eq_symm_apply.mpr h)
    simp [hx']
  · intro h; exact absurd (Finset.mem_univ _) h

lemma permMatrix_mul_apply {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (σ : Equiv.Perm (Fin n))
    (v w' : Fin n) :
    (σ.permMatrix ℝ * B) v w' = B (σ v) w' := by
  simp only [Matrix.mul_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (σ v)]
  · simp
  · intro b _ hb; simp [hb.symm]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma costEdPerm_eq_frob {n : ℕ} (G H : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n)) :
    costEdPerm G H σ =
      ∑ v : Fin n, ∑ w' : Fin n, (adj G v (σ.symm w') - adj H (σ v) w') ^ 2 := by
  unfold costEdPerm edNorm
  rw [← Fintype.sum_equiv σ (fun v => ∑ j : Fin n, |(permAdj G σ - adj H) (σ v) j|)
        (fun w => ∑ j : Fin n, |(permAdj G σ - adj H) w j|) (fun _ => rfl)]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w' _
  change |adj G (σ.symm (σ v)) (σ.symm w') - adj H (σ v) w'| =
    (adj G v (σ.symm w') - adj H (σ v) w') ^ 2
  rw [Equiv.symm_apply_apply]
  rw [abs_sub_eq_sq_of_zero_one (adj_zero_or_one G v (σ.symm w')) (adj_zero_or_one H (σ v) w')]
  ring

lemma prod_four_sum {n : ℕ} (f : Fin n → Fin n → ℝ) (g1 g2 : Fin n → Fin n → ℝ) :
    (∑ v : Fin n, ∑ w : Fin n, ∑ v' : Fin n, ∑ w' : Fin n, g1 v w * g2 v' w' * f v v') =
      ∑ v : Fin n, ∑ v' : Fin n, f v v' * (∑ w : Fin n, g1 v w) * (∑ w' : Fin n, g2 v' w') := by
  apply Finset.sum_congr rfl; intro v _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro v' _
  calc
    (∑ w : Fin n, ∑ w' : Fin n, g1 v w * g2 v' w' * f v v')
        = ∑ w : Fin n, (f v v' * g1 v w) * (∑ w' : Fin n, g2 v' w') := by
            apply Finset.sum_congr rfl; intro w _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro w' _; ring
    _ = f v v' * (∑ w : Fin n, g1 v w) * (∑ w' : Fin n, g2 v' w') := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]

lemma costEd_eq_frob {n : ℕ} (G H : SimpleGraph (Fin n)) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q ∈ doublyStochastic ℝ (Fin n)) :
    costEd G H Q =
      (∑ v : Fin n, ∑ v' : Fin n, adj G v v' ^ 2) +
      (∑ w : Fin n, ∑ w' : Fin n, adj H w w' ^ 2) -
      2 * ∑ v : Fin n, ∑ w' : Fin n, (adj G * Q) v w' * (Q * adj H) v w' := by
  rw [mem_doublyStochastic_iff_sum] at hQ
  rcases hQ with ⟨hQnn, hQrow, hQcol⟩
  unfold costEd edNorm Bmat disc
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  have hterm : ∀ v w v' w' : Fin n,
      |Q v w * (adj G v v' - adj H w w') * Q v' w'| =
        Q v w * Q v' w' * adj G v v' ^ 2 +
        Q v w * Q v' w' * adj H w w' ^ 2 -
        2 * (adj G v v' * Q v' w') * (Q v w * adj H w w') := by
    intro v w v' w'
    have h1 : |Q v w * (adj G v v' - adj H w w') * Q v' w'| =
        Q v w * Q v' w' * |adj G v v' - adj H w w'| := by
      calc
        |Q v w * (adj G v v' - adj H w w') * Q v' w'|
            = |(Q v w * Q v' w') * (adj G v v' - adj H w w')| := by ring_nf
        _ = |Q v w * Q v' w'| * |adj G v v' - adj H w w'| := abs_mul _ _
        _ = Q v w * Q v' w' * |adj G v v' - adj H w w'| := by
            rw [abs_of_nonneg (mul_nonneg (hQnn v w) (hQnn v' w'))]
    rw [h1, abs_sub_eq_sq_of_zero_one (adj_zero_or_one G v v') (adj_zero_or_one H w w')]
    ring
  simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have ht1 : (∑ x : Fin n, ∑ y : Fin n, ∑ x_1 : Fin n, ∑ y_1 : Fin n,
      Q x y * Q x_1 y_1 * adj G x x_1 ^ 2) =
      ∑ v : Fin n, ∑ v' : Fin n, adj G v v' ^ 2 := by
    rw [prod_four_sum (fun v v' => adj G v v' ^ 2) (fun v w => Q v w) (fun v' w' => Q v' w')]
    apply Finset.sum_congr rfl; intro v _
    apply Finset.sum_congr rfl; intro v' _
    rw [hQrow v, hQrow v', mul_one, mul_one]
  have ht2 : (∑ x : Fin n, ∑ y : Fin n, ∑ x_1 : Fin n, ∑ y_1 : Fin n,
      Q x y * Q x_1 y_1 * adj H y y_1 ^ 2) =
      ∑ w : Fin n, ∑ w' : Fin n, adj H w w' ^ 2 := by
    have hswap : (∑ x : Fin n, ∑ y : Fin n, ∑ x_1 : Fin n, ∑ y_1 : Fin n,
        Q x y * Q x_1 y_1 * adj H y y_1 ^ 2) =
        ∑ w : Fin n, ∑ v : Fin n, ∑ w' : Fin n, ∑ v' : Fin n,
          Q v w * Q v' w' * adj H w w' ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro w _
      apply Finset.sum_congr rfl; intro v _
      exact Finset.sum_comm
    rw [hswap, prod_four_sum (fun w w' => adj H w w' ^ 2) (fun w v => Q v w) (fun w' v' => Q v' w')]
    apply Finset.sum_congr rfl; intro w _
    apply Finset.sum_congr rfl; intro w' _
    rw [hQcol w, hQcol w', mul_one, mul_one]
  have ht3 : (∑ x : Fin n, ∑ y : Fin n, ∑ x_1 : Fin n, ∑ y_1 : Fin n,
      2 * (adj G x x_1 * Q x_1 y_1) * (Q x y * adj H y y_1)) =
      2 * ∑ v : Fin n, ∑ w' : Fin n, (adj G * Q) v w' * (Q * adj H) v w' := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro v _
    rw [Finset.mul_sum]
    calc
      (∑ y : Fin n, ∑ x_1 : Fin n, ∑ y_1 : Fin n,
          2 * (adj G v x_1 * Q x_1 y_1) * (Q v y * adj H y y_1))
          = ∑ y : Fin n, ∑ y_1 : Fin n, ∑ x_1 : Fin n,
              2 * (adj G v x_1 * Q x_1 y_1) * (Q v y * adj H y y_1) := by
              apply Finset.sum_congr rfl; intro y _; exact Finset.sum_comm
      _ = ∑ w' : Fin n, ∑ y : Fin n, ∑ x_1 : Fin n,
            2 * (adj G v x_1 * Q x_1 w') * (Q v y * adj H y w') := Finset.sum_comm
      _ = ∑ w' : Fin n, 2 * ((adj G * Q) v w' * (Q * adj H) v w') := by
            apply Finset.sum_congr rfl; intro w' _
            simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
            apply Finset.sum_congr rfl; intro y _
            apply Finset.sum_congr rfl; intro x_1 _; ring
  rw [ht1, ht2, ht3]

lemma decomp_bound {n : ℕ} (G H : SimpleGraph (Fin n)) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q ∈ doublyStochastic ℝ (Fin n))
    {ι : Type*} [Fintype ι] (lam : ι → ℝ) (π : ι → Equiv.Perm (Fin n))
    (hlam0 : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1)
    (hQeq : Q = ∑ i, lam i • (π i).permMatrix ℝ) :
    ∑ i, lam i * costEdPerm G H (π i) ≤ 2 * costEd G H Q := by
  let X : Fin n → Fin n → ι → ℝ := fun v w' i => adj G v ((π i).symm w')
  let Y : Fin n → Fin n → ι → ℝ := fun v w' i => adj H (π i v) w'
  have hscalar : ∀ (x y : ι → ℝ),
      ∑ i, lam i * (x i - y i) ^ 2 ≤
        2 * (∑ i, lam i * x i ^ 2) + 2 * (∑ i, lam i * y i ^ 2) -
          4 * (∑ i, lam i * x i) * (∑ i, lam i * y i) := by
    intro x y
    set ybar : ℝ := ∑ i, lam i * y i
    have hpt : ∀ i, lam i * (x i - y i) ^ 2 ≤
        lam i * (2 * (x i - ybar) ^ 2 + 2 * (y i - ybar) ^ 2) := by
      intro i
      apply mul_le_mul_of_nonneg_left _ (hlam0 i)
      have hsq : 0 ≤ (x i + y i - 2 * ybar) ^ 2 := sq_nonneg _
      linarith
    calc
      ∑ i, lam i * (x i - y i) ^ 2
          ≤ ∑ i, lam i * (2 * (x i - ybar) ^ 2 + 2 * (y i - ybar) ^ 2) :=
            Finset.sum_le_sum fun i _ => hpt i
      _ = 2 * (∑ i, lam i * x i ^ 2) - 4 * ybar * (∑ i, lam i * x i) +
          4 * ybar ^ 2 * (∑ i, lam i) +
          2 * (∑ i, lam i * y i ^ 2) - 4 * ybar * (∑ i, lam i * y i) := by
            simp only [Finset.mul_sum]
            rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
                ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl; intro i _; ring
      _ = 2 * (∑ i, lam i * x i ^ 2) + 2 * (∑ i, lam i * y i ^ 2) -
          4 * (∑ i, lam i * x i) * (∑ i, lam i * y i) := by
            rw [hlam1]; simp only [ybar]; ring
  have hAQ : ∀ v w' : Fin n, ∑ i : ι, lam i * X v w' i = (adj G * Q) v w' := by
    intro v w'
    have h1 : ∀ i : ι, X v w' i = (adj G * (π i).permMatrix ℝ) v w' := fun i =>
      (mul_permMatrix_apply (adj G) (π i) v w').symm
    simp_rw [h1]
    rw [hQeq, Matrix.mul_sum]
    simp [Matrix.sum_apply]
  have hQB : ∀ v w' : Fin n, ∑ i : ι, lam i * Y v w' i = (Q * adj H) v w' := by
    intro v w'
    have h1 : ∀ i : ι, Y v w' i = ((π i).permMatrix ℝ * adj H) v w' := fun i =>
      (permMatrix_mul_apply (adj H) (π i) v w').symm
    simp_rw [h1]
    rw [hQeq, Matrix.sum_mul]
    simp [Matrix.sum_apply]
  have hLHS : ∑ i : ι, lam i * costEdPerm G H (π i) =
      ∑ v : Fin n, ∑ w' : Fin n, ∑ i : ι, lam i * (X v w' i - Y v w' i) ^ 2 := by
    simp_rw [costEdPerm_eq_frob]
    change ∑ i : ι, lam i * (∑ v : Fin n, ∑ w' : Fin n, (X v w' i - Y v w' i) ^ 2) = _
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro v _; exact Finset.sum_comm
  have hX_sq : (∑ v : Fin n, ∑ w' : Fin n, ∑ i : ι, lam i * X v w' i ^ 2) =
      ∑ v : Fin n, ∑ v' : Fin n, adj G v v' ^ 2 := by
    calc
      _ = ∑ i : ι, lam i * (∑ v : Fin n, ∑ w' : Fin n, X v w' i ^ 2) := by
          calc
            (∑ v : Fin n, ∑ w' : Fin n, ∑ i : ι, lam i * X v w' i ^ 2)
                = ∑ v : Fin n, ∑ i : ι, ∑ w' : Fin n, lam i * X v w' i ^ 2 := by
                    apply Finset.sum_congr rfl; intro v _; exact Finset.sum_comm
            _ = ∑ i : ι, ∑ v : Fin n, ∑ w' : Fin n, lam i * X v w' i ^ 2 := Finset.sum_comm
            _ = _ := by
                  apply Finset.sum_congr rfl; intro i _
                  simp only [Finset.mul_sum]
      _ = ∑ i : ι, lam i * (∑ v : Fin n, ∑ v' : Fin n, adj G v v' ^ 2) := by
          apply Finset.sum_congr rfl; intro i _
          congr 1
          apply Finset.sum_congr rfl; intro v _
          exact Fintype.sum_equiv (π i).symm _ _ (fun _ => rfl)
      _ = (∑ i : ι, lam i) * (∑ v : Fin n, ∑ v' : Fin n, adj G v v' ^ 2) := by
          rw [Finset.sum_mul]
      _ = ∑ v : Fin n, ∑ v' : Fin n, adj G v v' ^ 2 := by rw [hlam1, one_mul]
  have hY_sq : (∑ v : Fin n, ∑ w' : Fin n, ∑ i : ι, lam i * Y v w' i ^ 2) =
      ∑ w : Fin n, ∑ w' : Fin n, adj H w w' ^ 2 := by
    calc
      _ = ∑ i : ι, lam i * (∑ v : Fin n, ∑ w' : Fin n, Y v w' i ^ 2) := by
          calc
            (∑ v : Fin n, ∑ w' : Fin n, ∑ i : ι, lam i * Y v w' i ^ 2)
                = ∑ v : Fin n, ∑ i : ι, ∑ w' : Fin n, lam i * Y v w' i ^ 2 := by
                    apply Finset.sum_congr rfl; intro v _; exact Finset.sum_comm
            _ = ∑ i : ι, ∑ v : Fin n, ∑ w' : Fin n, lam i * Y v w' i ^ 2 := Finset.sum_comm
            _ = _ := by
                  apply Finset.sum_congr rfl; intro i _
                  simp only [Finset.mul_sum]
      _ = ∑ i : ι, lam i * (∑ w : Fin n, ∑ w' : Fin n, adj H w w' ^ 2) := by
          apply Finset.sum_congr rfl; intro i _
          congr 1
          exact Fintype.sum_equiv (π i) _ _ (fun _ => rfl)
      _ = (∑ i : ι, lam i) * (∑ w : Fin n, ∑ w' : Fin n, adj H w w' ^ 2) := by
          rw [Finset.sum_mul]
      _ = ∑ w : Fin n, ∑ w' : Fin n, adj H w w' ^ 2 := by rw [hlam1, one_mul]
  rw [hLHS, costEd_eq_frob G H Q hQ]
  let Z : Fin n → Fin n → ℝ := fun v w' => (adj G * Q) v w' * (Q * adj H) v w'
  change (∑ v : Fin n, ∑ w' : Fin n, ∑ i : ι, lam i * (X v w' i - Y v w' i) ^ 2) ≤
    2 * ((∑ v : Fin n, ∑ v' : Fin n, adj G v v' ^ 2) +
         (∑ w : Fin n, ∑ w' : Fin n, adj H w w' ^ 2) -
         2 * ∑ v : Fin n, ∑ w' : Fin n, Z v w')
  rw [← hX_sq, ← hY_sq]
  calc
    (∑ v : Fin n, ∑ w' : Fin n, ∑ i : ι, lam i * (X v w' i - Y v w' i) ^ 2)
        ≤ ∑ v : Fin n, ∑ w' : Fin n,
            (2 * (∑ i : ι, lam i * X v w' i ^ 2) +
             2 * (∑ i : ι, lam i * Y v w' i ^ 2) -
             4 * Z v w') := by
          apply Finset.sum_le_sum; intro v _
          apply Finset.sum_le_sum; intro w' _
          have hs := hscalar (X v w') (Y v w')
          rw [hAQ v w', hQB v w'] at hs
          simpa only [Z, mul_assoc] using hs
    _ = 2 * ((∑ v : Fin n, ∑ w' : Fin n, ∑ i : ι, lam i * X v w' i ^ 2) +
             (∑ v : Fin n, ∑ w' : Fin n, ∑ i : ι, lam i * Y v w' i ^ 2) -
             2 * ∑ v : Fin n, ∑ w' : Fin n, Z v w') := by
          simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
          ring

lemma part2 (n : ℕ) (G H : SimpleGraph (Fin n)) : dEd G H ≤ 2 * dOTEd G H := by
  rw [← div_le_iff₀' (by norm_num : (0 : ℝ) < 2)]
  unfold dOTEd
  have hne : ((doublyStochastic ℝ (Fin n) : Set (Matrix (Fin n) (Fin n) ℝ))).Nonempty :=
    ⟨1, Submonoid.one_mem _⟩
  apply le_csInf (hne.image _)
  rintro _ ⟨Q, hQ, rfl⟩
  rw [div_le_iff₀' (by norm_num : (0 : ℝ) < 2)]
  have hconv : Q ∈ convexHull ℝ {x : Matrix (Fin n) (Fin n) ℝ | ∃ σ : Equiv.Perm (Fin n), σ.permMatrix ℝ = x} := by
    rw [← doublyStochastic_eq_convexHull_permMatrix]
    exact hQ
  rw [mem_convexHull_iff_exists_fintype] at hconv
  rcases hconv with ⟨ι, instFintype, w, z, hw0, hw1, hz, hQeq⟩
  choose π hπ using hz
  have hQeq' : Q = ∑ i : ι, w i • (π i).permMatrix ℝ := by
    rw [← hQeq]
    apply Finset.sum_congr rfl; intro i _
    rw [hπ i]
  have hd : dEd G H ≤ ∑ i : ι, w i * costEdPerm G H (π i) := by
    calc
      dEd G H = (∑ i : ι, w i) * dEd G H := by rw [hw1, one_mul]
      _ = ∑ i : ι, w i * dEd G H := Finset.sum_mul _ _ _
      _ ≤ ∑ i : ι, w i * costEdPerm G H (π i) := by
          apply Finset.sum_le_sum; intro i _
          exact mul_le_mul_of_nonneg_left (Finset.inf'_le _ (Finset.mem_univ (π i))) (hw0 i)
  exact hd.trans (decomp_bound G H Q hQ w π hw0 hw1 hQeq')

end Theorem6Aux

theorem solution :
    (∀ (n : ℕ) (G H : SimpleGraph (Fin n)) (Q : Matrix (Fin n) (Fin n) ℝ),
      Q ∈ doublyStochastic ℝ (Fin n) →
      ∀ (m : ℕ) (lam : Fin m → ℝ) (π : Fin m → Equiv.Perm (Fin n)),
        (∀ i, 0 < lam i) → ∑ i, lam i = 1 → Q = ∑ i, lam i • (π i).permMatrix ℝ →
        ∑ i, lam i * costEdPerm G H (π i) ≤ 2 * costEd G H Q) ∧
    (∀ (n : ℕ) (G H : SimpleGraph (Fin n)), dEd G H ≤ 2 * dOTEd G H) :=
  ⟨fun _ G H Q hQ _ lam π hlam0 hlam1 hQeq =>
    Theorem6Aux.decomp_bound G H Q hQ lam π (fun i => (hlam0 i).le) hlam1 hQeq,
   Theorem6Aux.part2⟩
