-- Prove2me | solution 1 for GlobalSinkhorn.column_error_of_potential
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-14T13:35:32.576391+00:00
-- url     : https://prove2.me/submissions/97d0ae20-ec44-44af-96dd-c737e393ad85

import Definitions.Def_GlobalSinkhorn_potential
import Definitions.Def_GlobalSinkhorn_Mw
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

open Matrix GlobalSinkhorn
open scoped BigOperators

private lemma potential_div {n : ℕ} (w : Fin n → ℝ) (c : ℝ) (hc : c ≠ 0) :
    potential (fun i => w i / c) = potential w := by
  have ha : avg (fun i => (w i/c)^2) = avg (fun i => w i^2) / c^2 := by
    unfold avg
    simp_rw [div_pow]
    rw [← Finset.sum_div]
    ring
  have hb : avg (fun i => (w i/c)⁻¹^2) = c^2 * avg (fun i => (w i)⁻¹^2) := by
    unfold avg
    simp_rw [inv_div, div_pow, div_eq_mul_inv, inv_pow]
    rw [← Finset.mul_sum]
    ring
  simp only [potential, ha, hb]
  field_simp

private lemma normalized_variance {n : ℕ} (hn : (0 : ℝ) < n) (v : Fin n → ℝ)
    (hv : ∀ i, 0 < v i) (hs : ∑ i, v i = n) :
    ∑ i, (v i-1)^2 ≤ (n : ℝ) * potential v := by
  have hi (i : Fin n) : 2-v i ≤ (v i)⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (hv i)).mpr
    nlinarith [sq_nonneg (v i-1)]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hi i)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [hs] at hsum
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
    (fun _ => (1 : ℝ)) (fun i => (v i)⁻¹)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hCS
  have hsum0 : (0 : ℝ) ≤ ∑ i, (v i)⁻¹ := Finset.sum_nonneg (fun i _ => (inv_pos.mpr (hv i)).le)
  have hinv : (n : ℝ) ≤ ∑ i, (v i)⁻¹^2 := by nlinarith
  have hnonneg : 0 ≤ ∑ i, (v i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hinv hnonneg
  have hexpand : ∑ i, (v i-1)^2 = (∑ i, (v i)^2)-(n : ℝ) := by
    simp_rw [sub_sq]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      one_pow, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum, hs]
    ring
  have heq : (n : ℝ)*potential v = (∑ i, v i^2)*(∑ i, (v i)⁻¹^2)/(n : ℝ)-(n : ℝ) := by
    unfold potential avg
    field_simp [hn.ne']
    <;> ring
  rw [hexpand, heq]
  have := (le_div_iff₀ hn).mpr hmul
  linarith

theorem solution {n : ℕ} (hn : 2 ≤ n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S ∈ doublyStochastic ℝ (Fin n)) (w : Fin n → ℝ) (hw : ∀ j, 0 < w j)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hΦ : potential w ≤ ε ^ 2 / (16 * (n : ℝ) ^ 3)) (j : Fin n) :
    |∑ i, Mw S w i j - 1| ≤ ε / n := by
  letI : NeZero n := ⟨by omega⟩
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0 : ℝ) < n := by linarith
  let c := avg w
  have hsumw : 0 < ∑ i, w i := Finset.sum_pos (fun i _ => hw i)
    (by simpa using (Finset.univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty))
  have hc : 0 < c := div_pos hsumw hnp
  let v : Fin n → ℝ := fun i => w i/c
  have hv : ∀ i, 0 < v i := fun i => div_pos (hw i) hc
  have hsumv : ∑ i, v i = n := by
    dsimp [v,c,avg]
    rw [← Finset.sum_div]
    field_simp
  have hpot : potential v = potential w := potential_div w c hc.ne'
  have hvar := normalized_variance hnp v hv hsumv
  rw [hpot] at hvar
  let δ : ℝ := ε/(4*(n : ℝ))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδ14 : δ ≤ 1/4 := by
    dsimp [δ]
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hpoint : ∀ i, |v i-1| ≤ δ := by
    intro i
    have hs : (v i-1)^2 ≤ ∑ k, (v k-1)^2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg (v k-1)) (Finset.mem_univ i)
    have hΦ' := mul_le_mul_of_nonneg_left hΦ hnp.le
    have heq : (n : ℝ)*(ε^2/(16*(n : ℝ)^3)) = δ^2 := by dsimp [δ]; field_simp <;> ring
    rw [heq] at hΦ'
    have hsq := hs.trans (hvar.trans hΦ')
    nlinarith [sq_abs (v i-1), abs_nonneg (v i-1)]
  have hrow : ∀ i, 1-δ ≤ (S *ᵥ v) i ∧ (S *ᵥ v) i ≤ 1+δ := by
    intro i
    have lo := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin n))) =>
      mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp (hpoint k)).1] : 1-δ ≤ v k)
        (nonneg_of_mem_doublyStochastic hS : 0 ≤ S i k))
    have up := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin n))) =>
      mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp (hpoint k)).2] : v k ≤ 1+δ)
        (nonneg_of_mem_doublyStochastic hS : 0 ≤ S i k))
    simp only [← Finset.sum_mul, sum_row_of_mem_doublyStochastic hS i, one_mul] at lo up
    exact ⟨lo,up⟩
  have hrowp : ∀ i, 0 < (S *ᵥ v) i := by intro i; have := (hrow i).1; linarith
  have hSw : ∀ i, (S *ᵥ w) i = c*(S *ᵥ v) i := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [v]
    field_simp
    <;> ring
  have hentry : ∀ i, Mw S w i j = S i j * (v j / (S *ᵥ v) i) := by
    intro i
    simp only [Mw, Matrix.diagonal_mul, Matrix.mul_diagonal, hSw i]
    dsimp [v]
    field_simp [(hrowp i).ne', hc.ne']
    <;> ring
  have hratio : ∀ i, |v j / (S *ᵥ v) i-1| ≤ ε/n := by
    intro i
    have hlo := (hrow i).1
    have hup := (hrow i).2
    have hp := abs_le.mp (hpoint j)
    have hs : (1/2 : ℝ) ≤ (S *ᵥ v) i := by linarith
    have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 4*δ)
    have hfour : 4*δ = ε/(n : ℝ) := by dsimp [δ]; ring
    rw [← hfour]
    apply abs_le.mpr
    constructor
    · rw [le_sub_iff_add_le, le_div_iff₀ (hrowp i)]
      nlinarith
    · rw [sub_le_iff_le_add, div_le_iff₀ (hrowp i)]
      nlinarith
  have hsum : ∑ i, Mw S w i j-1 = ∑ i, S i j * (v j/(S *ᵥ v) i-1) := by
    simp_rw [mul_sub, mul_one]
    rw [Finset.sum_sub_distrib]
    simp only [mul_one, sum_col_of_mem_doublyStochastic hS j, hentry]
  rw [hsum]
  calc
    _ ≤ ∑ i, |S i j*(v j/(S *ᵥ v) i-1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, S i j*(ε/n) := Finset.sum_le_sum (fun i _ => by
      rw [abs_mul, abs_of_nonneg (nonneg_of_mem_doublyStochastic hS)]
      exact mul_le_mul_of_nonneg_left (hratio i) (nonneg_of_mem_doublyStochastic hS))
    _ = ε/n := by rw [← Finset.sum_mul, sum_col_of_mem_doublyStochastic hS j, one_mul]

#print axioms solution
