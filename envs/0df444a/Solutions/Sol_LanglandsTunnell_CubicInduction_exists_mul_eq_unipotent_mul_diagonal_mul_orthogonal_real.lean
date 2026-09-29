-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_mul_eq_unipotent_mul_diagonal_mul_orthogonal_real
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/88cc62bb-fe11-52c2-9b20-be2ee389ade6

import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Abel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_mul_eq_unipotent_mul_diagonal_mul_orthogonal_real

set_option autoImplicit false

open Matrix

noncomputable section

namespace HermiteThree

private def nsq (v : Fin 3 → ℝ) : ℝ := v ⬝ᵥ v

private theorem dot3 (v w : Fin 3 → ℝ) : v ⬝ᵥ w = v 0 * w 0 + v 1 * w 1 + v 2 * w 2 := by
  simp [dotProduct, Fin.sum_univ_three]

private theorem nsq_eq (v : Fin 3 → ℝ) : nsq v = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  rw [nsq, dot3]; ring

private theorem nsq_nonneg (v : Fin 3 → ℝ) : 0 ≤ nsq v := by
  rw [nsq_eq]; positivity

private theorem sq_le_nsq (v : Fin 3 → ℝ) (i : Fin 3) : v i ^ 2 ≤ nsq v := by
  rw [nsq_eq]
  fin_cases i
  · show v 0 ^ 2 ≤ _; nlinarith [sq_nonneg (v 1), sq_nonneg (v 2)]
  · show v 1 ^ 2 ≤ _; nlinarith [sq_nonneg (v 0), sq_nonneg (v 2)]
  · show v 2 ^ 2 ≤ _; nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

private theorem abs_le_sqrt_nsq (v : Fin 3 → ℝ) (i : Fin 3) : |v i| ≤ Real.sqrt (nsq v) :=
  Real.abs_le_sqrt (sq_le_nsq v i)

private theorem eq_zero_of_nsq_eq_zero {v : Fin 3 → ℝ} (h : nsq v = 0) : v = 0 := by
  rw [nsq_eq] at h
  have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  have h2 : v 2 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

private theorem nsq_pos {v : Fin 3 → ℝ} (hv : v ≠ 0) : 0 < nsq v :=
  lt_of_le_of_ne (nsq_nonneg v) fun h => hv (eq_zero_of_nsq_eq_zero h.symm)

private theorem nsq_add (v w : Fin 3 → ℝ) : nsq (v + w) = nsq v + 2 * (v ⬝ᵥ w) + nsq w := by
  simp only [nsq_eq, dot3, Pi.add_apply]; ring

private theorem nsq_sub (v w : Fin 3 → ℝ) : nsq (v - w) = nsq v - 2 * (v ⬝ᵥ w) + nsq w := by
  simp only [nsq_eq, dot3, Pi.sub_apply]; ring

section Lattice

variable (M B : Matrix (Fin 3) (Fin 3) ℝ)

private def latVec (a : Fin 3 → ℤ) : Fin 3 → ℝ := (fun i => (a i : ℝ)) ᵥ* M

private def latLen (a : Fin 3 → ℤ) : ℝ := nsq (latVec M a)

private theorem latVec_add (a b : Fin 3 → ℤ) : latVec M (a + b) = latVec M a + latVec M b := by
  have h : (fun i => ((a + b) i : ℝ)) = (fun i => (a i : ℝ)) + fun i => (b i : ℝ) := by
    funext i; simp
  unfold latVec; rw [h, Matrix.add_vecMul]

private theorem latVec_sub (a b : Fin 3 → ℤ) : latVec M (a - b) = latVec M a - latVec M b := by
  have h : (fun i => ((a - b) i : ℝ)) = (fun i => (a i : ℝ)) - fun i => (b i : ℝ) := by
    funext i; simp
  unfold latVec; rw [h, Matrix.sub_vecMul]

private theorem latVec_zsmul (m : ℤ) (a : Fin 3 → ℤ) : latVec M (m • a) = (m : ℝ) • latVec M a := by
  have h : (fun i => ((m • a) i : ℝ)) = (m : ℝ) • fun i => (a i : ℝ) := by
    funext i; simp
  unfold latVec; rw [h, Matrix.smul_vecMul]

private theorem row_map_mul (γ : GL (Fin 3) ℤ) (Mg : GL (Fin 3) ℝ) (i : Fin 3) :
    ((Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) γ * Mg : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) i =
      latVec (Mg : Matrix (Fin 3) (Fin 3) ℝ) ((γ : Matrix (Fin 3) (Fin 3) ℤ) i) := by
  funext j
  rfl

variable {M B}

private theorem abs_cast_le (hMB : M * B = 1) (a : Fin 3 → ℤ) (j : Fin 3) :
    |(a j : ℝ)| ≤ 3 * (∑ i, ∑ l, |B i l|) * Real.sqrt (latLen M a) := by
  have hrec : (fun i => (a i : ℝ)) = latVec M a ᵥ* B := by
    rw [latVec, Matrix.vecMul_vecMul, hMB, Matrix.vecMul_one]
  have hj : (a j : ℝ) = ∑ i, latVec M a i * B i j := by
    have h := congrFun hrec j
    simpa [Matrix.vecMul, dotProduct] using h
  have hB : ∀ i, |B i j| ≤ ∑ i, ∑ l, |B i l| := fun i =>
    calc |B i j| ≤ ∑ l, |B i l| := Finset.single_le_sum (fun l _ => abs_nonneg (B i l)) (Finset.mem_univ j)
      _ ≤ ∑ i, ∑ l, |B i l| :=
        Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun l _ => abs_nonneg (B i l)) (Finset.mem_univ i)
  have hv : ∀ i, |latVec M a i| ≤ Real.sqrt (latLen M a) := fun i => abs_le_sqrt_nsq _ i
  rw [hj]
  calc |∑ i, latVec M a i * B i j| ≤ ∑ i, |latVec M a i * B i j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |latVec M a i| * |B i j| := by simp_rw [abs_mul]
    _ ≤ ∑ _i : Fin 3, Real.sqrt (latLen M a) * ∑ i, ∑ l, |B i l| :=
        Finset.sum_le_sum fun i _ => mul_le_mul (hv i) (hB i) (abs_nonneg _) (Real.sqrt_nonneg _)
    _ = 3 * (∑ i, ∑ l, |B i l|) * Real.sqrt (latLen M a) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring

private theorem finite_sublevel (hMB : M * B = 1) (R : ℝ) : {a : Fin 3 → ℤ | latLen M a ≤ R}.Finite := by
  have hK : 0 ≤ ∑ i, ∑ l, |B i l| := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun l _ => abs_nonneg _
  refine (Set.Finite.pi (t := fun _ : Fin 3 => Set.Icc (-⌈3 * (∑ i, ∑ l, |B i l|) * Real.sqrt R⌉)
    ⌈3 * (∑ i, ∑ l, |B i l|) * Real.sqrt R⌉) fun _ => Set.finite_Icc _ _).subset ?_
  intro a ha
  rw [Set.mem_univ_pi]
  intro j
  have h1 : |(a j : ℝ)| ≤ 3 * (∑ i, ∑ l, |B i l|) * Real.sqrt R :=
    (abs_cast_le hMB a j).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ha) (by positivity))
  have h2 : |(a j : ℝ)| ≤ ((⌈3 * (∑ i, ∑ l, |B i l|) * Real.sqrt R⌉ : ℤ) : ℝ) := h1.trans (Int.le_ceil _)
  have h3 : |a j| ≤ ⌈3 * (∑ i, ∑ l, |B i l|) * Real.sqrt R⌉ := by exact_mod_cast h2
  exact abs_le.mp h3

private theorem exists_min (hMB : M * B = 1) (P : (Fin 3 → ℤ) → Prop) {a₀ : Fin 3 → ℤ} (h₀ : P a₀) :
    ∃ a, P a ∧ ∀ b, P b → latLen M a ≤ latLen M b := by
  classical
  have hfin : {a | P a ∧ latLen M a ≤ latLen M a₀}.Finite :=
    (finite_sublevel hMB (latLen M a₀)).subset fun a ha => ha.2
  obtain ⟨a, ha, hmin⟩ :=
    hfin.toFinset.exists_min_image (latLen M) ⟨a₀, hfin.mem_toFinset.mpr ⟨h₀, le_rfl⟩⟩
  rw [Set.Finite.mem_toFinset] at ha
  refine ⟨a, ha.1, fun b hb => ?_⟩
  by_cases hle : latLen M b ≤ latLen M a₀
  · exact hmin b (hfin.mem_toFinset.mpr ⟨hb, hle⟩)
  · exact ha.2.trans (not_le.mp hle).le

end Lattice

private def sh01 (m : ℤ) : GL (Fin 3) ℤ where
  val := !![1, m, 0; 0, 1, 0; 0, 0, 1]
  inv := !![1, -m, 0; 0, 1, 0; 0, 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private def sh02 (m : ℤ) : GL (Fin 3) ℤ where
  val := !![1, 0, m; 0, 1, 0; 0, 0, 1]
  inv := !![1, 0, -m; 0, 1, 0; 0, 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private def sh12 (m : ℤ) : GL (Fin 3) ℤ where
  val := !![1, 0, 0; 0, 1, m; 0, 0, 1]
  inv := !![1, 0, 0; 0, 1, -m; 0, 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private def sw01 : GL (Fin 3) ℤ where
  val := !![0, 1, 0; 1, 0, 0; 0, 0, 1]
  inv := !![0, 1, 0; 1, 0, 0; 0, 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private def sw12 : GL (Fin 3) ℤ where
  val := !![1, 0, 0; 0, 0, 1; 0, 1, 0]
  inv := !![1, 0, 0; 0, 0, 1; 0, 1, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

section Rows

variable (γ : GL (Fin 3) ℤ) (m : ℤ)

private theorem sh01_row0 : ((sh01 m * γ : GL (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) 0 =
    (γ : Matrix (Fin 3) (Fin 3) ℤ) 0 + m • (γ : Matrix (Fin 3) (Fin 3) ℤ) 1 := by
  funext j; simp [sh01, Matrix.mul_apply, Fin.sum_univ_three]

private theorem sh01_row1 :
    ((sh01 m * γ : GL (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) 1 = (γ : Matrix (Fin 3) (Fin 3) ℤ) 1 := by
  funext j; simp [sh01, Matrix.mul_apply, Fin.sum_univ_three]

private theorem sh01_row2 :
    ((sh01 m * γ : GL (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) 2 = (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 := by
  funext j; simp [sh01, Matrix.mul_apply, Fin.sum_univ_three]

private theorem sh02_row0 : ((sh02 m * γ : GL (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) 0 =
    (γ : Matrix (Fin 3) (Fin 3) ℤ) 0 + m • (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 := by
  funext j; simp [sh02, Matrix.mul_apply, Fin.sum_univ_three]

private theorem sh02_row1 :
    ((sh02 m * γ : GL (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) 1 = (γ : Matrix (Fin 3) (Fin 3) ℤ) 1 := by
  funext j; simp [sh02, Matrix.mul_apply, Fin.sum_univ_three]

private theorem sh02_row2 :
    ((sh02 m * γ : GL (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) 2 = (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 := by
  funext j; simp [sh02, Matrix.mul_apply, Fin.sum_univ_three]

private theorem sh12_row1 : ((sh12 m * γ : GL (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) 1 =
    (γ : Matrix (Fin 3) (Fin 3) ℤ) 1 + m • (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 := by
  funext j; simp [sh12, Matrix.mul_apply, Fin.sum_univ_three]

private theorem sh12_row2 :
    ((sh12 m * γ : GL (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) 2 = (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 := by
  funext j; simp [sh12, Matrix.mul_apply, Fin.sum_univ_three]

private theorem sw01_row1 :
    ((sw01 * γ : GL (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) 1 = (γ : Matrix (Fin 3) (Fin 3) ℤ) 0 := by
  funext j; simp [sw01, Matrix.mul_apply, Fin.sum_univ_three]

private theorem sw01_row2 :
    ((sw01 * γ : GL (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) 2 = (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 := by
  funext j; simp [sw01, Matrix.mul_apply, Fin.sum_univ_three]

private theorem sw12_row2 :
    ((sw12 * γ : GL (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) 2 = (γ : Matrix (Fin 3) (Fin 3) ℤ) 1 := by
  funext j; simp [sw12, Matrix.mul_apply, Fin.sum_univ_three]

end Rows

section GramSchmidt

variable (N : Matrix (Fin 3) (Fin 3) ℝ)

private def q2 : ℝ := nsq (N 2)

private def c12 : ℝ := (N 1 ⬝ᵥ N 2) / q2 N

private def u1 : Fin 3 → ℝ := N 1 - c12 N • N 2

private def q1 : ℝ := nsq (u1 N)

private def c02 : ℝ := (N 0 ⬝ᵥ N 2) / q2 N

private def c01 : ℝ := (N 0 ⬝ᵥ u1 N) / q1 N

private def u0 : Fin 3 → ℝ := N 0 - c02 N • N 2 - c01 N • u1 N

private def q0 : ℝ := nsq (u0 N)

private def nU : Matrix (Fin 3) (Fin 3) ℝ := !![1, c01 N, c02 N; 0, 1, c12 N; 0, 0, 1]

private def tD : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.sqrt (q0 N), 0, 0; 0, Real.sqrt (q1 N), 0; 0, 0, Real.sqrt (q2 N)]

private def kO : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(Real.sqrt (q0 N))⁻¹ * u0 N 0, (Real.sqrt (q0 N))⁻¹ * u0 N 1, (Real.sqrt (q0 N))⁻¹ * u0 N 2;
     (Real.sqrt (q1 N))⁻¹ * u1 N 0, (Real.sqrt (q1 N))⁻¹ * u1 N 1, (Real.sqrt (q1 N))⁻¹ * u1 N 2;
     (Real.sqrt (q2 N))⁻¹ * N 2 0, (Real.sqrt (q2 N))⁻¹ * N 2 1, (Real.sqrt (q2 N))⁻¹ * N 2 2]

private def uM : Matrix (Fin 3) (Fin 3) ℝ := !![u0 N 0, u0 N 1, u0 N 2; u1 N 0, u1 N 1, u1 N 2; N 2 0, N 2 1, N 2 2]

variable {N}

private theorem q2_pos (hN : N.det ≠ 0) : 0 < q2 N := by
  refine nsq_pos fun h => hN (Matrix.det_eq_zero_of_row_eq_zero 2 fun j => ?_)
  rw [h]; rfl

private theorem u1_dot_row2 (hN : N.det ≠ 0) : u1 N ⬝ᵥ N 2 = 0 := by
  have hq : q2 N ≠ 0 := (q2_pos hN).ne'
  rw [u1, sub_dotProduct, smul_dotProduct, smul_eq_mul, c12, show N 2 ⬝ᵥ N 2 = q2 N from rfl,
    div_mul_cancel₀ _ hq]
  exact sub_self _

private theorem row1_eq : N 1 = u1 N + c12 N • N 2 := by
  rw [u1, sub_add_cancel]

private theorem q1_pos (hN : N.det ≠ 0) : 0 < q1 N := by
  refine nsq_pos fun h => hN ?_
  have hdet := Matrix.det_updateRow_add_smul_self N (show (1 : Fin 3) ≠ 2 by decide) (-c12 N)
  have hrow : N 1 + -c12 N • N 2 = u1 N := by rw [u1, neg_smul, sub_eq_add_neg]
  rw [hrow, h] at hdet
  rw [← hdet]
  exact Matrix.det_eq_zero_of_row_eq_zero 1 fun j => by simp [Matrix.updateRow_self]

private theorem row1_dot_u1 (hN : N.det ≠ 0) : N 1 ⬝ᵥ u1 N = q1 N := by
  conv_lhs => rw [row1_eq (N := N)]
  rw [add_dotProduct, smul_dotProduct, smul_eq_mul, dotProduct_comm (N 2), u1_dot_row2 hN, mul_zero, add_zero]
  rfl

private theorem row2_dot_u1 (hN : N.det ≠ 0) : N 2 ⬝ᵥ u1 N = 0 := by
  rw [dotProduct_comm, u1_dot_row2 hN]

private theorem u0_dot_row2 (hN : N.det ≠ 0) : u0 N ⬝ᵥ N 2 = 0 := by
  have hq : q2 N ≠ 0 := (q2_pos hN).ne'
  rw [u0, sub_dotProduct, sub_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul,
    u1_dot_row2 hN, mul_zero, sub_zero, c02, show N 2 ⬝ᵥ N 2 = q2 N from rfl, div_mul_cancel₀ _ hq]
  exact sub_self _

private theorem u0_dot_u1 (hN : N.det ≠ 0) : u0 N ⬝ᵥ u1 N = 0 := by
  have hq : q1 N ≠ 0 := (q1_pos hN).ne'
  rw [u0, sub_dotProduct, sub_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul,
    row2_dot_u1 hN, mul_zero, sub_zero, c01, show u1 N ⬝ᵥ u1 N = q1 N from rfl, div_mul_cancel₀ _ hq]
  exact sub_self _

private theorem row0_eq : N 0 = u0 N + c01 N • u1 N + c02 N • N 2 := by
  rw [u0]; abel

private theorem q0_pos (hN : N.det ≠ 0) : 0 < q0 N := by
  refine nsq_pos fun h => hN ?_

  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  set N' := N.updateRow 0 (N 0 + -c01 N • N 1) with hN'
  have hdet' : N'.det = N.det := Matrix.det_updateRow_add_smul_self N h01 _
  have hN'0 : N' 0 = N 0 + -c01 N • N 1 := by rw [hN', Matrix.updateRow_self]
  have hN'1 : N' 1 = N 1 := by rw [hN', Matrix.updateRow_ne (by decide)]
  have hN'2 : N' 2 = N 2 := by rw [hN', Matrix.updateRow_ne (by decide)]
  set N'' := N'.updateRow 0 (N' 0 + (c01 N * c12 N - c02 N) • N' 2) with hN''
  have hdet'' : N''.det = N'.det := Matrix.det_updateRow_add_smul_self N' h02 _
  have hN''0 : N'' 0 = u0 N := by
    rw [hN'', Matrix.updateRow_self, hN'0, hN'2, u0, u1]
    funext j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, neg_mul]
    ring
  rw [← hdet', ← hdet'']
  exact Matrix.det_eq_zero_of_row_eq_zero 0 fun j => by rw [hN''0, h]; rfl

private theorem tD_mul_kO (hN : N.det ≠ 0) : tD N * kO N = uM N := by
  have h0 : Real.sqrt (q0 N) ≠ 0 := (Real.sqrt_pos.mpr (q0_pos hN)).ne'
  have h1 : Real.sqrt (q1 N) ≠ 0 := (Real.sqrt_pos.mpr (q1_pos hN)).ne'
  have h2 : Real.sqrt (q2 N) ≠ 0 := (Real.sqrt_pos.mpr (q2_pos hN)).ne'
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tD, kO, uM, Matrix.mul_apply, Fin.sum_univ_three, h0, h1, h2]

private theorem nU_mul_uM : nU N * uM N = N := by
  have e0 : ∀ j, N 0 j = u0 N j + c01 N * u1 N j + c02 N * N 2 j := fun j => by
    have := congrFun (row0_eq (N := N)) j
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
  have e1 : ∀ j, N 1 j = u1 N j + c12 N * N 2 j := fun j => by
    have := congrFun (row1_eq (N := N)) j
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nU, uM, Matrix.mul_apply, Fin.sum_univ_three] <;>
    linarith [e0 0, e0 1, e0 2, e1 0, e1 1, e1 2]

private theorem nU_mul_tD_mul_kO (hN : N.det ≠ 0) : nU N * tD N * kO N = N := by
  rw [Matrix.mul_assoc, tD_mul_kO hN, nU_mul_uM]

private theorem kO_mul_kO_transpose (hN : N.det ≠ 0) : kO N * (kO N)ᵀ = 1 := by
  have hq0 := q0_pos hN
  have hq1 := q1_pos hN
  have hq2 := q2_pos hN
  have h0 : Real.sqrt (q0 N) ≠ 0 := (Real.sqrt_pos.mpr hq0).ne'
  have h1 : Real.sqrt (q1 N) ≠ 0 := (Real.sqrt_pos.mpr hq1).ne'
  have h2 : Real.sqrt (q2 N) ≠ 0 := (Real.sqrt_pos.mpr hq2).ne'
  have s0 : u0 N 0 ^ 2 + u0 N 1 ^ 2 + u0 N 2 ^ 2 = Real.sqrt (q0 N) ^ 2 := by
    rw [Real.sq_sqrt hq0.le, q0, nsq_eq]
  have s1 : u1 N 0 ^ 2 + u1 N 1 ^ 2 + u1 N 2 ^ 2 = Real.sqrt (q1 N) ^ 2 := by
    rw [Real.sq_sqrt hq1.le, q1, nsq_eq]
  have s2 : N 2 0 ^ 2 + N 2 1 ^ 2 + N 2 2 ^ 2 = Real.sqrt (q2 N) ^ 2 := by
    rw [Real.sq_sqrt hq2.le, q2, nsq_eq]
  have k0 : (Real.sqrt (q0 N))⁻¹ * (Real.sqrt (q0 N))⁻¹ * Real.sqrt (q0 N) ^ 2 = 1 := by
    field_simp
  have k1 : (Real.sqrt (q1 N))⁻¹ * (Real.sqrt (q1 N))⁻¹ * Real.sqrt (q1 N) ^ 2 = 1 := by
    field_simp
  have k2 : (Real.sqrt (q2 N))⁻¹ * (Real.sqrt (q2 N))⁻¹ * Real.sqrt (q2 N) ^ 2 = 1 := by
    field_simp
  have o01 : u0 N 0 * u1 N 0 + u0 N 1 * u1 N 1 + u0 N 2 * u1 N 2 = 0 := by
    rw [← dot3]; exact u0_dot_u1 hN
  have o02 : u0 N 0 * N 2 0 + u0 N 1 * N 2 1 + u0 N 2 * N 2 2 = 0 := by
    rw [← dot3]; exact u0_dot_row2 hN
  have o12 : u1 N 0 * N 2 0 + u1 N 1 * N 2 1 + u1 N 2 * N 2 2 = 0 := by
    rw [← dot3]; exact u1_dot_row2 hN
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kO, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]
  · linear_combination (Real.sqrt (q0 N))⁻¹ * (Real.sqrt (q0 N))⁻¹ * s0 + k0
  · linear_combination (Real.sqrt (q0 N))⁻¹ * (Real.sqrt (q1 N))⁻¹ * o01
  · linear_combination (Real.sqrt (q0 N))⁻¹ * (Real.sqrt (q2 N))⁻¹ * o02
  · linear_combination (Real.sqrt (q0 N))⁻¹ * (Real.sqrt (q1 N))⁻¹ * o01
  · linear_combination (Real.sqrt (q1 N))⁻¹ * (Real.sqrt (q1 N))⁻¹ * s1 + k1
  · linear_combination (Real.sqrt (q1 N))⁻¹ * (Real.sqrt (q2 N))⁻¹ * o12
  · linear_combination (Real.sqrt (q0 N))⁻¹ * (Real.sqrt (q2 N))⁻¹ * o02
  · linear_combination (Real.sqrt (q1 N))⁻¹ * (Real.sqrt (q2 N))⁻¹ * o12
  · linear_combination (Real.sqrt (q2 N))⁻¹ * (Real.sqrt (q2 N))⁻¹ * s2 + k2

private theorem kO_transpose_mul_kO (hN : N.det ≠ 0) : (kO N)ᵀ * kO N = 1 := by
  have h := kO_mul_kO_transpose hN
  rw [← Matrix.inv_eq_right_inv h]
  exact Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_right_inverse h)

private theorem nsq_row1 (hN : N.det ≠ 0) : nsq (N 1) = q1 N + c12 N ^ 2 * q2 N := by
  have hq : q2 N ≠ 0 := (q2_pos hN).ne'
  have hc : c12 N * q2 N = N 1 ⬝ᵥ N 2 := div_mul_cancel₀ _ hq
  calc nsq (N 1) = N 1 ⬝ᵥ (u1 N + c12 N • N 2) := by rw [← row1_eq]; rfl
    _ = q1 N + c12 N * (N 1 ⬝ᵥ N 2) := by
        rw [dotProduct_add, dotProduct_smul, smul_eq_mul, row1_dot_u1 hN]
    _ = q1 N + c12 N ^ 2 * q2 N := by rw [← hc]; ring

private theorem nsq_row0 (hN : N.det ≠ 0) : nsq (N 0) = q0 N + c01 N ^ 2 * q1 N + c02 N ^ 2 * q2 N := by
  have hq2 : q2 N ≠ 0 := (q2_pos hN).ne'
  have hq1 : q1 N ≠ 0 := (q1_pos hN).ne'
  have hc2 : c02 N * q2 N = N 0 ⬝ᵥ N 2 := div_mul_cancel₀ _ hq2
  have hc1 : c01 N * q1 N = N 0 ⬝ᵥ u1 N := div_mul_cancel₀ _ hq1
  have hu0 : N 0 ⬝ᵥ u0 N = q0 N := by
    have e : N 0 ⬝ᵥ u0 N = (u0 N + c01 N • u1 N + c02 N • N 2) ⬝ᵥ u0 N := by rw [← row0_eq]
    rw [e, add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul,
      dotProduct_comm (u1 N), u0_dot_u1 hN, dotProduct_comm (N 2), u0_dot_row2 hN, mul_zero, mul_zero,
      add_zero, add_zero]
    rfl
  calc nsq (N 0) = N 0 ⬝ᵥ (u0 N + c01 N • u1 N + c02 N • N 2) := by rw [← row0_eq]; rfl
    _ = q0 N + c01 N * (N 0 ⬝ᵥ u1 N) + c02 N * (N 0 ⬝ᵥ N 2) := by
        rw [dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, hu0]
    _ = q0 N + c01 N ^ 2 * q1 N + c02 N ^ 2 * q2 N := by rw [← hc1, ← hc2]; ring

private theorem abs_c12_le (hN : N.det ≠ 0) (hp : nsq (N 1) ≤ nsq (N 1 + N 2)) (hm : nsq (N 1) ≤ nsq (N 1 - N 2)) :
    |c12 N| ≤ 1 / 2 := by
  have hq := q2_pos hN
  have e2 : nsq (N 2) = q2 N := rfl
  rw [nsq_add, e2] at hp
  rw [nsq_sub, e2] at hm
  rw [c12, abs_div, abs_of_pos hq, div_le_iff₀ hq, abs_le]
  constructor <;> nlinarith [hp, hm]

private theorem ratio_bounds (hN : N.det ≠ 0) (h32 : nsq (N 2) ≤ nsq (N 1)) (h21 : nsq (N 1) ≤ nsq (N 0))
    (h12 : |c12 N| ≤ 1 / 2) (h01 : |c01 N| ≤ 1 / 2) (h02 : |c02 N| ≤ 1 / 2) :
    q2 N ≤ 4 * q1 N ∧ q1 N ≤ 4 * q0 N := by
  have hq0 := q0_pos hN
  have hq1 := q1_pos hN
  have hq2 := q2_pos hN
  rw [nsq_row1 hN] at h32 h21
  rw [nsq_row0 hN] at h21
  have e2 : nsq (N 2) = q2 N := rfl
  rw [e2] at h32
  have b12 : c12 N ^ 2 ≤ 1 / 4 := by nlinarith [abs_le.mp h12, sq_abs (c12 N)]
  have b01 : c01 N ^ 2 ≤ 1 / 4 := by nlinarith [abs_le.mp h01, sq_abs (c01 N)]
  have b02 : c02 N ^ 2 ≤ 1 / 4 := by nlinarith [abs_le.mp h02, sq_abs (c02 N)]
  have t12 : c12 N ^ 2 * q2 N ≤ 1 / 4 * q2 N := mul_le_mul_of_nonneg_right b12 hq2.le
  have t01 : c01 N ^ 2 * q1 N ≤ 1 / 4 * q1 N := mul_le_mul_of_nonneg_right b01 hq1.le
  have t02 : c02 N ^ 2 * q2 N ≤ 1 / 4 * q2 N := mul_le_mul_of_nonneg_right b02 hq2.le
  have n12 : 0 ≤ c12 N ^ 2 * q2 N := mul_nonneg (sq_nonneg _) hq2.le
  constructor
  · linarith
  · linarith

variable {N' : Matrix (Fin 3) (Fin 3) ℝ}

private theorem c12_congr (h1 : N' 1 = N 1) (h2 : N' 2 = N 2) : c12 N' = c12 N := by
  simp only [c12, q2, h1, h2]

private theorem u1_congr (h1 : N' 1 = N 1) (h2 : N' 2 = N 2) : u1 N' = u1 N := by
  simp only [u1, c12_congr h1 h2, h1, h2]

private theorem q1_congr (h1 : N' 1 = N 1) (h2 : N' 2 = N 2) : q1 N' = q1 N := by
  simp only [q1, u1_congr h1 h2]

private theorem q2_congr (h2 : N' 2 = N 2) : q2 N' = q2 N := by
  simp only [q2, h2]

private theorem c01_shear01 (hN : N.det ≠ 0) (m : ℝ) (h0 : N' 0 = N 0 + m • N 1) (h1 : N' 1 = N 1)
    (h2 : N' 2 = N 2) : c01 N' = c01 N + m := by
  have hq : q1 N ≠ 0 := (q1_pos hN).ne'
  rw [c01, u1_congr h1 h2, q1_congr h1 h2, h0, add_dotProduct, smul_dotProduct, smul_eq_mul, row1_dot_u1 hN,
    c01, add_div, mul_div_cancel_right₀ _ hq]

private theorem c02_shear02 (hN : N.det ≠ 0) (m : ℝ) (h0 : N' 0 = N 0 + m • N 2) (h2 : N' 2 = N 2) :
    c02 N' = c02 N + m := by
  have hq : q2 N ≠ 0 := (q2_pos hN).ne'
  rw [c02, q2_congr h2, h0, h2, add_dotProduct, smul_dotProduct, smul_eq_mul, c02, add_div]
  congr 1
  rw [show N 2 ⬝ᵥ N 2 = q2 N from rfl, mul_div_cancel_right₀ _ hq]

private theorem c01_shear02 (hN : N.det ≠ 0) (m : ℝ) (h0 : N' 0 = N 0 + m • N 2) (h1 : N' 1 = N 1)
    (h2 : N' 2 = N 2) : c01 N' = c01 N := by
  rw [c01, u1_congr h1 h2, q1_congr h1 h2, h0, add_dotProduct, smul_dotProduct, smul_eq_mul, row2_dot_u1 hN,
    mul_zero, add_zero, c01]

end GramSchmidt

private theorem exists_reduced (Mg : GL (Fin 3) ℝ) :
    ∃ (γ : GL (Fin 3) ℤ) (n t k : GL (Fin 3) ℝ),
      Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) γ * Mg = n * t * k ∧
      (∀ i j : Fin 3,
        (n : Matrix (Fin 3) (Fin 3) ℝ) i i = 1 ∧ (j < i → (n : Matrix (Fin 3) (Fin 3) ℝ) i j = 0) ∧
        ‖(n : Matrix (Fin 3) (Fin 3) ℝ) i j‖ ≤ 1) ∧
      (∀ i j : Fin 3, i ≠ j → (t : Matrix (Fin 3) (Fin 3) ℝ) i j = 0) ∧
      (∀ i : Fin 3, 0 < (t : Matrix (Fin 3) (Fin 3) ℝ) i i) ∧
      1 / 2 ≤ (t : Matrix (Fin 3) (Fin 3) ℝ) 0 0 / (t : Matrix (Fin 3) (Fin 3) ℝ) 1 1 ∧
      1 / 2 ≤ (t : Matrix (Fin 3) (Fin 3) ℝ) 1 1 / (t : Matrix (Fin 3) (Fin 3) ℝ) 2 2 ∧
      (k : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * (k : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  set M : Matrix (Fin 3) (Fin 3) ℝ := (Mg : Matrix (Fin 3) (Fin 3) ℝ) with hM
  have hMB : M * ((Mg⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = 1 := Mg.mul_inv

  obtain ⟨a₃, ⟨γ₃, hγ₃⟩, hmin₃⟩ := exists_min hMB (fun a => ∃ γ : GL (Fin 3) ℤ, (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 = a)
    (a₀ := ((1 : GL (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ) 2) ⟨1, rfl⟩

  obtain ⟨a₂, ⟨γ₂, hγ₂3, hγ₂2⟩, hmin₂⟩ := exists_min hMB
    (fun a => ∃ γ : GL (Fin 3) ℤ, (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 = a₃ ∧ (γ : Matrix (Fin 3) (Fin 3) ℤ) 1 = a)
    (a₀ := (γ₃ : Matrix (Fin 3) (Fin 3) ℤ) 1) ⟨γ₃, hγ₃, rfl⟩

  set N₂ : Matrix (Fin 3) (Fin 3) ℝ :=
    ((Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) γ₂ * Mg : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)
    with hN₂
  set m : ℤ := -round (c01 N₂) with hm
  set γ' : GL (Fin 3) ℤ := sh01 m * γ₂ with hγ'
  set N₃ : Matrix (Fin 3) (Fin 3) ℝ :=
    ((Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) γ' * Mg : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)
    with hN₃
  set m' : ℤ := -round (c02 N₃) with hm'
  set γ : GL (Fin 3) ℤ := sh02 m' * γ' with hγdef
  set NGL : GL (Fin 3) ℝ := Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) γ * Mg with hNGL
  set N : Matrix (Fin 3) (Fin 3) ℝ := (NGL : Matrix (Fin 3) (Fin 3) ℝ) with hN

  have rγ'0 : (γ' : Matrix (Fin 3) (Fin 3) ℤ) 0 = (γ₂ : Matrix (Fin 3) (Fin 3) ℤ) 0 + m • a₂ := by
    rw [hγ', sh01_row0, hγ₂2]
  have rγ'1 : (γ' : Matrix (Fin 3) (Fin 3) ℤ) 1 = a₂ := by rw [hγ', sh01_row1, hγ₂2]
  have rγ'2 : (γ' : Matrix (Fin 3) (Fin 3) ℤ) 2 = a₃ := by rw [hγ', sh01_row2, hγ₂3]
  have rγ0 : (γ : Matrix (Fin 3) (Fin 3) ℤ) 0 = (γ' : Matrix (Fin 3) (Fin 3) ℤ) 0 + m' • a₃ := by
    rw [hγdef, sh02_row0, rγ'2]
  have rγ1 : (γ : Matrix (Fin 3) (Fin 3) ℤ) 1 = a₂ := by rw [hγdef, sh02_row1, rγ'1]
  have rγ2 : (γ : Matrix (Fin 3) (Fin 3) ℤ) 2 = a₃ := by rw [hγdef, sh02_row2, rγ'2]
  have hN₂0 : N₂ 0 = latVec M ((γ₂ : Matrix (Fin 3) (Fin 3) ℤ) 0) := row_map_mul γ₂ Mg 0
  have hN₂1 : N₂ 1 = latVec M a₂ := by rw [hN₂, row_map_mul, hγ₂2]
  have hN₂2 : N₂ 2 = latVec M a₃ := by rw [hN₂, row_map_mul, hγ₂3]
  have hN₃0 : N₃ 0 = N₂ 0 + (m : ℝ) • N₂ 1 := by
    rw [hN₃, row_map_mul, rγ'0, latVec_add, latVec_zsmul, hN₂0, hN₂1]
  have hN₃1 : N₃ 1 = N₂ 1 := by rw [hN₃, row_map_mul, rγ'1, hN₂1]
  have hN₃2 : N₃ 2 = N₂ 2 := by rw [hN₃, row_map_mul, rγ'2, hN₂2]
  have hN0 : N 0 = N₃ 0 + (m' : ℝ) • N₃ 2 := by
    rw [hN, hNGL, row_map_mul, rγ0, latVec_add, latVec_zsmul, hN₃, row_map_mul, row_map_mul, rγ'2]
  have hN1 : N 1 = N₂ 1 := by rw [hN, hNGL, row_map_mul, rγ1, hN₂1]
  have hN2 : N 2 = N₂ 2 := by rw [hN, hNGL, row_map_mul, rγ2, hN₂2]
  have hN1' : N 1 = N₃ 1 := by rw [hN1, hN₃1]
  have hN2' : N 2 = N₃ 2 := by rw [hN2, hN₃2]
  have hN1v : N 1 = latVec M a₂ := by rw [hN1, hN₂1]
  have hN2v : N 2 = latVec M a₃ := by rw [hN2, hN₂2]
  have hN0v : N 0 = latVec M ((γ : Matrix (Fin 3) (Fin 3) ℤ) 0) := by rw [hN, hNGL, row_map_mul]

  have detne : ∀ (δ : GL (Fin 3) ℤ),
      (((Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) δ * Mg : GL (Fin 3) ℝ) :
        Matrix (Fin 3) (Fin 3) ℝ)).det ≠ 0 := fun δ => by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) δ * Mg)).ne_zero
  have hdet₂ : N₂.det ≠ 0 := detne γ₂
  have hdet₃ : N₃.det ≠ 0 := detne γ'
  have hdet : N.det ≠ 0 := detne γ

  have hc01 : |c01 N| ≤ 1 / 2 := by
    have e3 : c01 N₃ = c01 N₂ + (m : ℝ) := c01_shear01 hdet₂ _ hN₃0 hN₃1 hN₃2
    have e : c01 N = c01 N₃ := c01_shear02 hdet₃ _ hN0 hN1' hN2'
    rw [e, e3, hm, Int.cast_neg, ← sub_eq_add_neg]
    exact abs_sub_round _
  have hc02 : |c02 N| ≤ 1 / 2 := by
    have e : c02 N = c02 N₃ + (m' : ℝ) := c02_shear02 hdet₃ _ hN0 hN2'
    rw [e, hm', Int.cast_neg, ← sub_eq_add_neg]
    exact abs_sub_round _

  have h32 : nsq (N 2) ≤ nsq (N 1) := by
    rw [hN1v, hN2v]
    exact hmin₃ a₂ ⟨sw12 * γ₂, by rw [sw12_row2, hγ₂2]⟩

  have h2p : nsq (N 1) ≤ nsq (N 1 + N 2) := by
    rw [hN1v, hN2v, ← latVec_add]
    refine hmin₂ (a₂ + a₃) ⟨sh12 1 * γ₂, by rw [sh12_row2, hγ₂3], ?_⟩
    rw [sh12_row1, hγ₂2, hγ₂3, one_zsmul]
  have h2m : nsq (N 1) ≤ nsq (N 1 - N 2) := by
    rw [hN1v, hN2v, ← latVec_sub]
    refine hmin₂ (a₂ - a₃) ⟨sh12 (-1) * γ₂, by rw [sh12_row2, hγ₂3], ?_⟩
    rw [sh12_row1, hγ₂2, hγ₂3, neg_one_zsmul, sub_eq_add_neg]
  have h21 : nsq (N 1) ≤ nsq (N 0) := by
    rw [hN1v, hN0v]
    exact hmin₂ _ ⟨sw01 * γ, by rw [sw01_row2, rγ2], by rw [sw01_row1]⟩
  have hc12 : |c12 N| ≤ 1 / 2 := abs_c12_le hdet h2p h2m
  obtain ⟨hr2, hr1⟩ := ratio_bounds hdet h32 h21 hc12 hc01 hc02

  have hq0 := q0_pos hdet
  have hq1 := q1_pos hdet
  have hq2 := q2_pos hdet
  have hdn : (nU N).det ≠ 0 := by
    simp [nU, Matrix.det_fin_three]
  have hdt : (tD N).det ≠ 0 := by
    have h0 : Real.sqrt (q0 N) ≠ 0 := (Real.sqrt_pos.mpr hq0).ne'
    have h1 : Real.sqrt (q1 N) ≠ 0 := (Real.sqrt_pos.mpr hq1).ne'
    have h2 : Real.sqrt (q2 N) ≠ 0 := (Real.sqrt_pos.mpr hq2).ne'
    simp [tD, Matrix.det_fin_three, h0, h1, h2]
  set nGL : GL (Fin 3) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero (nU N) hdn with hnGL
  set tGL : GL (Fin 3) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero (tD N) hdt with htGL
  set kGL : GL (Fin 3) ℝ := (nGL * tGL)⁻¹ * NGL with hkGL
  have hrec : (NGL : Matrix (Fin 3) (Fin 3) ℝ) = nU N * tD N * kO N := (nU_mul_tD_mul_kO hdet).symm
  have hk : ((kGL : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = kO N := by
    have hnt : ((nGL * tGL : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = nU N * tD N := rfl
    calc ((kGL : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)
        = (((nGL * tGL)⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) * (NGL : Matrix (Fin 3) (Fin 3) ℝ) := rfl
      _ = (((nGL * tGL)⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *
            (((nGL * tGL : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) * kO N) := by rw [hnt, ← hrec]
      _ = kO N := Units.inv_mul_cancel_left _ _
  refine ⟨γ, nGL, tGL, kGL, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hkGL, mul_inv_cancel_left]
  · have b01 : |c01 N| ≤ 1 := hc01.trans (by norm_num)
    have b02 : |c02 N| ≤ 1 := hc02.trans (by norm_num)
    have b12 : |c12 N| ≤ 1 := hc12.trans (by norm_num)
    show ∀ i j : Fin 3, nU N i i = 1 ∧ (j < i → nU N i j = 0) ∧ ‖nU N i j‖ ≤ 1
    intro i j
    fin_cases i <;> fin_cases j <;> simp [nU, Real.norm_eq_abs, b01, b02, b12]
  · show ∀ i j : Fin 3, i ≠ j → tD N i j = 0
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [tD] at hij ⊢
  · show ∀ i : Fin 3, 0 < tD N i i
    intro i
    fin_cases i <;> simp [tD, Real.sqrt_pos, hq0, hq1, hq2]
  · show 1 / 2 ≤ Real.sqrt (q0 N) / Real.sqrt (q1 N)
    rw [le_div_iff₀ (Real.sqrt_pos.mpr hq1)]
    refine (Real.le_sqrt ?_ hq0.le).mpr ?_
    · positivity
    · rw [mul_pow, Real.sq_sqrt hq1.le]
      norm_num
      linarith
  · show 1 / 2 ≤ Real.sqrt (q1 N) / Real.sqrt (q2 N)
    rw [le_div_iff₀ (Real.sqrt_pos.mpr hq2)]
    refine (Real.le_sqrt ?_ hq1.le).mpr ?_
    · positivity
    · rw [mul_pow, Real.sq_sqrt hq2.le]
      norm_num
      linarith
  · rw [hk]
    exact kO_transpose_mul_kO hdet

end HermiteThree

end

theorem solution :
    ∃ c C : ℝ, 0 < c ∧ ∀ M : GL (Fin 3) ℝ,
      ∃ (γ : GL (Fin 3) ℤ) (n t k : GL (Fin 3) ℝ),
        Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) γ * M = n * t * k ∧
        (∀ i j : Fin 3,
          (n : Matrix (Fin 3) (Fin 3) ℝ) i i = 1 ∧ (j < i → (n : Matrix (Fin 3) (Fin 3) ℝ) i j = 0) ∧
          ‖(n : Matrix (Fin 3) (Fin 3) ℝ) i j‖ ≤ C) ∧
        (∀ i j : Fin 3, i ≠ j → (t : Matrix (Fin 3) (Fin 3) ℝ) i j = 0) ∧
        (∀ i : Fin 3, 0 < (t : Matrix (Fin 3) (Fin 3) ℝ) i i) ∧
        c ≤ (t : Matrix (Fin 3) (Fin 3) ℝ) 0 0 / (t : Matrix (Fin 3) (Fin 3) ℝ) 1 1 ∧
        c ≤ (t : Matrix (Fin 3) (Fin 3) ℝ) 1 1 / (t : Matrix (Fin 3) (Fin 3) ℝ) 2 2 ∧
        (k : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * (k : Matrix (Fin 3) (Fin 3) ℝ) = 1 :=
  ⟨1 / 2, 1, by norm_num, HermiteThree.exists_reduced⟩

end S_LanglandsTunnell_CubicInduction_exists_mul_eq_unipotent_mul_diagonal_mul_orthogonal_real
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_mul_eq_unipotent_mul_diagonal_mul_orthogonal_real (solution)
