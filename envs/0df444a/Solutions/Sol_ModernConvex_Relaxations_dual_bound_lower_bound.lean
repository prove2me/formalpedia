-- Prove2me | solution 1 for ModernConvex.Relaxations.dual_bound_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:10:28.663507+00:00
-- url     : https://prove2.me/submissions/e295c7d9-7baf-4814-a72d-e4a3bf18a5d4

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_ShorScheme

open Matrix
open ModernConvex.Relaxations

theorem g69a2_bord_quad {n : ℕ} (c : ℝ) (b : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (v : Unit ⊕ Fin n → ℝ) :
    v ⬝ᵥ (borderedMatrix c b A *ᵥ v) = v (Sum.inl ()) ^ 2 * c +
      2 * v (Sum.inl ()) * (b ⬝ᵥ (v ∘ Sum.inr)) + (v ∘ Sum.inr) ⬝ᵥ (A *ᵥ (v ∘ Sum.inr)) := by
  simp only [dotProduct, mulVec, Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton]
  simp [borderedMatrix, Finset.mul_sum, Finset.sum_mul, mul_add, add_mul, Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun i _ => (by ring : v (Sum.inr i) * (b i * v (Sum.inl ())) =
      v (Sum.inl ()) * (b i * v (Sum.inr i))))]
  simp only [← Finset.mul_sum]
  ring

theorem g69a2_psd_of_quad {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (b : Fin n → ℝ) (c : ℝ) (h : ∀ x : Fin n → ℝ, 0 ≤ quadForm A b c x) :
    (borderedMatrix c b A).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · unfold borderedMatrix
    refine IsHermitian.fromBlocks ?_ ?_ hA
    · ext i j; simp
    · ext i j; simp
  · intro v
    simp only [star_trivial]
    rw [g69a2_bord_quad]
    set s := v (Sum.inl ())
    set y := v ∘ Sum.inr
    by_cases hs : s = 0
    · rw [hs]
      have hq : 0 ≤ y ⬝ᵥ (A *ᵥ y) := by
        by_contra hneg
        push Not at hneg
        set q := y ⬝ᵥ (A *ᵥ y)
        set t := Real.sqrt ((|c| + 1) / (-q))
        have ht : t ^ 2 = (|c| + 1) / (-q) := Real.sq_sqrt (by
          apply div_nonneg (by positivity); linarith)
        have h1 := h (t • y)
        have h2 := h ((-t) • y)
        simp only [quadForm, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h1 h2
        have : q * t ^ 2 = -(|c| + 1) := by
          have hq0 : q ≠ 0 := ne_of_lt hneg
          rw [ht]; field_simp
        have hc := le_abs_self c
        nlinarith
      nlinarith
    · have := h (s⁻¹ • y)
      simp only [quadForm, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at this
      have hs2 : 0 < s ^ 2 := by positivity
      have key : s ^ 2 * (s⁻¹ * (s⁻¹ * (y ⬝ᵥ (A *ᵥ y))) + 2 * (s⁻¹ * (b ⬝ᵥ y)) + c) =
          s ^ 2 * c + 2 * s * (b ⬝ᵥ y) + y ⬝ᵥ (A *ᵥ y) := by
        field_simp
        ring
      rw [← key]; positivity

theorem g69a2_bord_elim {n : ℕ} (c : ℝ) (b : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) :
    (Sum.elim (fun _ => 1) x) ⬝ᵥ (borderedMatrix c b A *ᵥ (Sum.elim (fun _ => 1) x)) =
      quadForm A b c x := by
  rw [g69a2_bord_quad]
  have e : (Sum.elim (fun _ : Unit => (1:ℝ)) x) ∘ Sum.inr = x := by ext; simp
  rw [e]
  simp only [Sum.elim_inl]
  unfold quadForm; ring

theorem g69a2_trace_vmv {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (v : ι → ℝ) :
    (M * vecMulVec v v).trace = v ⬝ᵥ (M *ᵥ v) := by
  rw [mul_vecMulVec, trace_vecMulVec, dotProduct_comm]

theorem g69a2_quadForm_lin {n m : ℕ} (A₀ : Matrix (Fin n) (Fin n) ℝ) (b₀ : Fin n → ℝ) (c₀ : ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → Fin n → ℝ) (c : Fin m → ℝ)
    (lam : Fin m → ℝ) (ζ : ℝ) (x : Fin n → ℝ) :
    quadForm (A₀ + ∑ i, lam i • A i) (b₀ + ∑ i, lam i • b i) (c₀ + ∑ i, lam i * c i - ζ) x =
      quadForm A₀ b₀ c₀ x + ∑ i, lam i * quadForm (A i) (b i) (c i) x - ζ := by
  simp only [quadForm, add_mulVec, sum_mulVec, smul_mulVec, dotProduct_add, dotProduct_sum,
    add_dotProduct, sum_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    Finset.sum_add_distrib, Finset.mul_sum, mul_add]
  have : ∑ i, 2 * (lam i * (b i ⬝ᵥ x)) = ∑ i, lam i * (2 * (b i ⬝ᵥ x)) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [this]; ring

theorem g69a2_quad_of_psd {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) (c : ℝ) (h : (borderedMatrix c b A).PosSemidef) (x : Fin n → ℝ) :
    0 ≤ quadForm A b c x := by
  have := h.dotProduct_mulVec_nonneg (Sum.elim (fun _ => 1) x)
  simp only [star_trivial] at this
  rw [g69a2_bord_quad] at this
  have e : (Sum.elim (fun _ : Unit => (1:ℝ)) x) ∘ Sum.inr = x := by ext; simp
  rw [e] at this
  simp only [Sum.elim_inl] at this
  unfold quadForm; linarith


/-- Ben-Tal–Nemirovski, Proposition 4.3.1, p. 163: the optimal value of the semidefinite program
(4.3.9) is a lower bound for the optimal value of (4.3.5). Both optimal values are taken in
`[−∞, +∞]` (a supremum and an infimum in `EReal`), so the statement also covers infeasible and
unbounded instances. -/
theorem solution {n m : ℕ} (P : QuadraticProblem n m) (hP : P.IsSymmetric) :
    P.dualBoundValue ≤ P.optimalValue := by
  unfold QuadraticProblem.dualBoundValue QuadraticProblem.optimalValue
  refine iSup_le fun ζ => iSup_le fun lam => iSup_le fun hfeas => le_iInf fun x => le_iInf fun hx => ?_
  rw [EReal.coe_le_coe_iff]
  have h1 := g69a2_quad_of_psd _ _ _ hfeas x
  rw [g69a2_quadForm_lin] at h1
  have h2 : ∑ i, lam i * quadForm (P.A i) (P.b i) (P.c i) x = 0 :=
    Finset.sum_eq_zero fun i _ => by
      have := hx i
      unfold QuadraticProblem.f at this
      rw [this, mul_zero]
  unfold QuadraticProblem.f₀
  linarith

