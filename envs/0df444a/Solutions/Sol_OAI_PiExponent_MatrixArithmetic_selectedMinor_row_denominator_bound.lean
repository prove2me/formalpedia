-- Prove2me | solution 1 for OAI.PiExponent.MatrixArithmetic.selectedMinor_row_denominator_bound
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:49:41.04203+00:00
-- url     : https://prove2.me/submissions/a29750c0-68c4-46ac-97c3-84f9e4331067

import Mathlib
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData

open scoped BigOperators

lemma exp20 : (2:ℝ)^28 + 1 ≤ Real.exp 20 := by
  have h : Real.exp 20 = Real.exp 1 ^ 20 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  have := Real.exp_one_gt_d9
  calc (2:ℝ)^28 + 1 ≤ (2.7:ℝ)^20 := by norm_num
    _ ≤ Real.exp 1 ^ 20 := by gcongr; linarith

lemma exp19 : Real.exp 19 < (2:ℝ)^28 := by
  have h : Real.exp 19 = Real.exp 1 ^ 19 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  have := Real.exp_one_lt_d9
  calc Real.exp 1 ^ 19 < (2.72:ℝ)^19 := by gcongr; linarith
    _ ≤ (2:ℝ)^28 := by norm_num

lemma ceil_log_eq (x : ℝ) (h1 : Real.exp 19 < x) (h2 : x ≤ Real.exp 20) : ⌈Real.log x⌉₊ = 20 := by
  have hx : 0 < x := lt_trans (Real.exp_pos _) h1
  rw [Nat.ceil_eq_iff (by norm_num)]
  constructor
  · rw [Real.lt_log_iff_exp_lt hx]; norm_num; exact h1
  · rw [Real.log_le_iff_le_exp hx]; norm_num; exact h2

open OAI.PiExponent OAI.PiExponent.InterpolationMatrix OAI.PiExponent.MatrixArithmetic

noncomputable def qq : Fin 2 → ℕ := ![2^28+1, 2^28]

lemma lw (i : Fin 2) : logWeights qq i = 20 := by
  unfold logWeights
  have := exp19; have := exp20
  rw [ceil_log_eq]
  · norm_num
  · fin_cases i <;> simp [qq] <;> push_cast <;> linarith
  · fin_cases i <;> simp [qq] <;> push_cast <;> linarith

lemma lwf : logWeights qq = fun _ => 20 := funext lw


lemma h0 : (0 : Fin 3 → ℕ) ∈ strictWeightedSimplex (rowWeights 1 1 (logWeights qq)) 20 := by
  simp [strictWeightedSimplex, realWeightedSimplex]
lemma hc1 : (![0,1,0] : Fin 3 → ℕ) ∈ realWeightedSimplex (columnWeights 1 (logWeights qq)) 20 := by
  simp [realWeightedSimplex, lwf, columnWeights, Fin.forall_fin_succ, Fin.sum_univ_succ]
lemma hc2 : (![0,0,1] : Fin 3 → ℕ) ∈ realWeightedSimplex (columnWeights 1 (logWeights qq)) 20 := by
  simp [realWeightedSimplex, lwf, columnWeights, Fin.forall_fin_succ, Fin.sum_univ_succ]

lemma hz : (Finsupp.equivFunOnFinite.symm fun _ : Fin 2 => (0:ℕ)) = 0 := by ext; simp

noncomputable def ρ1 : Row 2 1 1 (logWeights qq) 20 := (1, ⟨0, h0⟩)
noncomputable def ρ0 : Row 2 1 1 (logWeights qq) 20 := (0, ⟨0, h0⟩)
noncomputable def sel : Row 2 1 1 (logWeights qq) 20 → Column 1 (logWeights qq) 20 :=
  fun ρ => if ρ.1 = 1 then ⟨_, hc1⟩ else ⟨_, hc2⟩

lemma e1 : selectedMinor 2 1 1 1 0 20 (fun _ => 1) qq sel ρ1 ρ1 = 2 * Complex.I / ((2^28+1 : ℕ) : ℂ) := by
  simp only [selectedMinor, truncatedLogMatrix, Matrix.submatrix_apply, id]
  simp [InterpolationMatrix.matrix, entry, monomialImage, sel, ρ1, truncationOrders,
    truncatedLog, rationalCenters, exponentVector, Fin.prod_univ_succ, qq, hz, MvPolynomial.coeff_X]

lemma e2 : selectedMinor 2 1 1 1 0 20 (fun _ => 1) qq sel ρ1 ρ0 = 2 * Complex.I / ((2^28 : ℕ) : ℂ) := by
  simp only [selectedMinor, truncatedLogMatrix, Matrix.submatrix_apply, id]
  simp [InterpolationMatrix.matrix, entry, monomialImage, sel, ρ1, ρ0, truncationOrders,
    truncatedLog, rationalCenters, exponentVector, Fin.prod_univ_succ, qq, hz, MvPolynomial.coeff_X]

lemma dvd_of_gauss (N d : ℕ) (hN : 0 < N) (g : GaussianInt)
    (h : (d : ℂ) * (2 * Complex.I / (N : ℂ)) = (g : ℂ)) : N ∣ 2 * d := by
  have him := congrArg Complex.im h
  simp [Complex.div_im] at him
  have hgi : (GaussianInt.toComplex g).im = (g.im : ℝ) := Eq.symm (GaussianInt.intCast_im g)
  rw [hgi] at him
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have : ((2 * d : ℕ) : ℝ) = (N : ℝ) * (g.im : ℝ) := by
    push_cast; field_simp at him; linarith
  have h2 : ((2 * d : ℕ) : ℤ) = (N : ℤ) * g.im := by exact_mod_cast this
  have : (N : ℤ) ∣ ((2 * d : ℕ) : ℤ) := ⟨g.im, h2⟩
  exact_mod_cast this

theorem solution : ¬ (∀ {m K : ℕ} {w0 v0 θ F H wmin : ℝ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hK : 0 < K) (hw0 : 0 < w0) (hv0 : 0 < v0) (hθ : 0 < θ)
    (hF : 0 ≤ F) (hH : 0 < H) (hmin : 0 < wmin)
    (hwmin : ∀ i, wmin ≤ OAI.PiExponent.MatrixArithmetic.logWeights q i)
    (selection : OAI.PiExponent.InterpolationMatrix.Row K v0 θ
        (OAI.PiExponent.MatrixArithmetic.logWeights q) H →
      OAI.PiExponent.InterpolationMatrix.Column w0
        (OAI.PiExponent.MatrixArithmetic.logWeights q) H),
    ∃ d : OAI.PiExponent.InterpolationMatrix.Row K v0 θ
        (OAI.PiExponent.MatrixArithmetic.logWeights q) H → ℕ,
      (∀ ρ, 0 < d ρ) ∧
      (∀ ρ c, ∃ g : GaussianInt,
        (d ρ : ℂ) *
          OAI.PiExponent.MatrixArithmetic.selectedMinor K w0 v0 θ F H p q selection ρ c = (g : ℂ)) ∧
      (∀ ρ, Real.log (d ρ : ℝ) ≤
        H - (∑ i, (ρ.2.1 i.succ : ℝ) * OAI.PiExponent.MatrixArithmetic.logWeights q i) +
          H * (OAI.PiExponent.Arithmetic.lcmConstant * F * m / v0 +
            OAI.PiExponent.Arithmetic.lcmConstant *
              (∑ i, 1 / OAI.PiExponent.MatrixArithmetic.logWeights q i) + θ / wmin))) := by
  intro Hyp
  obtain ⟨d, hd, hg, hl⟩ := Hyp (m := 2) (K := 2) (w0 := 1) (v0 := 1) (θ := 1) (F := 0) (H := 20)
    (wmin := 20) (fun _ => 1) qq (by intro i; fin_cases i <;> simp [qq]) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num) (fun i => by rw [lw]) sel
  obtain ⟨g1, hg1⟩ := hg ρ1 ρ1
  obtain ⟨g2, hg2⟩ := hg ρ1 ρ0
  rw [e1] at hg1
  rw [e2] at hg2
  have d1 := dvd_of_gauss _ _ (by norm_num) g1 hg1
  have d2 := dvd_of_gauss _ _ (by norm_num) g2 hg2
  have d1' : (2^28+1) ∣ d ρ1 := by
    have hc : Nat.Coprime (2^28+1) 2 := by norm_num
    exact hc.dvd_of_dvd_mul_left d1
  have d2' : 2^27 ∣ d ρ1 := by
    have : 2^28 = 2 * 2^27 := by norm_num
    rw [this] at d2
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) d2
  have d3 : (2^28+1) * 2^27 ∣ d ρ1 :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d1' d2'
  have hle : (2:ℝ)^55 ≤ (d ρ1 : ℝ) := by
    have := Nat.le_of_dvd (hd ρ1) d3
    have : (2^55 : ℕ) ≤ d ρ1 := le_trans (by norm_num) this
    exact_mod_cast this
  have hlog : (55:ℝ) * Real.log 2 ≤ Real.log (d ρ1 : ℝ) := by
    have e := Real.log_pow (n := 55) (x := (2:ℝ)); push_cast at e; rw [← e]; exact Real.log_le_log (by positivity) (by exact_mod_cast hle)
  rw [show ρ1 = (1, ⟨0, h0⟩) from rfl] at hlog
  have hb := hl ρ1
  simp [ρ1, lwf, OAI.PiExponent.Arithmetic.lcmConstant] at hb
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_gt_d9
  rw [h4] at hb
  linarith
