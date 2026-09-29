-- Prove2me | solution 1 for ModularCurve.isBoundedAtImInfty_eisensteinTwoSlash_slash
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/60f3e15d-9813-5042-9774-7a92d6ae96ad

import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isBoundedAtImInfty_eisensteinTwoSlash_slash
set_option autoImplicit false
noncomputable section
open UpperHalfPlane Complex Filter Matrix MatrixGroups EisensteinSeries Real
open scoped ModularForm

namespace S09RD

lemma summable_majorant :
    Summable (fun n : ℕ ↦ (ArithmeticFunction.sigma 1 n : ℝ) * Real.exp (-(2 * π)) ^ n) := by
  apply Summable.of_norm_bounded
    (summable_norm_pow_mul_geometric_of_norm_lt_one 2 (r := Real.exp (-(2 * π)))
      (by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact Real.exp_lt_one_iff.mpr (neg_neg_iff_pos.mpr (by positivity))))
  intro n
  simp only [norm_mul, Real.norm_eq_abs, Nat.abs_cast, norm_pow]
  gcongr
  exact_mod_cast (ArithmeticFunction.sigma_le_pow_succ 1 n).trans_eq (by norm_num)

lemma isBoundedAtImInfty_E2 : UpperHalfPlane.IsBoundedAtImInfty EisensteinSeries.E2 := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  refine ⟨1 + 24 * ∑' n : ℕ+,
    (ArithmeticFunction.sigma 1 (n : ℕ) : ℝ) * Real.exp (-(2 * π)) ^ (n : ℕ), 1,
    fun z hz => ?_⟩
  rw [EisensteinSeries.E2_eq_tsum_cexp]
  have hmaj : Summable (fun n : ℕ+ ↦
      (ArithmeticFunction.sigma 1 (n : ℕ) : ℝ) * Real.exp (-(2 * π)) ^ (n : ℕ)) :=
    (summable_pnat_iff_summable_succ
      (f := fun n : ℕ => (ArithmeticFunction.sigma 1 n : ℝ) * Real.exp (-(2 * π)) ^ n)).mpr
      ((summable_nat_add_iff 1).mpr summable_majorant)
  have hqnorm : ‖Complex.exp (2 * (π : ℂ) * Complex.I * (z : ℂ))‖
      = Real.exp (-(2 * π) * z.im) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.mul_im]
  have hq : ‖Complex.exp (2 * (π : ℂ) * Complex.I * (z : ℂ))‖ ≤ Real.exp (-(2 * π)) := by
    rw [hqnorm]
    apply Real.exp_le_exp.mpr
    have h2 := mul_le_mul_of_nonpos_left hz (neg_nonpos.mpr (by positivity : (0:ℝ) ≤ 2 * π))
    simpa using h2
  have hT : ‖∑' n : ℕ+,
      (ArithmeticFunction.sigma 1 (n : ℕ) : ℂ) * Complex.exp (2 * (π : ℂ) * Complex.I * (z : ℂ)) ^ (n : ℕ)‖
      ≤ ∑' n : ℕ+, (ArithmeticFunction.sigma 1 (n : ℕ) : ℝ) * Real.exp (-(2 * π)) ^ (n : ℕ) := by
    apply tsum_of_norm_bounded hmaj.hasSum
    intro n
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    gcongr
  calc ‖1 - 24 * ∑' n : ℕ+,
      (ArithmeticFunction.sigma 1 (n : ℕ) : ℂ) * Complex.exp (2 * (π : ℂ) * Complex.I * (z : ℂ)) ^ (n : ℕ)‖
      ≤ ‖(1 : ℂ)‖ + ‖24 * ∑' n : ℕ+,
        (ArithmeticFunction.sigma 1 (n : ℕ) : ℂ) * Complex.exp (2 * (π : ℂ) * Complex.I * (z : ℂ)) ^ (n : ℕ)‖ :=
        norm_sub_le _ _
    _ = 1 + 24 * ‖∑' n : ℕ+,
        (ArithmeticFunction.sigma 1 (n : ℕ) : ℂ) * Complex.exp (2 * (π : ℂ) * Complex.I * (z : ℂ)) ^ (n : ℕ)‖ := by
        simp
    _ ≤ 1 + 24 * ∑' n : ℕ+,
        (ArithmeticFunction.sigma 1 (n : ℕ) : ℝ) * Real.exp (-(2 * π)) ^ (n : ℕ) := by
        gcongr

lemma isBoundedAtImInfty_D2 (γ : SL(2, ℤ)) :
    UpperHalfPlane.IsBoundedAtImInfty (EisensteinSeries.D2 γ) := by
  rcases eq_or_ne (γ 1 0) 0 with hc | hc
  · have hD : EisensteinSeries.D2 γ = 0 := by
      funext z
      simp [EisensteinSeries.D2, hc]
    rw [hD]
    exact UpperHalfPlane.zero_form_isBoundedAtImInfty
  · rw [UpperHalfPlane.isBoundedAtImInfty_iff]
    refine ⟨‖2 * (π : ℂ) * Complex.I * ((γ 1 0 : ℤ) : ℂ)‖, 1, fun z hz => ?_⟩
    have him : (UpperHalfPlane.denom γ z).im = ((γ 1 0 : ℤ) : ℝ) * z.im := by
      rw [ModularGroup.denom_apply]
      simp
    have hc1 : (1 : ℝ) ≤ |((γ 1 0 : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs hc
    have hlow : |((γ 1 0 : ℤ) : ℝ)| ≤ ‖UpperHalfPlane.denom γ z‖ :=
      calc |((γ 1 0 : ℤ) : ℝ)| = |((γ 1 0 : ℤ) : ℝ)| * 1 := (mul_one _).symm
        _ ≤ |((γ 1 0 : ℤ) : ℝ)| * z.im := by gcongr
        _ = |((γ 1 0 : ℤ) : ℝ) * z.im| := by
            rw [abs_mul, abs_of_pos z.im_pos]
        _ = |(UpperHalfPlane.denom γ z).im| := by rw [him]
        _ ≤ ‖UpperHalfPlane.denom γ z‖ := Complex.abs_im_le_norm _
    have hone : (1 : ℝ) ≤ ‖UpperHalfPlane.denom γ z‖ := hc1.trans hlow
    show ‖(2 * (π : ℂ) * Complex.I * ((γ 1 0 : ℤ) : ℂ)) / UpperHalfPlane.denom γ z‖ ≤ _
    rw [norm_div]
    exact div_le_self (norm_nonneg _) hone

lemma isBoundedAtImInfty_E2_slash_SL (γ : SL(2, ℤ)) :
    UpperHalfPlane.IsBoundedAtImInfty (EisensteinSeries.E2 ∣[(2 : ℤ)] γ) := by
  rw [EisensteinSeries.E2_slash_action, sub_eq_add_neg]
  exact isBoundedAtImInfty_E2.add ((isBoundedAtImInfty_D2 γ).smul _).neg

lemma isBoundedAtImInfty_E2_slash_of_row (g : GL (Fin 2) ℝ) (N : SL(2, ℤ))
    (hN : (Matrix.SpecialLinearGroup.mapGL ℝ N * g) 1 0 = 0) :
    UpperHalfPlane.IsBoundedAtImInfty (EisensteinSeries.E2 ∣[(2 : ℤ)] g) := by
  have h1 : UpperHalfPlane.IsBoundedAtImInfty
      (EisensteinSeries.E2 ∣[(2 : ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ N⁻¹) :=
    isBoundedAtImInfty_E2_slash_SL N⁻¹
  have h2 := h1.slash (2 : ℤ) hN
  rwa [← SlashAction.slash_mul, map_inv, inv_mul_cancel_left] at h2

lemma exists_row_zero (p : ℕ) (hp : p ≠ 0) (γ : SL(2, ℤ)) :
    ∃ N : SL(2, ℤ), (Matrix.SpecialLinearGroup.mapGL ℝ N *
      (ModularForm.heckeDiagMatrix p * Matrix.SpecialLinearGroup.mapGL ℝ γ)) 1 0 = 0 := by
  have hentry : ∀ N : SL(2, ℤ), (Matrix.SpecialLinearGroup.mapGL ℝ N *
      (ModularForm.heckeDiagMatrix p * Matrix.SpecialLinearGroup.mapGL ℝ γ)) 1 0
      = ((N 1 0 : ℤ) : ℝ) * ((p : ℝ) * ((γ 0 0 : ℤ) : ℝ))
        + ((N 1 1 : ℤ) : ℝ) * ((γ 1 0 : ℤ) : ℝ) := by
    intro N
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
      ModularForm.val_heckeDiagMatrix hp, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.map_apply, algebraMap_int_eq, Int.coe_castRingHom, Matrix.vecMul, dotProduct]
  rcases eq_or_ne (γ 1 0) 0 with hc | hc
  · refine ⟨1, ?_⟩
    rw [hentry 1]
    simp [hc]
  · have hpos : 0 < Int.gcd ((p : ℤ) * γ 0 0) (γ 1 0) :=
      Nat.pos_of_ne_zero fun h => hc (Int.gcd_eq_zero_iff.mp h).2
    obtain ⟨a', c', hcop, ha, hcc⟩ := Int.exists_gcd_one hpos
    have hmem : (![-c', a'] : Fin 2 → ℤ) ∈ {cd : Fin 2 → ℤ | IsCoprime (cd 0) (cd 1)} := by
      simpa using (Int.isCoprime_iff_gcd_eq_one.mpr hcop).symm.neg_left
    obtain ⟨N, -, hN⟩ := ModularGroup.bottom_row_surj hmem
    have hN0 : N 1 0 = -c' := by simpa using congrFun hN 0
    have hN1 : N 1 1 = a' := by simpa using congrFun hN 1
    have hz0 : -c' * ((p : ℤ) * γ 0 0) + a' * γ 1 0 = 0 := by
      set G : ℤ := (Int.gcd ((p : ℤ) * γ 0 0) (γ 1 0) : ℤ)
      rw [ha, hcc]
      ring
    refine ⟨N, ?_⟩
    rw [hentry N, hN0, hN1]
    exact_mod_cast hz0

end S09RD

private theorem ModularCurve.isBoundedAtImInfty_eisensteinTwoSlash_slash (p : ℕ) [NeZero p] :
    ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      UpperHalfPlane.IsBoundedAtImInfty ((EisensteinSeries.E2 ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix p - EisensteinSeries.E2) ∣[(2 : ℤ)] γ) := by
  intro γ
  have hp : p ≠ 0 := NeZero.ne p
  have hsplit : (EisensteinSeries.E2 ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix p
        - EisensteinSeries.E2) ∣[(2 : ℤ)] γ
      = (EisensteinSeries.E2 ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix p) ∣[(2 : ℤ)] γ
        - EisensteinSeries.E2 ∣[(2 : ℤ)] γ := by
    rw [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, ← sub_eq_add_neg]
  have hAγ : (EisensteinSeries.E2 ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix p) ∣[(2 : ℤ)] γ
      = EisensteinSeries.E2 ∣[(2 : ℤ)]
        (ModularForm.heckeDiagMatrix p * Matrix.SpecialLinearGroup.mapGL ℝ γ) := by
    rw [SlashAction.slash_mul]
    rfl
  obtain ⟨N, hN⟩ := S09RD.exists_row_zero p hp γ
  have h1 : UpperHalfPlane.IsBoundedAtImInfty
      ((EisensteinSeries.E2 ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix p) ∣[(2 : ℤ)] γ) := by
    rw [hAγ]
    exact S09RD.isBoundedAtImInfty_E2_slash_of_row _ N hN
  rw [hsplit, sub_eq_add_neg]
  exact h1.add (S09RD.isBoundedAtImInfty_E2_slash_SL γ).neg

open scoped ModularForm in
theorem solution : ∀ (p : ℕ) [NeZero p], ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, UpperHalfPlane.IsBoundedAtImInfty ((EisensteinSeries.E2 ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix p - EisensteinSeries.E2) ∣[(2 : ℤ)] γ) :=
  @ModularCurve.isBoundedAtImInfty_eisensteinTwoSlash_slash

end
end S_ModularCurve_isBoundedAtImInfty_eisensteinTwoSlash_slash
end P2MW
export P2MW.S_ModularCurve_isBoundedAtImInfty_eisensteinTwoSlash_slash (solution)
