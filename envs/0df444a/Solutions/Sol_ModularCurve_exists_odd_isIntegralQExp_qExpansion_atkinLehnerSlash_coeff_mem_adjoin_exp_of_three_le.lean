-- Prove2me | solution 1 for ModularCurve.exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp_of_three_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/73a969cf-bcb2-5384-ae40-99a3d4f6c5c0

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Theorems.Thm_ModularCurve_nonempty_integralWeightOneForm
import Theorems.Thm_ModularCurve_exists_ratCast_qExpansion_slash_of_mem_Gamma0
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp_of_three_le

set_option autoImplicit false

open UpperHalfPlane ConjAct Pointwise
open scoped MatrixGroups ModularForm

namespace AUXODDM3

abbrev Γ1 (N : ℕ) : Subgroup (GL (Fin 2) ℝ) := ((CongruenceSubgroup.Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem one_mem_strictPeriods_conj {M : ℕ} (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) :
    (1 : ℝ) ∈ (toConjAct (γ : GL (Fin 2) ℝ)⁻¹ • Γ1 M).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, inv_inv, toConjAct_smul]
  have hc : (M : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp hγ)
  obtain ⟨c', hc'⟩ := hc
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.det_coe; rw [Matrix.det_fin_two] at h; exact h
  let δ' : SL(2, ℤ) := ⟨!![1 - γ 0 0 * γ 1 0, γ 0 0 * γ 0 0; -(γ 1 0 * γ 1 0), 1 + γ 0 0 * γ 1 0], by
    rw [Matrix.det_fin_two_of]; ring⟩
  have hmem : δ' ∈ CongruenceSubgroup.Gamma1 M := by
    rw [CongruenceSubgroup.Gamma1_mem]
    simp only [δ', Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val']
    refine ⟨?_, ?_, ?_⟩
    · rw [show (1 - γ 0 0 * γ 1 0 : ℤ) = 1 + (M : ℤ) * (-(γ 0 0 * c')) by rw [hc']; ring]
      simp only [Int.cast_add, Int.cast_one, Int.cast_mul, Int.cast_natCast, Int.cast_neg, ZMod.natCast_self, zero_mul, add_zero]
    · rw [show (1 + γ 0 0 * γ 1 0 : ℤ) = 1 + (M : ℤ) * (γ 0 0 * c') by rw [hc']; ring]
      simp only [Int.cast_add, Int.cast_one, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, add_zero]
    · rw [show (-(γ 1 0 * γ 1 0) : ℤ) = (M : ℤ) * (-(c' * γ 1 0)) by rw [hc']; ring]
      simp only [Int.cast_mul, Int.cast_natCast, Int.cast_neg, ZMod.natCast_self, zero_mul]
  have hdetR : ((γ 0 0 : ℤ) : ℝ) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by exact_mod_cast hdet
  have hconj : (γ : GL (Fin 2) ℝ) * Matrix.GeneralLinearGroup.upperRightHom (1 : ℝ)
      = (δ' : GL (Fin 2) ℝ) * (γ : GL (Fin 2) ℝ) := by
    apply Units.ext
    ext i j
    simp only [Units.val_mul]
    fin_cases i <;> fin_cases j <;>
      simp [δ', Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.upperRightHom,
        Matrix.SpecialLinearGroup.toGL, Matrix.SpecialLinearGroup.map] <;>
      first | ring1 | linear_combination (-((γ 0 0 : ℤ) : ℝ)) * hdetR
            | linear_combination (-((γ 1 0 : ℤ) : ℝ)) * hdetR
  rw [show (γ : GL (Fin 2) ℝ) * Matrix.GeneralLinearGroup.upperRightHom (1 : ℝ) * (γ : GL (Fin 2) ℝ)⁻¹ = (δ' : GL (Fin 2) ℝ)
    from by rw [mul_inv_eq_iff_eq_mul]; exact hconj]
  exact Subgroup.mem_map_of_mem _ hmem

end AUXODDM3

open AUXODDM3 UpperHalfPlane ConjAct Pointwise in
open scoped MatrixGroups ModularForm in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) (hM : 3 ≤ M)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγp : (p : ℤ) ∣ γ 1 1) :
    ∃ (k' : ℤ) (h : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k')
      (r : PowerSeries ℤ),
      Odd k' ∧ ModularCurve.IsIntegralQExp h r ∧ (⇑h : UpperHalfPlane → ℂ) ≠ 0 ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion 1 (fun τ : UpperHalfPlane =>
          ((⇑h : UpperHalfPlane → ℂ) ∣[k'] γ) (ModularForm.heckeDiagMatrix p • τ))).coeff n ∈
        IntermediateField.adjoin ℚ ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))} : Set ℂ) := by
  classical
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) (Fact.out : p.Prime).ne_zero⟩
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero

  obtain ⟨w⟩ := ModularCurve.nonempty_integralWeightOneForm ℚ M hM
  have hle : Γ1 (M * p) ≤ Γ1 M := by
    refine Subgroup.map_mono fun δ hδ => ?_
    obtain ⟨h1, h2, h3⟩ := (CongruenceSubgroup.Gamma1_mem _ _).mp hδ
    rw [CongruenceSubgroup.Gamma1_mem]
    have cast : ∀ x : ℤ, ((x : ZMod (M * p)) = 1 → (x : ZMod M) = 1) ∧ ((x : ZMod (M * p)) = 0 → (x : ZMod M) = 0) := by
      intro x
      constructor
      · intro hx
        have := congrArg (ZMod.castHom (Nat.dvd_mul_right M p) (ZMod M)) hx
        simpa using this
      · intro hx
        have := congrArg (ZMod.castHom (Nat.dvd_mul_right M p) (ZMod M)) hx
        simpa using this
    exact ⟨(cast _).1 h1, (cast _).1 h2, (cast _).2 h3⟩
  refine ⟨1, ModularCurve.restrictForm hle w.form, w.series, odd_one, w.isIntegralQExp, ?_, ?_⟩
  ·
    intro h0
    apply w.intSeriesC_ne_zero
    have hq : qExpansion 1 (⇑w.form : ℍ → ℂ) = 0 := by
      have : (⇑w.form : ℍ → ℂ) = 0 := h0
      rw [this, UpperHalfPlane.qExpansion_zero]
    have hser : w.series = 0 := by
      have hint : (w.series).map (Int.castRingHom ℂ) = 0 := by rw [w.isIntegralQExp, hq]
      exact (PowerSeries.map_injective (Int.castRingHom ℂ) Int.cast_injective) (by rw [hint, map_zero])
    simp [ModularCurve.intSeriesC, hser]
  ·
    intro n

    let F : ModularForm (toConjAct (γ : GL (Fin 2) ℝ)⁻¹ • Γ1 M) 1 := ModularForm.translate w.form (γ : GL (Fin 2) ℝ)
    have hF : (⇑F : ℍ → ℂ) = (⇑w.form : ℍ → ℂ) ∣[(1 : ℤ)] γ := by rw [ModularForm.coe_translate, ModularForm.SL_slash]
    have hrat : ∀ m : ℕ, ∃ r : ℚ, (qExpansion 1 (⇑F : ℍ → ℂ)).coeff m = (r : ℂ) := by
      intro m
      rw [hF]
      exact ModularCurve.exists_ratCast_qExpansion_slash_of_mem_Gamma0 M w.form
        (fun n => ⟨((PowerSeries.coeff n w.series : ℤ) : ℚ), by rw [← w.isIntegralQExp.coeff n]; push_cast; rfl⟩) γ hγ m
    have hdil := ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul F (one_mem_strictPeriods_conj γ hγ) hp0 n
    simp only [ModularFormClass.qCoeff] at hdil
    have hcoe : (fun τ : ℍ => ((⇑(ModularCurve.restrictForm hle w.form) : ℍ → ℂ) ∣[(1 : ℤ)] γ) (ModularForm.heckeDiagMatrix p • τ))
        = fun τ : ℍ => F (ModularForm.heckeDiagMatrix p • τ) := by
      ext τ; rw [ModularCurve.coe_restrictForm, hF]
    rw [hcoe, hdil]
    split_ifs with hd
    · obtain ⟨r, hr⟩ := hrat (n / p)
      rw [hr]; exact SubfieldClass.ratCast_mem _ r
    · exact zero_mem _

end S_ModularCurve_exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp_of_three_le
end P2MW
export P2MW.S_ModularCurve_exists_odd_isIntegralQExp_qExpansion_atkinLehnerSlash_coeff_mem_adjoin_exp_of_three_le (solution)
