-- Prove2me | solution 1 for ModularCurve.relIndex_gamma0_le_relrank_adjoin_insert_jqNModC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/3b87e9e7-d89b-5824-b346-617c8d104a78

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Theorems.Thm_Matrix_exists_specialLinearGroup_mul_upperTriangular
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_ModularCurve_coeff_jqModC_pow_of_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_relIndex_gamma0_le_relrank_adjoin_insert_jqNModC

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm Pointwise

namespace RelIndexJqSol

open ModularCurve HahnSeries UpperHalfPlane CongruenceSubgroup IntermediateField ModularForm EisensteinSeries Matrix

section LevelOne

abbrev SLtop : Subgroup (GL (Fin 2) ℝ) := ((⊤ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem one_mem_strictPeriods {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) :
    (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples _

theorem hSL1 : (1 : ℝ) ∈ (SLtop).strictPeriods := one_mem_strictPeriods (Subgroup.mem_top _)

theorem isIntegralQExp_E4 : IsIntegralQExp (E₄ : ℍ → ℂ) eisenstein4 := by
  rw [isIntegralQExp_iff]
  intro n
  rw [E_qExpansion_coeff (by norm_num) (by decide) n, eisenstein4, PowerSeries.coeff_mk]
  split_ifs with h
  · simp
  · rw [show _root_.bernoulli 4 = -1 / 30 by decide +kernel, ArithmeticFunction.sigma_apply]
    push_cast
    ring

def AF : ModularForm SLtop 12 :=
  restrictForm (Subgroup.map_le_range _ ⊤) ((E₄.pow 3).mcast (by norm_num))

def DF : ModularForm SLtop 12 :=
  restrictForm (Subgroup.map_le_range _ ⊤) (CuspForm.discriminant : ModularForm 𝒮ℒ 12)

theorem isIntegralQExp_AF : IsIntegralQExp (AF : ℍ → ℂ) (eisenstein4 ^ 3) := by
  rw [IsIntegralQExp, AF, coe_restrictForm, map_pow, isIntegralQExp_E4]
  rw [ModularForm.qExpansion_mcast, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

theorem coe_DF : (DF : ℍ → ℂ) = ModularForm.discriminant := rfl

theorem isIntegralQExp_DF : IsIntegralQExp (DF : ℍ → ℂ) (PowerSeries.X * dedekindEtaUnit) := by
  rw [IsIntegralQExp, coe_DF]
  exact ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit.symm

def qC (F : ℍ → ℂ) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 F)

theorem intSeriesC_eq_qC {F : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp F p) :
    intSeriesC ℂ p = qC F := by
  rw [intSeriesC, qC]; exact congrArg _ h

def XA : LaurentSeries ℂ := qC AF
def XD : LaurentSeries ℂ := qC DF
def jC : LaurentSeries ℂ := XA / XD

theorem XD_ne_zero : XD ≠ 0 := by
  rw [XD, ← intSeriesC_eq_qC isIntegralQExp_DF]
  intro h
  have h1 := congrArg (fun z : LaurentSeries ℂ => z.coeff 1) h
  simp only [intSeriesC, HahnSeries.coeff_zero] at h1
  have h2 : (HahnSeries.ofPowerSeries ℤ ℂ
      ((PowerSeries.X * dedekindEtaUnit).map (Int.castRingHom ℂ))).coeff ((1 : ℕ) : ℤ) = 1 := by
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_dedekindEtaUnit, map_one]
  rw [show ((1 : ℕ) : ℤ) = 1 from rfl] at h2
  rw [h2] at h1
  exact one_ne_zero h1

theorem jqModC_mul_delta :
    jqModC ℂ * intSeriesC ℂ (PowerSeries.X * dedekindEtaUnit) = intSeriesC ℂ (eisenstein4 ^ 3) := by
  rw [jqModC, intSeriesC, intSeriesC, jNum, mul_assoc, ← map_mul, ← map_mul,
    show eisenstein4 ^ 3 * dedekindEtaUnitInv * (PowerSeries.X * dedekindEtaUnit) =
      PowerSeries.X * eisenstein4 ^ 3 by
        rw [mul_comm PowerSeries.X dedekindEtaUnit, ← mul_assoc, mul_assoc (eisenstein4 ^ 3),
          mul_comm dedekindEtaUnitInv, dedekindEtaUnit_mul_inv, mul_one, mul_comm],
    map_mul, PowerSeries.map_X, map_mul, HahnSeries.ofPowerSeries_X, ← mul_assoc,
    HahnSeries.single_mul_single]
  simp

theorem jqModC_eq_jC : jqModC ℂ = jC := by
  rw [jC, XA, XD, ← intSeriesC_eq_qC isIntegralQExp_AF, ← intSeriesC_eq_qC isIntegralQExp_DF,
    eq_div_iff, jqModC_mul_delta]
  rw [intSeriesC_eq_qC isIntegralQExp_DF]
  exact XD_ne_zero

theorem XA_ne_zero : XA ≠ 0 := by
  intro h
  have : jqModC ℂ = 0 := by rw [jqModC_eq_jC, jC, h, zero_div]
  have h1 := ModularCurve.coeff_jqModC_neg_one ℂ
  rw [this, HahnSeries.coeff_zero] at h1
  exact zero_ne_one h1

theorem jC_ne_zero : jC ≠ 0 := div_ne_zero XA_ne_zero XD_ne_zero

theorem jC_coeff_neg_one : jC.coeff (-1) = 1 := by
  rw [← jqModC_eq_jC]; exact ModularCurve.coeff_jqModC_neg_one ℂ

theorem jC_coeff_of_lt {m : ℤ} (hm : m < -1) : jC.coeff m = 0 := by
  rw [← jqModC_eq_jC]
  have := ModularCurve.coeff_jqModC_pow_of_lt ℂ (b := 1) (m := m) (by simpa using hm)
  rwa [pow_one] at this

end LevelOne

section Groups

variable (N : ℕ) [NeZero N]

def dMul (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ := !![(N : ℤ) * γ 0 0, (N : ℤ) * γ 0 1; γ 1 0, γ 1 1]

theorem det_dMul (γ : SL(2, ℤ)) : (dMul N γ).det = N := by
  have hdet := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at hdet
  rw [dMul, Matrix.det_fin_two_of]
  linear_combination (N : ℤ) * hdet

theorem dMul_eq (γ : SL(2, ℤ)) : dMul N γ = !![(N : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dMul, Matrix.mul_apply, Fin.sum_univ_two]

theorem exists_hermite (γ : SL(2, ℤ)) :
    ∃ (δ : SL(2, ℤ)) (a b d : ℤ), 0 < a ∧ 0 ≤ b ∧ b < d ∧ 0 < d ∧ a * d = N ∧
      dMul N γ = (δ : Matrix (Fin 2) (Fin 2) ℤ) * !![a, b; 0, d] := by
  obtain ⟨B, a, b, d, ha, hb, hbd, had, hM⟩ :=
    Matrix.exists_specialLinearGroup_mul_upperTriangular (dMul N γ)
      (by rw [det_dMul]; exact_mod_cast NeZero.ne N)
  rw [det_dMul] at had
  have hd : 0 < d := by
    have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    rw [← had] at hN
    exact pos_of_mul_pos_right hN ha.le
  refine ⟨B, a, b, d, ha, hb, ?_, hd, had, hM⟩
  rwa [abs_of_pos hd] at hbd

def hδ (γ : SL(2, ℤ)) : SL(2, ℤ) := (exists_hermite N γ).choose
def hA (γ : SL(2, ℤ)) : ℤ := (exists_hermite N γ).choose_spec.choose
def hB (γ : SL(2, ℤ)) : ℤ := (exists_hermite N γ).choose_spec.choose_spec.choose
def hD (γ : SL(2, ℤ)) : ℤ := (exists_hermite N γ).choose_spec.choose_spec.choose_spec.choose

theorem hermite_spec (γ : SL(2, ℤ)) :
    0 < hA N γ ∧ 0 ≤ hB N γ ∧ hB N γ < hD N γ ∧ 0 < hD N γ ∧ hA N γ * hD N γ = N ∧
      dMul N γ = (hδ N γ : Matrix (Fin 2) (Fin 2) ℤ) * !![hA N γ, hB N γ; 0, hD N γ] :=
  (exists_hermite N γ).choose_spec.choose_spec.choose_spec.choose_spec

theorem hA_pos (γ : SL(2, ℤ)) : 0 < hA N γ := (hermite_spec N γ).1
theorem hB_nonneg (γ : SL(2, ℤ)) : 0 ≤ hB N γ := (hermite_spec N γ).2.1
theorem hB_lt (γ : SL(2, ℤ)) : hB N γ < hD N γ := (hermite_spec N γ).2.2.1
theorem hD_pos (γ : SL(2, ℤ)) : 0 < hD N γ := (hermite_spec N γ).2.2.2.1
theorem hA_mul_hD (γ : SL(2, ℤ)) : hA N γ * hD N γ = N := (hermite_spec N γ).2.2.2.2.1
theorem dMul_eq_hermite (γ : SL(2, ℤ)) :
    dMul N γ = (hδ N γ : Matrix (Fin 2) (Fin 2) ℤ) * !![hA N γ, hB N γ; 0, hD N γ] :=
  (hermite_spec N γ).2.2.2.2.2

def nA (γ : SL(2, ℤ)) : ℕ := (hA N γ).toNat
def nB (γ : SL(2, ℤ)) : ℕ := (hB N γ).toNat
def nD (γ : SL(2, ℤ)) : ℕ := (hD N γ).toNat

theorem nA_cast (γ : SL(2, ℤ)) : (nA N γ : ℤ) = hA N γ := Int.toNat_of_nonneg (hA_pos N γ).le
theorem nB_cast (γ : SL(2, ℤ)) : (nB N γ : ℤ) = hB N γ := Int.toNat_of_nonneg (hB_nonneg N γ)
theorem nD_cast (γ : SL(2, ℤ)) : (nD N γ : ℤ) = hD N γ := Int.toNat_of_nonneg (hD_pos N γ).le

theorem nA_ne_zero (γ : SL(2, ℤ)) : nA N γ ≠ 0 := by
  intro h; have := nA_cast N γ; rw [h] at this; have := hA_pos N γ; omega
theorem nD_ne_zero (γ : SL(2, ℤ)) : nD N γ ≠ 0 := by
  intro h; have := nD_cast N γ; rw [h] at this; have := hD_pos N γ; omega
theorem nB_lt_nD (γ : SL(2, ℤ)) : nB N γ < nD N γ := by
  have h1 := nB_cast N γ; have h2 := nD_cast N γ; have := hB_lt N γ; omega
theorem nA_mul_nD (γ : SL(2, ℤ)) : nA N γ * nD N γ = N := by
  have h1 := nA_cast N γ; have h2 := nD_cast N γ; have := hA_mul_hD N γ
  have : ((nA N γ * nD N γ : ℕ) : ℤ) = N := by push_cast; rw [h1, h2, this]
  exact_mod_cast this

theorem mul_inv_mem_Gamma0_of_hermite_eq {γ₁ γ₂ : SL(2, ℤ)} (ha : hA N γ₁ = hA N γ₂)
    (hb : hB N γ₁ = hB N γ₂) (hd : hD N γ₁ = hD N γ₂) : γ₂ * γ₁⁻¹ ∈ Gamma0 N := by

  set H : Matrix (Fin 2) (Fin 2) ℤ := !![hA N γ₁, hB N γ₁; 0, hD N γ₁] with hH
  have h1 : dMul N γ₁ = (hδ N γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * H := dMul_eq_hermite N γ₁
  have h2 : dMul N γ₂ = (hδ N γ₂ : Matrix (Fin 2) (Fin 2) ℤ) * H := by
    rw [dMul_eq_hermite N γ₂, hH, ha, hb, hd]
  set Dm : Matrix (Fin 2) (Fin 2) ℤ := !![(N : ℤ), 0; 0, 1] with hDm
  have hX : Dm * ((γ₂ * γ₁⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      ((hδ N γ₂ * (hδ N γ₁)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * Dm := by
    have e1 : Dm * (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) = (hδ N γ₁ : Matrix _ _ ℤ) * H := by
      rw [← dMul_eq]; exact h1
    have e2 : Dm * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) = (hδ N γ₂ : Matrix _ _ ℤ) * H := by
      rw [← dMul_eq]; exact h2
    have hinv1 : (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ₁⁻¹ : SL(2, ℤ)) : Matrix _ _ ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hinv2 : (((hδ N γ₁)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (hδ N γ₁ : Matrix _ _ ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

    have eH : H = (((hδ N γ₁)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (Dm * (γ₁ : Matrix _ _ ℤ)) := by
      rw [e1, ← Matrix.mul_assoc, hinv2, Matrix.one_mul]
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mul_assoc, e2, eH]
    simp only [Matrix.mul_assoc]
    rw [hinv1, Matrix.mul_one]

  have h10 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A 1 0) hX
  simp only [hDm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h10
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
  refine ⟨((hδ N γ₂ * (hδ N γ₁)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0, ?_⟩
  linarith

def hP (γ : SL(2, ℤ)) : GL (Fin 2) ℝ :=
  upperTriangularGL (hA N γ) (hB N γ) (hD N γ)
    (by exact_mod_cast (mul_pos (hA_pos N γ) (hD_pos N γ)).ne')

theorem val_hP (γ : SL(2, ℤ)) :
    ((hP N γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(hA N γ : ℝ), (hB N γ : ℝ); 0, (hD N γ : ℝ)] :=
  rfl

theorem heckeDiag_mul_eq (γ : SL(2, ℤ)) :
    heckeDiagMatrix N * ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) = ((hδ N γ : SL(2, ℤ)) : GL (Fin 2) ℝ) * hP N γ := by
  have hM := dMul_eq_hermite N γ
  have hent : ∀ i j, (dMul N γ i j : ℝ) =
      (((hδ N γ : Matrix (Fin 2) (Fin 2) ℤ) * !![hA N γ, hB N γ; 0, hD N γ]) i j : ℝ) := by
    intro i j; rw [hM]
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, val_heckeDiagMatrix (NeZero.ne N), val_hP]
  have h := hent i j
  fin_cases i <;> fin_cases j <;>
    simp [dMul, Matrix.mul_apply, Fin.sum_univ_two] at h ⊢ <;> linarith

theorem heckeDiag_smul_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    heckeDiagMatrix N • ((γ : SL(2, ℤ)) • τ) = (hδ N γ : SL(2, ℤ)) • (hP N γ • τ) := by
  rw [ModularGroup.sl_moeb, ModularGroup.sl_moeb, ← mul_smul, ← mul_smul, heckeDiag_mul_eq]

theorem coe_upperRightHom_smul (x : ℝ) (τ : ℍ) :
    (((Matrix.GeneralLinearGroup.upperRightHom x • τ : ℍ)) : ℂ) = (τ : ℂ) + x := by
  have hdet : 0 < ((Matrix.GeneralLinearGroup.upperRightHom x).det : ℝˣ).val := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    simp [Matrix.det_fin_two_of]
  rw [UpperHalfPlane.coe_smul_of_det_pos hdet]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom]

theorem coe_hP_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    (((hP N γ • τ : ℍ)) : ℂ) = ((hA N γ : ℂ) * τ + (hB N γ : ℂ)) / (hD N γ : ℂ) := by
  have hdet : 0 < ((hP N γ).det : ℝˣ).val := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, val_hP, Matrix.det_fin_two_of]
    have := mul_pos (hA_pos N γ) (hD_pos N γ)
    simp only [mul_zero, sub_zero]
    exact_mod_cast this
  rw [UpperHalfPlane.coe_smul_of_det_pos hdet]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, val_hP]

theorem hP_smul_heckeDiag_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    hP N γ • (heckeDiagMatrix N • τ) =
      Matrix.GeneralLinearGroup.upperRightHom ((hB N γ : ℝ) / (hD N γ : ℝ)) •
        (heckeDiagMatrix (nA N γ ^ 2) • τ) := by
  have hN : N ≠ 0 := NeZero.ne N
  have ha2 : nA N γ ^ 2 ≠ 0 := pow_ne_zero _ (nA_ne_zero N γ)
  have hd' : (hD N γ : ℂ) ≠ 0 := by exact_mod_cast (hD_pos N γ).ne'
  have had : (hA N γ : ℂ) * (hD N γ : ℂ) = N := by exact_mod_cast hA_mul_hD N γ
  have haN : ((nA N γ ^ 2 : ℕ) : ℂ) = (hA N γ : ℂ) ^ 2 := by
    push_cast; rw [← nA_cast N γ]; push_cast; ring
  apply UpperHalfPlane.ext
  rw [coe_hP_smul, coe_heckeDiagMatrix_smul hN, coe_upperRightHom_smul, coe_heckeDiagMatrix_smul ha2,
    haN]
  push_cast
  field_simp
  rw [← had]
  ring

end Groups

section Raise

variable {Γg : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

theorem one_mem_strictPeriods_conj (g : GL (Fin 2) ℝ)
    (h : g * Matrix.GeneralLinearGroup.upperRightHom (1 : ℝ) * g⁻¹ ∈ Γg) :
    (1 : ℝ) ∈ (ConjAct.toConjAct g⁻¹ • Γg).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ← ConjAct.toConjAct_inv, inv_inv, ConjAct.toConjAct_smul]
  exact h

theorem natCast_mem_strictPeriods (hΓ : (1 : ℝ) ∈ Γg.strictPeriods) (t : ℕ) :
    (t : ℝ) ∈ Γg.strictPeriods := by
  simpa using AddSubgroup.nsmul_mem _ hΓ t

theorem heckeDiag_conj_upperRightHom {t : ℕ} (ht : t ≠ 0) :
    heckeDiagMatrix t * Matrix.GeneralLinearGroup.upperRightHom (1 : ℝ) * (heckeDiagMatrix t)⁻¹ =
      Matrix.GeneralLinearGroup.upperRightHom (t : ℝ) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, val_heckeDiagMatrix ht]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.upperRightHom]

theorem one_mem_strictPeriods_conjDiag (hΓ : (1 : ℝ) ∈ Γg.strictPeriods) {t : ℕ} (ht : t ≠ 0) :
    (1 : ℝ) ∈ (ConjAct.toConjAct (heckeDiagMatrix t)⁻¹ • Γg).strictPeriods := by
  refine one_mem_strictPeriods_conj _ ?_
  rw [heckeDiag_conj_upperRightHom ht]
  exact (Subgroup.mem_strictPeriods_iff).mp (natCast_mem_strictPeriods hΓ t)

def raise (t : ℕ) [NeZero t] (f : ModularForm Γg k) :
    ModularForm (ConjAct.toConjAct (heckeDiagMatrix t)⁻¹ • Γg) k :=
  ((t : ℝ) ^ (k - 1))⁻¹ • ModularForm.translate f (heckeDiagMatrix t)

theorem raise_apply (t : ℕ) [NeZero t] (f : ModularForm Γg k) (τ : ℍ) :
    raise t f τ = f (heckeDiagMatrix t • τ) := by
  have ht : (t : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne t
  show ((t : ℝ) ^ (k - 1))⁻¹ • ((⇑f ∣[k] heckeDiagMatrix t) τ) = _
  rw [slash_heckeDiagMatrix_apply k (NeZero.ne t), Complex.real_smul]
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ ht), one_mul]

theorem coe_raise (t : ℕ) [NeZero t] (f : ModularForm Γg k) :
    ⇑(raise t f) = fun τ => f (heckeDiagMatrix t • τ) :=
  funext (raise_apply t f)

theorem coeff_qExpansion_raise (hΓ : (1 : ℝ) ∈ Γg.strictPeriods) (t : ℕ) [NeZero t]
    (f : ModularForm Γg k) (n : ℕ) :
    PowerSeries.coeff n (qExpansion 1 (raise t f)) =
      if t ∣ n then PowerSeries.coeff (n / t) (qExpansion 1 f) else 0 := by
  rw [coe_raise]
  exact ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul f hΓ (NeZero.ne t) n

theorem qC_eq_qExpand_of_coeff {G F : ℍ → ℂ} (t : ℕ) [NeZero t]
    (h : ∀ n : ℕ, PowerSeries.coeff n (qExpansion 1 G) =
      if t ∣ n then PowerSeries.coeff (n / t) (qExpansion 1 F) else 0) :
    qC G = qExpand ℂ t (qC F) := by
  ext m
  rw [qC, qC]
  by_cases hdvd : (t : ℤ) ∣ m
  · obtain ⟨j, rfl⟩ := hdvd
    rw [qExpand_coeff_mul, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
    have ht0 : (0 : ℤ) < t := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne t)
    by_cases hj : j < 0
    · rw [if_pos hj, if_pos (mul_neg_of_pos_of_neg ht0 hj)]
    · rw [if_neg hj, if_neg (by push Not at hj ⊢; positivity)]
      rw [h]
      have h1 : ((t : ℤ) * j).natAbs = t * j.natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      rw [h1, if_pos (Dvd.intro _ rfl), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne t))]
  · rw [qExpand_coeff_of_not_dvd t _ hdvd, PowerSeries.coeff_coe]
    split_ifs with hm
    · rfl
    · rw [h, if_neg]
      rintro ⟨c, hc⟩
      apply hdvd
      refine ⟨c, ?_⟩
      have : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg (le_of_not_gt hm)
      rw [← this, hc]; push_cast; ring

theorem qC_raise (hΓ : (1 : ℝ) ∈ Γg.strictPeriods) (t : ℕ) [NeZero t] (f : ModularForm Γg k) :
    qC (raise t f) = qExpand ℂ t (qC f) :=
  qC_eq_qExpand_of_coeff t (coeff_qExpansion_raise hΓ t f)

abbrev Ux (x : ℝ) : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.upperRightHom x

def twist (x : ℝ) (F : ModularForm Γg k) : ModularForm (ConjAct.toConjAct (Ux x)⁻¹ • Γg) k :=
  ModularForm.translate F (Ux x)

theorem twist_apply (x : ℝ) (F : ModularForm Γg k) (τ : ℍ) : twist x F τ = F (Ux x • τ) := by
  rw [twist, ModularForm.coe_translate, ModularForm.slash_apply]
  have hdet : ((Ux x).det : ℝˣ).val = 1 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]; simp [Matrix.det_fin_two_of]
  have hσ : UpperHalfPlane.σ (Ux x) = .refl ℝ ℂ := by
    rw [UpperHalfPlane.σ, if_pos (by rw [hdet]; exact one_pos)]
  have hden : UpperHalfPlane.denom (Ux x) τ = 1 := by
    simp [UpperHalfPlane.denom]
  rw [hσ, hdet, hden]
  simp

theorem coe_twist (x : ℝ) (F : ModularForm Γg k) : ⇑(twist x F) = fun τ => F (Ux x • τ) :=
  funext (twist_apply x F)

theorem one_mem_strictPeriods_twist (hΓ : (1 : ℝ) ∈ Γg.strictPeriods) (x : ℝ) :
    (1 : ℝ) ∈ (ConjAct.toConjAct (Ux x)⁻¹ • Γg).strictPeriods := by
  refine one_mem_strictPeriods_conj _ ?_
  have hcomm : Ux x * Matrix.GeneralLinearGroup.upperRightHom (1 : ℝ) * (Ux x)⁻¹ =
      Matrix.GeneralLinearGroup.upperRightHom (1 : ℝ) := by
    rw [Ux, ← AddChar.map_add_eq_mul, ← AddChar.map_neg_eq_inv, ← AddChar.map_add_eq_mul]
    congr 1; ring
  rw [hcomm]
  exact (Subgroup.mem_strictPeriods_iff).mp hΓ

theorem qParam_Ux_smul (x : ℝ) (τ : ℍ) :
    Function.Periodic.qParam 1 ((Ux x • τ : ℍ) : ℂ) =
      Complex.exp (2 * Real.pi * Complex.I * x) * Function.Periodic.qParam 1 τ := by
  rw [Function.Periodic.qParam, Function.Periodic.qParam, coe_upperRightHom_smul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem coeff_qExpansion_twist (hΓ : (1 : ℝ) ∈ Γg.strictPeriods) (x : ℝ) (F : ModularForm Γg k) (m : ℕ) :
    (qExpansion 1 (twist x F)).coeff m =
      Complex.exp (2 * Real.pi * Complex.I * x) ^ m * (qExpansion 1 F).coeff m := by
  haveI : Fact (IsCusp OnePoint.infty Γg) := ⟨Γg.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex F hΓ
  have hhol := ModularFormClass.holo F
  have hbdd : IsBoundedAtImInfty (F : ℍ → ℂ) := ModularFormClass.bdd_at_infty F
  have hF : ∀ τ : ℍ, HasSum (fun n : ℕ => (Complex.exp (2 * Real.pi * Complex.I * x) ^ n *
      (qExpansion 1 F).coeff n) • Function.Periodic.qParam 1 τ ^ n) (twist x F τ) := by
    intro τ
    have h := hasSum_qExpansion one_pos hper hhol hbdd (Ux x • τ)
    have hfun : (fun n : ℕ => (Complex.exp (2 * Real.pi * Complex.I * x) ^ n * (qExpansion 1 F).coeff n) •
        Function.Periodic.qParam 1 τ ^ n) =
        fun n : ℕ => (qExpansion 1 F).coeff n • Function.Periodic.qParam 1 ((Ux x • τ : ℍ) : ℂ) ^ n := by
      funext n
      rw [qParam_Ux_smul, mul_pow, smul_eq_mul, smul_eq_mul]
      ring
    rw [hfun, twist_apply]
    exact h
  exact (ModularFormClass.qExpansion_coeff_unique one_pos (one_mem_strictPeriods_twist hΓ x) hF m).symm

end Raise

section TwistRaise

variable {Γg : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

def expU (x : ℝ) : ℂˣ := Units.mk0 (Complex.exp (2 * Real.pi * Complex.I * x)) (Complex.exp_ne_zero _)

@[scoped simp] theorem val_expU (x : ℝ) : (expU x : ℂ) = Complex.exp (2 * Real.pi * Complex.I * x) := rfl

theorem qC_twist (hΓ : (1 : ℝ) ∈ Γg.strictPeriods) (x : ℝ) (F : ModularForm Γg k) :
    qC (twist x F) = qTwist (expU x) (qC F) := by
  ext n
  rw [qTwist_coeff, qC, qC]
  by_cases hn : 0 ≤ n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [ofPowerSeries_apply_coeff, ofPowerSeries_apply_coeff, coeff_qExpansion_twist hΓ]
    rw [zpow_natCast, Units.val_pow_eq_pow_val, val_expU]
  · have h1 : (ofPowerSeries ℤ ℂ (qExpansion 1 (twist x F))).coeff n = 0 := by
      rw [PowerSeries.coeff_coe, if_pos (lt_of_not_ge hn)]
    have h2 : (ofPowerSeries ℤ ℂ (qExpansion 1 F)).coeff n = 0 := by
      rw [PowerSeries.coeff_coe, if_pos (lt_of_not_ge hn)]
    rw [h1, h2, mul_zero]

def twRaiseFn (x : ℝ) (t : ℕ) (F : ModularForm Γg k) : ℍ → ℂ :=
  fun τ => F (Ux x • (heckeDiagMatrix t • τ))

theorem twRaiseFn_eq (x : ℝ) (t : ℕ) [NeZero t] (F : ModularForm Γg k) :
    twRaiseFn x t F = ⇑(raise t (twist x F)) := by
  funext τ
  rw [raise_apply, twist_apply]
  rfl

theorem qC_twRaiseFn (hΓ : (1 : ℝ) ∈ Γg.strictPeriods) (x : ℝ) (t : ℕ) [NeZero t] (F : ModularForm Γg k) :
    qC (twRaiseFn x t F) = qExpand ℂ t (qTwist (expU x) (qC F)) := by
  rw [twRaiseFn_eq, qC_raise (one_mem_strictPeriods_twist hΓ x), qC_twist hΓ]

end TwistRaise

section Analytic

def An1 (f : ℍ → ℂ) : Prop := AnalyticAt ℂ (cuspFunction 1 f) 0

theorem cuspFunction_one' : cuspFunction 1 (1 : ℍ → ℂ) = 1 := by
  ext q
  rcases eq_or_ne q 0 with rfl | hq
  · simp [cuspFunction, Function.Periodic.cuspFunction]
    exact Filter.Tendsto.limUnder_eq
      (tendsto_const_nhds (x := (1 : ℂ)))
  · simp [cuspFunction, Function.Periodic.cuspFunction_eq_of_nonzero 1 _ hq]

theorem An1.one : An1 (1 : ℍ → ℂ) := by
  rw [An1, cuspFunction_one']; exact analyticAt_const

theorem An1.mul {f g : ℍ → ℂ} (hf : An1 f) (hg : An1 g) : An1 (f * g) := by
  rw [An1, cuspFunction_mul hf.continuousAt hg.continuousAt]
  exact AnalyticAt.mul hf hg

theorem An1.pow {f : ℍ → ℂ} (hf : An1 f) (n : ℕ) : An1 (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact An1.one
  | succ n ih => rw [pow_succ]; exact ih.mul hf

theorem qExpansion_pow' {f : ℍ → ℂ} (hf : An1 f) (n : ℕ) :
    qExpansion 1 (f ^ n) = qExpansion 1 f ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, qExpansion_one]
  | succ n ih => rw [pow_succ, pow_succ, qExpansion_mul (hf.pow n) hf, ih]

theorem cuspFunction_zero' : cuspFunction 1 (0 : ℍ → ℂ) = 0 := by
  ext q
  rcases eq_or_ne q 0 with rfl | hq
  · simp [cuspFunction, Function.Periodic.cuspFunction]
    exact Filter.Tendsto.limUnder_eq
      (tendsto_const_nhds (x := (0 : ℂ)))
  · simp [cuspFunction, Function.Periodic.cuspFunction_eq_of_nonzero 1 _ hq]

theorem An1.zero : An1 (0 : ℍ → ℂ) := by
  rw [An1, cuspFunction_zero']; exact analyticAt_const

theorem An1.add {f g : ℍ → ℂ} (hf : An1 f) (hg : An1 g) : An1 (f + g) := by
  rw [An1, cuspFunction_add hf.continuousAt hg.continuousAt]
  exact AnalyticAt.add hf hg

theorem An1.sum {ι : Type*} (s : Finset ι) {f : ι → ℍ → ℂ} (hf : ∀ i ∈ s, An1 (f i)) :
    An1 (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact An1.zero
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem qExpansion_sum' {ι : Type*} (s : Finset ι) {f : ι → ℍ → ℂ} (hf : ∀ i ∈ s, An1 (f i)) :
    qExpansion 1 (∑ i ∈ s, f i) = ∑ i ∈ s, qExpansion 1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, qExpansion_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        qExpansion_add (hf a (Finset.mem_insert_self a s))
          (An1.sum s fun i hi => hf i (Finset.mem_insert_of_mem hi)),
        ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem An1.of_form {Γg : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (hΓ : (1 : ℝ) ∈ Γg.strictPeriods)
    (f : ModularForm Γg k) : An1 ⇑f :=
  ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ

end Analytic

section Core

variable (Γ : Subgroup SL(2, ℤ)) (N : ℕ) [NeZero N]

abbrev GamGL : Subgroup (GL (Fin 2) ℝ) := ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

abbrev Gam'GL : Subgroup (GL (Fin 2) ℝ) := ((Γ ⊓ Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {Γ N}

theorem T_mem_inf (hT : ModularGroup.T ∈ Γ) : ModularGroup.T ∈ Γ ⊓ Gamma0 N := by
  refine Subgroup.mem_inf.mpr ⟨hT, ?_⟩
  rw [Gamma0_mem]
  simp [ModularGroup.T]

theorem hΓ1 (hT : ModularGroup.T ∈ Γ) : (1 : ℝ) ∈ (GamGL Γ).strictPeriods := one_mem_strictPeriods hT

theorem hΓ'1 (hT : ModularGroup.T ∈ Γ) : (1 : ℝ) ∈ (Gam'GL Γ N).strictPeriods :=
  one_mem_strictPeriods (T_mem_inf hT)

def conjMat (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![γ 0 0, (N : ℤ) * γ 0 1; γ 1 0 / N, γ 1 1]

theorem det_conjMat (γ : SL(2, ℤ)) (h : (N : ℤ) ∣ γ 1 0) : (conjMat (N := N) γ).det = 1 := by
  obtain ⟨c, hc⟩ := h
  have hdet := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at hdet ⊢
  have h0 : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have h1 : (N : ℤ) * c / N = c := by rw [mul_comm]; exact Int.mul_ediv_cancel c h0
  simp only [conjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, hc, h1] at hdet ⊢
  linear_combination hdet

def conjSL (γ : SL(2, ℤ)) (h : (N : ℤ) ∣ γ 1 0) : SL(2, ℤ) := ⟨conjMat (N := N) γ, det_conjMat γ h⟩

theorem dvd_of_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) : (N : ℤ) ∣ γ 1 0 := by
  rw [Gamma0_mem] at hγ
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ

theorem heckeDiag_mul_mul_inv {γ : SL(2, ℤ)} (h : (N : ℤ) ∣ γ 1 0) :
    heckeDiagMatrix N * (γ : GL (Fin 2) ℝ) * (heckeDiagMatrix N)⁻¹ =
      ((conjSL γ h : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  obtain ⟨c, hc⟩ := h
  have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have h10 : (conjSL γ ⟨c, hc⟩ : SL(2, ℤ)) 1 0 = c := by
    show γ 1 0 / N = c
    rw [hc]; exact Int.mul_ediv_cancel_left _ hN'
  have h00 : (conjSL γ ⟨c, hc⟩ : SL(2, ℤ)) 0 0 = γ 0 0 := rfl
  have h01 : (conjSL γ ⟨c, hc⟩ : SL(2, ℤ)) 0 1 = (N : ℤ) * γ 0 1 := rfl
  have h11 : (conjSL γ ⟨c, hc⟩ : SL(2, ℤ)) 1 1 = γ 1 1 := rfl
  simp only [Matrix.GeneralLinearGroup.coe_mul, val_heckeDiagMatrix (NeZero.ne N)]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h10, h00, h01, h11, hc] <;> ring

variable (Γ N) in

theorem gam'_le_conj :
    Gam'GL Γ N ≤ ConjAct.toConjAct (heckeDiagMatrix N)⁻¹ • SLtop := by
  rintro x ⟨γ, hγ, rfl⟩
  obtain ⟨-, hγ0⟩ := Subgroup.mem_inf.mp hγ
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  exact ⟨_, Subgroup.mem_top _, (heckeDiag_mul_mul_inv (dvd_of_mem_Gamma0 hγ0)).symm⟩

variable (Γ N) in

def LA : ModularForm (Gam'GL Γ N) 12 := restrictForm (gam'_le_conj Γ N) (raise N AF)
variable (Γ N) in

def LD : ModularForm (Gam'GL Γ N) 12 := restrictForm (gam'_le_conj Γ N) (raise N DF)

theorem LA_apply (τ : ℍ) : LA Γ N τ = AF (heckeDiagMatrix N • τ) := by
  rw [LA, restrictForm_apply, raise_apply]

theorem LD_apply (τ : ℍ) : LD Γ N τ = DF (heckeDiagMatrix N • τ) := by
  rw [LD, restrictForm_apply, raise_apply]

theorem qC_LA : qC (LA Γ N) = qExpand ℂ N XA := by
  rw [LA, coe_restrictForm]; exact qC_raise hSL1 N AF

theorem qC_LD : qC (LD Γ N) = qExpand ℂ N XD := by
  rw [LD, coe_restrictForm]; exact qC_raise hSL1 N DF

theorem weight_eq (k : ℤ) {m : ℕ} (i : Fin (m + 1)) :
    k + ((((i : ℕ) : ℤ)) * 12 + ((m - (i : ℕ) : ℕ) : ℤ) * 12) = k + 12 * m := by
  have hi : (i : ℕ) ≤ m := Nat.lt_succ_iff.mp i.is_lt
  push_cast [Nat.cast_sub hi]
  ring

variable (Γ N) in

def termF {k : ℤ} {m : ℕ} (f : Fin (m + 1) → ModularForm (GamGL Γ) k) (i : Fin (m + 1)) :
    ModularForm (Gam'GL Γ N) (k + 12 * m) :=
  ((restrictForm (Subgroup.map_mono inf_le_left) (f i)).mul
    (((LA Γ N).pow (i : ℕ)).mul ((LD Γ N).pow (m - (i : ℕ))))).mcast (weight_eq k i)

variable (Γ N) in

def Phi {k : ℤ} {m : ℕ} (f : Fin (m + 1) → ModularForm (GamGL Γ) k) :
    ModularForm (Gam'GL Γ N) (k + 12 * m) :=
  ∑ i, termF Γ N f i

theorem coe_termF {k : ℤ} {m : ℕ} (f : Fin (m + 1) → ModularForm (GamGL Γ) k) (i : Fin (m + 1)) (τ : ℍ) :
    termF Γ N f i τ = f i τ * LA Γ N τ ^ (i : ℕ) * LD Γ N τ ^ (m - (i : ℕ)) := by
  rw [termF, coe_mcast]
  simp only [coe_mul, coe_pow, Pi.mul_apply, Pi.pow_apply, coe_restrictForm]
  ring

theorem coe_finset_sum {Γg : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {ι : Type*} (s : Finset ι)
    (F : ι → ModularForm Γg k) (τ : ℍ) : (∑ i ∈ s, F i) τ = ∑ i ∈ s, F i τ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ModularForm.add_apply, ih]

theorem Phi_apply {k : ℤ} {m : ℕ} (f : Fin (m + 1) → ModularForm (GamGL Γ) k) (τ : ℍ) :
    Phi Γ N f τ = ∑ i, f i τ * LA Γ N τ ^ (i : ℕ) * LD Γ N τ ^ (m - (i : ℕ)) := by
  rw [Phi, coe_finset_sum]
  simp only [coe_termF]

theorem qExpansion_finset_sum {Γg : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (hΓ : (1 : ℝ) ∈ Γg.strictPeriods)
    {ι : Type*} (s : Finset ι) (F : ι → ModularForm Γg k) :
    qExpansion 1 (⇑(∑ i ∈ s, F i)) = ∑ i ∈ s, qExpansion 1 (F i) := by
  have := map_sum (ModularForm.qExpansionAddHom one_pos hΓ k) F s
  exact this

theorem qC_termF (hT : ModularGroup.T ∈ Γ) {k : ℤ} {m : ℕ} (f : Fin (m + 1) → ModularForm (GamGL Γ) k)
    (i : Fin (m + 1)) :
    qC (termF Γ N f i) = qC (f i) * qExpand ℂ N XA ^ (i : ℕ) * qExpand ℂ N XD ^ (m - (i : ℕ)) := by
  rw [qC, termF, ModularForm.qExpansion_mcast, ModularForm.qExpansion_mul one_pos (hΓ'1 hT),
    ModularForm.qExpansion_mul one_pos (hΓ'1 hT), ModularForm.qExpansion_pow one_pos (hΓ'1 hT),
    ModularForm.qExpansion_pow one_pos (hΓ'1 hT), map_mul, map_mul, map_pow, map_pow,
    ← qC_LA (Γ := Γ) (N := N), ← qC_LD (Γ := Γ) (N := N), mul_assoc]
  rfl

theorem qC_Phi (hT : ModularGroup.T ∈ Γ) {k : ℤ} {m : ℕ} (f : Fin (m + 1) → ModularForm (GamGL Γ) k) :
    qC (Phi Γ N f) = ∑ i, qC (f i) * qExpand ℂ N XA ^ (i : ℕ) * qExpand ℂ N XD ^ (m - (i : ℕ)) := by
  rw [qC, Phi, qExpansion_finset_sum (hΓ'1 hT), map_sum]
  exact Finset.sum_congr rfl fun i _ => qC_termF hT f i

theorem Phi_eq_zero (hT : ModularGroup.T ∈ Γ) {k : ℤ} {m : ℕ} (f : Fin (m + 1) → ModularForm (GamGL Γ) k)
    (hrel : ∑ i, qC (f i) * qExpand ℂ N XA ^ (i : ℕ) * qExpand ℂ N XD ^ (m - (i : ℕ)) = 0) :
    Phi Γ N f = 0 := by
  have h1 : qC (Phi Γ N f) = 0 := by rw [qC_Phi hT, hrel]
  have h2 : qExpansion 1 (Phi Γ N f) = 0 := by
    rw [qC, ← map_zero (ofPowerSeries ℤ ℂ)] at h1
    exact ofPowerSeries_injective h1
  exact (ModularForm.qExpansion_eq_zero_iff one_pos (hΓ'1 hT) _).mp h2

theorem rel_at_P {k : ℤ} {m : ℕ} (f : Fin (m + 1) → ModularForm (GamGL Γ) k)
    (hΦ : Phi Γ N f = 0) {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (τ : ℍ) :
    ∑ i, f i τ * AF (hP N γ • τ) ^ (i : ℕ) * DF (hP N γ • τ) ^ (m - (i : ℕ)) = 0 := by
  have h0 : Phi Γ N f ((γ : SL(2, ℤ)) • τ) = 0 := by rw [hΦ]; rfl
  rw [Phi_apply] at h0
  set d : ℂ := UpperHalfPlane.denom (γ : SL(2, ℤ)) τ with hd
  set w : ℍ := hP N γ • τ with hw
  set e : ℂ := UpperHalfPlane.denom (hδ N γ : SL(2, ℤ)) w with he
  have hd0 : d ≠ 0 := UpperHalfPlane.denom_ne_zero _ _
  have he0 : e ≠ 0 := UpperHalfPlane.denom_ne_zero _ _
  have hf : ∀ i, f i ((γ : SL(2, ℤ)) • τ) = d ^ k * f i τ := fun i =>
    SlashInvariantForm.slash_action_eqn_SL'' (f i) hγ τ
  have hA : LA Γ N ((γ : SL(2, ℤ)) • τ) = e ^ (12 : ℤ) * AF w := by
    rw [LA_apply, heckeDiag_smul_smul]
    exact SlashInvariantForm.slash_action_eqn_SL'' AF (Subgroup.mem_top _) w
  have hD : LD Γ N ((γ : SL(2, ℤ)) • τ) = e ^ (12 : ℤ) * DF w := by
    rw [LD_apply, heckeDiag_smul_smul]
    exact SlashInvariantForm.slash_action_eqn_SL'' DF (Subgroup.mem_top _) w
  simp only [hf, hA, hD] at h0
  have key : ∀ i : Fin (m + 1),
      d ^ k * f i τ * (e ^ (12 : ℤ) * AF w) ^ (i : ℕ) * (e ^ (12 : ℤ) * DF w) ^ (m - (i : ℕ)) =
        (d ^ k * (e ^ (12 : ℤ)) ^ m) * (f i τ * AF w ^ (i : ℕ) * DF w ^ (m - (i : ℕ))) := by
    intro i
    have hi : (i : ℕ) ≤ m := Nat.lt_succ_iff.mp i.is_lt
    have hE : (e ^ (12 : ℤ)) ^ (i : ℕ) * (e ^ (12 : ℤ)) ^ (m - (i : ℕ)) = (e ^ (12 : ℤ)) ^ m := by
      rw [← _root_.pow_add, Nat.add_sub_cancel' hi]
    rw [mul_pow, mul_pow, ← hE]
    ring
  simp only [key, ← Finset.mul_sum] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · exfalso
    exact mul_ne_zero (zpow_ne_zero _ hd0) (pow_ne_zero _ (zpow_ne_zero _ he0)) h
  · exact h

def xOf (γ : SL(2, ℤ)) : ℝ := (hB N γ : ℝ) / (hD N γ : ℝ)

theorem rel_twisted {k : ℤ} {m : ℕ} (f : Fin (m + 1) → ModularForm (GamGL Γ) k)
    (hΦ : Phi Γ N f = 0) {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (τ : ℍ) :
    ∑ i, raise N (f i) τ * twRaiseFn (xOf (N := N) γ) (nA N γ ^ 2) AF τ ^ (i : ℕ) *
      twRaiseFn (xOf (N := N) γ) (nA N γ ^ 2) DF τ ^ (m - (i : ℕ)) = 0 := by
  have := rel_at_P f hΦ hγ (heckeDiagMatrix N • τ)
  rw [hP_smul_heckeDiag_smul] at this
  simp only [raise_apply]
  exact this

def RHom (γ : SL(2, ℤ)) : LaurentSeries ℂ →+* LaurentSeries ℂ :=
  haveI : NeZero (nA N γ ^ 2) := ⟨pow_ne_zero _ (nA_ne_zero N γ)⟩
  (qExpand ℂ (nA N γ ^ 2)).comp (qTwist (expU (xOf (N := N) γ)))

theorem RHom_apply (γ : SL(2, ℤ)) (Y : LaurentSeries ℂ) :
    RHom (N := N) γ Y = (haveI : NeZero (nA N γ ^ 2) := ⟨pow_ne_zero _ (nA_ne_zero N γ)⟩;
      qExpand ℂ (nA N γ ^ 2) (qTwist (expU (xOf (N := N) γ)) Y)) := rfl

theorem RHom_injective (γ : SL(2, ℤ)) : Function.Injective (RHom (N := N) γ) := by
  haveI : NeZero (nA N γ ^ 2) := ⟨pow_ne_zero _ (nA_ne_zero N γ)⟩
  intro Y Z h
  rw [RHom_apply, RHom_apply] at h
  have h1 := qExpand_injective (nA N γ ^ 2) h
  ext n
  have := congrArg (fun z : LaurentSeries ℂ => z.coeff n) h1
  simp only [qTwist_coeff] at this
  exact mul_left_cancel₀ (Units.ne_zero _) this

theorem rel_R (hT : ModularGroup.T ∈ Γ) {k : ℤ} {m : ℕ} (f : Fin (m + 1) → ModularForm (GamGL Γ) k)
    (hΦ : Phi Γ N f = 0) {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) :
    ∑ i, qExpand ℂ N (qC (f i)) * RHom (N := N) γ XA ^ (i : ℕ) * RHom (N := N) γ XD ^ (m - (i : ℕ)) = 0 := by
  haveI : NeZero (nA N γ ^ 2) := ⟨pow_ne_zero _ (nA_ne_zero N γ)⟩
  set x := xOf (N := N) γ with hx
  set t := nA N γ ^ 2 with ht

  set ψ : ℍ → ℂ := ∑ i : Fin (m + 1), (⇑(raise N (f i)) * twRaiseFn x t AF ^ (i : ℕ) *
    twRaiseFn x t DF ^ (m - (i : ℕ))) with hψ
  have hψ0 : ψ = 0 := by
    funext τ
    simp only [hψ, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, Pi.zero_apply]
    exact rel_twisted f hΦ hγ τ
  have hLR : ∀ i, An1 (⇑(raise N (f i))) := fun i =>
    An1.of_form (one_mem_strictPeriods_conjDiag (hΓ1 hT) (NeZero.ne N)) _
  have hTA : An1 (twRaiseFn x t AF) := by
    rw [twRaiseFn_eq]
    exact An1.of_form (one_mem_strictPeriods_conjDiag (one_mem_strictPeriods_twist hSL1 x) (NeZero.ne t)) _
  have hTD : An1 (twRaiseFn x t DF) := by
    rw [twRaiseFn_eq]
    exact An1.of_form (one_mem_strictPeriods_conjDiag (one_mem_strictPeriods_twist hSL1 x) (NeZero.ne t)) _
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin (m + 1))),
      An1 (⇑(raise N (f i)) * twRaiseFn x t AF ^ (i : ℕ) * twRaiseFn x t DF ^ (m - (i : ℕ))) := fun i _ =>
    ((hLR i).mul (hTA.pow _)).mul (hTD.pow _)
  have hq : qExpansion 1 ψ = ∑ i : Fin (m + 1), qExpansion 1 (raise N (f i)) *
      qExpansion 1 (twRaiseFn x t AF) ^ (i : ℕ) * qExpansion 1 (twRaiseFn x t DF) ^ (m - (i : ℕ)) := by
    rw [hψ, qExpansion_sum' _ hterm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [qExpansion_mul ((hLR i).mul (hTA.pow _)) (hTD.pow _), qExpansion_mul (hLR i) (hTA.pow _),
      qExpansion_pow' hTA, qExpansion_pow' hTD]
  rw [hψ0, qExpansion_zero] at hq
  have h2 := congrArg (ofPowerSeries ℤ ℂ) hq
  rw [map_zero, map_sum] at h2
  refine Eq.trans ?_ h2.symm
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, map_pow, map_pow]
  have e1 : ofPowerSeries ℤ ℂ (qExpansion 1 (raise N (f i))) = qExpand ℂ N (qC (f i)) := qC_raise (hΓ1 hT) N (f i)
  have e2 : ofPowerSeries ℤ ℂ (qExpansion 1 (twRaiseFn x t AF)) = RHom (N := N) γ XA := by
    rw [RHom_apply]; exact qC_twRaiseFn hSL1 x t AF
  have e3 : ofPowerSeries ℤ ℂ (qExpansion 1 (twRaiseFn x t DF)) = RHom (N := N) γ XD := by
    rw [RHom_apply]; exact qC_twRaiseFn hSL1 x t DF
  rw [e1, e2, e3]

def rho (γ : SL(2, ℤ)) : LaurentSeries ℂ := RHom (N := N) γ jC

theorem rho_eq_div (γ : SL(2, ℤ)) : rho (N := N) γ = RHom (N := N) γ XA / RHom (N := N) γ XD := by
  rw [rho, jC, map_div₀]

theorem isRoot_of_rel {R : Type*} [Field R] {n : ℕ} (a : Fin (n + 1) → R) {u v : R} (hv : v ≠ 0)
    (h : ∑ i, a i * u ^ (i : ℕ) * v ^ (n - (i : ℕ)) = 0) :
    (∑ i : Fin (n + 1), Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)).IsRoot (u / v) := by
  rw [Polynomial.IsRoot, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have key : (∑ i : Fin (n + 1), a i * (u / v) ^ (i : ℕ)) * v ^ n =
      ∑ i : Fin (n + 1), a i * u ^ (i : ℕ) * v ^ (n - (i : ℕ)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.is_lt
    have hv' : v ^ n = v ^ (i : ℕ) * v ^ (n - (i : ℕ)) := by
      rw [← _root_.pow_add, Nat.add_sub_cancel' hi]
    rw [hv', div_pow]
    field_simp
  rw [h] at key
  rcases mul_eq_zero.mp key with h1 | h1
  · exact h1
  · exact absurd h1 (pow_ne_zero _ hv)

theorem coeff_sum_C_mul_X_pow {R : Type*} [Semiring R] {n : ℕ} (a : Fin (n + 1) → R) (i : Fin (n + 1)) :
    (∑ j : Fin (n + 1), Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)).coeff (i : ℕ) = a i := by
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl]
  · intro j _ hji
    rw [if_neg]
    exact fun h => hji (Fin.ext h.symm)
  · intro h; exact absurd (Finset.mem_univ i) h

theorem natDegree_sum_le {R : Type*} [Semiring R] {n : ℕ} (a : Fin (n + 1) → R) :
    (∑ j : Fin (n + 1), Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)).natDegree ≤ n := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp j.is_lt)

theorem rho_coeff_mul (γ : SL(2, ℤ)) (m' : ℤ) :
    (rho (N := N) γ).coeff (((nA N γ ^ 2 : ℕ) : ℤ) * m') =
      ((expU (xOf (N := N) γ) ^ m' : ℂˣ) : ℂ) * jC.coeff m' := by
  haveI : NeZero (nA N γ ^ 2) := ⟨pow_ne_zero _ (nA_ne_zero N γ)⟩
  rw [rho, RHom_apply, qExpand_coeff_mul, qTwist_coeff]

theorem rho_coeff_of_not_dvd (γ : SL(2, ℤ)) {m' : ℤ} (h : ¬ ((nA N γ ^ 2 : ℕ) : ℤ) ∣ m') :
    (rho (N := N) γ).coeff m' = 0 := by
  haveI : NeZero (nA N γ ^ 2) := ⟨pow_ne_zero _ (nA_ne_zero N γ)⟩
  rw [rho, RHom_apply, qExpand_coeff_of_not_dvd _ _ h]

theorem rho_coeff_neg_sq (γ : SL(2, ℤ)) :
    (rho (N := N) γ).coeff (-((nA N γ ^ 2 : ℕ) : ℤ)) = ((expU (xOf (N := N) γ))⁻¹ : ℂˣ) := by
  have := rho_coeff_mul (N := N) γ (-1)
  rw [mul_neg_one] at this
  rw [this, jC_coeff_neg_one, mul_one, _root_.zpow_neg_one]

theorem nA_eq_of_rho_eq {γ₁ γ₂ : SL(2, ℤ)} (h : rho (N := N) γ₁ = rho (N := N) γ₂) :
    nA N γ₁ = nA N γ₂ := by
  have h1 : (rho (N := N) γ₂).coeff (-((nA N γ₁ ^ 2 : ℕ) : ℤ)) ≠ 0 := by
    rw [← h, rho_coeff_neg_sq]
    exact Units.ne_zero _

  by_cases hdvd : ((nA N γ₂ ^ 2 : ℕ) : ℤ) ∣ -((nA N γ₁ ^ 2 : ℕ) : ℤ)
  · obtain ⟨m', hm'⟩ := hdvd
    rw [hm', rho_coeff_mul] at h1
    have hj : jC.coeff m' ≠ 0 := fun h0 => h1 (by rw [h0, mul_zero])
    have hm'ge : -1 ≤ m' := by
      by_contra hlt
      exact hj (jC_coeff_of_lt (by omega))
    have hpos1 : (0 : ℤ) < ((nA N γ₁ ^ 2 : ℕ) : ℤ) := by
      have := pow_pos (Nat.pos_of_ne_zero (nA_ne_zero N γ₁)) 2
      exact_mod_cast this
    have hpos2 : (0 : ℤ) < ((nA N γ₂ ^ 2 : ℕ) : ℤ) := by
      have := pow_pos (Nat.pos_of_ne_zero (nA_ne_zero N γ₂)) 2
      exact_mod_cast this
    have hm'neg : m' < 0 := by
      by_contra hge
      push Not at hge
      have : (0 : ℤ) ≤ ((nA N γ₂ ^ 2 : ℕ) : ℤ) * m' := mul_nonneg hpos2.le hge
      rw [← hm'] at this
      linarith
    have hm1 : m' = -1 := by omega
    rw [hm1, mul_neg_one, neg_inj] at hm'
    have hsq : nA N γ₁ ^ 2 = nA N γ₂ ^ 2 := by exact_mod_cast hm'
    exact Nat.pow_left_injective (by norm_num) hsq
  · exact absurd (rho_coeff_of_not_dvd γ₂ hdvd) h1

theorem expU_xOf_eq (γ : SL(2, ℤ)) :
    (expU (xOf (N := N) γ) : ℂ) = Complex.exp (2 * Real.pi * Complex.I / (nD N γ)) ^ (nB N γ) := by
  rw [val_expU, ← Complex.exp_nat_mul, xOf]
  congr 1
  have h1 : (hB N γ : ℂ) = (nB N γ : ℂ) := by rw [← nB_cast N γ]; norm_cast
  have h2 : (hD N γ : ℂ) = (nD N γ : ℂ) := by rw [← nD_cast N γ]; norm_cast
  push_cast
  rw [h1, h2]
  have hd : (nD N γ : ℂ) ≠ 0 := by exact_mod_cast nD_ne_zero N γ
  field_simp

theorem mul_inv_mem_of_rho_eq {γ₁ γ₂ : SL(2, ℤ)} (h : rho (N := N) γ₁ = rho (N := N) γ₂) :
    γ₂ * γ₁⁻¹ ∈ Gamma0 N := by
  have ha : nA N γ₁ = nA N γ₂ := nA_eq_of_rho_eq h
  have haI : hA N γ₁ = hA N γ₂ := by rw [← nA_cast, ← nA_cast, ha]
  have hdI : hD N γ₁ = hD N γ₂ := by
    have h1 := hA_mul_hD N γ₁
    have h2 := hA_mul_hD N γ₂
    rw [haI] at h1
    exact mul_left_cancel₀ (hA_pos N γ₂).ne' (h1.trans h2.symm)
  have hd : nD N γ₁ = nD N γ₂ := by
    have := nD_cast N γ₁; have := nD_cast N γ₂; omega

  have hu : (expU (xOf (N := N) γ₁) : ℂ) = expU (xOf (N := N) γ₂) := by
    have h1 := rho_coeff_neg_sq (N := N) γ₁
    have h2 := rho_coeff_neg_sq (N := N) γ₂
    rw [h, ha] at h1
    rw [h1] at h2
    have h3 : (expU (xOf (N := N) γ₁))⁻¹ = (expU (xOf (N := N) γ₂))⁻¹ := Units.val_injective h2
    rw [_root_.inv_inj] at h3
    rw [h3]
  rw [expU_xOf_eq, expU_xOf_eq, hd] at hu
  have hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (nD N γ₂))) (nD N γ₂) :=
    Complex.isPrimitiveRoot_exp _ (nD_ne_zero N γ₂)
  have hb : nB N γ₁ = nB N γ₂ :=
    hprim.pow_inj (lt_of_lt_of_eq (nB_lt_nD N γ₁) hd) (nB_lt_nD N γ₂) hu
  have hbI : hB N γ₁ = hB N γ₂ := by rw [← nB_cast, ← nB_cast, hb]
  exact mul_inv_mem_Gamma0_of_hermite_eq N haI hbI hdI

variable (Γ N) in

abbrev Q : Type := ↥Γ ⧸ (Gamma0 N).subgroupOf Γ

scoped instance : Finite (Q Γ N) := Subgroup.finite_quotient_of_finiteIndex

theorem card_Q : Nat.card (Q Γ N) = (Gamma0 N).relIndex Γ := rfl

def rep (q : Q Γ N) : ↥Γ := (Quotient.out q)⁻¹

theorem rep_spec (q : Q Γ N) : (QuotientGroup.mk ((rep q)⁻¹) : Q Γ N) = q := by
  rw [rep, inv_inv]; exact Quotient.out_eq q

theorem rho_rep_injective : Function.Injective fun q : Q Γ N => rho (N := N) ((rep q : ↥Γ) : SL(2, ℤ)) := by
  intro q₁ q₂ h
  have hmem := mul_inv_mem_of_rho_eq (N := N) h

  rw [← rep_spec q₁, ← rep_spec q₂]
  apply Eq.symm
  apply QuotientGroup.eq.mpr
  rw [Subgroup.mem_subgroupOf]
  simpa [rep] using hmem

theorem core (hT : ModularGroup.T ∈ Γ) {k : ℤ} {m : ℕ} (hm : m < (Gamma0 N).relIndex Γ)
    (f : Fin (m + 1) → ModularForm (GamGL Γ) k)
    (hrel : ∑ i, qC (f i) * qExpand ℂ N XA ^ (i : ℕ) * qExpand ℂ N XD ^ (m - (i : ℕ)) = 0) :
    ∀ i, f i = 0 := by
  classical
  have hΦ := Phi_eq_zero hT f hrel

  set a : Fin (m + 1) → LaurentSeries ℂ := fun i => qExpand ℂ N (qC (f i)) with ha
  set P : Polynomial (LaurentSeries ℂ) := ∑ i : Fin (m + 1), Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)
    with hP

  have hroot : ∀ q : Q Γ N, P.IsRoot (rho (N := N) ((rep q : ↥Γ) : SL(2, ℤ))) := by
    intro q
    have h := rel_R hT f hΦ (rep q).2
    have hv : RHom (N := N) ((rep q : ↥Γ) : SL(2, ℤ)) XD ≠ 0 := fun h0 =>
      XD_ne_zero (RHom_injective _ (by rw [h0, map_zero]))
    have := isRoot_of_rel a hv h
    rwa [← rho_eq_div] at this

  haveI : Fintype (Q Γ N) := Fintype.ofFinite _
  set Z : Finset (LaurentSeries ℂ) :=
    Finset.univ.image (fun q : Q Γ N => rho (N := N) ((rep q : ↥Γ) : SL(2, ℤ))) with hZ
  have hcard : Z.card = (Gamma0 N).relIndex Γ := by
    rw [hZ, Finset.card_image_of_injective _ rho_rep_injective, Finset.card_univ, ← card_Q,
      Nat.card_eq_fintype_card]

  have hP0 : P = 0 := by
    by_contra hP0
    have hsub : Z.val ⊆ P.roots := by
      intro z hz'
      rw [Polynomial.mem_roots hP0]
      have hz'' : z ∈ Z := hz'
      rw [hZ, Finset.mem_image] at hz''
      obtain ⟨q, -, rfl⟩ := hz''
      exact hroot q
    have h1 := Polynomial.card_le_degree_of_subset_roots hsub
    have h2 : P.natDegree ≤ m := natDegree_sum_le a
    rw [hcard] at h1
    omega

  intro i
  have hai : qExpand ℂ N (qC (f i)) = 0 := by
    have := coeff_sum_C_mul_X_pow a i
    rw [← hP, hP0, Polynomial.coeff_zero] at this
    exact this.symm
  have hq : qC (f i) = 0 := qExpand_injective N (by rw [map_zero, hai])
  have hq' : qExpansion 1 (f i) = 0 := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
    rw [map_zero]
    exact hq
  exact (ModularForm.qExpansion_eq_zero_iff one_pos (hΓ1 hT) _).mp hq'

end Core

section Ratio

variable {Γ : Subgroup SL(2, ℤ)}

variable (Γ) in

abbrev S : Set (LaurentSeries ℂ) :=
  {x : LaurentSeries ℂ | ∃ (k : ℤ) (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k),
    UpperHalfPlane.qExpansion 1 (⇑g) ≠ 0 ∧
      x = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) /
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g)}

theorem qC_ne_zero_iff {F : ℍ → ℂ} : qC F ≠ 0 ↔ qExpansion 1 F ≠ 0 := by
  rw [qC, Ne, Ne, ← map_zero (ofPowerSeries ℤ ℂ), (ofPowerSeries_injective).eq_iff]

theorem mem_S_iff {x : LaurentSeries ℂ} :
    x ∈ S Γ ↔ ∃ (k : ℤ) (f g : ModularForm (GamGL Γ) k), qC g ≠ 0 ∧ x = qC f / qC g := by
  simp only [S, Set.mem_setOf_eq, qC_ne_zero_iff]
  rfl

variable (hT : ModularGroup.T ∈ Γ)
include hT

theorem qC_mul {k₁ k₂ : ℤ} (f : ModularForm (GamGL Γ) k₁) (g : ModularForm (GamGL Γ) k₂) :
    qC (f.mul g) = qC f * qC g := by
  rw [qC, ModularForm.coe_mul, ModularForm.qExpansion_mul_coe one_pos (hΓ1 hT), map_mul]; rfl

theorem qC_add {k : ℤ} (f g : ModularForm (GamGL Γ) k) : qC (⇑(f + g)) = qC f + qC g := by
  show qC (⇑f + ⇑g) = _
  rw [qC, ModularForm.qExpansion_add one_pos (hΓ1 hT) f g, map_add]; rfl

theorem qC_neg {k : ℤ} (f : ModularForm (GamGL Γ) k) : qC (⇑(-f)) = -qC f := by
  show qC (-⇑f) = _
  rw [qC, ModularForm.qExpansion_neg one_pos (hΓ1 hT) f, map_neg]; rfl

theorem mul_mem_S {a b : LaurentSeries ℂ} (ha : a ∈ S Γ) (hb : b ∈ S Γ) : a * b ∈ S Γ := by
  rw [mem_S_iff] at ha hb ⊢
  obtain ⟨k₁, f₁, g₁, hg₁, rfl⟩ := ha
  obtain ⟨k₂, f₂, g₂, hg₂, rfl⟩ := hb
  refine ⟨k₁ + k₂, f₁.mul f₂, g₁.mul g₂, ?_, ?_⟩
  · rw [qC_mul hT]; exact mul_ne_zero hg₁ hg₂
  · rw [qC_mul hT, qC_mul hT, div_mul_div_comm]

theorem add_mem_S {a b : LaurentSeries ℂ} (ha : a ∈ S Γ) (hb : b ∈ S Γ) : a + b ∈ S Γ := by
  rw [mem_S_iff] at ha hb ⊢
  obtain ⟨k₁, f₁, g₁, hg₁, rfl⟩ := ha
  obtain ⟨k₂, f₂, g₂, hg₂, rfl⟩ := hb
  refine ⟨k₁ + k₂, f₁.mul g₂ + g₁.mul f₂, g₁.mul g₂, ?_, ?_⟩
  · rw [qC_mul hT]; exact mul_ne_zero hg₁ hg₂
  · rw [qC_add hT, qC_mul hT, qC_mul hT, qC_mul hT, div_add_div _ _ hg₁ hg₂]

theorem neg_mem_S {a : LaurentSeries ℂ} (ha : a ∈ S Γ) : -a ∈ S Γ := by
  rw [mem_S_iff] at ha ⊢
  obtain ⟨k, f, g, hg, rfl⟩ := ha
  exact ⟨k, -f, g, hg, by rw [qC_neg hT]; ring⟩

omit hT in
theorem inv_mem_S {a : LaurentSeries ℂ} (ha : a ∈ S Γ) : a⁻¹ ∈ S Γ := by
  rw [mem_S_iff] at ha ⊢
  obtain ⟨k, f, g, hg, rfl⟩ := ha
  by_cases hf : qC f = 0
  · rw [hf, zero_div, _root_.inv_zero]
    exact ⟨k, f, g, hg, by rw [hf, zero_div]⟩
  · exact ⟨k, g, f, hf, by rw [inv_div]⟩

theorem qC_const (c : ℂ) : qC ((ModularForm.const c : ModularForm (GamGL Γ) 0) : ℍ → ℂ) = HahnSeries.C c := by
  have hcoe : ((ModularForm.const c : ModularForm (GamGL Γ) 0) : ℍ → ℂ) =
      c • ((1 : ModularForm (GamGL Γ) 0) : ℍ → ℂ) := by
    funext z
    rw [Pi.smul_apply, ModularForm.const_apply, ModularForm.one_coe_eq_one, Pi.one_apply, smul_eq_mul,
      mul_one]
  rw [qC, hcoe, ModularForm.qExpansion_smul one_pos (hΓ1 hT), ModularForm.qExpansion_one,
    PowerSeries.smul_eq_C_mul, mul_one, HahnSeries.ofPowerSeries_C]

theorem algebraMap_mem_S (c : ℂ) : algebraMap ℂ (LaurentSeries ℂ) c ∈ S Γ := by
  rw [mem_S_iff]
  refine ⟨0, ModularForm.const c, ModularForm.const 1, ?_, ?_⟩
  · rw [qC_const hT]; simp
  · rw [qC_const hT, qC_const hT, map_one, div_one, HahnSeries.C_apply, algebraMap_laurentSeries_eq_single]

variable (Γ) in

def SField : IntermediateField ℂ (LaurentSeries ℂ) where
  carrier := S Γ
  mul_mem' ha hb := mul_mem_S hT ha hb
  one_mem' := by simpa using algebraMap_mem_S hT 1
  add_mem' ha hb := add_mem_S hT ha hb
  zero_mem' := by simpa using algebraMap_mem_S hT 0
  algebraMap_mem' c := algebraMap_mem_S hT c
  inv_mem' a ha := inv_mem_S ha

theorem mem_S_of_mem {y : LaurentSeries ℂ} (hy : y ∈ IntermediateField.adjoin ℂ (S Γ)) : y ∈ S Γ := by
  have hle : IntermediateField.adjoin ℂ (S Γ) ≤ SField Γ hT :=
    IntermediateField.adjoin_le_iff.mpr (fun _ h => h)
  exact hle hy

theorem common_denominator (n : ℕ) (c : Fin n → LaurentSeries ℂ) (hc : ∀ i, c i ∈ S Γ) :
    ∃ (k : ℤ) (g : ModularForm (GamGL Γ) k) (f : Fin n → ModularForm (GamGL Γ) k),
      qC g ≠ 0 ∧ ∀ i, c i * qC g = qC (f i) := by
  induction n with
  | zero =>
      refine ⟨0, 1, Fin.elim0, ?_, fun i => Fin.elim0 i⟩
      rw [qC, ModularForm.one_coe_eq_one, qExpansion_one, map_one]; exact one_ne_zero
  | succ n ih =>
      obtain ⟨k, g, f, hg0, hf⟩ := ih (Fin.tail c) (fun i => hc i.succ)
      obtain ⟨k₀, f₀, g₀, hg₀, hc0⟩ := (mem_S_iff).mp (hc 0)
      refine ⟨k₀ + k, g₀.mul g, Fin.cons (f₀.mul g) (fun i => g₀.mul (f i)), ?_, ?_⟩
      · rw [qC_mul hT]; exact mul_ne_zero hg₀ hg0
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.cons_zero]
          rw [hc0, qC_mul hT, qC_mul hT]
          field_simp
        · simp only [Fin.cons_succ]
          have h2 : c j.succ * qC g = qC (f j) := hf j
          rw [qC_mul hT, qC_mul hT, ← h2]
          ring

end Ratio

section Final

variable (Γ : Subgroup SL(2, ℤ)) (hT : ModularGroup.T ∈ Γ) (N : ℕ) [NeZero N]

theorem jqNModC_eq : jqNModC ℂ N = qExpand ℂ N XA / qExpand ℂ N XD := by
  rw [jqNModC, jqModC_eq_jC, jC, map_div₀]

theorem theta_mem : jqNModC ℂ N ∈ IntermediateField.adjoin ℂ (insert (jqNModC ℂ N) (S Γ)) :=
  IntermediateField.subset_adjoin ℂ _ (Set.mem_insert _ _)

theorem le_insert : IntermediateField.adjoin ℂ (S Γ) ≤ IntermediateField.adjoin ℂ (insert (jqNModC ℂ N) (S Γ)) :=
  IntermediateField.adjoin.mono ℂ _ _ (Set.subset_insert _ _)

include hT in

theorem linearIndependent_pow_theta :
    LinearIndependent (IntermediateField.adjoin ℂ (S Γ))
      (fun i : Fin ((Gamma0 N).relIndex Γ) =>
        (⟨jqNModC ℂ N ^ (i : ℕ), pow_mem (theta_mem Γ N) _⟩ :
          extendScalars (le_insert Γ N))) := by

  obtain ⟨m, hm⟩ : ∃ m, (Gamma0 N).relIndex Γ = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := (Gamma0 N).subgroupOf Γ))
  rw [hm]
  rw [Fintype.linearIndependent_iff]
  intro g hg i₀

  have hrelQ : ∑ i, ((g i : IntermediateField.adjoin ℂ (S Γ)) : LaurentSeries ℂ) *
      jqNModC ℂ N ^ (i : ℕ) = 0 := by
    have := congrArg (fun z : extendScalars (le_insert Γ N) =>
      ((z : IntermediateField.adjoin ℂ (insert (jqNModC ℂ N) (S Γ))) : LaurentSeries ℂ)) hg
    simp at this
    exact this

  obtain ⟨k, gF, f, hg0, hf⟩ :=
    common_denominator hT (m + 1) (fun i => ((g i : IntermediateField.adjoin ℂ (S Γ)) : LaurentSeries ℂ))
      (fun i => mem_S_of_mem hT (g i).2)

  have hrel1 : ∑ i, qC (f i) * jqNModC ℂ N ^ (i : ℕ) = 0 := by
    have := congrArg (· * qC gF) hrelQ
    simp only [zero_mul, Finset.sum_mul] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hf i]; ring

  have hYD : qExpand ℂ N XD ≠ 0 := fun h0 => XD_ne_zero (qExpand_injective N (by rw [h0, map_zero]))
  have hrel2 : ∑ i, qC (f i) * qExpand ℂ N XA ^ (i : ℕ) * qExpand ℂ N XD ^ (m - (i : ℕ)) = 0 := by
    have key : (∑ i : Fin (m + 1), qC (f i) * jqNModC ℂ N ^ (i : ℕ)) * qExpand ℂ N XD ^ m =
        ∑ i : Fin (m + 1), qC (f i) * qExpand ℂ N XA ^ (i : ℕ) * qExpand ℂ N XD ^ (m - (i : ℕ)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hi : (i : ℕ) ≤ m := Nat.lt_succ_iff.mp i.is_lt
      have hv' : qExpand ℂ N XD ^ m = qExpand ℂ N XD ^ (i : ℕ) * qExpand ℂ N XD ^ (m - (i : ℕ)) := by
        rw [← _root_.pow_add, Nat.add_sub_cancel' hi]
      rw [jqNModC_eq, hv', div_pow]
      field_simp
    rw [hrel1, zero_mul] at key
    exact key.symm

  have hlt : m < (Gamma0 N).relIndex Γ := by omega
  have hfi := core hT hlt f hrel2 i₀

  have h3 : ((g i₀ : IntermediateField.adjoin ℂ (S Γ)) : LaurentSeries ℂ) = 0 := by
    have := hf i₀
    rw [hfi, ModularForm.coe_zero, show qC (0 : ℍ → ℂ) = 0 by rw [qC, qExpansion_zero, map_zero]] at this
    exact (mul_eq_zero.mp this).resolve_right hg0
  exact_mod_cast h3

end Final

end RelIndexJqSol
p2m_reactivate "P2MW.S_ModularCurve_relIndex_gamma0_le_relrank_adjoin_insert_jqNModC.RelIndexJqSol"

theorem solution (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hT : ModularGroup.T ∈ Γ)
    (N : ℕ) [NeZero N] :
    (((CongruenceSubgroup.Gamma0 N).relIndex Γ : ℕ) : Cardinal) ≤
      IntermediateField.relrank
        (IntermediateField.adjoin ℂ {x : LaurentSeries ℂ | ∃ (k : ℤ)
            (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k),
            UpperHalfPlane.qExpansion 1 (⇑g) ≠ 0 ∧
              x = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) /
                HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g)})
        (IntermediateField.adjoin ℂ (insert (ModularCurve.jqNModC ℂ N)
          {x : LaurentSeries ℂ | ∃ (k : ℤ)
            (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k),
            UpperHalfPlane.qExpansion 1 (⇑g) ≠ 0 ∧
              x = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) /
                HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g)})) := by
  change (((CongruenceSubgroup.Gamma0 N).relIndex Γ : ℕ) : Cardinal) ≤
    IntermediateField.relrank (IntermediateField.adjoin ℂ (RelIndexJqSol.S Γ))
      (IntermediateField.adjoin ℂ (insert (ModularCurve.jqNModC ℂ N) (RelIndexJqSol.S Γ)))
  rw [IntermediateField.relrank_eq_rank_of_le (RelIndexJqSol.le_insert Γ N)]
  have h := (RelIndexJqSol.linearIndependent_pow_theta Γ hT N).cardinal_le_rank
  rw [Cardinal.mk_fin] at h
  exact h

end
p2m_reactivate "P2MW.S_ModularCurve_relIndex_gamma0_le_relrank_adjoin_insert_jqNModC.RelIndexJqSol"

end S_ModularCurve_relIndex_gamma0_le_relrank_adjoin_insert_jqNModC
end P2MW
export P2MW.S_ModularCurve_relIndex_gamma0_le_relrank_adjoin_insert_jqNModC (solution)
