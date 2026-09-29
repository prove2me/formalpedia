-- Prove2me | solution 1 for ModularCurve.XOneP.exists_algEquiv_x1FunctionFieldBar_coeffMap_apply_eq_atkinLehnerSlash_p
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/055af2fe-395e-5eec-8651-594e021ccae9

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularCurve_AtkinLehnerPartial

import Theorems.Thm_ModularCurve_exists_algEquiv_laurentBaseChange_qExpFunctionFieldC_coeffMap_apply_eq_of_slash_heckeDiagMatrix
import Theorems.Thm_ModularCurve_exists_sum_smul_eq_smul_atkinLehnerSlash_gamma1_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_algEquiv_x1FunctionFieldBar_coeffMap_apply_eq_atkinLehnerSlash_p
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite"
p2m_attr_erase "simp" "ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq"

set_option autoImplicit false

open scoped MatrixGroups ModularForm

noncomputable section

namespace TBODY

open UpperHalfPlane ModularCurve
open scoped MatrixGroups ModularForm

def Wfun (p : ℕ) (γ : SL(2, ℤ)) (k : ℤ) (f : ℍ → ℂ) : ℍ → ℂ := fun τ => (f ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)

theorem Wfun_smul {p : ℕ} {γ : SL(2, ℤ)} (k : ℤ) (c : ℂ) (f : ℍ → ℂ) : Wfun p γ k (c • f) = c • Wfun p γ k f := by
  ext τ; simp [Wfun, ModularForm.SL_smul_slash]

theorem Wfun_eq_smul_slash {p : ℕ} [NeZero p] (g : SL(2, ℤ)) (k : ℤ) (F : ℍ → ℂ) :
    Wfun p g k F = ((p : ℂ) ^ (k - 1))⁻¹ • (F ∣[k] ((g : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix p)) := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  ext τ
  simp only [Wfun, Pi.smul_apply, smul_eq_mul]
  rw [SlashAction.slash_mul, ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne p), ← mul_assoc,
    inv_mul_cancel₀ (zpow_ne_zero _ hp0), one_mul, ModularForm.SL_slash]

theorem Wfun_Wfun_of_mul_eq_scalar {p : ℕ} [NeZero p] (γ γ' : SL(2, ℤ)) (u : ℝˣ) (hu : (u : ℝ) = p)
    (hmat : ((γ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix p) * ((γ' : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix p)
      = Matrix.GeneralLinearGroup.scalar (Fin 2) u)
    (k : ℤ) (h : ℍ → ℂ) : Wfun p γ' k (Wfun p γ k h) = ((p : ℂ) ^ k)⁻¹ • h := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  have hdet : (Matrix.GeneralLinearGroup.scalar (Fin 2) u).det.val = (u : ℝ) * u := by
    simp [Matrix.GeneralLinearGroup.scalar, sq]
  have hdetpos : 0 < (Matrix.GeneralLinearGroup.scalar (Fin 2) u).det.val := by
    rw [hdet, hu]; exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p) |> fun h => Nat.mul_pos h h
  rw [Wfun_eq_smul_slash γ, Wfun_smul, Wfun_eq_smul_slash γ', ← SlashAction.slash_mul, hmat]
  ext τ
  rw [Pi.smul_apply, Pi.smul_apply, ModularForm.slash_apply, UpperHalfPlane.σ, if_pos hdetpos,
    UpperHalfPlane.glScalar_smul, UpperHalfPlane.denom_scalar, hdet, hu, ContinuousAlgEquiv.refl_apply,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (p : ℝ) * p)]
  simp only [smul_eq_mul]
  push_cast
  rw [show ((p : ℂ) * p) ^ (k - 1) = (p : ℂ) ^ (k - 1) * (p : ℂ) ^ (k - 1) from mul_zpow _ _ _]
  have hz : (p : ℂ) ^ (k - 1) ≠ 0 := zpow_ne_zero _ hp0
  have hzk : (p : ℂ) ^ k ≠ 0 := zpow_ne_zero _ hp0
  rw [zpow_neg, ← inv_zpow, inv_zpow', zpow_neg]
  field_simp
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

def pUnit (p : ℕ) [Fact p.Prime] : ℝˣ := Units.mk0 (p : ℝ) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

theorem adjoin_exp_le (p : ℕ) [Fact p.Prime] (ι : AlgebraicClosure ℚ →+* ℂ) (c : ℂ)
    (hc : c ∈ IntermediateField.adjoin ℚ ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))} : Set ℂ)) :
    c ∈ ι.fieldRange := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic p (AlgebraicClosure ℚ))
    (by rw [Polynomial.degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos p)).ne')
  have hζp : IsPrimitiveRoot ζ p := (Polynomial.isRoot_cyclotomic_iff).mp hζ
  have hζ' : IsPrimitiveRoot (ι ζ) p := hζp.map_of_injective ι.injective
  have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ)) ^ p = 1 :=
    (Complex.isPrimitiveRoot_exp p (NeZero.ne p)).pow_eq_one
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hexp
  have hmem : Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ)) ∈ ι.fieldRange := by
    rw [← hi, ← map_pow]; exact ⟨_, rfl⟩
  have hle : (IntermediateField.adjoin ℚ ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))} : Set ℂ)).toSubfield
      ≤ ι.fieldRange := by
    rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    rintro z (⟨q, rfl⟩ | hz)
    · exact ⟨algebraMap ℚ _ q, by simp⟩
    · rw [Set.mem_singleton_iff] at hz; rw [hz]; exact hmem
  exact hle hc

end TBODY

end

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)

    (y w₀ : ℤ) (hrel : (p : ℤ) * w₀ - (M : ℤ) * y = 1)
    (γ γ' : SL(2, ℤ)) (hγ : (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![1, y; (M : ℤ), (p : ℤ) * w₀])
    (hγ' : (γ' : Matrix (Fin 2) (Fin 2) ℤ) = !![w₀, -y; -(M : ℤ), (p : ℤ)])
    (ι : AlgebraicClosure ℚ →+* ℂ) :
    ∃ τ : ↥(ModularCurve.x1FunctionFieldBar (M * p)) ≃ₐ[(AlgebraicClosure ℚ)] ↥(ModularCurve.x1FunctionFieldBar (M * p)),

      (∀ x : ↥(ModularCurve.x1FunctionFieldBar (M * p)), ∃ (k : ℤ) (f g : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k),
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ≠ 0 ∧
        ModularCurve.coeffMap ι ((x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ∧
        (∃ (φ : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (D : ℤ), D ≠ 0 ∧ (⇑φ : UpperHalfPlane → ℂ) = (D : ℂ) • (fun z : UpperHalfPlane => ((⇑f) ∣[k] γ) (ModularForm.heckeDiagMatrix p • z))) ∧
        (∃ (ψ : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (E : ℤ), E ≠ 0 ∧ (⇑ψ : UpperHalfPlane → ℂ) = (E : ℂ) • (fun z : UpperHalfPlane => ((⇑g) ∣[k] γ) (ModularForm.heckeDiagMatrix p • z))) ∧
        (∃ (φ' : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (D' : ℤ), D' ≠ 0 ∧ (⇑φ' : UpperHalfPlane → ℂ) = (D' : ℂ) • (fun z : UpperHalfPlane => ((⇑f) ∣[k] γ') (ModularForm.heckeDiagMatrix p • z))) ∧
        (∃ (ψ' : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (E' : ℤ), E' ≠ 0 ∧ (⇑ψ' : UpperHalfPlane → ℂ) = (E' : ℂ) • (fun z : UpperHalfPlane => ((⇑g) ∣[k] γ') (ModularForm.heckeDiagMatrix p • z)))) ∧

      (∀ (x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) (k : ℤ) (f g φ ψ : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (D E : ℤ),
        D ≠ 0 → E ≠ 0 →
        (⇑φ : UpperHalfPlane → ℂ) = (D : ℂ) • (fun z : UpperHalfPlane => ((⇑f) ∣[k] γ) (ModularForm.heckeDiagMatrix p • z)) →
        (⇑ψ : UpperHalfPlane → ℂ) = (E : ℂ) • (fun z : UpperHalfPlane => ((⇑g) ∣[k] γ) (ModularForm.heckeDiagMatrix p • z)) →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ≠ 0 →
        ModularCurve.coeffMap ι ((x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) →
        ModularCurve.coeffMap ι ((τ x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
          HahnSeries.C ((E : ℂ) / (D : ℂ)) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑φ) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑ψ)) ∧

      (∀ (x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) (k : ℤ) (f g φ ψ : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (D E : ℤ),
        D ≠ 0 → E ≠ 0 →
        (⇑φ : UpperHalfPlane → ℂ) = (D : ℂ) • (fun z : UpperHalfPlane => ((⇑f) ∣[k] γ') (ModularForm.heckeDiagMatrix p • z)) →
        (⇑ψ : UpperHalfPlane → ℂ) = (E : ℂ) • (fun z : UpperHalfPlane => ((⇑g) ∣[k] γ') (ModularForm.heckeDiagMatrix p • z)) →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ≠ 0 →
        ModularCurve.coeffMap ι ((x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) →
        ModularCurve.coeffMap ι ((τ.symm x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
          HahnSeries.C ((E : ℂ) / (D : ℂ)) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑φ) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑ψ)) ∧

      (∀ j : ↥(ModularCurve.x1FunctionFieldBar (M * p)), ((j : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq →
        ((τ j : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ p ModularCurve.jq)) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hrelR : (p : ℝ) * (w₀ : ℝ) - (M : ℝ) * (y : ℝ) = 1 := by exact_mod_cast hrel

  have hγ10 : (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = M := by rw [hγ]; rfl
  have hγ11 : (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = p * w₀ := by rw [hγ]; rfl
  have hγ'10 : (γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = -M := by rw [hγ']; rfl
  have hγ'11 : (γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = p := by rw [hγ']; rfl
  have hγ0 : γ ∈ CongruenceSubgroup.Gamma0 M := by
    rw [CongruenceSubgroup.Gamma0_mem, hγ10]; simp
  have hγ'0 : γ' ∈ CongruenceSubgroup.Gamma0 M := by
    rw [CongruenceSubgroup.Gamma0_mem, hγ'10]; simp
  have hγp : (p : ℤ) ∣ γ 1 1 := by rw [hγ11]; exact dvd_mul_right _ _
  have hγ'p : (p : ℤ) ∣ γ' 1 1 := by rw [hγ'11]

  have hW : ∀ (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (p₀ : PowerSeries ℤ),
      ModularCurve.IsIntegralQExp (⇑f) p₀ →
      ∃ (D : ℤ) (n : ℕ) (c : Fin n → ℂ) (F : Fin n → ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k)
        (r : Fin n → PowerSeries ℤ),
        D ≠ 0 ∧ (∀ i, c i ∈ ι.fieldRange) ∧ (∀ i, ModularCurve.IsIntegralQExp (⇑(F i)) (r i)) ∧
        ((D : ℂ) • (fun τ : UpperHalfPlane => ((⇑f) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ))) = ∑ i, c i • (⇑(F i) : UpperHalfPlane → ℂ) := by
    intro k f p₀ hf
    obtain ⟨D, n, c, F, r, hD, hc, hF, heq⟩ := ModularCurve.exists_sum_smul_eq_smul_atkinLehnerSlash_gamma1_mul p M hpM f hf γ hγ0 hγp
    exact ⟨D, n, c, F, r, hD, fun i => TBODY.adjoin_exp_le p ι _ (hc i), hF, heq⟩
  have hW' : ∀ (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (p₀ : PowerSeries ℤ),
      ModularCurve.IsIntegralQExp (⇑f) p₀ →
      ∃ (D : ℤ) (n : ℕ) (c : Fin n → ℂ) (F : Fin n → ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k)
        (r : Fin n → PowerSeries ℤ),
        D ≠ 0 ∧ (∀ i, c i ∈ ι.fieldRange) ∧ (∀ i, ModularCurve.IsIntegralQExp (⇑(F i)) (r i)) ∧
        ((D : ℂ) • (fun τ : UpperHalfPlane => ((⇑f) ∣[k] γ') (ModularForm.heckeDiagMatrix p • τ))) = ∑ i, c i • (⇑(F i) : UpperHalfPlane → ℂ) := by
    intro k f p₀ hf
    obtain ⟨D, n, c, F, r, hD, hc, hF, heq⟩ := ModularCurve.exists_sum_smul_eq_smul_atkinLehnerSlash_gamma1_mul p M hpM f hf γ' hγ'0 hγ'p
    exact ⟨D, n, c, F, r, hD, fun i => TBODY.adjoin_exp_le p ι _ (hc i), hF, heq⟩

  have hmat : ((γ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix p) * ((γ' : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix p)
      = Matrix.GeneralLinearGroup.scalar (Fin 2) (TBODY.pUnit p) := by
    apply Units.ext
    ext i j
    rw [Matrix.GeneralLinearGroup.scalar, Units.coe_map]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, Matrix.scalar_apply, ModularForm.val_heckeDiagMatrix hp0,
        TBODY.pUnit, Matrix.SpecialLinearGroup.toGL, Matrix.SpecialLinearGroup.map, Units.val_mul, Matrix.natCast_apply, hγ, hγ'] <;>
      first | ring1 | linear_combination (p : ℝ) * hrelR
  have hmat' : ((γ' : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix p) * ((γ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix p)
      = Matrix.GeneralLinearGroup.scalar (Fin 2) (TBODY.pUnit p) := by
    apply Units.ext
    ext i j
    rw [Matrix.GeneralLinearGroup.scalar, Units.coe_map]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, Matrix.scalar_apply, ModularForm.val_heckeDiagMatrix hp0,
        TBODY.pUnit, Matrix.SpecialLinearGroup.toGL, Matrix.SpecialLinearGroup.map, Units.val_mul, Matrix.natCast_apply, hγ, hγ'] <;>
      first | ring1 | linear_combination (p : ℝ) * hrelR
  have hu : ((TBODY.pUnit p : ℝˣ) : ℝ) = p := rfl
  have hcomp : ∀ (k : ℤ) (h : UpperHalfPlane → ℂ),
      (fun τ : UpperHalfPlane => ((fun τ : UpperHalfPlane => (h ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ)) ∣[k] γ') (ModularForm.heckeDiagMatrix p • τ))
        = ((p : ℂ) ^ k)⁻¹ • h :=
    fun k h => TBODY.Wfun_Wfun_of_mul_eq_scalar γ γ' (TBODY.pUnit p) hu hmat k h
  have hcomp' : ∀ (k : ℤ) (h : UpperHalfPlane → ℂ),
      (fun τ : UpperHalfPlane => ((fun τ : UpperHalfPlane => (h ∣[k] γ') (ModularForm.heckeDiagMatrix p • τ)) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ))
        = ((p : ℂ) ^ k)⁻¹ • h :=
    fun k h => TBODY.Wfun_Wfun_of_mul_eq_scalar γ' γ (TBODY.pUnit p) hu hmat' k h

  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 (M * p) := by
    rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.T]
  obtain ⟨τ, hE0, hE1, hE1', hE2⟩ :=
    ModularCurve.exists_algEquiv_laurentBaseChange_qExpFunctionFieldC_coeffMap_apply_eq_of_slash_heckeDiagMatrix
      (CongruenceSubgroup.Gamma1 (M * p)) hT p γ γ' (AlgebraicClosure ℚ) ι (ModularCurve.x1FunctionFieldBar (M * p)) rfl
      hW hW' (fun k => ((p : ℂ) ^ k)⁻¹) (fun k => ((p : ℂ) ^ k)⁻¹) hcomp hcomp'
  exact ⟨τ, hE0, hE1, hE1', hE2⟩

end S_ModularCurve_XOneP_exists_algEquiv_x1FunctionFieldBar_coeffMap_apply_eq_atkinLehnerSlash_p
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_algEquiv_x1FunctionFieldBar_coeffMap_apply_eq_atkinLehnerSlash_p (solution)
