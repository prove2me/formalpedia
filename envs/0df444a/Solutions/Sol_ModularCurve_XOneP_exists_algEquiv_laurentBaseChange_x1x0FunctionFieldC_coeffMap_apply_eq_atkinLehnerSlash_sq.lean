-- Prove2me | solution 1 for ModularCurve.XOneP.exists_algEquiv_laurentBaseChange_x1x0FunctionFieldC_coeffMap_apply_eq_atkinLehnerSlash_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/90d6b896-d023-59a9-b224-8d82a87eaaf4

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Theorems.Thm_ModularCurve_exists_algEquiv_laurentBaseChange_qExpFunctionFieldC_coeffMap_apply_eq_of_slash_heckeDiagMatrix
import Theorems.Thm_ModularForm_exists_coe_eq_slash_and_qExpansion_coeff_mem_range_of_mem_gamma0_of_mul_eq
import Theorems.Thm_ModularCurve_exists_sum_smul_eq_of_qExpansion_coeff_mem_x1x0_gamma0_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_algEquiv_laurentBaseChange_x1x0FunctionFieldC_coeffMap_apply_eq_atkinLehnerSlash_sq
p2m_attr_erase "instance" "CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex WeierstrassCurve.Affine.Point.instFinite TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime"
p2m_attr_erase "simp" "CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply"
p2m_attr_erase "simp" "CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ModularForm

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace ROOFW

variable {P : ℕ} [NeZero P]

def Wfun (P : ℕ) (γ : SL(2, ℤ)) (k : ℤ) (F : ℍ → ℂ) : ℍ → ℂ := fun τ => (F ∣[k] γ) (ModularForm.heckeDiagMatrix P • τ)

theorem Wfun_smul (γ : SL(2, ℤ)) (k : ℤ) (c : ℂ) (f : ℍ → ℂ) : Wfun P γ k (c • f) = c • Wfun P γ k f := by
  ext τ; simp [Wfun, ModularForm.SL_smul_slash]

theorem Wfun_eq_smul_slash (g : SL(2, ℤ)) (k : ℤ) (F : ℍ → ℂ) :
    Wfun P g k F = ((P : ℂ) ^ (k - 1))⁻¹ • (F ∣[k] ((g : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix P)) := by
  have hp0 : (P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne P)
  ext τ
  simp only [Wfun, Pi.smul_apply, smul_eq_mul]
  rw [SlashAction.slash_mul, ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne P), ← mul_assoc,
    inv_mul_cancel₀ (zpow_ne_zero _ hp0), one_mul, ModularForm.SL_slash]

theorem Wfun_Wfun_of_mul_eq_scalar (γ γ' : SL(2, ℤ)) (u : ℝˣ) (hu : (u : ℝ) = P)
    (hmat : ((γ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix P) * ((γ' : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix P)
      = Matrix.GeneralLinearGroup.scalar (Fin 2) u)
    (k : ℤ) (h : ℍ → ℂ) : Wfun P γ' k (Wfun P γ k h) = ((P : ℂ) ^ k)⁻¹ • h := by
  have hp0 : (P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne P)
  have hdet : (Matrix.GeneralLinearGroup.scalar (Fin 2) u).det.val = (u : ℝ) * u := by
    simp [Matrix.GeneralLinearGroup.scalar, sq]
  have hdetpos : 0 < (Matrix.GeneralLinearGroup.scalar (Fin 2) u).det.val := by
    rw [hdet, hu]; exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne P) |> fun h => Nat.mul_pos h h
  rw [Wfun_eq_smul_slash γ, Wfun_smul, Wfun_eq_smul_slash γ', ← SlashAction.slash_mul, hmat]
  ext τ
  rw [Pi.smul_apply, Pi.smul_apply, ModularForm.slash_apply, UpperHalfPlane.σ, if_pos hdetpos,
    UpperHalfPlane.glScalar_smul, UpperHalfPlane.denom_scalar, hdet, hu, ContinuousAlgEquiv.refl_apply,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (P : ℝ) * P)]
  simp only [smul_eq_mul]
  push_cast
  rw [show ((P : ℂ) * P) ^ (k - 1) = (P : ℂ) ^ (k - 1) * (P : ℂ) ^ (k - 1) from mul_zpow _ _ _]
  have hz : (P : ℂ) ^ (k - 1) ≠ 0 := zpow_ne_zero _ hp0
  have hzk : (P : ℂ) ^ k ≠ 0 := zpow_ne_zero _ hp0
  rw [zpow_neg, ← inv_zpow, inv_zpow', zpow_neg]
  field_simp
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

theorem slash_scalar (u : ℝˣ) (hu : 0 < (u : ℝ)) (k : ℤ) (F : ℍ → ℂ) :
    F ∣[k] (Matrix.GeneralLinearGroup.scalar (Fin 2) u) = ((u : ℂ) ^ (k - 2)) • F := by
  have hu0 : ((u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  have hdet : (Matrix.GeneralLinearGroup.scalar (Fin 2) u).det.val = (u : ℝ) * u := by
    simp [Matrix.GeneralLinearGroup.scalar, sq]
  have hdetpos : 0 < (Matrix.GeneralLinearGroup.scalar (Fin 2) u).det.val := by rw [hdet]; positivity
  ext τ
  rw [Pi.smul_apply, ModularForm.slash_apply, UpperHalfPlane.σ, if_pos hdetpos,
    UpperHalfPlane.glScalar_smul, UpperHalfPlane.denom_scalar, hdet, ContinuousAlgEquiv.refl_apply,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (u : ℝ) * u), smul_eq_mul]
  push_cast
  rw [show (((u : ℝ) : ℂ) * (u : ℝ)) ^ (k - 1) = ((u : ℝ) : ℂ) ^ (k - 1) * ((u : ℝ) : ℂ) ^ (k - 1) from mul_zpow _ _ _,
    show (k - 2) = (k - 1) + (k - 1) + (-k) by ring, zpow_add₀ hu0, zpow_add₀ hu0, zpow_neg]
  ring

section Roof

variable (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]

abbrev Nroof : Subgroup SL(2, ℤ) := CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * p)

scoped instance : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) (Fact.out : p.Prime).ne_zero⟩

theorem T_mem_roof : ModularGroup.T ∈ Nroof p M := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩ <;> simp [ModularGroup.T]
  · rw [CongruenceSubgroup.Gamma0_mem]
    simp [ModularGroup.T]

def pUnit : ℝˣ := Units.mk0 (p : ℝ) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

def pUnit2 : ℝˣ := Units.mk0 ((p : ℝ) ^ 2) (pow_ne_zero 2 (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))

theorem pUnit2_val : ((pUnit2 p : ℝˣ) : ℝ) = ((p ^ 2 : ℕ) : ℝ) := by simp [pUnit2]

variable {p M}

theorem wp (ι : AlgebraicClosure ℚ →+* ℂ) (γ γ' : SL(2, ℤ)) (hγ' : γ' ∈ CongruenceSubgroup.Gamma0 M)
    (h : GL (Fin 2) ℝ)
    (hh : (h : Matrix (Fin 2) (Fin 2) ℝ) = !![((γ' 0 0 : ℤ) : ℝ), ((γ' 0 1 : ℤ) : ℝ) / (p : ℝ); (p : ℝ) * ((γ' 1 0 : ℤ) : ℝ), ((γ' 1 1 : ℤ) : ℝ)])
    (hrel : (γ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix (p ^ 2) = Matrix.GeneralLinearGroup.scalar (Fin 2) (pUnit p) * h)
    (k : ℤ) (f : ModularForm ((Nroof p M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (p₀ : PowerSeries ℤ)
    (hf : ModularCurve.IsIntegralQExp (⇑f) p₀) :
    ∃ (D : ℤ) (n : ℕ) (c : Fin n → ℂ) (F : Fin n → ModularForm ((Nroof p M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
      (r : Fin n → PowerSeries ℤ),
      D ≠ 0 ∧ (∀ i, c i ∈ ι.fieldRange) ∧ (∀ i, ModularCurve.IsIntegralQExp (⇑(F i)) (r i)) ∧
      ((D : ℂ) • (fun τ : UpperHalfPlane => ((⇑f) ∣[k] γ) (ModularForm.heckeDiagMatrix (p ^ 2) • τ))) = ∑ i, c i • (⇑(F i) : UpperHalfPlane → ℂ) := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero

  have hfq : ∀ n : ℕ, (PowerSeries.coeff n) (UpperHalfPlane.qExpansion 1 ⇑f) ∈ Set.range ι := by
    intro n
    have h1 := hf
    unfold ModularCurve.IsIntegralQExp at h1
    rw [← h1, PowerSeries.coeff_map]
    refine ⟨((PowerSeries.coeff n p₀ : ℤ) : AlgebraicClosure ℚ), ?_⟩
    simp
  obtain ⟨f', hf'c, hf'q⟩ := ModularForm.exists_coe_eq_slash_and_qExpansion_coeff_mem_range_of_mem_gamma0_of_mul_eq M p (M * p) rfl k ι f hfq γ' hγ' h hh

  let K₀ : IntermediateField ℚ ℂ := ι.fieldRange.toIntermediateField (fun q => ⟨(q : AlgebraicClosure ℚ), by simp⟩)
  obtain ⟨n, c, G, r, hc, hG, hsum⟩ := ModularCurve.exists_sum_smul_eq_of_qExpansion_coeff_mem_x1x0_gamma0_mul p M p K₀ f' (fun n => hf'q n)

  have hWf : (fun τ : UpperHalfPlane => ((⇑f) ∣[k] γ) (ModularForm.heckeDiagMatrix (p ^ 2) • τ)) =
      ((((p ^ 2 : ℕ) : ℂ) ^ (k - 1))⁻¹ * ((p : ℝ) : ℂ) ^ (k - 2)) • (⇑f' : UpperHalfPlane → ℂ) := by
    have h1 := Wfun_eq_smul_slash (P := p ^ 2) γ k (⇑f)
    have hp0R : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    have hslR : ((γ' 0 0 : ℤ) : ℝ) * ((γ' 1 1 : ℤ) : ℝ) - ((γ' 0 1 : ℤ) : ℝ) * ((γ' 1 0 : ℤ) : ℝ) = 1 := by
      have hsl := Matrix.SpecialLinearGroup.det_coe γ'
      rw [Matrix.det_fin_two] at hsl
      exact_mod_cast hsl
    have hdeth : 0 < (h.det : ℝˣ).val := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, hh, Matrix.det_fin_two_of,
        show ((γ' 0 0 : ℤ) : ℝ) * ((γ' 1 1 : ℤ) : ℝ) - ((γ' 0 1 : ℤ) : ℝ) / (p : ℝ) * ((p : ℝ) * ((γ' 1 0 : ℤ) : ℝ)) = 1 by
          field_simp; linear_combination hslR]
      exact one_pos
    change Wfun (p ^ 2) γ k ⇑f = _
    rw [h1, hrel, SlashAction.slash_mul, slash_scalar (pUnit p) (by simp [pUnit]; exact_mod_cast (Fact.out : p.Prime).pos),
      ModularForm.smul_slash, UpperHalfPlane.σ, if_pos hdeth, ContinuousAlgEquiv.refl_apply, smul_smul, hf'c]
    rfl
  refine ⟨1, n, fun i => ((((p ^ 2 : ℕ) : ℂ) ^ (k - 1))⁻¹ * ((p : ℝ) : ℂ) ^ (k - 2)) * c i, G, r, one_ne_zero, fun i => ?_, hG, ?_⟩
  · refine mul_mem (mul_mem (inv_mem (zpow_mem ?_ _)) (zpow_mem ?_ _)) (hc i)
    · exact ⟨((p ^ 2 : ℕ) : AlgebraicClosure ℚ), by simp⟩
    · exact ⟨(p : AlgebraicClosure ℚ), by simp⟩
  · rw [Int.cast_one, one_smul, hWf, hsum, Finset.smul_sum]
    simp only [smul_smul]

end Roof

end ROOFW
p2m_reactivate "P2MW.S_ModularCurve_XOneP_exists_algEquiv_laurentBaseChange_x1x0FunctionFieldC_coeffMap_apply_eq_atkinLehnerSlash_sq.ROOFW"

end
p2m_reactivate "P2MW.S_ModularCurve_XOneP_exists_algEquiv_laurentBaseChange_x1x0FunctionFieldC_coeffMap_apply_eq_atkinLehnerSlash_sq.ROOFW"

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)

    (y w : ℤ) (hrel : (p : ℤ) ^ 2 * w - (M : ℤ) * y = 1)
    (δ δ' : SL(2, ℤ)) (hδ : (δ : Matrix (Fin 2) (Fin 2) ℤ) = !![1, y; (M : ℤ), (p : ℤ) ^ 2 * w])
    (hδ' : (δ' : Matrix (Fin 2) (Fin 2) ℤ) = !![w, -y; -(M : ℤ), (p : ℤ) ^ 2])
    (ι : AlgebraicClosure ℚ →+* ℂ) :
    ∃ W : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p))) ≃ₐ[(AlgebraicClosure ℚ)] ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p))),

      (∀ x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p))), ∃ (k : ℤ) (f g : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k),
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ≠ 0 ∧
        ModularCurve.coeffMap ι ((x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ∧
        (∃ (φ : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (D : ℤ), D ≠ 0 ∧ (⇑φ : UpperHalfPlane → ℂ) = (D : ℂ) • (fun z : UpperHalfPlane => ((⇑f) ∣[k] δ) (ModularForm.heckeDiagMatrix (p ^ 2) • z))) ∧
        (∃ (ψ : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (E : ℤ), E ≠ 0 ∧ (⇑ψ : UpperHalfPlane → ℂ) = (E : ℂ) • (fun z : UpperHalfPlane => ((⇑g) ∣[k] δ) (ModularForm.heckeDiagMatrix (p ^ 2) • z))) ∧
        (∃ (φ' : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (D' : ℤ), D' ≠ 0 ∧ (⇑φ' : UpperHalfPlane → ℂ) = (D' : ℂ) • (fun z : UpperHalfPlane => ((⇑f) ∣[k] δ') (ModularForm.heckeDiagMatrix (p ^ 2) • z))) ∧
        (∃ (ψ' : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (E' : ℤ), E' ≠ 0 ∧ (⇑ψ' : UpperHalfPlane → ℂ) = (E' : ℂ) • (fun z : UpperHalfPlane => ((⇑g) ∣[k] δ') (ModularForm.heckeDiagMatrix (p ^ 2) • z)))) ∧

      (∀ (x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) (k : ℤ) (f g φ ψ : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (D E : ℤ),
        D ≠ 0 → E ≠ 0 →
        (⇑φ : UpperHalfPlane → ℂ) = (D : ℂ) • (fun z : UpperHalfPlane => ((⇑f) ∣[k] δ) (ModularForm.heckeDiagMatrix (p ^ 2) • z)) →
        (⇑ψ : UpperHalfPlane → ℂ) = (E : ℂ) • (fun z : UpperHalfPlane => ((⇑g) ∣[k] δ) (ModularForm.heckeDiagMatrix (p ^ 2) • z)) →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ≠ 0 →
        ModularCurve.coeffMap ι ((x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) →
        ModularCurve.coeffMap ι ((W x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) =
          HahnSeries.C ((E : ℂ) / (D : ℂ)) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑φ) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑ψ)) ∧

      (∀ (x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) (k : ℤ) (f g φ ψ : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (D E : ℤ),
        D ≠ 0 → E ≠ 0 →
        (⇑φ : UpperHalfPlane → ℂ) = (D : ℂ) • (fun z : UpperHalfPlane => ((⇑f) ∣[k] δ') (ModularForm.heckeDiagMatrix (p ^ 2) • z)) →
        (⇑ψ : UpperHalfPlane → ℂ) = (E : ℂ) • (fun z : UpperHalfPlane => ((⇑g) ∣[k] δ') (ModularForm.heckeDiagMatrix (p ^ 2) • z)) →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ≠ 0 →
        ModularCurve.coeffMap ι ((x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) →
        ModularCurve.coeffMap ι ((W.symm x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) =
          HahnSeries.C ((E : ℂ) / (D : ℂ)) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑φ) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑ψ)) ∧

      (∀ j : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p))), ((j : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq →
        ((W j : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ (p ^ 2) ModularCurve.jq)) := by
  classical
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 (Fact.out : p.Prime).ne_zero⟩
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hp20 : p ^ 2 ≠ 0 := pow_ne_zero 2 (Fact.out : p.Prime).ne_zero
  have hrelR : (p : ℝ) ^ 2 * w - (M : ℝ) * y = 1 := by exact_mod_cast hrel

  obtain ⟨γ₁, hγ₁v⟩ : ∃ γ₁ : SL(2, ℤ), (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) = !![(p : ℤ), y; (M : ℤ), (p : ℤ) * w] :=
    ⟨⟨_, by rw [Matrix.det_fin_two_of]; linear_combination hrel⟩, rfl⟩
  obtain ⟨γ₂, hγ₂v⟩ : ∃ γ₂ : SL(2, ℤ), (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) = !![(p : ℤ) * w, -y; -(M : ℤ), (p : ℤ)] :=
    ⟨⟨_, by rw [Matrix.det_fin_two_of]; linear_combination hrel⟩, rfl⟩
  have hγ₁ : γ₁ ∈ CongruenceSubgroup.Gamma0 M := by
    rw [CongruenceSubgroup.Gamma0_mem, show (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = (M : ℤ) by rw [hγ₁v]; rfl]; simp
  have hγ₂ : γ₂ ∈ CongruenceSubgroup.Gamma0 M := by
    rw [CongruenceSubgroup.Gamma0_mem, show (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = -(M : ℤ) by rw [hγ₂v]; rfl]; simp
  obtain ⟨h₁, hh₁v⟩ : ∃ h₁ : GL (Fin 2) ℝ, (h₁ : Matrix (Fin 2) (Fin 2) ℝ) = !![(p : ℝ), (y : ℝ) / p; (p : ℝ) * M, (p : ℝ) * w] :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ (by
      rw [Matrix.det_fin_two_of, show (p : ℝ) * ((p : ℝ) * w) - (y : ℝ) / p * ((p : ℝ) * M) = 1 by field_simp; linear_combination hrelR]
      exact one_ne_zero), Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _⟩
  obtain ⟨h₂, hh₂v⟩ : ∃ h₂ : GL (Fin 2) ℝ, (h₂ : Matrix (Fin 2) (Fin 2) ℝ) = !![(p : ℝ) * w, -(y : ℝ) / p; (p : ℝ) * (-(M : ℝ)), (p : ℝ)] :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ (by
      rw [Matrix.det_fin_two_of, show (p : ℝ) * w * (p : ℝ) - -(y : ℝ) / p * ((p : ℝ) * -(M : ℝ)) = 1 by field_simp; linear_combination hrelR]
      exact one_ne_zero), Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _⟩
  have hγ₁e : ∀ i j, (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) i j = !![(p : ℤ), y; (M : ℤ), (p : ℤ) * w] i j := fun i j => by rw [hγ₁v]
  have hγ₂e : ∀ i j, (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) i j = !![(p : ℤ) * w, -y; -(M : ℤ), (p : ℤ)] i j := fun i j => by rw [hγ₂v]
  have hh₁ : (h₁ : Matrix (Fin 2) (Fin 2) ℝ) = !![((γ₁ 0 0 : ℤ) : ℝ), ((γ₁ 0 1 : ℤ) : ℝ) / (p : ℝ); (p : ℝ) * ((γ₁ 1 0 : ℤ) : ℝ), ((γ₁ 1 1 : ℤ) : ℝ)] := by
    rw [hh₁v]
    ext i j; fin_cases i <;> fin_cases j <;> simp [hγ₁e]
  have hh₂ : (h₂ : Matrix (Fin 2) (Fin 2) ℝ) = !![((γ₂ 0 0 : ℤ) : ℝ), ((γ₂ 0 1 : ℤ) : ℝ) / (p : ℝ); (p : ℝ) * ((γ₂ 1 0 : ℤ) : ℝ), ((γ₂ 1 1 : ℤ) : ℝ)] := by
    rw [hh₂v]
    ext i j; fin_cases i <;> fin_cases j <;> simp [hγ₂e, neg_div]

  have hδR : ((δ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), (y : ℝ); (M : ℝ), (p : ℝ) ^ 2 * w] := by
    show ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) δ) : Matrix (Fin 2) (Fin 2) ℝ) = _
    rw [Matrix.SpecialLinearGroup.map_apply_coe, hδ]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hδ'R : ((δ' : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(w : ℝ), -(y : ℝ); -(M : ℝ), (p : ℝ) ^ 2] := by
    show ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) δ') : Matrix (Fin 2) (Fin 2) ℝ) = _
    rw [Matrix.SpecialLinearGroup.map_apply_coe, hδ']
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hD : ((ModularForm.heckeDiagMatrix (p ^ 2) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(p : ℝ) ^ 2, 0; 0, 1] := by
    rw [ModularForm.val_heckeDiagMatrix hp20]; push_cast; rfl
  have hS1 : ((Matrix.GeneralLinearGroup.scalar (Fin 2) (ROOFW.pUnit p) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(p : ℝ), 0; 0, (p : ℝ)] := by
    rw [Matrix.GeneralLinearGroup.scalar, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Matrix.scalar_apply]
    ext i j; fin_cases i <;> fin_cases j <;> simp [ROOFW.pUnit]
  have hS2 : ((Matrix.GeneralLinearGroup.scalar (Fin 2) (ROOFW.pUnit2 p) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(p : ℝ) ^ 2, 0; 0, (p : ℝ) ^ 2] := by
    rw [Matrix.GeneralLinearGroup.scalar, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Matrix.scalar_apply]
    ext i j; fin_cases i <;> fin_cases j <;> simp [ROOFW.pUnit2]

  have hrel₁ : (δ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix (p ^ 2) = Matrix.GeneralLinearGroup.scalar (Fin 2) (ROOFW.pUnit p) * h₁ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hδR, hD, hS1, hh₁v]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
  have hrel₂ : (δ' : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix (p ^ 2) = Matrix.GeneralLinearGroup.scalar (Fin 2) (ROOFW.pUnit p) * h₂ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hδ'R, hD, hS1, hh₂v]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

  have hmat : ((δ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix (p ^ 2)) * ((δ' : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix (p ^ 2))
      = Matrix.GeneralLinearGroup.scalar (Fin 2) (ROOFW.pUnit2 p) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, hδR, hδ'R, hD, hS2]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination (p : ℝ) ^ 2 * hrelR
  have hmat' : ((δ' : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix (p ^ 2)) * ((δ : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix (p ^ 2))
      = Matrix.GeneralLinearGroup.scalar (Fin 2) (ROOFW.pUnit2 p) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, hδR, hδ'R, hD, hS2]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination (p : ℝ) ^ 2 * hrelR

  obtain ⟨σ, h0, h1, h1', h2⟩ := ModularCurve.exists_algEquiv_laurentBaseChange_qExpFunctionFieldC_coeffMap_apply_eq_of_slash_heckeDiagMatrix
    (ROOFW.Nroof p M) (ROOFW.T_mem_roof p M) (p ^ 2) δ δ' (AlgebraicClosure ℚ) ι
    (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p))) rfl
    (fun k f p₀ hf => ROOFW.wp ι δ γ₁ hγ₁ h₁ hh₁ hrel₁ k f p₀ hf)
    (fun k f p₀ hf => ROOFW.wp ι δ' γ₂ hγ₂ h₂ hh₂ hrel₂ k f p₀ hf)
    (fun k => (((p ^ 2 : ℕ) : ℂ) ^ k)⁻¹) (fun k => (((p ^ 2 : ℕ) : ℂ) ^ k)⁻¹)
    (fun k hh => ROOFW.Wfun_Wfun_of_mul_eq_scalar (P := p ^ 2) δ δ' (ROOFW.pUnit2 p) (ROOFW.pUnit2_val p) hmat k hh)
    (fun k hh => ROOFW.Wfun_Wfun_of_mul_eq_scalar (P := p ^ 2) δ' δ (ROOFW.pUnit2 p) (ROOFW.pUnit2_val p) hmat' k hh)
  exact ⟨σ, h0, h1, h1', h2⟩

end S_ModularCurve_XOneP_exists_algEquiv_laurentBaseChange_x1x0FunctionFieldC_coeffMap_apply_eq_atkinLehnerSlash_sq
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_algEquiv_laurentBaseChange_x1x0FunctionFieldC_coeffMap_apply_eq_atkinLehnerSlash_sq (solution)
