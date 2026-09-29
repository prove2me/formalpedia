-- Prove2me | solution 1 for ModularCurve.exists_isIntegral_level_pow_mul_qExpansion_slash_fricke_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/d95132d3-c43f-5296-87db-b81dddc49536

import Mathlib
import Theorems.Thm_ModularForm_qExpansion_slash_coeff_mem_of_peaked_auxiliary
import Theorems.Thm_ModularCurve_exists_gamma1_peaked_auxiliary_form
import Theorems.Thm_ModularCurve_exists_ne_zero_isIntegral_mul_qExpansion_slash_fricke_coeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_fricke_coeff
p2m_attr_erase "instance" "ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex WeierstrassCurve.Affine.Point.instFinite TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "instance" "CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime"
p2m_attr_erase "simp" "ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.intSeriesC_one ModularCurve.JOne.torsionGaloisRep_apply ModularCurve.coe_restrictForm ModularCurve.intSeriesC_zero ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero"
p2m_attr_erase "simp" "TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Function
open scoped Real Manifold MatrixGroups ModularForm Topology Pointwise

namespace R1FrickeInt

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section RN

def RN (N : ℕ) : Subring ℂ where
  carrier := {x | ∃ b : ℕ, IsIntegral ℤ ((N : ℂ) ^ b * x)}
  mul_mem' := by
    rintro x y ⟨b₁, h₁⟩ ⟨b₂, h₂⟩
    refine ⟨b₁ + b₂, ?_⟩
    rw [pow_add, mul_mul_mul_comm]
    exact h₁.mul h₂
  one_mem' := ⟨0, by simpa using isIntegral_one⟩
  add_mem' := by
    rintro x y ⟨b₁, h₁⟩ ⟨b₂, h₂⟩
    refine ⟨b₁ + b₂, ?_⟩
    have e : (N : ℂ) ^ (b₁ + b₂) * (x + y) =
        (N : ℂ) ^ b₂ * ((N : ℂ) ^ b₁ * x) + (N : ℂ) ^ b₁ * ((N : ℂ) ^ b₂ * y) := by
      rw [pow_add]; ring
    rw [e]
    have hN : IsIntegral ℤ (N : ℂ) := by
      have := isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (N : ℤ))
      simpa using this
    exact ((hN.pow b₂).mul h₁).add ((hN.pow b₁).mul h₂)
  zero_mem' := ⟨0, by simpa using isIntegral_zero⟩
  neg_mem' := by
    rintro x ⟨b, h⟩
    exact ⟨b, by rw [mul_neg]; exact h.neg⟩

variable {N : ℕ}

theorem mem_RN_iff {x : ℂ} : x ∈ RN N ↔ ∃ b : ℕ, IsIntegral ℤ ((N : ℂ) ^ b * x) := Iff.rfl

theorem mem_RN_of_isIntegral_mul {a : ℕ} {x : ℂ} (h : IsIntegral ℤ ((N : ℂ) ^ a * x)) : x ∈ RN N :=
  ⟨a, h⟩

theorem mem_RN_of_isIntegral {x : ℂ} (h : IsIntegral ℤ x) : x ∈ RN N :=
  ⟨0, by simpa using h⟩

theorem isIntegral_intCast (z : ℤ) : IsIntegral ℤ (z : ℂ) := by
  have := isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := z)
  simpa using this

theorem isIntegral_natCast (n : ℕ) : IsIntegral ℤ (n : ℂ) := by
  have := isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (n : ℤ))
  simpa using this

theorem inv_natCast_mem_RN [NeZero N] : ((N : ℂ))⁻¹ ∈ RN N := by
  refine ⟨1, ?_⟩
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [pow_one, mul_inv_cancel₀ hN]
  exact isIntegral_one

theorem isIntegral_neg_one_zpow (k : ℤ) : IsIntegral ℤ ((-1 : ℂ) ^ (-k)) := by
  rcases Int.even_or_odd k with ⟨r, hr⟩ | ⟨r, hr⟩
  · have : (-1 : ℂ) ^ (-k) = 1 := by
      rw [hr, show -(r + r) = 2 * (-r) by ring, zpow_mul]; norm_num
    rw [this]; exact isIntegral_one
  · have : (-1 : ℂ) ^ (-k) = -1 := by
      rw [hr, show -(2 * r + 1) = 2 * (-r - 1) + 1 by ring, zpow_add₀ (by norm_num), zpow_mul]
      norm_num
    rw [this]; exact isIntegral_one.neg

theorem neg_one_zpow_mul_self (k : ℤ) : (-1 : ℂ) ^ (-k) * (-1 : ℂ) ^ (-k) = 1 := by
  rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), show -k + -k = 2 * (-k) by ring, zpow_mul]
  norm_num

end RN

section Group

variable {N : ℕ}

theorem T_mem_Gamma1 (N : ℕ) : ModularGroup.T ∈ Gamma1 N := by
  simp [Gamma1_mem, ModularGroup.T]

theorem one_mem_strictPeriods (N : ℕ) : (1 : ℝ) ∈ (Γ₁(N)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma1 N)]
  exact AddSubgroup.mem_zmultiples 1

theorem T_pow_mem_Gamma (N : ℕ) : ModularGroup.T ^ N ∈ CongruenceSubgroup.Gamma N := by
  rw [Gamma_mem, ← zpow_natCast]
  simp only [ModularGroup.coe_T_zpow]
  simp

theorem Gamma_le_Gamma1 (N : ℕ) : CongruenceSubgroup.Gamma N ≤ Gamma1 N := by
  intro g hg
  rw [Gamma_mem] at hg
  rw [Gamma1_mem]
  exact ⟨hg.1, hg.2.2.2, hg.2.2.1⟩

theorem conj_mem_Gamma (α : SL(2, ℤ)) {g : SL(2, ℤ)} (hg : g ∈ CongruenceSubgroup.Gamma N) :
    α * g * α⁻¹ ∈ CongruenceSubgroup.Gamma N :=
  (Gamma_normal N).conj_mem g hg α

theorem coeGL_mul (β γ : SL(2, ℤ)) :
    ((β * γ : SL(2, ℤ)) : GL (Fin 2) ℝ) = (β : GL (Fin 2) ℝ) * (γ : GL (Fin 2) ℝ) :=
  map_mul (Matrix.SpecialLinearGroup.mapGL ℝ) β γ

theorem coeGL_inv (β : SL(2, ℤ)) :
    ((β⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) = (β : GL (Fin 2) ℝ)⁻¹ :=
  map_inv (Matrix.SpecialLinearGroup.mapGL ℝ) β

theorem S_conj_eq (γ : SL(2, ℤ)) :
    ModularGroup.S⁻¹ * γ * ModularGroup.S = ModularGroup.S * γ * ModularGroup.S⁻¹ := by
  rw [ModularGroup.S_inv, neg_mul, neg_mul, mul_neg]

theorem S_mul_S : ModularGroup.S * ModularGroup.S = -1 := by
  have h : ModularGroup.S * ModularGroup.S⁻¹ = 1 := mul_inv_cancel _
  rw [ModularGroup.S_inv, mul_neg] at h
  rw [← neg_eq_iff_eq_neg.mpr h.symm]

def frickeGL (N : ℕ) [NeZero N] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (N : ℝ), 0]
    (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne N])

@[scoped simp]
theorem val_frickeGL (N : ℕ) [NeZero N] :
    ((frickeGL N : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (N : ℝ), 0] := rfl

def frickeConjMat (N : ℕ) (δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![δ 1 1, -(δ 1 0 / N); -((N : ℤ) * δ 0 1), δ 0 0]

theorem det_frickeConjMat (δ : SL(2, ℤ)) (h : (N : ℤ) ∣ δ 1 0) (hN : (N : ℤ) ≠ 0) :
    (frickeConjMat N δ).det = 1 := by
  obtain ⟨c, hc⟩ := h
  have hdet := Matrix.SpecialLinearGroup.det_coe δ
  rw [Matrix.det_fin_two] at hdet ⊢
  have h1 : (N : ℤ) * c / N = c := by rw [mul_comm]; exact Int.mul_ediv_cancel c hN
  simp only [frickeConjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, hc, h1] at hdet ⊢
  linear_combination hdet

def frickeConjSL (δ : SL(2, ℤ)) (h : (N : ℤ) ∣ δ 1 0) (hN : (N : ℤ) ≠ 0) : SL(2, ℤ) :=
  ⟨frickeConjMat N δ, det_frickeConjMat δ h hN⟩

theorem frickeGL_mul_mul_inv [NeZero N] (δ : SL(2, ℤ)) (h : (N : ℤ) ∣ δ 1 0) :
    frickeGL N * Matrix.SpecialLinearGroup.mapGL ℝ δ * (frickeGL N)⁻¹ =
      Matrix.SpecialLinearGroup.mapGL ℝ
        (frickeConjSL δ h (by exact_mod_cast NeZero.ne N)) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  obtain ⟨c, hc⟩ := h
  have hc' : (δ 1 0 / N : ℤ) = c := by rw [hc, Int.mul_ediv_cancel_left _ hN']
  have e00 : (frickeConjSL δ ⟨c, hc⟩ hN' : SL(2, ℤ)) 0 0 = δ 1 1 := rfl
  have e01 : (frickeConjSL δ ⟨c, hc⟩ hN' : SL(2, ℤ)) 0 1 = -(δ 1 0 / N) := rfl
  have e10 : (frickeConjSL δ ⟨c, hc⟩ hN' : SL(2, ℤ)) 1 0 = -((N : ℤ) * δ 0 1) := rfl
  have e11 : (frickeConjSL δ ⟨c, hc⟩ hN' : SL(2, ℤ)) 1 1 = δ 0 0 := rfl
  simp only [Matrix.GeneralLinearGroup.coe_mul, val_frickeGL]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, e00, e01, e10, e11, hc', hc] <;> ring

theorem fricke_conj_mem [NeZero N] {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma1 N) :
    frickeGL N * (δ : GL (Fin 2) ℝ) * (frickeGL N)⁻¹ ∈ Γ₁(N) := by
  rw [Gamma1_mem] at hδ
  obtain ⟨h00, h11, h10⟩ := hδ
  have hdvd : (N : ℤ) ∣ δ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h10
  have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  refine ⟨frickeConjSL δ hdvd hN', ?_, (frickeGL_mul_mul_inv δ hdvd).symm⟩
  show frickeConjSL δ hdvd hN' ∈ Gamma1 N
  rw [Gamma1_mem]
  refine ⟨h11, h00, ?_⟩
  show ((-((N : ℤ) * δ 0 1) : ℤ) : ZMod N) = 0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact ⟨-δ 0 1, by ring⟩

def GammaS (N : ℕ) : Subgroup SL(2, ℤ) :=
  (ConjAct.toConjAct ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ)⁻¹ • Γ₁(N)).comap
    (Matrix.SpecialLinearGroup.mapGL ℝ)

theorem mem_conj_iff (g x : GL (Fin 2) ℝ) (Γ : Subgroup (GL (Fin 2) ℝ)) :
    x ∈ ConjAct.toConjAct g⁻¹ • Γ ↔ g * x * g⁻¹ ∈ Γ := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]

theorem mem_GammaS_iff {γ : SL(2, ℤ)} :
    γ ∈ GammaS N ↔ ((ModularGroup.S * γ * ModularGroup.S⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ Γ₁(N) := by
  rw [GammaS, Subgroup.mem_comap, mem_conj_iff, coeGL_mul, coeGL_mul, coeGL_inv]
  rfl

theorem mem_GammaS_of {γ : SL(2, ℤ)} (h : ModularGroup.S * γ * ModularGroup.S⁻¹ ∈ Gamma1 N) :
    γ ∈ GammaS N :=
  mem_GammaS_iff.mpr ⟨_, h, rfl⟩

theorem conj_mem_Gamma1_of_mem_GammaS {γ : SL(2, ℤ)} (h : γ ∈ GammaS N) :
    ModularGroup.S * γ * ModularGroup.S⁻¹ ∈ Gamma1 N := by
  rw [mem_GammaS_iff] at h
  obtain ⟨γ₁, hγ₁, e⟩ := h
  have : γ₁ = ModularGroup.S * γ * ModularGroup.S⁻¹ :=
    Matrix.SpecialLinearGroup.mapGL_injective e
  rwa [← this]

theorem not_mem_GammaS_iff {γ : SL(2, ℤ)} :
    γ ∉ GammaS N ↔ ModularGroup.S * γ * ModularGroup.S⁻¹ ∉ Gamma1 N :=
  not_congr ⟨conj_mem_Gamma1_of_mem_GammaS, mem_GammaS_of⟩

theorem Gamma_le_GammaS (N : ℕ) : CongruenceSubgroup.Gamma N ≤ GammaS N := fun _ hγ =>
  mem_GammaS_of (Gamma_le_Gamma1 N (conj_mem_Gamma ModularGroup.S hγ))

scoped instance instFiniteIndexGammaS (N : ℕ) [NeZero N] : (GammaS N).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma_le_GammaS N)

theorem T_pow_mem_GammaS (N : ℕ) : ModularGroup.T ^ N ∈ GammaS N :=
  Gamma_le_GammaS N (T_pow_mem_Gamma N)

theorem STS_mem_GammaS (N : ℕ) :
    ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹ ∈ GammaS N := by
  apply mem_GammaS_of
  have : ModularGroup.S * (ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹) * ModularGroup.S⁻¹ =
      ModularGroup.T := by
    rw [ModularGroup.S_inv]
    simp only [mul_neg, neg_mul, neg_neg, ← mul_assoc, S_mul_S, one_mul]
    rw [mul_assoc, S_mul_S]
    simp
  rw [this]
  exact T_mem_Gamma1 N

theorem natCast_mem_strictPeriods_GammaS (N : ℕ) :
    (N : ℝ) ∈ ((GammaS N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine ⟨ModularGroup.T ^ N, T_pow_mem_GammaS N, ?_⟩
  apply Units.ext
  ext i j
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
    ← zpow_natCast, ModularGroup.coe_T_zpow]
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.upperRightHom_apply]

theorem GammaS_le_conjS (N : ℕ) :
    ((GammaS N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ)⁻¹ • Γ₁(N) :=
  Subgroup.map_comap_le _ _

theorem GammaS_le_conj_g₀ (N : ℕ) [NeZero N] :
    ((GammaS N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct (frickeGL N * ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ)⁻¹)⁻¹ • Γ₁(N) := by
  rintro x ⟨γ, hγ, rfl⟩
  rw [mem_conj_iff]
  have hmem := conj_mem_Gamma1_of_mem_GammaS hγ
  have e : frickeGL N * ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ)⁻¹ *
      Matrix.SpecialLinearGroup.mapGL ℝ γ *
        (frickeGL N * ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ)⁻¹)⁻¹ =
      frickeGL N * ((ModularGroup.S * γ * ModularGroup.S⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
        (frickeGL N)⁻¹ := by
    rw [← S_conj_eq, coeGL_mul, coeGL_mul, coeGL_inv, mul_inv_rev, inv_inv]
    simp only [mul_assoc]
    rfl
  rw [e]
  exact fricke_conj_mem hmem

end Group

section Forms

variable {N : ℕ} [NeZero N] {k w : ℤ}

def restrictMF {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (h : Γ' ≤ Γ) (f : ModularForm Γ k) :
    ModularForm Γ' k where
  toFun := f
  slash_action_eq' A hA := f.slash_action_eq' A (h hA)
  holo' := f.holo'
  bdd_at_cusps' hc := f.bdd_at_cusps' (hc.mono h)

def g₀ (N : ℕ) [NeZero N] : GL (Fin 2) ℝ :=
  frickeGL N * ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ)⁻¹

def Gform (f : ModularForm Γ₁(N) k) :
    ModularForm ((GammaS N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k :=
  restrictMF (GammaS_le_conj_g₀ N) (ModularForm.translate f (g₀ N))

theorem coe_Gform (f : ModularForm Γ₁(N) k) : (⇑(Gform f) : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] g₀ N := rfl

def Thetaform (ϑ : ModularForm Γ₁(N) w) :
    ModularForm ((GammaS N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) w :=
  restrictMF (GammaS_le_conjS N)
    (ModularForm.translate ϑ ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))

theorem coe_Thetaform (ϑ : ModularForm Γ₁(N) w) :
    (⇑(Thetaform ϑ) : ℍ → ℂ) = (⇑ϑ : ℍ → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) :=
  rfl

def diagGL (N : ℕ) [NeZero N] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℝ), 0; 0, (N : ℝ)]
    (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne N])

@[scoped simp]
theorem val_diagGL : ((diagGL N : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    !![(1 : ℝ), 0; 0, (N : ℝ)] := rfl

theorem val_S : (((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    !![(0 : ℝ), -1; 1, 0] := by
  ext i j
  rw [show (((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j =
    ((ModularGroup.S i j : ℤ) : ℝ) from rfl, ModularGroup.S]
  fin_cases i <;> fin_cases j <;> simp

theorem g₀_eq_diagGL : g₀ N = diagGL N := by
  rw [g₀, mul_inv_eq_iff_eq_mul]
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, val_frickeGL, val_diagGL, val_S]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem det_diagGL : ((diagGL N).det : ℝ) = (N : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_diagGL, Matrix.det_fin_two_of]; ring

theorem det_diagGL_pos : 0 < ((diagGL N).det : ℝ) := by
  rw [det_diagGL]; exact_mod_cast NeZero.pos N

theorem coe_diagGL_smul (τ : ℍ) : ((diagGL N • τ : ℍ) : ℂ) = (τ : ℂ) / (N : ℂ) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos det_diagGL_pos]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, val_diagGL]

theorem denom_diagGL (τ : ℍ) : UpperHalfPlane.denom (diagGL N) τ = N := by
  simp [UpperHalfPlane.denom, val_diagGL]

theorem σ_diagGL : UpperHalfPlane.σ (diagGL N) = .refl ℝ ℂ := by
  rw [UpperHalfPlane.σ, if_pos det_diagGL_pos]

theorem slash_diagGL_apply (k : ℤ) (φ : ℍ → ℂ) (τ : ℍ) :
    (φ ∣[k] diagGL N) τ = ((N : ℂ))⁻¹ * φ (diagGL N • τ) := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [ModularForm.slash_apply, σ_diagGL, det_diagGL, denom_diagGL]
  simp only [ContinuousAlgEquiv.refl_apply]
  have habs : |(N : ℝ)| = (N : ℝ) := abs_of_nonneg (Nat.cast_nonneg N)
  rw [habs]
  push_cast
  rw [show φ (diagGL N • τ) * (N : ℂ) ^ (k - 1) * (N : ℂ) ^ (-k) =
      ((N : ℂ) ^ (k - 1) * (N : ℂ) ^ (-k)) * φ (diagGL N • τ) by ring, ← zpow_add₀ hN,
    show k - 1 + -k = -1 by ring, zpow_neg_one]

theorem qParam_diagGL_smul (τ : ℍ) :
    Periodic.qParam 1 ((diagGL N • τ : ℍ) : ℂ) = Periodic.qParam (N : ℝ) τ := by
  simp only [Periodic.qParam, coe_diagGL_smul]
  congr 1
  push_cast
  ring

theorem natCast_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)

theorem coeff_qExpansion_Gform (f : ModularForm Γ₁(N) k) (n : ℕ) :
    (qExpansion (N : ℝ) (⇑(Gform f) : ℍ → ℂ)).coeff n =
      ((N : ℂ))⁻¹ * (qExpansion 1 (⇑f : ℍ → ℂ)).coeff n := by
  set c : ℕ → ℂ := fun n => ((N : ℂ))⁻¹ * (qExpansion 1 (⇑f : ℍ → ℂ)).coeff n with hc
  have hsum : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam (N : ℝ) τ ^ m) (Gform f τ) := by
    intro τ
    have h1 := hasSum_qExpansion one_pos
      (SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods N)) f.holo'
      (ModularFormClass.bdd_at_infty f) (diagGL N • τ)
    have h2 := h1.mul_left ((N : ℂ))⁻¹
    have happ : (Gform f : ℍ → ℂ) τ = ((N : ℂ))⁻¹ * f (diagGL N • τ) := by
      rw [coe_Gform, g₀_eq_diagGL, slash_diagGL_apply]
    rw [happ]
    convert h2 using 1 <;> first | (with_reducible_and_instances rfl) | rfl | skip
    funext m
    rw [qParam_diagGL_smul, smul_eq_mul, smul_eq_mul, hc]
    ring
  exact (ModularFormClass.qExpansion_coeff_unique natCast_pos (natCast_mem_strictPeriods_GammaS N)
    hsum n).symm

theorem Gform_slash_S (f : ModularForm Γ₁(N) k) :
    (⇑(Gform f) : ℍ → ℂ) ∣[k] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      (⇑f : ℍ → ℂ) ∣[k] frickeGL N := by
  rw [coe_Gform, ← SlashAction.slash_mul, g₀, inv_mul_cancel_right]

theorem slash_neg_one (ϑ : ModularForm Γ₁(N) w) :
    (⇑ϑ : ℍ → ℂ) ∣[w] (((-1 : SL(2, ℤ))) : GL (Fin 2) ℝ) = ((-1 : ℂ) ^ (-w)) • (⇑ϑ : ℍ → ℂ) := by
  funext τ
  have h1 : ((⇑ϑ : ℍ → ℂ) ∣[w] (((-1 : SL(2, ℤ))) : GL (Fin 2) ℝ)) τ =
      ((⇑ϑ : ℍ → ℂ) ∣[w] (-1 : SL(2, ℤ))) τ := rfl
  rw [h1, ModularForm.SL_slash_apply, ModularGroup.SL_neg_smul, one_smul]
  have hden : UpperHalfPlane.denom (-1 : SL(2, ℤ)) τ = -1 := by
    rw [ModularGroup.denom_apply]
    simp
  rw [hden, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem Thetaform_slash_S (ϑ : ModularForm Γ₁(N) w) :
    (⇑(Thetaform ϑ) : ℍ → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      ((-1 : ℂ) ^ (-w)) • (⇑ϑ : ℍ → ℂ) := by
  rw [coe_Thetaform, ← SlashAction.slash_mul, ← coeGL_mul, S_mul_S, slash_neg_one]

theorem coeff_qExpansion_Thetaform_slash_S (ϑ : ModularForm Γ₁(N) w) (n : ℕ) :
    (qExpansion 1 ((⇑(Thetaform ϑ) : ℍ → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n
      = (-1 : ℂ) ^ (-w) * (qExpansion 1 (⇑ϑ : ℍ → ℂ)).coeff n := by
  rw [Thetaform_slash_S, qExpansion_smul (ModularFormClass.analyticAt_cuspFunction_zero ϑ one_pos
    (one_mem_strictPeriods N))]
  simp

theorem Thetaform_slash (ϑ : ModularForm Γ₁(N) w) (β : SL(2, ℤ)) :
    (⇑(Thetaform ϑ) : ℍ → ℂ) ∣[w] (β : GL (Fin 2) ℝ) =
      (⇑ϑ : ℍ → ℂ) ∣[w] ((ModularGroup.S * β : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
  rw [coe_Thetaform, ← SlashAction.slash_mul, ← coeGL_mul]

end Forms

section Arith

theorem dvd_pow_self_of_dvd_pow {g N b : ℕ} (hg : g ≠ 0) (hN : N ≠ 0) (h : g ∣ N ^ b) :
    g ∣ N ^ g := by
  rw [← Nat.factorization_le_iff_dvd hg (pow_ne_zero _ hN)]
  intro p
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  by_cases hp : p ∈ g.primeFactors
  · have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpg : p ∣ g := Nat.dvd_of_mem_primeFactors hp
    have hpN : p ∣ N := hpp.dvd_of_dvd_pow (hpg.trans h)
    have h1 : 1 ≤ N.factorization p := by
      rwa [Nat.Prime.dvd_iff_one_le_factorization hpp hN] at hpN
    calc g.factorization p ≤ g := (Nat.factorization_lt p hg).le
      _ ≤ g * N.factorization p := Nat.le_mul_of_pos_right _ h1
  · rw [Finsupp.notMem_support_iff.mp hp]
    exact Nat.zero_le _

theorem isIntegral_pow_mul_of_isIntegral_mul {N D b : ℕ} (hN : N ≠ 0) (hD : D ≠ 0) {x : ℂ}
    (h1 : IsIntegral ℤ ((N : ℂ) ^ b * x)) (h2 : IsIntegral ℤ ((D : ℂ) * x)) :
    IsIntegral ℤ ((N : ℂ) ^ D * x) := by
  set g : ℕ := Nat.gcd D (N ^ b) with hg
  have hg0 : g ≠ 0 := Nat.gcd_ne_zero_left hD

  have hbez : (g : ℤ) = (D : ℤ) * Nat.gcdA D (N ^ b) + ((N ^ b : ℕ) : ℤ) * Nat.gcdB D (N ^ b) :=
    Nat.gcd_eq_gcd_ab D (N ^ b)
  have hgx : IsIntegral ℤ ((g : ℂ) * x) := by
    have e : (g : ℂ) * x = (Nat.gcdA D (N ^ b) : ℂ) * ((D : ℂ) * x) +
        (Nat.gcdB D (N ^ b) : ℂ) * ((N : ℂ) ^ b * x) := by
      have := congr_arg (fun z : ℤ => (z : ℂ)) hbez
      push_cast at this
      rw [this]; ring
    rw [e]
    exact ((isIntegral_intCast _).mul h2).add ((isIntegral_intCast _).mul h1)

  have hgdvd : g ∣ N ^ D := by
    have h1' : g ∣ N ^ g := dvd_pow_self_of_dvd_pow hg0 hN (Nat.gcd_dvd_right _ _)
    have hle : g ≤ D := Nat.le_of_dvd (Nat.pos_of_ne_zero hD) (Nat.gcd_dvd_left _ _)
    exact h1'.trans (Nat.pow_dvd_pow N hle)
  obtain ⟨q, hq⟩ := hgdvd
  have e : (N : ℂ) ^ D * x = (q : ℂ) * ((g : ℂ) * x) := by
    rw [← mul_assoc, ← Nat.cast_mul, mul_comm q, ← hq]; push_cast; ring
  rw [e]
  exact (isIntegral_natCast q).mul hgx

end Arith

section Main

variable {N : ℕ} [NeZero N] {k : ℤ}

theorem coeff_slash_fricke_mem_RN (hN : 2 ≤ N) (hk : Odd k → 3 ≤ N) (f : ModularForm Γ₁(N) k)
    {a : ℕ} (hf : ∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a * (qExpansion 1 (⇑f : ℍ → ℂ)).coeff n))
    (n : ℕ) :
    (qExpansion 1 ((⇑f : ℍ → ℂ) ∣[k] frickeGL N)).coeff n ∈ RN N := by
  obtain ⟨w, m₀, a', δ, ϑ, hpar, hm₀, hδ, hsrc, hz, hne, hinv, hint, hdec⟩ :=
    ModularCurve.exists_gamma1_peaked_auxiliary_form N hN k hk

  have hG : ∀ n : ℕ, (qExpansion ((N : ℕ) : ℝ) (⇑(Gform f) : ℍ → ℂ)).coeff n ∈ RN N := by
    intro n
    rw [coeff_qExpansion_Gform]
    exact (RN N).mul_mem inv_natCast_mem_RN (mem_RN_of_isIntegral_mul (hf n))
  have hΘ : ∀ n : ℕ, (qExpansion ((N : ℕ) : ℝ) (⇑(Thetaform ϑ) : ℍ → ℂ)).coeff n ∈ RN N := fun n =>
    mem_RN_of_isIntegral_mul (hsrc n)
  have hΘS₀ : ∀ n : ℕ, n < m₀ → (qExpansion 1 ((⇑(Thetaform ϑ) : ℍ → ℂ) ∣[w]
      ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n = 0 := by
    intro n hn
    rw [coeff_qExpansion_Thetaform_slash_S, hz n hn, mul_zero]
  have hΘS₁ : ∃ v ∈ RN N, v * (qExpansion 1 ((⇑(Thetaform ϑ) : ℍ → ℂ) ∣[w]
      ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff m₀ = 1 := by
    refine ⟨(-1 : ℂ) ^ (-w) * ((qExpansion 1 (⇑ϑ : ℍ → ℂ)).coeff m₀)⁻¹,
      (RN N).mul_mem (mem_RN_of_isIntegral (isIntegral_neg_one_zpow w))
        (mem_RN_of_isIntegral_mul hinv), ?_⟩
    rw [coeff_qExpansion_Thetaform_slash_S, mul_mul_mul_comm, neg_one_zpow_mul_self, one_mul,
      inv_mul_cancel₀ hne]
  have hΘS : ∀ n : ℕ, (qExpansion 1 ((⇑(Thetaform ϑ) : ℍ → ℂ) ∣[w]
      ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n ∈ RN N := by
    intro n
    rw [coeff_qExpansion_Thetaform_slash_S]
    exact (RN N).mul_mem (mem_RN_of_isIntegral (isIntegral_neg_one_zpow w))
      (mem_RN_of_isIntegral_mul (hint n))
  have hdecay : ∀ β : SL(2, ℤ),
      (∀ j : ℤ, β * ModularGroup.T ^ j ∉ GammaS N ∧ -(β * ModularGroup.T ^ j) ∉ GammaS N) →
      (β * ModularGroup.S⁻¹ ∉ GammaS N ∧ -(β * ModularGroup.S⁻¹) ∉ GammaS N) →
      ((⇑(Thetaform ϑ) : ℍ → ℂ) ∣[w] (β : GL (Fin 2) ℝ)) =O[atImInfty]
        fun τ : ℍ => Real.exp (-(2 * Real.pi * ((m₀ : ℝ) + δ)) * τ.im) := by
    intro β hT hS
    rw [Thetaform_slash]
    apply hdec (ModularGroup.S * β)
    ·
      constructor
      · intro hmem
        apply hS.2
        apply mem_GammaS_of
        have e : ModularGroup.S * -(β * ModularGroup.S⁻¹) * ModularGroup.S⁻¹ = ModularGroup.S * β := by
          rw [ModularGroup.S_inv]; simp only [mul_neg, neg_mul, neg_neg, mul_assoc, S_mul_S]; simp
        rwa [e]
      · intro hmem
        apply hS.1
        apply mem_GammaS_of
        have e : ModularGroup.S * (β * ModularGroup.S⁻¹) * ModularGroup.S⁻¹ = -(ModularGroup.S * β) := by
          rw [ModularGroup.S_inv]; simp only [mul_neg, neg_mul, neg_neg, mul_assoc, S_mul_S]; simp
        rwa [e]
    ·
      intro j
      constructor
      · intro hmem
        apply (hT j).1
        apply mem_GammaS_of
        simpa only [mul_assoc] using hmem
      · intro hmem
        apply (hT j).2
        apply mem_GammaS_of
        have e : ModularGroup.S * -(β * ModularGroup.T ^ j) * ModularGroup.S⁻¹ =
            -(ModularGroup.S * β * ModularGroup.T ^ j * ModularGroup.S⁻¹) := by
          simp only [mul_neg, neg_mul, mul_assoc]
        rwa [e]

  have key := ModularForm.qExpansion_slash_coeff_mem_of_peaked_auxiliary (GammaS N) N (NeZero.pos N)
    (T_pow_mem_GammaS N) (STS_mem_GammaS N) (RN N) hpar (Gform f) hG (Thetaform ϑ) hΘ m₀ hm₀
    hΘS₀ hΘS₁ hΘS δ hδ hdecay n
  rwa [Gform_slash_S] at key

theorem main_general (hN : 2 ≤ N) (hk : Odd k → 3 ≤ N) (f : ModularForm Γ₁(N) k)
    {a : ℕ} (hf : ∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a * (qExpansion 1 (⇑f : ℍ → ℂ)).coeff n)) :
    ∃ b : ℕ, ∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ b *
      (qExpansion 1 ((⇑f : ℍ → ℂ) ∣[k] frickeGL N)).coeff n) := by
  obtain ⟨D, hD, hBD⟩ := ModularCurve.exists_ne_zero_isIntegral_mul_qExpansion_slash_fricke_coeff N
    f a hf (frickeGL N) (val_frickeGL N)
  refine ⟨D, fun n => ?_⟩
  obtain ⟨b, hb⟩ := coeff_slash_fricke_mem_RN hN hk f hf n
  exact isIntegral_pow_mul_of_isIntegral_mul (NeZero.ne N) hD hb (hBD n)

theorem coe_eq_zero_of_odd (hN : N = 2) (hk : Odd k) (f : ModularForm Γ₁(N) k) :
    (⇑f : ℍ → ℂ) = 0 := by
  subst hN
  have hmem : (-1 : SL(2, ℤ)) ∈ Gamma1 2 := by
    rw [Gamma1_mem]
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (one_ne_zero : (1 : Fin 2) ≠ 0),
      neg_zero, Int.cast_zero, Int.cast_neg, Int.cast_one, and_true]
    decide
  have h1 : (⇑f : ℍ → ℂ) ∣[k] (((-1 : SL(2, ℤ))) : GL (Fin 2) ℝ) = ⇑f :=
    SlashInvariantFormClass.slash_action_eq f _ ⟨-1, hmem, rfl⟩
  rw [slash_neg_one] at h1
  obtain ⟨r, hr⟩ := hk
  have hneg : (-1 : ℂ) ^ (-k) = -1 := by
    rw [hr, show -(2 * r + 1) = 2 * (-r - 1) + 1 by ring, zpow_add₀ (by norm_num), zpow_mul]
    norm_num
  rw [hneg] at h1
  funext τ
  have := congr_fun h1 τ
  simp only [Pi.smul_apply, smul_eq_mul, neg_one_mul] at this
  have h2 : (2 : ℂ) * f τ = 0 := by linear_combination -this
  simpa using h2

theorem slash_eq_self_of_one (hN : N = 1) (f : ModularForm Γ₁(N) k) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (N : ℝ), 0]) :
    (⇑f : ℍ → ℂ) ∣[k] W = ⇑f := by
  subst hN
  have hWS : W = ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
    apply Units.ext
    rw [hW, val_S]
    simp
  rw [hWS]
  refine SlashInvariantFormClass.slash_action_eq f _ ⟨ModularGroup.S, ?_, rfl⟩
  show ModularGroup.S ∈ Gamma1 1
  rw [Gamma1_mem]
  refine ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

theorem main (f : ModularForm Γ₁(N) k) (a : ℕ)
    (hf : ∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a * (qExpansion 1 (⇑f : ℍ → ℂ)).coeff n))
    (W : GL (Fin 2) ℝ) (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (N : ℝ), 0]) :
    ∃ b : ℕ, ∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ b *
      (qExpansion 1 ((⇑f : ℍ → ℂ) ∣[k] W)).coeff n) := by
  by_cases hN1 : N = 1
  · refine ⟨a, fun n => ?_⟩
    rw [slash_eq_self_of_one hN1 f W hW]
    exact hf n
  have hN2 : 2 ≤ N := by
    have := NeZero.pos N
    omega
  have hWeq : W = frickeGL N := Units.ext hW
  by_cases hbad : N = 2 ∧ Odd k
  · refine ⟨0, fun n => ?_⟩
    rw [coe_eq_zero_of_odd hbad.1 hbad.2 f, SlashAction.zero_slash, qExpansion_zero]
    simpa using isIntegral_zero
  have hk : Odd k → 3 ≤ N := by
    intro hodd
    by_contra h
    exact hbad ⟨by omega, hodd⟩
  rw [hWeq]
  exact main_general hN2 hk f hf

end Main

end R1FrickeInt
p2m_reactivate "P2MW.S_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_fricke_coeff.R1FrickeInt"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_fricke_coeff.R1FrickeInt"

set_option autoImplicit false
open scoped MatrixGroups ModularForm in
theorem solution (N : ℕ)
    [NeZero N] {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) (a : ℕ)
    (hf : ∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a *
      (UpperHalfPlane.qExpansion 1 (⇑f : UpperHalfPlane → ℂ)).coeff n))
    (W : GL (Fin 2) ℝ) (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (N : ℝ), 0]) :
    ∃ b : ℕ, ∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ b *
      (UpperHalfPlane.qExpansion 1 ((⇑f : UpperHalfPlane → ℂ) ∣[k] W)).coeff n) :=
  R1FrickeInt.main f a hf W hW

end S_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_fricke_coeff
end P2MW
export P2MW.S_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_fricke_coeff (solution)
