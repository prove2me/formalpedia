-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_whittaker_localLevelOne_centralChar_admissible_principalSeries2_apply_one_ne_zero_of_norm_eq_one_of_higherUnitsAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/462cf19b-dcb1-56a7-af6f-fb89dcd12a41

import Mathlib
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_whittaker_localLevelOne_centralChar_admissible_principalSeries2_of_norm_eq_one_of_higherUnitsAt
import Theorems.Thm_AutomorphicForm_LocalFunctionSpace_eq_zero_of_forall_apply_diagOne_eq_zero_of_irreducible_of_admissible
import Theorems.Thm_NumberField_StandardAddChar_psiLocal_rat_eq_psiV
import Theorems.Thm_LocalGL2_iwasawa_decomposition_diag
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_whittaker_localLevelOne_centralChar_admissible_principalSeries2_apply_one_ne_zero_of_norm_eq_one_of_higherUnitsAt
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension"
p2m_attr_erase "instance" "NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension"
p2m_attr_erase "simp" "FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk"
p2m_attr_erase "simp" "FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply"
p2m_attr_erase "simp" "IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.longFile 0
noncomputable section

open IsDedekindDomain NumberField
open scoped WithZero

namespace PsNvLocal

variable {p : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => HeightOneSpectrum.adicCompletion ℚ p
local notation "Mat" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)
local notation "ψ" => NumberField.StandardAddChar.psiV p

variable (p) in

def unif : HeightOneSpectrum.adicCompletion ℚ p :=
  algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ p) ((Rat.HeightOneSpectrum.natGenerator p : ℕ) : ℚ)

theorem v_unif : Valued.v (unif p) = WithZero.exp (-1 : ℤ) := by
  rw [unif, RatIdele.valued_algebraMap_rat, RatIdele.valuation_natGenerator]

theorem unif_ne_zero : unif p ≠ 0 := by
  intro h
  have h1 := v_unif (p := p)
  rw [h, Valuation.map_zero] at h1
  exact WithZero.exp_ne_zero h1.symm

theorem v_unif_inv : Valued.v (unif p)⁻¹ = WithZero.exp (1 : ℤ) := by
  rw [map_inv₀, v_unif, ← WithZero.exp_neg, neg_neg]

theorem v_unif_pow (n : ℕ) : Valued.v (unif p ^ n) = WithZero.exp (-(n : ℤ)) := by
  rw [map_pow, v_unif, ← WithZero.exp_nsmul]; congr 1; simp

theorem psi_unif_inv_ne_one : ψ (unif p)⁻¹ ≠ 1 := by
  rw [unif, ← map_inv₀]
  exact NumberField.StandardAddChar.psiV_algebraMap_inv_ne_one p

theorem psi_eq_one_of_v_le_one {x : F} (hx : Valued.v x ≤ 1) : ψ x = 1 :=
  NumberField.StandardAddChar.psiV_eq_one_of_mem_integers p
    ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hx)

theorem v_add_le {x y : F} {γ : ℤᵐ⁰} (hx : Valued.v x ≤ γ) (hy : Valued.v y ≤ γ) :
    Valued.v (x + y) ≤ γ :=
  (Valuation.map_add _ x y).trans (max_le hx hy)

theorem v_sub_le {x y : F} {γ : ℤᵐ⁰} (hx : Valued.v x ≤ γ) (hy : Valued.v y ≤ γ) :
    Valued.v (x - y) ≤ γ := by
  rw [sub_eq_add_neg]; exact v_add_le hx (by rwa [Valuation.map_neg])

theorem v_ne_zero {x : F} (hx : x ≠ 0) : Valued.v x ≠ 0 := by
  rwa [ne_eq, Valuation.zero_iff]

theorem ne_zero_of_v_eq_one {x : F} (hx : Valued.v x = 1) : x ≠ 0 := by
  intro h; rw [h, Valuation.map_zero] at hx; exact zero_ne_one hx

theorem exp_neg_natCast_le_one (c : ℕ) : WithZero.exp (-(c : ℤ)) ≤ (1 : ℤᵐ⁰) := by
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega

theorem exp_succ_le_of_exp_lt {y : F} {i : ℤ} (h : WithZero.exp i < Valued.v y) :
    WithZero.exp (i + 1) ≤ Valued.v y := by
  have hy : Valued.v y ≠ 0 := (lt_of_le_of_lt zero_le' h).ne'
  rw [← WithZero.exp_log hy] at h ⊢
  rw [WithZero.exp_lt_exp] at h
  rw [WithZero.exp_le_exp]
  omega

theorem exists_v_le_exp (x : F) : ∃ j : ℕ, Valued.v x ≤ WithZero.exp (j : ℤ) := by
  by_cases hx : Valued.v x = 0
  · exact ⟨0, by rw [hx]; exact zero_le'⟩
  · refine ⟨(WithZero.log (Valued.v x)).toNat, ?_⟩
    conv_lhs => rw [← WithZero.exp_log hx]
    rw [WithZero.exp_le_exp]
    exact Int.self_le_toNat _

theorem v_eq_one_of_sub_one_lt {x : F} (hx : Valued.v (x - 1) < 1) : Valued.v x = 1 := by
  have : x = 1 + (x - 1) := by ring
  rw [this]
  exact Valuation.map_one_add_of_lt _ hx

theorem v_inv_sub_one {x : F} (h1 : Valued.v x = 1) : Valued.v (x⁻¹ - 1) = Valued.v (x - 1) := by
  have hx0 := ne_zero_of_v_eq_one h1
  have : x⁻¹ - 1 = x⁻¹ * (-(x - 1)) := by field_simp; ring
  rw [this, Valuation.map_mul, Valuation.map_neg, map_inv₀, h1, inv_one, one_mul]

abbrev nU (x : HeightOneSpectrum.adicCompletion ℚ p) : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) :=
  AutomorphicForm.unipotentGL2 x

def gl2 (a b c d : F) (h : a * d - b * c ≠ 0) : G :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; c, d] (by rwa [Matrix.det_fin_two_of])

@[scoped simp] theorem gl2_coe (a b c d : F) (h : a * d - b * c ≠ 0) :
    ((gl2 a b c d h : G) : Mat) = !![a, b; c, d] := rfl

theorem nU_coe (x : F) : ((nU x : G) : Mat) = !![1, x; 0, 1] := rfl

theorem diagOne_coe (a : Fˣ) :
    ((AdelicLevel.diagOne a : G) : Mat) = !![(a : F), 0; 0, 1] := by
  ext i j
  rw [AdelicLevel.diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem gl_eq_of_entries {g h : G}
    (h00 : (g : Mat) 0 0 = (h : Mat) 0 0) (h01 : (g : Mat) 0 1 = (h : Mat) 0 1)
    (h10 : (g : Mat) 1 0 = (h : Mat) 1 0) (h11 : (g : Mat) 1 1 = (h : Mat) 1 1) : g = h := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

theorem mul_coe_apply (g h : G) (i j : Fin 2) :
    ((g * h : G) : Mat) i j = (g : Mat) i 0 * (h : Mat) 0 j + (g : Mat) i 1 * (h : Mat) 1 j := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem nU_add (x y : F) : (nU (x + y) : G) = nU x * nU y := AutomorphicForm.unipotentGL2_add x y

theorem nU_zero : (nU (0 : F) : G) = 1 := AutomorphicForm.unipotentGL2_zero

theorem nU_inv (x : F) : ((nU x : G)⁻¹ : G) = nU (-x) := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← nU_add, neg_add_cancel, nU_zero]

theorem diagOne_mul_nU (a : Fˣ) (x : F) :
    (AdelicLevel.diagOne a : G) * nU x = nU ((a : F) * x) * AdelicLevel.diagOne a := by
  apply gl_eq_of_entries <;> simp [mul_coe_apply, nU_coe, diagOne_coe]

theorem nU_mul_diagOne (a : Fˣ) (x : F) :
    (nU x : G) * AdelicLevel.diagOne a = AdelicLevel.diagOne a * nU ((a : F)⁻¹ * x) := by
  rw [diagOne_mul_nU, ← mul_assoc, mul_inv_cancel₀ a.ne_zero, one_mul]

def lowU (y : F) : G := gl2 1 0 y 1 (by simp)

@[scoped simp] theorem lowU_coe (y : F) : ((lowU y : G) : Mat) = !![1, 0; y, 1] := rfl

theorem lowU_add (x y : F) : (lowU (x + y) : G) = lowU x * lowU y := by
  apply gl_eq_of_entries <;> simp [mul_coe_apply, lowU_coe] <;> ring

theorem lowU_zero : (lowU (0 : F) : G) = 1 := by
  apply gl_eq_of_entries <;> simp [lowU_coe]

theorem lowU_inv (y : F) : ((lowU y : G)⁻¹ : G) = lowU (-y) := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← lowU_add, neg_add_cancel, lowU_zero]

theorem diagOne_mul_lowU (a : Fˣ) (y : F) :
    (AdelicLevel.diagOne a : G) * lowU y = lowU ((a : F)⁻¹ * y) * AdelicLevel.diagOne a := by
  have ha : (a : F) ≠ 0 := a.ne_zero
  apply gl_eq_of_entries <;> simp [mul_coe_apply, lowU_coe, diagOne_coe] ; field_simp

theorem diag_mul_nU (t₁ t₂ : F) (h : t₁ * t₂ - 0 * 0 ≠ 0) (x : F) :
    gl2 t₁ 0 0 t₂ h * nU x = nU (t₁ * x * t₂⁻¹) * gl2 t₁ 0 0 t₂ h := by
  have ht₂ : t₂ ≠ 0 := by intro h'; apply h; simp [h']
  apply gl_eq_of_entries <;> simp [mul_coe_apply, nU_coe] ; field_simp

theorem diag_eq_prod (x y : F) (ht : 1 + x * y ≠ 0) (hdet : (1 + x * y) * (1 + x * y)⁻¹ - 0 * 0 ≠ 0) :
    gl2 (1 + x * y) 0 0 (1 + x * y)⁻¹ hdet =
      lowU (-(y / (1 + x * y))) * nU x * lowU y * nU (-(x / (1 + x * y))) := by
  have ht' : 1 + y * x ≠ 0 := by rwa [mul_comm y x]
  apply gl_eq_of_entries <;> simp [mul_coe_apply, nU_coe, lowU_coe] <;> field_simp <;> ring

def stab (W : G → ℂ) : Subgroup G where
  carrier := {h | ∀ g, W (g * h) = W g}
  one_mem' := fun g => by rw [mul_one]
  mul_mem' := by
    intro a b ha hb g
    rw [← mul_assoc, hb, ha]
  inv_mem' := by
    intro a ha g
    have := ha (g * a⁻¹)
    rw [inv_mul_cancel_right] at this
    exact this.symm

theorem mem_stab {W : G → ℂ} {h : G} : h ∈ stab W ↔ ∀ g, W (g * h) = W g := Iff.rfl

variable (p) in

abbrev K1 (c : ℕ) : Subgroup (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)) :=
  AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ c)

theorem pow_asIdeal_ne_bot (c : ℕ) : p.asIdeal ^ c ≠ ⊥ :=
  pow_ne_zero c p.ne_bot

theorem idealBound_pow (c : ℕ) :
    AdelicLevel.idealBound (𝓞 ℚ) (p.asIdeal ^ c) p = WithZero.exp (-(c : ℤ)) := by
  classical
  rw [AdelicLevel.idealBound_of_ne_bot (pow_asIdeal_ne_bot c), Associates.mk_pow,
    Associates.count_pow (Associates.mk_ne_zero.mpr p.ne_bot) (Associates.irreducible_mk.mpr p.irreducible),
    Associates.count_self (Associates.irreducible_mk.mpr p.irreducible), mul_one]

structure IsK1 (c : ℕ) (m : Mat) : Prop where
  integral : ∀ i j, Valued.v (m i j) ≤ 1
  lowerLeft : Valued.v (m 1 0) ≤ WithZero.exp (-(c : ℤ))
  lowerRight : Valued.v (m 1 1 - 1) ≤ WithZero.exp (-(c : ℤ))

theorem isK1_iff {c : ℕ} (m : Mat) : AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ c) m ↔ IsK1 c m := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h1 i j), ?_, ?_⟩
    · rwa [idealBound_pow] at h2
    · rwa [idealBound_pow] at h3
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (h1 i j), ?_, ?_⟩
    · rwa [idealBound_pow]
    · rwa [idealBound_pow]

theorem mem_K1_iff {c : ℕ} (k : G) : k ∈ K1 p c ↔ IsK1 c (k : Mat) ∧ IsK1 c ((k⁻¹ : G) : Mat) := by
  rw [AdelicDock.mem_localLevelOne_iff, isK1_iff, isK1_iff]

theorem nU_mem_K1 (c : ℕ) {t : F} (ht : Valued.v t ≤ 1) : (nU t : G) ∈ K1 p c := by
  have key : ∀ s : F, Valued.v s ≤ 1 → IsK1 c ((nU s : G) : Mat) := by
    intro s hs
    refine ⟨fun i j => ?_, ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [nU_coe, hs]
    · simp [nU_coe]
    · simp [nU_coe]
  rw [mem_K1_iff, nU_inv]
  exact ⟨key t ht, key (-t) (by rwa [Valuation.map_neg])⟩

theorem diagOne_mem_K1 (c : ℕ) {u : Fˣ} (hu : Valued.v (u : F) = 1) :
    (AdelicLevel.diagOne u : G) ∈ K1 p c := by
  have key : ∀ w : Fˣ, Valued.v (w : F) = 1 → IsK1 c ((AdelicLevel.diagOne w : G) : Mat) := by
    intro w hw
    refine ⟨fun i j => ?_, ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [diagOne_coe, hw]
    · simp [diagOne_coe]
    · simp [diagOne_coe]
  rw [mem_K1_iff, ← map_inv]
  refine ⟨key u hu, key u⁻¹ ?_⟩
  rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]

theorem lowU_mem_K1 (c : ℕ) {s : F} (hs : Valued.v s ≤ WithZero.exp (-(c : ℤ))) : (lowU s : G) ∈ K1 p c := by
  have key : ∀ r : F, Valued.v r ≤ WithZero.exp (-(c : ℤ)) → IsK1 c ((lowU r : G) : Mat) := by
    intro r hr
    refine ⟨fun i j => ?_, ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [lowU_coe, hr.trans (exp_neg_natCast_le_one c)]
    · simpa [lowU_coe] using hr
    · simp [lowU_coe]
  rw [mem_K1_iff, lowU_inv]
  exact ⟨key s hs, key (-s) (by rwa [Valuation.map_neg])⟩

theorem v_det_of_mem_K1 {c : ℕ} {k : G} (hk : k ∈ K1 p c) :
    Valued.v ((k : Mat) 0 0 * (k : Mat) 1 1 - (k : Mat) 0 1 * (k : Mat) 1 0) = 1 := by
  rw [mem_K1_iff] at hk
  have h1 : Valued.v (k : Mat).det ≤ 1 := by
    rw [Matrix.det_fin_two]
    exact v_sub_le (by rw [Valuation.map_mul]; exact mul_le_one' (hk.1.integral 0 0) (hk.1.integral 1 1))
      (by rw [Valuation.map_mul]; exact mul_le_one' (hk.1.integral 0 1) (hk.1.integral 1 0))
  have h2 : Valued.v ((k⁻¹ : G) : Mat).det ≤ 1 := by
    rw [Matrix.det_fin_two]
    exact v_sub_le (by rw [Valuation.map_mul]; exact mul_le_one' (hk.2.integral 0 0) (hk.2.integral 1 1))
      (by rw [Valuation.map_mul]; exact mul_le_one' (hk.2.integral 0 1) (hk.2.integral 1 0))
  have hprod : (k : Mat).det * ((k⁻¹ : G) : Mat).det = 1 := by
    rw [← Matrix.det_mul, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one,
      Matrix.det_one]
  have hv : Valued.v (k : Mat).det * Valued.v ((k⁻¹ : G) : Mat).det = 1 := by
    rw [← Valuation.map_mul, hprod, Valuation.map_one]
  rw [← Matrix.det_fin_two]
  exact le_antisymm h1 (by
    calc (1 : ℤᵐ⁰) = Valued.v (k : Mat).det * Valued.v ((k⁻¹ : G) : Mat).det := hv.symm
      _ ≤ Valued.v (k : Mat).det * 1 := mul_le_mul_right h2 _
      _ = Valued.v (k : Mat).det := mul_one _)

end PsNvLocal
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_whittaker_localLevelOne_centralChar_admissible_principalSeries2_apply_one_ne_zero_of_norm_eq_one_of_higherUnitsAt.PsNvLocal"

namespace PsNvLocal

variable {p : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => HeightOneSpectrum.adicCompletion ℚ p
local notation "Mat" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)
local notation "ψ" => NumberField.StandardAddChar.psiV p

section Main

variable {S : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ)}
  (hstab : ∀ W ∈ S, ∀ k : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p), (fun g => W (g * k)) ∈ S)
  (hsm : ∀ W ∈ S, ∃ K : Subgroup (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)),
      IsOpen (K : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) ∧ ∀ k ∈ K, (fun g => W (g * k)) = W)
  (hpsi : ∀ W ∈ S, ∀ (x : HeightOneSpectrum.adicCompletion ℚ p)
      (g : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)),
      W (AutomorphicForm.unipotentGL2 x * g) = NumberField.StandardAddChar.psiV p x * W g)
  (hirr : ∀ T : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ), T ≤ S →
      (∀ W ∈ T, ∀ k : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p), (fun g => W (g * k)) ∈ T) →
      T = ⊥ ∨ T = S)
  (hadm : ∀ K : Subgroup (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)),
      IsOpen (K : Set (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))) →
      ∀ T : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ), T ≤ S →
        (∀ W ∈ T, ∀ k ∈ K, (fun g => W (g * k)) = W) → FiniteDimensional ℂ T)

include hstab hsm hpsi hirr hadm in

theorem kirillov {W : G → ℂ} (hW : W ∈ S) (hW0 : ∀ y : Fˣ, W (AdelicLevel.diagOne y) = 0) : W = 0 :=
  AutomorphicForm.LocalFunctionSpace.eq_zero_of_forall_apply_diagOne_eq_zero_of_irreducible_of_admissible
    p S hstab hsm hpsi hirr hadm W hW hW0

include hpsi in

theorem apply_diagOne_eq_zero_of_nU_mem_stab {W : G → ℂ} (hW : W ∈ S) {j : ℤ}
    (hfix : ∀ t : F, Valued.v t ≤ WithZero.exp j → (nU t : G) ∈ stab W)
    (y : Fˣ) (hy : WithZero.exp (-j) < Valued.v (y : F)) : W (AdelicLevel.diagOne y) = 0 := by
  have hy1 := exp_succ_le_of_exp_lt hy
  set t : F := (y : F)⁻¹ * (unif p)⁻¹ with ht
  have hvt : Valued.v t ≤ WithZero.exp j := by
    have hy' : Valued.v (y : F) ≠ 0 := v_ne_zero y.ne_zero
    rw [ht, Valuation.map_mul, map_inv₀, v_unif_inv]
    rw [← WithZero.exp_log hy'] at hy1 ⊢
    rw [WithZero.exp_le_exp] at hy1
    rw [← WithZero.exp_neg, ← WithZero.exp_add, WithZero.exp_le_exp]
    omega
  have h1 : W (AdelicLevel.diagOne y * nU t) = W (AdelicLevel.diagOne y) := hfix t hvt _
  rw [diagOne_mul_nU, hpsi W hW, show (y : F) * t = (unif p)⁻¹ by rw [ht]; field_simp] at h1
  have h2 : (ψ (unif p)⁻¹ - 1) * W (AdelicLevel.diagOne y) = 0 := by rw [sub_mul, one_mul, h1, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr psi_unif_inv_ne_one)

include hstab hsm hpsi hirr hadm in

theorem nU_mem_stab_of_apply_one_eq_zero {c : ℕ} {W : G → ℂ} (hW : W ∈ S)
    (hfix : ∀ k ∈ K1 p c, ∀ g : G, W (g * k) = W g) (h1 : W 1 = 0)
    {s : F} (hs : Valued.v s ≤ WithZero.exp (1 : ℤ)) : (nU s : G) ∈ stab W := by

  have hN0 : ∀ t : F, Valued.v t ≤ WithZero.exp (0 : ℤ) → (nU t : G) ∈ stab W := by
    intro t ht g
    rw [WithZero.exp_zero] at ht
    exact hfix _ (nU_mem_K1 c ht) g
  have htor : ∀ y : Fˣ, 1 ≤ Valued.v (y : F) → W (AdelicLevel.diagOne y) = 0 := by
    intro y hy
    rcases hy.lt_or_eq with hlt | heq
    · exact apply_diagOne_eq_zero_of_nU_mem_stab hpsi hW hN0 y (by rwa [neg_zero, WithZero.exp_zero])
    · have := hfix _ (diagOne_mem_K1 c heq.symm) 1
      rw [one_mul, h1] at this
      exact this

  set W' : G → ℂ := (fun g => W (g * nU s)) - W with hW'
  have hW'S : W' ∈ S := S.sub_mem (hstab W hW _) hW
  have hW'0 : ∀ y : Fˣ, W' (AdelicLevel.diagOne y) = 0 := by
    intro y
    simp only [hW', Pi.sub_apply]
    rw [diagOne_mul_nU, hpsi W hW]
    by_cases hy : Valued.v (y : F) ≤ WithZero.exp (-1 : ℤ)
    · rw [psi_eq_one_of_v_le_one, one_mul, sub_self]
      simpa using (v_mul_le' hy hs)
    · rw [htor y, mul_zero, sub_self]
      have := exp_succ_le_of_exp_lt (lt_of_not_ge hy)
      simpa using this
  have hzero := kirillov hstab hsm hpsi hirr hadm hW'S hW'0
  intro g
  have := congrFun hzero g
  simp only [hW', Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
  exact this
where
  v_mul_le' {x y : F} {a b : ℤ} (hx : Valued.v x ≤ WithZero.exp a) (hy : Valued.v y ≤ WithZero.exp b) :
      Valued.v (x * y) ≤ WithZero.exp (a + b) := by
    rw [Valuation.map_mul, WithZero.exp_add]; exact mul_le_mul' hx hy

include hstab hsm hpsi hirr hadm in

theorem descent {c₀ : ℕ} {W : G → ℂ} (hW : W ∈ S)
    (hfix : ∀ k ∈ K1 p (c₀ + 1), ∀ g : G, W (g * k) = W g) (h1 : W 1 = 0) :
    ∀ k ∈ K1 p c₀, ∀ g : G,
      W (g * k * AdelicLevel.diagOne (Units.mk0 (unif p) unif_ne_zero)) =
        W (g * AdelicLevel.diagOne (Units.mk0 (unif p) unif_ne_zero)) := by
  set d : G := AdelicLevel.diagOne (Units.mk0 (unif p) unif_ne_zero) with hd
  set W₃ : G → ℂ := fun g => W (g * d) with hW₃

  have hconj : ∀ k ∈ K1 p (c₀ + 1), d * k * d⁻¹ ∈ stab W₃ := by
    intro k hk g
    simp only [hW₃]
    rw [show g * (d * k * d⁻¹) * d = g * d * k by group]
    exact hfix k hk _

  have hN : ∀ t : F, Valued.v t ≤ 1 → (nU t : G) ∈ stab W₃ := by
    intro t ht g
    simp only [hW₃]
    rw [mul_assoc, hd, nU_mul_diagOne, ← mul_assoc]
    refine nU_mem_stab_of_apply_one_eq_zero hstab hsm hpsi hirr hadm hW hfix h1 ?_ _
    rw [Units.val_mk0, Valuation.map_mul, v_unif_inv]
    calc WithZero.exp 1 * Valued.v t ≤ WithZero.exp 1 * 1 := mul_le_mul_right ht _
      _ = WithZero.exp 1 := mul_one _

  have hL : ∀ s : F, Valued.v s ≤ WithZero.exp (-(c₀ : ℤ)) → (lowU s : G) ∈ stab W₃ := by
    intro s hs
    have hmem : (lowU (unif p * s) : G) ∈ K1 p (c₀ + 1) := by
      refine lowU_mem_K1 _ ?_
      rw [Valuation.map_mul, v_unif]
      calc WithZero.exp (-1) * Valued.v s ≤ WithZero.exp (-1) * WithZero.exp (-(c₀ : ℤ)) := mul_le_mul_right hs _
        _ = WithZero.exp (-((c₀ + 1 : ℕ) : ℤ)) := by rw [← WithZero.exp_add]; congr 1; push_cast; ring
    have := hconj _ hmem
    rw [hd, diagOne_mul_lowU, mul_assoc, mul_inv_cancel, mul_one, Units.val_mk0, inv_mul_cancel_left₀ unif_ne_zero]
      at this
    exact this

  have hD : ∀ u : Fˣ, Valued.v (u : F) = 1 → (AdelicLevel.diagOne u : G) ∈ stab W₃ := by
    intro u hu
    have := hconj _ (diagOne_mem_K1 (c₀ + 1) hu)
    rwa [hd, ← map_mul, mul_comm, map_mul, mul_assoc, mul_inv_cancel, mul_one] at this

  have hunit : ∀ k ∈ K1 p c₀, Valued.v ((k : Mat) 1 1) = 1 → k ∈ stab W₃ := by
    intro k hk hδ
    have hk' := (mem_K1_iff k).mp hk
    have hδ0 : (k : Mat) 1 1 ≠ 0 := ne_zero_of_v_eq_one hδ
    have hdet : Valued.v ((k : Mat) 0 0 * (k : Mat) 1 1 - (k : Mat) 0 1 * (k : Mat) 1 0) = 1 := v_det_of_mem_K1 hk
    have hdet0 : (k : Mat) 0 0 * (k : Mat) 1 1 - (k : Mat) 0 1 * (k : Mat) 1 0 ≠ 0 := ne_zero_of_v_eq_one hdet

    have hDdet : ((k : Mat) 0 0 * (k : Mat) 1 1 - (k : Mat) 0 1 * (k : Mat) 1 0) / (k : Mat) 1 1 * (k : Mat) 1 1
        - 0 * 0 ≠ 0 := by
      field_simp; simpa using hdet0
    have hk_eq : k = nU ((k : Mat) 0 1 / (k : Mat) 1 1) *
        gl2 (((k : Mat) 0 0 * (k : Mat) 1 1 - (k : Mat) 0 1 * (k : Mat) 1 0) / (k : Mat) 1 1) 0 0 ((k : Mat) 1 1)
          hDdet * lowU ((k : Mat) 1 0 / (k : Mat) 1 1) := by
      apply gl_eq_of_entries <;> simp [mul_coe_apply, nU_coe, lowU_coe, hδ0] <;> field_simp <;> ring

    set detU : Fˣ := Units.mk0 ((k : Mat) 0 0 * (k : Mat) 1 1 - (k : Mat) 0 1 * (k : Mat) 1 0) hdet0 with hdetU
    have hy : 1 + (1 : F) * (((k : Mat) 1 1)⁻¹ - 1) ≠ 0 := by
      rw [one_mul, add_sub_cancel]; exact inv_ne_zero hδ0
    have htdet : (1 + (1 : F) * (((k : Mat) 1 1)⁻¹ - 1)) * (1 + (1 : F) * (((k : Mat) 1 1)⁻¹ - 1))⁻¹ - 0 * 0 ≠ 0 := by
      rw [mul_inv_cancel₀ hy]; simp
    have hD_eq : gl2 (((k : Mat) 0 0 * (k : Mat) 1 1 - (k : Mat) 0 1 * (k : Mat) 1 0) / (k : Mat) 1 1) 0 0
          ((k : Mat) 1 1) hDdet =
        AdelicLevel.diagOne detU * gl2 (1 + (1 : F) * (((k : Mat) 1 1)⁻¹ - 1)) 0 0
          (1 + (1 : F) * (((k : Mat) 1 1)⁻¹ - 1))⁻¹ htdet := by
      apply gl_eq_of_entries <;> simp [mul_coe_apply, diagOne_coe, detU, hδ0] ; field_simp
    have hT_eq := diag_eq_prod (1 : F) (((k : Mat) 1 1)⁻¹ - 1) hy htdet

    have hvδ1 : Valued.v (((k : Mat) 1 1)⁻¹ - 1) ≤ WithZero.exp (-(c₀ : ℤ)) := by
      rw [v_inv_sub_one hδ]; exact hk'.1.lowerRight
    have hm1 : (lowU (-((((k : Mat) 1 1)⁻¹ - 1) / (1 + 1 * (((k : Mat) 1 1)⁻¹ - 1)))) : G) ∈ stab W₃ := by
      refine hL _ ?_
      rw [Valuation.map_neg, one_mul, add_sub_cancel, div_eq_mul_inv, inv_inv, Valuation.map_mul, hδ, mul_one]
      exact hvδ1
    have hm2 : (nU (1 : F) : G) ∈ stab W₃ := hN 1 (by simp)
    have hm3 : (lowU (((k : Mat) 1 1)⁻¹ - 1) : G) ∈ stab W₃ := hL _ hvδ1
    have hm4 : (nU (-(1 / (1 + 1 * (((k : Mat) 1 1)⁻¹ - 1)))) : G) ∈ stab W₃ := by
      refine hN _ ?_
      rw [Valuation.map_neg, one_mul, add_sub_cancel, one_div, inv_inv]
      exact hδ.le
    have hT : (gl2 (1 + (1 : F) * (((k : Mat) 1 1)⁻¹ - 1)) 0 0 (1 + (1 : F) * (((k : Mat) 1 1)⁻¹ - 1))⁻¹ htdet : G)
        ∈ stab W₃ := by
      rw [hT_eq]
      exact (stab W₃).mul_mem ((stab W₃).mul_mem ((stab W₃).mul_mem hm1 hm2) hm3) hm4
    have hDm : (gl2 (((k : Mat) 0 0 * (k : Mat) 1 1 - (k : Mat) 0 1 * (k : Mat) 1 0) / (k : Mat) 1 1) 0 0
          ((k : Mat) 1 1) hDdet : G) ∈ stab W₃ := by
      rw [hD_eq]
      refine (stab W₃).mul_mem (hD detU ?_) hT
      rw [hdetU, Units.val_mk0]; exact hdet
    have hn : (nU ((k : Mat) 0 1 / (k : Mat) 1 1) : G) ∈ stab W₃ := by
      refine hN _ ?_
      rw [map_div₀, hδ, div_one]; exact hk'.1.integral 0 1
    have hl : (lowU ((k : Mat) 1 0 / (k : Mat) 1 1) : G) ∈ stab W₃ := by
      refine hL _ ?_
      rw [map_div₀, hδ, div_one]; exact hk'.1.lowerLeft
    rw [hk_eq]
    exact (stab W₃).mul_mem ((stab W₃).mul_mem hn hDm) hl

  intro k hk g
  suffices hk3 : k ∈ stab W₃ by exact hk3 g
  by_cases hδ : Valued.v ((k : Mat) 1 1) = 1
  · exact hunit k hk hδ
  · have hk' := (mem_K1_iff k).mp hk
    have hδlt : Valued.v ((k : Mat) 1 1) < 1 := lt_of_le_of_ne (hk'.1.integral 1 1) hδ

    have hk1 : k * nU 1 ∈ K1 p c₀ := (K1 p c₀).mul_mem hk (nU_mem_K1 c₀ (by simp))
    have hγ : Valued.v ((k : Mat) 1 0) = 1 := by
      have hdet : Valued.v ((k : Mat) 0 0 * (k : Mat) 1 1 - (k : Mat) 0 1 * (k : Mat) 1 0) = 1 :=
        v_det_of_mem_K1 hk
      have hlt : Valued.v ((k : Mat) 0 0 * (k : Mat) 1 1) < 1 := by
        rw [Valuation.map_mul]
        calc Valued.v ((k : Mat) 0 0) * Valued.v ((k : Mat) 1 1)
            ≤ 1 * Valued.v ((k : Mat) 1 1) := mul_le_mul_left (hk'.1.integral 0 0) _
          _ = Valued.v ((k : Mat) 1 1) := one_mul _
          _ < 1 := hδlt
      have hβγ : Valued.v ((k : Mat) 0 1 * (k : Mat) 1 0) = 1 := by
        by_contra hne
        have hle : Valued.v ((k : Mat) 0 1 * (k : Mat) 1 0) ≤ 1 := by
          rw [Valuation.map_mul]; exact mul_le_one' (hk'.1.integral 0 1) (hk'.1.integral 1 0)
        have hlt' : Valued.v ((k : Mat) 0 1 * (k : Mat) 1 0) < 1 := lt_of_le_of_ne hle hne
        have := v_sub_le hlt.le hlt'.le
        have h2 : Valued.v ((k : Mat) 0 0 * (k : Mat) 1 1 - (k : Mat) 0 1 * (k : Mat) 1 0) < 1 := by
          rw [sub_eq_add_neg]
          refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hlt ?_)
          rwa [Valuation.map_neg]
        rw [hdet] at h2
        exact lt_irrefl _ h2
      rw [Valuation.map_mul] at hβγ
      refine le_antisymm (hk'.1.integral 1 0) ?_
      calc (1 : ℤᵐ⁰) = Valued.v ((k : Mat) 0 1) * Valued.v ((k : Mat) 1 0) := hβγ.symm
        _ ≤ 1 * Valued.v ((k : Mat) 1 0) := mul_le_mul_left (hk'.1.integral 0 1) _
        _ = Valued.v ((k : Mat) 1 0) := one_mul _
    have hδ' : Valued.v (((k * nU 1 : G) : Mat) 1 1) = 1 := by
      rw [mul_coe_apply, nU_coe]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Matrix.cons_val_zero, mul_one]
      rw [Valuation.map_add_eq_of_lt_left]
      · exact hγ
      · rw [hγ]; exact hδlt
    have h1 : k * nU 1 ∈ stab W₃ := hunit _ hk1 hδ'
    have h2 : (nU (-1 : F) : G) ∈ stab W₃ := hN _ (by simp)
    have : k = k * nU 1 * nU (-1) := by rw [mul_assoc, ← nU_add, add_neg_cancel, nU_zero, mul_one]
    rw [this]
    exact (stab W₃).mul_mem h1 h2

include hstab hsm hpsi hirr hadm in

theorem eq_zero_of_level_zero {W : G → ℂ} (hW : W ∈ S)
    (hfix : ∀ k ∈ K1 p 0, ∀ g : G, W (g * k) = W g) (h1 : W 1 = 0) : W = 0 := by
  have hN1 : ∀ s : F, Valued.v s ≤ WithZero.exp (1 : ℤ) → (nU s : G) ∈ stab W :=
    fun s hs => nU_mem_stab_of_apply_one_eq_zero hstab hsm hpsi hirr hadm hW hfix h1 hs
  have hL : ∀ y : F, Valued.v y ≤ 1 → (lowU y : G) ∈ stab W := by
    intro y hy g
    refine hfix _ (lowU_mem_K1 0 ?_) g
    simpa using hy

  set x₀ : F := (unif p)⁻¹ with hx₀
  set y₀ : F := 1 - unif p with hy₀
  have ht : 1 + x₀ * y₀ = (unif p)⁻¹ := by rw [hx₀, hy₀]; field_simp [unif_ne_zero (p := p)]; ring
  have ht0 : 1 + x₀ * y₀ ≠ 0 := by rw [ht]; exact inv_ne_zero unif_ne_zero
  have htdet : (1 + x₀ * y₀) * (1 + x₀ * y₀)⁻¹ - 0 * 0 ≠ 0 := by rw [mul_inv_cancel₀ ht0]; simp
  have hvy₀ : Valued.v y₀ ≤ 1 := by
    rw [hy₀]; exact v_sub_le (by simp) (by rw [v_unif, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
  have hh : (gl2 (1 + x₀ * y₀) 0 0 (1 + x₀ * y₀)⁻¹ htdet : G) ∈ stab W := by
    rw [diag_eq_prod x₀ y₀ ht0 htdet]
    refine (stab W).mul_mem ((stab W).mul_mem ((stab W).mul_mem (hL _ ?_) (hN1 _ ?_)) (hL _ hvy₀)) (hN1 _ ?_)
    · rw [Valuation.map_neg, ht, div_eq_mul_inv, inv_inv, Valuation.map_mul, v_unif]
      calc Valued.v y₀ * WithZero.exp (-1) ≤ 1 * WithZero.exp (-1) := mul_le_mul_left hvy₀ _
        _ ≤ 1 := by rw [one_mul, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
    · rw [hx₀, v_unif_inv]
    · rw [Valuation.map_neg, ht, hx₀, div_self (inv_ne_zero unif_ne_zero), Valuation.map_one,
        ← WithZero.exp_zero, WithZero.exp_le_exp]; omega

  have hscale : ∀ s : F, (nU s : G) ∈ stab W → (nU ((unif p)⁻¹ * (unif p)⁻¹ * s) : G) ∈ stab W := by
    intro s hs
    have := (stab W).mul_mem ((stab W).mul_mem hh hs) ((stab W).inv_mem hh)
    have key : (1 + x₀ * y₀) * s * ((1 + x₀ * y₀)⁻¹)⁻¹ = (unif p)⁻¹ * (unif p)⁻¹ * s := by
      rw [ht, inv_inv]; ring
    rw [diag_mul_nU, mul_assoc, mul_inv_cancel, mul_one, key] at this
    exact this

  have hall : ∀ (m : ℕ) (s : F), Valued.v s ≤ WithZero.exp (1 + 2 * (m : ℤ)) → (nU s : G) ∈ stab W := by
    intro m
    induction m with
    | zero => intro s hs; exact hN1 s (by simpa using hs)
    | succ m ih =>
      intro s hs
      have hs' : Valued.v (unif p * unif p * s) ≤ WithZero.exp (1 + 2 * (m : ℤ)) := by
        rw [Valuation.map_mul, Valuation.map_mul, v_unif, ← WithZero.exp_add]
        calc WithZero.exp (-1 + -1) * Valued.v s ≤ WithZero.exp (-1 + -1) * WithZero.exp (1 + 2 * ((m + 1 : ℕ) : ℤ)) :=
              mul_le_mul_right hs _
          _ = WithZero.exp (1 + 2 * (m : ℤ)) := by rw [← WithZero.exp_add]; congr 1; push_cast; ring
      have := hscale _ (ih _ hs')
      rwa [show (unif p)⁻¹ * (unif p)⁻¹ * (unif p * unif p * s) = s by field_simp [unif_ne_zero (p := p)]] at this
  have hN : ∀ s : F, (nU s : G) ∈ stab W := by
    intro s
    obtain ⟨j, hj⟩ := exists_v_le_exp s
    exact hall j s (hj.trans (WithZero.exp_le_exp.mpr (by omega)))

  refine kirillov hstab hsm hpsi hirr hadm hW fun y => ?_
  exact apply_diagOne_eq_zero_of_nU_mem_stab hpsi hW (j := 1 - WithZero.log (Valued.v (y : F)))
    (fun t _ => hN t) y (by
      have hy' : Valued.v (y : F) ≠ 0 := v_ne_zero y.ne_zero
      conv_rhs => rw [← WithZero.exp_log hy']
      rw [WithZero.exp_lt_exp]; omega)

include hstab hsm hpsi hirr hadm in
theorem main (c : ℕ)
    (hmin : ∀ c' : ℕ, c' < c → ∀ W ∈ S, (∀ k ∈ K1 p c', ∀ g : G, W (g * k) = W g) → W = 0)
    {W : G → ℂ} (hW : W ∈ S) (hW0 : W ≠ 0) (hfix : ∀ k ∈ K1 p c, ∀ g : G, W (g * k) = W g) : W 1 ≠ 0 := by
  intro h1
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    exact hW0 (eq_zero_of_level_zero hstab hsm hpsi hirr hadm hW hfix h1)
  · obtain ⟨c₀, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hc.ne'
    set d : G := AdelicLevel.diagOne (Units.mk0 (unif p) unif_ne_zero) with hd
    set W₃ : G → ℂ := fun g => W (g * d) with hW₃
    have hW₃S : W₃ ∈ S := hstab W hW d
    have hW₃fix : ∀ k ∈ K1 p c₀, ∀ g : G, W₃ (g * k) = W₃ g :=
      descent hstab hsm hpsi hirr hadm hW hfix h1
    have hW₃0 := hmin c₀ (Nat.lt_succ_self c₀) W₃ hW₃S hW₃fix
    apply hW0
    funext g
    have := congrFun hW₃0 (g * d⁻¹)
    simp only [hW₃, inv_mul_cancel_right, Pi.zero_apply] at this
    rw [this, Pi.zero_apply]

end Main
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_whittaker_localLevelOne_centralChar_admissible_principalSeries2_apply_one_ne_zero_of_norm_eq_one_of_higherUnitsAt.PsNvLocal"

end PsNvLocal
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_whittaker_localLevelOne_centralChar_admissible_principalSeries2_apply_one_ne_zero_of_norm_eq_one_of_higherUnitsAt.PsNvLocal"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_whittaker_localLevelOne_centralChar_admissible_principalSeries2_apply_one_ne_zero_of_norm_eq_one_of_higherUnitsAt.PsNvLocal"

noncomputable section

namespace PsNvMain

open IsDedekindDomain NumberField UnramifiedWhittaker
open scoped WithZero

variable {p : HeightOneSpectrum (𝓞 ℚ)}

local notation "F" => HeightOneSpectrum.adicCompletion ℚ p
local notation "O" => HeightOneSpectrum.adicCompletionIntegers ℚ p
local notation "Mat" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)

section Cyclic

variable {H : Type*} [Group H]

abbrev cyc (w : H → ℂ) : Submodule ℂ (H → ℂ) :=
  Submodule.span ℂ (Set.range fun h : H => fun g : H => w (g * h))

theorem gen_mem (w : H → ℂ) (h : H) : (fun g : H => w (g * h)) ∈ cyc w :=
  Submodule.subset_span ⟨h, rfl⟩

theorem self_mem (w : H → ℂ) : w ∈ cyc w := by
  have := gen_mem w 1
  simpa only [mul_one] using this

theorem translate_mem (w : H → ℂ) {f : H → ℂ} (hf : f ∈ cyc w) (k : H) :
    (fun g : H => f (g * k)) ∈ cyc w := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    simpa only [mul_assoc] using gen_mem w (k * h)
  | zero => exact (cyc w).zero_mem
  | add x y _ _ hx hy => exact (cyc w).add_mem hx hy
  | smul a x _ hx => exact (cyc w).smul_mem a hx

theorem cyc_le_of_mem (w : H → ℂ) {f : H → ℂ} (hf : f ∈ cyc w) : cyc f ≤ cyc w := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨h, rfl⟩
  exact translate_mem w hf h

theorem leftLaw_of_mem (w : H → ℂ) (a : H) (c : ℂ) (hlaw : ∀ g : H, w (a * g) = c * w g)
    {f : H → ℂ} (hf : f ∈ cyc w) : ∀ g : H, f (a * g) = c * f g := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    intro g
    simp only [mul_assoc, hlaw]
  | zero => intro g; simp
  | add x y _ _ hx hy => intro g; simp only [Pi.add_apply, hx g, hy g, mul_add]
  | smul r x _ hx => intro g; simp only [Pi.smul_apply, hx g, smul_eq_mul]; ring

end Cyclic
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_whittaker_localLevelOne_centralChar_admissible_principalSeries2_apply_one_ne_zero_of_norm_eq_one_of_higherUnitsAt.PsNvLocal"

section CyclicTop

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

theorem smooth_of_mem (w : H → ℂ) (U : Subgroup H) (hU : IsOpen (U : Set H))
    (hwU : ∀ k ∈ U, ∀ g : H, w (g * k) = w g) {f : H → ℂ} (hf : f ∈ cyc w) :
    ∃ K' : Subgroup H, IsOpen (K' : Set H) ∧ ∀ k ∈ K', (fun g : H => f (g * k)) = f := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    refine ⟨U.comap (MulAut.conj h⁻¹).toMonoidHom, ?_, ?_⟩
    · rw [Subgroup.coe_comap]
      refine hU.preimage ?_
      change Continuous fun k : H => h⁻¹ * k * h⁻¹⁻¹
      fun_prop
    · intro k hk
      rw [Subgroup.mem_comap] at hk
      change h⁻¹ * k * h⁻¹⁻¹ ∈ U at hk
      rw [inv_inv] at hk
      funext g
      have := hwU _ hk (g * h)
      rw [show g * h * (h⁻¹ * k * h) = g * k * h by group] at this
      exact this
  | zero => exact ⟨⊤, by rw [Subgroup.coe_top]; exact isOpen_univ, fun k _ => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨K₁, hK₁, h₁⟩ := hx
    obtain ⟨K₂, hK₂, h₂⟩ := hy
    refine ⟨K₁ ⊓ K₂, by rw [Subgroup.coe_inf]; exact hK₁.inter hK₂, fun k hk => ?_⟩
    funext g
    have e₁ := congrFun (h₁ k hk.1) g
    have e₂ := congrFun (h₂ k hk.2) g
    simp only [Pi.add_apply] at e₁ e₂ ⊢
    rw [e₁, e₂]
  | smul r x _ hx =>
    obtain ⟨K₁, hK₁, h₁⟩ := hx
    refine ⟨K₁, hK₁, fun k hk => ?_⟩
    funext g
    have e₁ := congrFun (h₁ k hk) g
    simp only [Pi.smul_apply] at e₁ ⊢
    rw [e₁]

theorem continuous_of_rightInvariant (f : H → ℂ) (U : Subgroup H) (hU : IsOpen (U : Set H))
    (hf : ∀ k ∈ U, ∀ g : H, f (g * k) = f g) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hmem : {y : H | x⁻¹ * y ∈ (U : Set H)} ∈ nhds x :=
    (hU.preimage (continuous_mul_left x⁻¹)).mem_nhds (by simp [U.one_mem])
  refine (continuousAt_const : ContinuousAt (fun _ : H => f x) x).congr_of_eventuallyEq ?_
  refine Filter.mem_of_superset hmem fun y hy => ?_
  have := hf _ hy x
  rw [mul_inv_cancel_left] at this
  exact this

end CyclicTop
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_whittaker_localLevelOne_centralChar_admissible_principalSeries2_apply_one_ne_zero_of_norm_eq_one_of_higherUnitsAt.PsNvLocal"

section Growth

variable {H : Type*} [Group H]

def GrAt (Np : ℝ) (Kset : Set H) (d : ℤ → H) (f : H → ℂ) (h : H) : Prop :=
  ∃ C A : ℝ, ∀ m : ℤ, 0 ≤ m → ∀ k ∈ Kset, ‖f (d m * k * h)‖ ≤ C * Np ^ (A * m)

variable {Np : ℝ} (hNp : 1 ≤ Np) {Kset : Set H} {d : ℤ → H}

include hNp in

theorem GrAt.nonneg {f : H → ℂ} {h : H} (hf : GrAt Np Kset d f h) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ m : ℤ, 0 ≤ m → ∀ k ∈ Kset, ‖f (d m * k * h)‖ ≤ C * Np ^ (A * m) := by
  obtain ⟨C, A, hCA⟩ := hf
  refine ⟨max C 0, max A 0, le_max_right _ _, le_max_right _ _, fun m hm k hk => ?_⟩
  have hm' : (0 : ℝ) ≤ m := by exact_mod_cast hm
  calc ‖f (d m * k * h)‖ ≤ C * Np ^ (A * m) := hCA m hm k hk
    _ ≤ max C 0 * Np ^ (A * m) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)
    _ ≤ max C 0 * Np ^ (max A 0 * m) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hNp (mul_le_mul_of_nonneg_right (le_max_left _ _) hm'))
          (le_max_right _ _)

include hNp in
theorem grAt_add {f g : H → ℂ} {h : H} (hf : GrAt Np Kset d f h) (hg : GrAt Np Kset d g h) :
    GrAt Np Kset d (f + g) h := by
  obtain ⟨C₁, A₁, hC₁, hA₁, h₁⟩ := hf.nonneg hNp
  obtain ⟨C₂, A₂, hC₂, hA₂, h₂⟩ := hg.nonneg hNp
  refine ⟨C₁ + C₂, A₁ + A₂, fun m hm k hk => ?_⟩
  have hm' : (0 : ℝ) ≤ m := by exact_mod_cast hm
  have hpow₁ : Np ^ (A₁ * m) ≤ Np ^ ((A₁ + A₂) * m) :=
    Real.rpow_le_rpow_of_exponent_le hNp (by nlinarith)
  have hpow₂ : Np ^ (A₂ * m) ≤ Np ^ ((A₁ + A₂) * m) :=
    Real.rpow_le_rpow_of_exponent_le hNp (by nlinarith)
  calc ‖(f + g) (d m * k * h)‖ ≤ ‖f (d m * k * h)‖ + ‖g (d m * k * h)‖ := norm_add_le _ _
    _ ≤ C₁ * Np ^ (A₁ * m) + C₂ * Np ^ (A₂ * m) := add_le_add (h₁ m hm k hk) (h₂ m hm k hk)
    _ ≤ C₁ * Np ^ ((A₁ + A₂) * m) + C₂ * Np ^ ((A₁ + A₂) * m) :=
        add_le_add (mul_le_mul_of_nonneg_left hpow₁ hC₁) (mul_le_mul_of_nonneg_left hpow₂ hC₂)
    _ = (C₁ + C₂) * Np ^ ((A₁ + A₂) * m) := by ring

theorem grAt_smul {f : H → ℂ} {h : H} (hf : GrAt Np Kset d f h) (r : ℂ) : GrAt Np Kset d (r • f) h := by
  obtain ⟨C, A, hCA⟩ := hf
  refine ⟨‖r‖ * C, A, fun m hm k hk => ?_⟩
  calc ‖(r • f) (d m * k * h)‖ = ‖r‖ * ‖f (d m * k * h)‖ := by
        rw [Pi.smul_apply, smul_eq_mul]; exact Complex.norm_mul r _
    _ ≤ ‖r‖ * (C * Np ^ (A * m)) := mul_le_mul_of_nonneg_left (hCA m hm k hk) (norm_nonneg _)
    _ = ‖r‖ * C * Np ^ (A * m) := by ring

theorem grAt_zero (h : H) : GrAt Np Kset d (0 : H → ℂ) h :=
  ⟨0, 0, fun m _ k _ => by simp⟩

theorem grAt_translate {f : H → ℂ} {h h₀ : H} (hf : GrAt Np Kset d f (h * h₀)) :
    GrAt Np Kset d (fun g : H => f (g * h₀)) h := by
  obtain ⟨C, A, hCA⟩ := hf
  refine ⟨C, A, fun m hm k hk => ?_⟩
  have := hCA m hm k hk
  show ‖f (d m * k * h * h₀)‖ ≤ _
  rwa [← mul_assoc] at this

include hNp in

theorem grAt_of_mem (w : H → ℂ) (hw : ∀ h : H, GrAt Np Kset d w h) {f : H → ℂ} (hf : f ∈ cyc w) :
    ∀ h : H, GrAt Np Kset d f h := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h₀, rfl⟩ := hx
    intro h
    exact grAt_translate (hw (h * h₀))
  | zero => intro h; exact grAt_zero h
  | add x y _ _ hx hy => intro h; exact grAt_add hNp (hx h) (hy h)
  | smul r x _ hx => intro h; exact grAt_smul (hx h) r

end Growth
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_whittaker_localLevelOne_centralChar_admissible_principalSeries2_apply_one_ne_zero_of_norm_eq_one_of_higherUnitsAt.PsNvLocal"

theorem idealBound_eq_idealBound_pow {N : Ideal (𝓞 ℚ)} {b : ℕ}
    (hNb : p.asIdeal ^ b ∣ N ∧ ¬ p.asIdeal ^ (b + 1) ∣ N) :
    AdelicLevel.idealBound (𝓞 ℚ) N p = AdelicLevel.idealBound (𝓞 ℚ) (p.asIdeal ^ b) p := by
  classical
  have hN : N ≠ ⊥ := by
    rintro rfl
    exact hNb.2 (dvd_zero _)
  have hN0 : Associates.mk N ≠ 0 := Associates.mk_ne_zero.mpr hN
  have hirr : Irreducible (Associates.mk p.asIdeal) := Associates.irreducible_mk.mpr p.irreducible
  have hcount : (Associates.mk p.asIdeal).count (Associates.mk N).factors = b := by
    refine le_antisymm (not_lt.mp fun hlt => hNb.2 ?_) ?_
    · rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow, Associates.prime_pow_dvd_iff_le hN0 hirr]
      exact hlt
    · rw [← Associates.prime_pow_dvd_iff_le hN0 hirr, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd]
      exact hNb.1
  rw [AdelicLevel.idealBound_of_ne_bot (pow_ne_zero b p.ne_bot), Associates.mk_pow,
    Associates.count_pow (Associates.mk_ne_zero.mpr p.ne_bot) hirr, Associates.count_self hirr, mul_one,
    AdelicLevel.idealBound_of_ne_bot hN, hcount]

theorem localLevelOne_eq_localLevelOne_pow {N : Ideal (𝓞 ℚ)} {b : ℕ}
    (hNb : p.asIdeal ^ b ∣ N ∧ ¬ p.asIdeal ^ (b + 1) ∣ N) :
    AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N = PsNvLocal.K1 p b := by
  have h := idealBound_eq_idealBound_pow hNb
  have hiff : ∀ m : Mat,
      AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p N m ↔ AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) m := fun m =>
    ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h ▸ h2, h ▸ h3⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h.symm ▸ h2, h.symm ▸ h3⟩⟩
  ext k
  rw [AdelicDock.mem_localLevelOne_iff, AdelicDock.mem_localLevelOne_iff, hiff, hiff]

theorem K1_le_K1 {c b : ℕ} (hcb : c ≤ b) : PsNvLocal.K1 p b ≤ PsNvLocal.K1 p c := by
  intro k hk
  rw [PsNvLocal.mem_K1_iff] at hk ⊢
  have hle : WithZero.exp (-(b : ℤ)) ≤ WithZero.exp (-(c : ℤ)) := by
    rw [WithZero.exp_le_exp]; omega
  have key : ∀ m : Mat, PsNvLocal.IsK1 b m → PsNvLocal.IsK1 c m := fun m hm =>
    ⟨hm.integral, hm.lowerLeft.trans hle, hm.lowerRight.trans hle⟩
  exact ⟨key _ hk.1, key _ hk.2⟩

theorem localLevelOne_top_eq_K1_zero :
    AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ = PsNvLocal.K1 p 0 := by
  rw [PsNvLocal.K1, pow_zero, Ideal.one_eq_top]

theorem unipotent_eq (x : F) : (UnramifiedWhittaker.unipotent x : G) = AutomorphicForm.unipotentGL2 x :=
  Units.ext rfl

theorem diagZ_eq_diagOne (π : F) (hπ : π ≠ 0) (m : ℤ) :
    (diagZ π hπ m : G) = AdelicLevel.diagOne ((Units.mk0 π hπ) ^ m) := by
  refine Units.ext ?_
  change (!![π ^ m, 0; 0, 1] : Mat) = _
  ext i j
  rw [AdelicLevel.diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp

section Transport

def diagU (a b : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : G where
  val := !![(a : F), 0; 0, (b : F)]
  inv := !![((a⁻¹ : Fˣ) : F), 0; 0, ((b⁻¹ : Fˣ) : F)]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] theorem coe_diagU (a b : Fˣ) : ((diagU a b : G) : Mat) = !![(a : F), 0; 0, (b : F)] := rfl

theorem diagU_inv (a b : Fˣ) : (diagU a b)⁻¹ = diagU a⁻¹ b⁻¹ := by
  refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
  change ((diagU a b : G) : Mat) * ((diagU a⁻¹ b⁻¹ : G) : Mat) = 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] theorem coe_diagZ (π : F) (hπ : π ≠ 0) (m : ℤ) : ((diagZ π hπ m : G) : Mat) = !![π ^ m, 0; 0, 1] := rfl

@[scoped simp] theorem coe_unipotent (x : F) : ((UnramifiedWhittaker.unipotent x : G) : Mat) = !![1, x; 0, 1] := rfl

@[scoped simp] theorem coe_scalar (z : Fˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) z : G) : Mat) = !![(z : F), 0; 0, (z : F)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.one_apply]

theorem gl_ext {g h : G} (hgh : (g : Mat) = (h : Mat)) : g = h := Units.ext hgh

theorem mem_kzero_iff (k : G) :
    k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ ↔
      (∀ i j, (k : Mat) i j ∈ (O)) ∧ ∀ i j, ((k⁻¹ : G) : Mat) i j ∈ (O) := by
  have key : ∀ m : Mat, (∀ i j, m i j ∈ (O)) → AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p ⊤ m := by
    intro m h
    refine ⟨h, ?_, ?_⟩
    · rw [AdelicLevel.idealBound_top]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 0)
    · rw [AdelicLevel.idealBound_top]
      calc Valued.v (m 1 1 - 1) ≤ max (Valued.v (m 1 1)) (Valued.v (1 : F)) := Valuation.map_sub _ _ _
        _ ≤ 1 := max_le ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 1)) (by simp)
  rw [AdelicDock.mem_localLevelOne_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1.integral, h2.integral⟩
  · rintro ⟨h1, h2⟩; exact ⟨key _ h1, key _ h2⟩

theorem coe_kzero_eq_localIntegralSet :
    ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup G) : Set G) = AutomorphicForm.localIntegralSet ℚ p := by
  ext k
  rw [SetLike.mem_coe, mem_kzero_iff, AutomorphicForm.mem_localIntegralSet]

theorem isCompact_kzero : IsCompact ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup G) : Set G) := by
  rw [coe_kzero_eq_localIntegralSet]; exact AutomorphicForm.isCompact_localIntegralSet ℚ p

theorem isOpen_kzero : IsOpen ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup G) : Set G) := by
  rw [coe_kzero_eq_localIntegralSet]; exact AutomorphicForm.isOpen_localIntegralSet ℚ p

theorem mem_kzero_of_mem_integralSubgroup {k : G}
    (hk : k ∈ LocalGL2.integralSubgroup (HeightOneSpectrum.adicCompletionIntegers ℚ p)
      (HeightOneSpectrum.adicCompletion ℚ p)) : k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
  rw [mem_kzero_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · obtain ⟨r, hr⟩ := LocalGL2.exists_entry_eq_of_mem_integralSubgroup hk i j
    rw [← hr]; exact r.2
  · obtain ⟨r, hr⟩ := LocalGL2.exists_entry_eq_of_mem_integralSubgroup (inv_mem hk) i j
    rw [← hr]; exact r.2

theorem diagU_mem_kzero {a b : Fˣ} (ha : Valued.v (a : F) = 1) (hb : Valued.v (b : F) = 1) :
    diagU a b ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
  have key : ∀ c d : Fˣ, Valued.v (c : F) = 1 → Valued.v (d : F) = 1 →
      ∀ i j, ((diagU c d : G) : Mat) i j ∈ (O) := by
    intro c d hc hd i j
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, coe_diagU]
    fin_cases i <;> fin_cases j <;> simp [hc, hd]
  rw [mem_kzero_iff]
  refine ⟨key a b ha hb, ?_⟩
  rw [diagU_inv]
  refine key a⁻¹ b⁻¹ ?_ ?_
  · rw [Units.val_inv_eq_inv_val, map_inv₀, ha, inv_one]
  · rw [Units.val_inv_eq_inv_val, map_inv₀, hb, inv_one]

variable (π : HeightOneSpectrum.adicCompletion ℚ p) (hπ : π ≠ 0)
  (hϖ : Valued.v π = WithZero.exp (-1 : ℤ))

include hϖ in
theorem v_pi_zpow (k : ℤ) : Valued.v (((Units.mk0 π hπ) ^ k : Fˣ) : F) = WithZero.exp (-k) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, Units.val_mk0, hϖ, ← WithZero.exp_zsmul, smul_neg, zsmul_one,
    Int.cast_id]

include hϖ in

theorem exists_eq_pi_zpow_mul (u : Fˣ) :
    ∃ (m : ℤ) (w : Fˣ), Valued.v (w : F) = 1 ∧ u = (Units.mk0 π hπ) ^ m * w := by
  have hu : Valued.v (u : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr u.ne_zero
  set e : ℤ := WithZero.log (Valued.v (u : F)) with he
  refine ⟨-e, (Units.mk0 π hπ) ^ e * u, ?_, ?_⟩
  · rw [Units.val_mul, map_mul, v_pi_zpow π hπ hϖ, ← WithZero.exp_log hu, ← he, ← WithZero.exp_add,
      neg_add_cancel, WithZero.exp_zero]
  · rw [← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]

theorem diagZ_mul_unipotent (m : ℤ) (z : F) :
    (diagZ π hπ m : G) * UnramifiedWhittaker.unipotent z = UnramifiedWhittaker.unipotent (π ^ m * z) * diagZ π hπ m := by
  apply gl_ext
  simp only [Units.val_mul, coe_diagZ, coe_unipotent]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagZ_mul_scalar (m : ℤ) (a : Fˣ) :
    (diagZ π hπ m : G) * Matrix.GeneralLinearGroup.scalar (Fin 2) a =
      Matrix.GeneralLinearGroup.scalar (Fin 2) a * diagZ π hπ m := by
  apply gl_ext
  simp only [Units.val_mul, coe_diagZ, coe_scalar]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem diagZ_mul_diagZ (m e : ℤ) : (diagZ π hπ m : G) * diagZ π hπ e = diagZ π hπ (m + e) := by
  apply gl_ext
  simp only [Units.val_mul, coe_diagZ]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, zpow_add₀ hπ]

theorem exists_iwasawa_pi (hϖ : Valued.v π = WithZero.exp (-1 : ℤ)) (x : G) :
    ∃ (z : F) (a₂ : Fˣ) (e : ℤ) (u : Fˣ) (k₀ : G), Valued.v (u : F) = 1 ∧
      k₀ ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ ∧
      x = UnramifiedWhittaker.unipotent z * Matrix.GeneralLinearGroup.scalar (Fin 2) a₂ * diagZ π hπ e *
        diagU u 1 * k₀ := by
  obtain ⟨z, a₁, a₂, k₀, hk₀, hx⟩ :=
    LocalGL2.iwasawa_decomposition_diag (HeightOneSpectrum.adicCompletionIntegers ℚ p)
      (HeightOneSpectrum.adicCompletion ℚ p) x
  obtain ⟨e, u, hu, hau⟩ := exists_eq_pi_zpow_mul π hπ hϖ (a₁ * a₂⁻¹)
  refine ⟨z, a₂, e, u, k₀, hu, mem_kzero_of_mem_integralSubgroup hk₀, ?_⟩
  have hrel : (a₁ : F) = (a₂ : F) * (π ^ e * (u : F)) := by
    have := congrArg (fun t : Fˣ => (t : F)) hau
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0] at this
    rw [← this, Units.val_inv_eq_inv_val]
    field_simp
  rw [hrel] at hx
  have hM : (!![1, z; 0, 1] * !![(a₂ : F) * (π ^ e * (u : F)), 0; 0, (a₂ : F)] : Mat) =
      ((UnramifiedWhittaker.unipotent z * Matrix.GeneralLinearGroup.scalar (Fin 2) a₂ * diagZ π hπ e *
        diagU u 1 : G) : Mat) := by
    simp only [Units.val_mul, coe_unipotent, coe_scalar, coe_diagZ, coe_diagU, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  apply gl_ext
  rw [hx, hM]
  simp only [Units.val_mul]

end Transport
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_whittaker_localLevelOne_centralChar_admissible_principalSeries2_apply_one_ne_zero_of_norm_eq_one_of_higherUnitsAt.PsNvLocal"

theorem norm_psiLocal (y : F) : ‖NumberField.StandardAddChar.psiLocal ℚ p y‖ = 1 := by
  set ψ := NumberField.StandardAddChar.psiLocal ℚ p with hψdef

  obtain ⟨j, hj⟩ := PsNvLocal.exists_v_le_exp y
  set n : ℕ := (Rat.HeightOneSpectrum.natGenerator p : ℕ) ^ j with hn
  have hcast : ((n : ℕ) : F) = PsNvLocal.unif p ^ j := by
    rw [hn, Nat.cast_pow, PsNvLocal.unif, map_natCast]
  have hn0 : n ≠ 0 := by
    intro h0
    have : (PsNvLocal.unif p : F) ^ j = 0 := by rw [← hcast, h0, Nat.cast_zero]
    exact pow_ne_zero j PsNvLocal.unif_ne_zero this
  have hint : Valued.v ((n : F) * y) ≤ 1 := by
    rw [hcast, map_mul, PsNvLocal.v_unif_pow]
    calc WithZero.exp (-(j : ℤ)) * Valued.v y ≤ WithZero.exp (-(j : ℤ)) * WithZero.exp (j : ℤ) :=
          mul_le_mul_right hj _
      _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
  have hone : ψ y ^ n = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, hψdef, NumberField.StandardAddChar.psiLocal_rat_eq_psiV]
    exact NumberField.StandardAddChar.psiV_eq_one_of_mem_integers p
      ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hint)
  have := congrArg norm hone
  rw [norm_pow, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn0).mp this

section TransportMain

variable (π : HeightOneSpectrum.adicCompletion ℚ p) (hπ : π ≠ 0)
  (hϖ : Valued.v π = WithZero.exp (-1 : ℤ))
  (w : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p) → ℂ)
  (hlaw : ∀ (x : HeightOneSpectrum.adicCompletion ℚ p) (g : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)),
    w (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g)
  (θc : (HeightOneSpectrum.adicCompletion ℚ p)ˣ → ℂ) (hθc : ∀ z : (HeightOneSpectrum.adicCompletion ℚ p)ˣ, ‖θc z‖ = 1)
  (hcent : ∀ (z : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) (g : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p)),
    w (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = θc z * w g)
  (hcont : Continuous w)
  (Np : ℝ) (hNp : 1 ≤ Np)
  (C₀ A₀ : ℝ) (hC₀ : 0 ≤ C₀) (hA₀ : 0 ≤ A₀)
  (hgr : ∀ m : ℤ, 0 ≤ m → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ‖w (diagZ π hπ m * k)‖ ≤ C₀ * Np ^ (A₀ * m))

include hϖ hlaw hθc hcent hcont hNp hC₀ hA₀ hgr in

theorem growth_rep (x : G) :
    ∃ Cx : ℝ, 0 ≤ Cx ∧ ∀ m : ℤ, 0 ≤ m → ∀ κ ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
      ‖w (diagZ π hπ m * (x * κ))‖ ≤ Cx * Np ^ (A₀ * m) := by
  obtain ⟨z, a₂, e, u, k₀, hu, hk₀, hx⟩ := exists_iwasawa_pi π hπ hϖ x
  have hNp0 : 0 < Np := by linarith

  set 𝒦 : Set G := ⋃ j ∈ Finset.Ico e 0, (fun κ : G => diagZ π hπ j * κ) ''
    ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup G) : Set G) with h𝒦
  have h𝒦c : IsCompact 𝒦 :=
    (Finset.Ico e 0).isCompact_biUnion fun j _ => isCompact_kzero.image (continuous_mul_left _)
  obtain ⟨B, hB⟩ := h𝒦c.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨C₀ * Np ^ (A₀ * e) + max B 0, by positivity, fun m hm κ hκ => ?_⟩

  set κ' : G := diagU u 1 * k₀ * κ with hκ'
  have hκ'K : κ' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ :=
    mul_mem (mul_mem (diagU_mem_kzero hu (by simp)) hk₀) hκ
  have hid : diagZ π hπ m * (x * κ) =
      UnramifiedWhittaker.unipotent (π ^ m * z) *
        (Matrix.GeneralLinearGroup.scalar (Fin 2) a₂ * (diagZ π hπ (m + e) * κ')) := by
    rw [hx, hκ', ← diagZ_mul_diagZ π hπ m e]
    simp only [← mul_assoc]
    rw [diagZ_mul_unipotent, mul_assoc (UnramifiedWhittaker.unipotent (π ^ m * z)), diagZ_mul_scalar,
      ← mul_assoc]
  have hval : ‖w (diagZ π hπ m * (x * κ))‖ = ‖w (diagZ π hπ (m + e) * κ')‖ := by
    rw [hid, hlaw, hcent, norm_mul, norm_mul, norm_psiLocal, hθc, one_mul, one_mul]
  rw [hval]
  have hm' : (0 : ℝ) ≤ m := by exact_mod_cast hm
  have hpow1 : 1 ≤ Np ^ (A₀ * m) := Real.one_le_rpow hNp (by positivity)
  by_cases hme : 0 ≤ m + e
  · have h1 := hgr (m + e) hme κ' hκ'K
    have hsplit : Np ^ (A₀ * ((m + e : ℤ) : ℝ)) = Np ^ (A₀ * m) * Np ^ (A₀ * e) := by
      rw [Int.cast_add, mul_add, Real.rpow_add hNp0]
    calc ‖w (diagZ π hπ (m + e) * κ')‖ ≤ C₀ * Np ^ (A₀ * ((m + e : ℤ) : ℝ)) := h1
      _ = C₀ * Np ^ (A₀ * e) * Np ^ (A₀ * m) := by rw [hsplit]; ring
      _ ≤ (C₀ * Np ^ (A₀ * e) + max B 0) * Np ^ (A₀ * m) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (le_max_right _ _)) (by positivity)
  · have hmem : diagZ π hπ (m + e) * κ' ∈ 𝒦 := by
      rw [h𝒦]
      refine Set.mem_iUnion₂.2 ⟨m + e, ?_, ⟨κ', hκ'K, rfl⟩⟩
      rw [Finset.mem_Ico]
      omega
    calc ‖w (diagZ π hπ (m + e) * κ')‖ ≤ B := hB _ hmem
      _ ≤ max B 0 := le_max_left _ _
      _ ≤ max B 0 * Np ^ (A₀ * m) := le_mul_of_one_le_right (le_max_right _ _) hpow1
      _ ≤ (C₀ * Np ^ (A₀ * e) + max B 0) * Np ^ (A₀ * m) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (by positivity)

include hϖ hlaw hθc hcent hcont hNp hC₀ hA₀ hgr in

theorem growth_translate (h : G) :
    GrAt Np ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup G) : Set G) (fun m => diagZ π hπ m) w h := by
  classical
  set Kset : Set G := ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup G) : Set G) with hKset

  have hT : IsCompact ((fun k : G => k * h) '' Kset) := isCompact_kzero.image (continuous_mul_right _)
  have hUo : ∀ x : G, IsOpen {y : G | x⁻¹ * y ∈ Kset} := fun x =>
    isOpen_kzero.preimage (continuous_mul_left x⁻¹)
  have hcov : (fun k : G => k * h) '' Kset ⊆ ⋃ x : G, {y : G | x⁻¹ * y ∈ Kset} := by
    intro y _
    exact Set.mem_iUnion.2 ⟨y, by simp [hKset, Subgroup.one_mem]⟩
  obtain ⟨t, ht⟩ := hT.elim_finite_subcover _ hUo hcov
  choose Cx hCx0 hCx using growth_rep π hπ hϖ w hlaw θc hθc hcent hcont Np hNp C₀ A₀ hC₀ hA₀ hgr
  refine ⟨∑ x ∈ t, Cx x, A₀, fun m hm k hk => ?_⟩
  have hkh : k * h ∈ (fun k : G => k * h) '' Kset := ⟨k, hk, rfl⟩
  obtain ⟨x, hxt, hx⟩ : ∃ x ∈ t, x⁻¹ * (k * h) ∈ Kset := by
    have := ht hkh
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at this
    exact this
  have heq : diagZ π hπ m * k * h = diagZ π hπ m * (x * (x⁻¹ * (k * h))) := by
    rw [mul_inv_cancel_left, mul_assoc]
  rw [heq]
  calc ‖w (diagZ π hπ m * (x * (x⁻¹ * (k * h))))‖ ≤ Cx x * Np ^ (A₀ * m) := hCx x m hm _ hx
    _ ≤ (∑ x ∈ t, Cx x) * Np ^ (A₀ * m) :=
        mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _ => hCx0 i) hxt)
          (Real.rpow_nonneg (by linarith) _)

end TransportMain
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_whittaker_localLevelOne_centralChar_admissible_principalSeries2_apply_one_ne_zero_of_norm_eq_one_of_higherUnitsAt.PsNvLocal"

end PsNvMain
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_whittaker_localLevelOne_centralChar_admissible_principalSeries2_apply_one_ne_zero_of_norm_eq_one_of_higherUnitsAt.PsNvLocal P2MW.S_LanglandsTunnell_CubicInduction_exists_whittaker_localLevelOne_centralChar_admissible_principalSeries2_apply_one_ne_zero_of_norm_eq_one_of_higherUnitsAt.PsNvMain"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_whittaker_localLevelOne_centralChar_admissible_principalSeries2_apply_one_ne_zero_of_norm_eq_one_of_higherUnitsAt.PsNvLocal P2MW.S_LanglandsTunnell_CubicInduction_exists_whittaker_localLevelOne_centralChar_admissible_principalSeries2_apply_one_ne_zero_of_norm_eq_one_of_higherUnitsAt.PsNvMain"

open IsDedekindDomain NumberField UnramifiedWhittaker LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (θ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (hθu : ∀ (i : Fin 2) (z : (p.adicCompletion ℚ)ˣ), ‖((θ i z : ℂˣ) : ℂ)‖ = 1)
    (c : Fin 2 → ℕ)
    (hcθ : ∀ i : Fin 2, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (c i), θ i u = 1)
    (N : Ideal (𝓞 ℚ)) (_hN : N ≠ ⊥) (b : ℕ)
    (hNb : p.asIdeal ^ b ∣ N ∧ ¬ p.asIdeal ^ (b + 1) ∣ N)
    (hcb : c 0 + c 1 ≤ b)
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (_hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ)) :
    ∃ w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ,
      (∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g) ∧
      (∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) ∧
      w ≠ 0 ∧
      w 1 ≠ 0 ∧
      (∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)),
        w' ≠ 0 → w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w' (g * h))) ∧
      (∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
        ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
          ∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)),
            (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w' (g * k) = w' g) →
              w' ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))) ∧
      (∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        w (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ 0 z * θ 1 z : ℂˣ) : ℂ) * w g) ∧
      (∃ Φ : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        (∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)), ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
          Φ (fun g => w' (g * h)) = fun g => Φ w' (g * h)) ∧
        (∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)), Φ w' = 0 → w' = 0) ∧
        (∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)), Φ w' ∈ principalSeries2 p θ)) ∧
      (∃ (C A : ℝ), ∀ (m : ℤ), 0 ≤ m → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
        ‖w (UnramifiedWhittaker.diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m * k)‖ ≤
          C * (Ideal.absNorm p.asIdeal : ℝ) ^ (A * m)) := by
  classical

  obtain ⟨w₀, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    LanglandsTunnell.CubicInduction.exists_whittaker_localLevelOne_centralChar_admissible_principalSeries2_of_norm_eq_one_of_higherUnitsAt
      p θ hθu c hcθ N _hN b hNb hcb hπ _hϖ

  set S : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) := PsNvMain.cyc w₀ with hSdef
  have hK1N : AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N = PsNvLocal.K1 p b :=
    PsNvMain.localLevelOne_eq_localLevelOne_pow hNb
  have hK1Nopen : IsOpen ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) :
      Set (GL (Fin 2) (p.adicCompletion ℚ))) :=
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N _hN).2

  have hstab : ∀ W ∈ S, ∀ k : GL (Fin 2) (p.adicCompletion ℚ), (fun g => W (g * k)) ∈ S :=
    fun W hW k => PsNvMain.translate_mem w₀ hW k
  have hsm : ∀ W ∈ S, ∃ K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)),
      IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ K, (fun g => W (g * k)) = W :=
    fun W hW => PsNvMain.smooth_of_mem w₀ _ hK1Nopen h2 hW
  have hpsi : ∀ W ∈ S, ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      W (AutomorphicForm.unipotentGL2 x * g) = NumberField.StandardAddChar.psiV p x * W g := by
    intro W hW x g
    rw [← PsNvMain.unipotent_eq, ← NumberField.StandardAddChar.psiLocal_rat_eq_psiV]
    exact PsNvMain.leftLaw_of_mem w₀ (unipotent x) _ (h1 x) hW g
  have hirr : ∀ T : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), T ≤ S →
      (∀ W ∈ T, ∀ k : GL (Fin 2) (p.adicCompletion ℚ), (fun g => W (g * k)) ∈ T) → T = ⊥ ∨ T = S := by
    intro T hTS hTstab
    by_cases hT : T = ⊥
    · exact Or.inl hT
    · right
      refine le_antisymm hTS ?_
      obtain ⟨w', hw'T, hw'0⟩ := (Submodule.ne_bot_iff T).1 hT
      have hw₀ : w₀ ∈ PsNvMain.cyc w' := h4 w' (hTS hw'T) hw'0
      have hcycT : PsNvMain.cyc w' ≤ T :=
        Submodule.span_le.2 (by rintro _ ⟨h, rfl⟩; exact hTstab w' hw'T h)
      exact ((PsNvMain.cyc_le_of_mem w' hw₀).trans hcycT)
  have hadm : ∀ K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)),
      IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∀ T : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), T ≤ S →
        (∀ W ∈ T, ∀ k ∈ K, (fun g => W (g * k)) = W) → FiniteDimensional ℂ T := by
    intro K hK T hTS hTfix
    obtain ⟨B, hB⟩ := h5 K hK
    have hle : T ≤ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)) :=
      fun W hW => hB W (hTS hW) fun k hk g => congrFun (hTfix W hW k hk) g
    exact Submodule.finiteDimensional_of_le hle

  have hex : ∃ c₀ : ℕ, ∃ W ∈ S, W ≠ 0 ∧ ∀ k ∈ PsNvLocal.K1 p c₀, ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
      W (g * k) = W g :=
    ⟨b, w₀, PsNvMain.self_mem w₀, h3, fun k hk => h2 k (by rw [hK1N]; exact hk)⟩
  obtain ⟨W, hWS, hW0, hWfix⟩ := Nat.find_spec hex
  have hc₀b : Nat.find hex ≤ b :=
    Nat.find_min' hex ⟨w₀, PsNvMain.self_mem w₀, h3, fun k hk => h2 k (by rw [hK1N]; exact hk)⟩
  have hmin : ∀ c' : ℕ, c' < Nat.find hex → ∀ W' ∈ S,
      (∀ k ∈ PsNvLocal.K1 p c', ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W' (g * k) = W' g) → W' = 0 := by
    intro c' hc' W' hW'S hfix'
    by_contra hne
    exact Nat.find_min hex hc' ⟨W', hW'S, hne, hfix'⟩

  have hW1 : W 1 ≠ 0 := PsNvLocal.main hstab hsm hpsi hirr hadm (Nat.find hex) hmin hWS hW0 hWfix
  have hWK1N : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
      W (g * k) = W g := by
    intro k hk
    rw [hK1N] at hk
    exact hWfix k (PsNvMain.K1_le_K1 hc₀b hk)
  have hcycW : PsNvMain.cyc W ≤ S := PsNvMain.cyc_le_of_mem w₀ hWS
  refine ⟨W, ?_, hWK1N, ?_, hW1, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x g
    exact PsNvMain.leftLaw_of_mem w₀ (unipotent x) _ (h1 x) hWS g
  ·
    intro hW
    exact hW1 (by rw [hW]; rfl)
  ·
    intro w' hw' hw'0
    have hw'S : w' ∈ S := hcycW hw'
    have hw₀ : w₀ ∈ PsNvMain.cyc w' := h4 w' hw'S hw'0
    exact PsNvMain.cyc_le_of_mem w' hw₀ hWS
  ·
    intro U hU
    obtain ⟨B, hB⟩ := h5 U hU
    exact ⟨B, fun w' hw' hfix => hB w' (hcycW hw') hfix⟩
  ·
    intro z g
    exact PsNvMain.leftLaw_of_mem w₀ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) _ (h6 z) hWS g
  ·
    obtain ⟨Φ, hΦ1, hΦ2, hΦ3⟩ := h7
    exact ⟨Φ, fun w' hw' => hΦ1 w' (hcycW hw'), fun w' hw' => hΦ2 w' (hcycW hw'), fun w' hw' => hΦ3 w' (hcycW hw')⟩
  ·
    have hNp : (1 : ℝ) ≤ (Ideal.absNorm p.asIdeal : ℝ) := by
      have h0 : Ideal.absNorm p.asIdeal ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]; exact p.ne_bot
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
    have hcont : Continuous w₀ := PsNvMain.continuous_of_rightInvariant w₀ _ hK1Nopen h2
    obtain ⟨C, A, hCA⟩ := h8
    have hgr1 : PsNvMain.GrAt (Ideal.absNorm p.asIdeal : ℝ)
        ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) :
          Set (GL (Fin 2) (p.adicCompletion ℚ)))
        (fun m => diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m) w₀ 1 :=
      ⟨C, A, fun m hm k hk => by rw [mul_one]; exact hCA m hm k hk⟩
    obtain ⟨C₀, A₀, hC₀, hA₀, hgr₀⟩ := hgr1.nonneg hNp
    have hθc : ∀ z : (p.adicCompletion ℚ)ˣ, ‖((θ 0 z * θ 1 z : ℂˣ) : ℂ)‖ = 1 := by
      intro z
      rw [Units.val_mul, norm_mul, hθu 0 z, hθu 1 z, one_mul]
    have hall : ∀ h : GL (Fin 2) (p.adicCompletion ℚ), PsNvMain.GrAt (Ideal.absNorm p.asIdeal : ℝ)
        ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) :
          Set (GL (Fin 2) (p.adicCompletion ℚ)))
        (fun m => diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m) w₀ h :=
      PsNvMain.growth_translate _ hπ _hϖ w₀ h1 (fun z => ((θ 0 z * θ 1 z : ℂˣ) : ℂ)) hθc h6 hcont _ hNp
        C₀ A₀ hC₀ hA₀ (fun m hm k hk => by have := hgr₀ m hm k hk; rwa [mul_one] at this)
    obtain ⟨C', A', hCA'⟩ := PsNvMain.grAt_of_mem hNp w₀ hall hWS 1
    exact ⟨C', A', fun m hm k hk => by have := hCA' m hm k hk; rwa [mul_one] at this⟩

end S_LanglandsTunnell_CubicInduction_exists_whittaker_localLevelOne_centralChar_admissible_principalSeries2_apply_one_ne_zero_of_norm_eq_one_of_higherUnitsAt
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_whittaker_localLevelOne_centralChar_admissible_principalSeries2_apply_one_ne_zero_of_norm_eq_one_of_higherUnitsAt (solution)
