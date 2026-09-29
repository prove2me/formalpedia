-- Prove2me | solution 1 for NumberField.TateGlobal.exists_forall_norm_partialEulerProduct_continuation_le_rpow_on_re_eq_neg_half_of_admitsModulus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/6d02f6c4-d1f3-5755-bc7d-63163de8eca0

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_LanglandsTunnell_HeckeTate
import Theorems.Thm_LanglandsTunnell_HeckeTate_isNicePinned_heckeDatum
import Theorems.Thm_LanglandsTunnell_TateLocal_norm_stdRootNumberAt_eq_one_of_hasConductorExponentAt
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_eq_count_differentIdeal
import Theorems.Thm_EulerProduct_norm_tprod_inv_one_sub_mul_natCast_cpow_neg_le_exp
import Theorems.Thm_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_exists_forall_norm_partialEulerProduct_continuation_le_rpow_on_re_eq_neg_half_of_admitsModulus
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec"
p2m_attr_erase "simp" "SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal NumberField.InfinitePlace
open LanglandsTunnell LanglandsTunnell.Converse LanglandsTunnell.HeckeTate LanglandsTunnell.TateLocal
open Complex Filter Set Polynomial
open scoped Topology ComplexConjugate

namespace R4G2b

theorem conj_two : conj (2 : ℂ) = 2 := map_ofNat _ 2

theorem Gammaℝ_conj (s : ℂ) : Gammaℝ (conj s) = conj (Gammaℝ s) := by
  rw [Gammaℝ_def, Gammaℝ_def, map_mul, ← Complex.Gamma_conj]
  have harg : ((Real.pi : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_ne_zero.symm
  have h1 : -conj s / 2 = conj (-s / 2) := by
    rw [map_div₀, map_neg, conj_two]
  have h2 : conj s / 2 = conj (s / 2) := by
    rw [map_div₀, conj_two]
  rw [h1, h2, Complex.cpow_conj _ _ harg, Complex.conj_ofReal]

theorem Gammaℂ_conj (s : ℂ) : Gammaℂ (conj s) = conj (Gammaℂ s) := by
  rw [Gammaℂ_def, Gammaℂ_def, map_mul, map_mul, ← Complex.Gamma_conj, conj_two]
  have harg : ((2 : ℂ) * (Real.pi : ℝ)).arg ≠ Real.pi := by
    have : (2 : ℂ) * (Real.pi : ℝ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.arg_ofReal_of_nonneg (by positivity)]; exact Real.pi_ne_zero.symm
  have h2 : conj ((2 : ℂ) * (Real.pi : ℝ)) = (2 : ℂ) * (Real.pi : ℝ) := by
    rw [map_mul, conj_two, Complex.conj_ofReal]
  have h3 : -conj s = conj (-s) := by rw [map_neg]
  rw [h3, Complex.cpow_conj _ _ harg, h2]

theorem Gammaℝ_zero : Gammaℝ 0 = 0 := Gammaℝ_eq_zero_iff.mpr ⟨0, by simp⟩

theorem Gammaℂ_zero : Gammaℂ 0 = 0 := by
  rw [Gammaℂ_def, Complex.Gamma_zero, mul_zero]

theorem Gammaℂ_neg_one : Gammaℂ (-1) = 0 := by
  rw [Gammaℂ_def]
  have : Complex.Gamma (-1) = 0 := by
    have := Complex.Gamma_neg_nat_eq_zero 1
    simpa using this
  rw [this, mul_zero]

theorem norm_Gammaℝ_conj_add_two_mul_inv_le (z : ℂ) :
    ‖Gammaℝ (conj z + 2)‖ * ‖(Gammaℝ z)⁻¹‖ ≤ ‖z‖ := by
  by_cases hz : Gammaℝ z = 0
  · rw [hz, inv_zero, norm_zero, mul_zero]; exact norm_nonneg _
  have hz0 : z ≠ 0 := by rintro rfl; exact hz Gammaℝ_zero
  have h1 : conj z + 2 = conj (z + 2) := by rw [map_add, conj_two]
  rw [h1, Gammaℝ_conj, Complex.norm_conj, Gammaℝ_add_two hz0, norm_div, norm_div, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, norm_inv]
  simp only [Complex.norm_ofNat]
  have hn : 0 < ‖Gammaℝ z‖ := norm_pos_iff.mpr hz
  have hπ : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  rw [div_div, mul_comm, ← mul_div_assoc, ← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul]
  calc ‖z‖ / (2 * Real.pi) ≤ ‖z‖ / 1 :=
        div_le_div_of_nonneg_left (norm_nonneg _) one_pos (by linarith)
    _ = ‖z‖ := div_one _

theorem norm_Gammaℂ_conj_add_two_mul_inv_le (z : ℂ) :
    ‖Gammaℂ (conj z + 2)‖ * ‖(Gammaℂ z)⁻¹‖ ≤ ‖z‖ * ‖z + 1‖ := by
  by_cases hz : Gammaℂ z = 0
  · rw [hz, inv_zero, norm_zero, mul_zero]; positivity
  have hz0 : z ≠ 0 := by rintro rfl; exact hz Gammaℂ_zero
  have hz1 : z + 1 ≠ 0 := by
    intro h
    have : z = -1 := by linear_combination h
    rw [this] at hz; exact hz Gammaℂ_neg_one
  have h1 : conj z + 2 = conj ((z + 1) + 1) := by rw [map_add, map_add, map_one]; ring
  rw [h1, Gammaℂ_conj, Complex.norm_conj, Gammaℂ_add_one hz1, Gammaℂ_add_one hz0]
  rw [norm_div, norm_div, norm_mul, norm_div, norm_div, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le, norm_inv]
  simp only [Complex.norm_ofNat]
  have hn : 0 < ‖Gammaℂ z‖ := norm_pos_iff.mpr hz
  have hπ : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hkey : ‖Gammaℂ z‖ * ‖z‖ / 2 / Real.pi * ‖z + 1‖ / 2 / Real.pi * ‖Gammaℂ z‖⁻¹ =
      ‖z‖ * ‖z + 1‖ / (2 * Real.pi) ^ 2 := by
    field_simp
  rw [hkey]
  have h4 : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith
  calc ‖z‖ * ‖z + 1‖ / (2 * Real.pi) ^ 2 ≤ ‖z‖ * ‖z + 1‖ / 1 :=
        div_le_div_of_nonneg_left (by positivity) one_pos h4
    _ = ‖z‖ * ‖z + 1‖ := div_one _

theorem differentiable_Gammaℂ_inv : Differentiable ℂ (fun s : ℂ => (Gammaℂ s)⁻¹) := by
  have : (fun s : ℂ => (Gammaℂ s)⁻¹) = fun s => (Gammaℝ s)⁻¹ * (Gammaℝ (s + 1))⁻¹ := by
    funext s; rw [← Gammaℝ_mul_Gammaℝ_add_one, mul_inv]
  rw [this]
  exact differentiable_Gammaℝ_inv.mul (differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1))

theorem Gammaℂ_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : Gammaℂ s ≠ 0 := by
  rw [← Gammaℝ_mul_Gammaℝ_add_one]
  refine mul_ne_zero (Gammaℝ_ne_zero_of_re_pos hs) (Gammaℝ_ne_zero_of_re_pos ?_)
  simp only [add_re, one_re]; linarith

section euler
variable {K : Type} [Field K] [NumberField K]

theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

def nC (v : HeightOneSpectrum (𝓞 K)) : ℂ := ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)

theorem nC_pos (v : HeightOneSpectrum (𝓞 K)) : 0 < Ideal.absNorm v.asIdeal :=
  lt_of_lt_of_le (by norm_num) (two_le_absNorm v)

theorem norm_nC_cpow_neg (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    ‖nC v ^ (-s)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) := by
  unfold nC
  rw [Complex.norm_natCast_cpow_of_pos (nC_pos v) (-s), Complex.neg_re]

theorem one_le_nR (v : HeightOneSpectrum (𝓞 K)) : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
  have := two_le_absNorm v
  exact_mod_cast (by omega : 1 ≤ Ideal.absNorm v.asIdeal)

theorem norm_nC_cpow_neg_le_half {s : ℂ} (hs : 1 ≤ s.re) (v : HeightOneSpectrum (𝓞 K)) :
    ‖nC v ^ (-s)‖ ≤ 1 / 2 := by
  rw [norm_nC_cpow_neg]
  have h2 : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast two_le_absNorm v
  calc (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (one_le_nR v) (by linarith)
    _ ≤ (2 : ℝ) ^ (-(1 : ℝ)) := by
        rw [Real.rpow_neg (by positivity), Real.rpow_neg (by norm_num), Real.rpow_one, Real.rpow_one]
        exact inv_anti₀ (by norm_num) h2
    _ = 1 / 2 := by rw [Real.rpow_neg (by norm_num), Real.rpow_one, one_div]

theorem norm_nC_cpow_neg_le {s : ℂ} (hs : -1 / 2 ≤ s.re) (v : HeightOneSpectrum (𝓞 K)) :
    ‖nC v ^ (-s)‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (1 / 2 : ℝ) := by
  rw [norm_nC_cpow_neg]
  exact Real.rpow_le_rpow_of_exponent_le (one_le_nR v) (by linarith)

open scoped Classical in

def coef (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) : ℂ :=
  if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0

open scoped Classical in

def coefD (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) : ℂ :=
  if IsUnramifiedCharAt χ v then (((χ (uniformizerIdele K v))⁻¹ : ℂˣ) : ℂ) else 0

theorem norm_coef_le_one {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hχu : IsUnitaryChar (𝓞 K) K χ)
    (v : HeightOneSpectrum (𝓞 K)) : ‖coef χ v‖ ≤ 1 := by
  unfold coef; split_ifs
  · exact (hχu _).le
  · simp

theorem norm_coefD_le_one {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hχu : IsUnitaryChar (𝓞 K) K χ)
    (v : HeightOneSpectrum (𝓞 K)) : ‖coefD χ v‖ ≤ 1 := by
  unfold coefD; split_ifs
  · have h := hχu (uniformizerIdele K v)
    rw [Units.val_inv_eq_inv_val, norm_inv, h, inv_one]
  · simp

def corr (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (T : Finset (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ :=
  ∏ v ∈ T, (1 - coef χ v * nC v ^ (-s))

theorem differentiable_corr (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (T : Finset (HeightOneSpectrum (𝓞 K))) :
    Differentiable ℂ (corr χ T) := by
  unfold corr
  refine Differentiable.fun_finsetProd fun v _ => ?_
  refine (differentiable_const _).sub ((differentiable_const _).mul ?_)
  refine Differentiable.const_cpow differentiable_neg (Or.inl ?_)
  unfold nC
  exact_mod_cast (nC_pos v).ne'

def PT (T : Finset (HeightOneSpectrum (𝓞 K))) : ℝ :=
  ∏ v ∈ T, (1 + (Ideal.absNorm v.asIdeal : ℝ) ^ (1 / 2 : ℝ))

theorem PT_pos (T : Finset (HeightOneSpectrum (𝓞 K))) : 0 < PT (K := K) T := by
  unfold PT
  exact Finset.prod_pos fun v _ => by positivity

theorem norm_corr_le {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hχu : IsUnitaryChar (𝓞 K) K χ)
    (T : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : -1 / 2 ≤ s.re) :
    ‖corr χ T s‖ ≤ PT (K := K) T := by
  unfold corr PT
  refine (Finset.norm_prod_le _ _).trans (Finset.prod_le_prod (fun v _ => norm_nonneg _) fun v _ => ?_)
  calc ‖(1 : ℂ) - coef χ v * nC v ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖coef χ v * nC v ^ (-s)‖ := norm_sub_le _ _
    _ ≤ 1 + 1 * (Ideal.absNorm v.asIdeal : ℝ) ^ (1 / 2 : ℝ) := by
        rw [norm_one, norm_mul]
        gcongr
        · exact norm_coef_le_one hχu v
        · exact norm_nC_cpow_neg_le hs v
    _ = 1 + (Ideal.absNorm v.asIdeal : ℝ) ^ (1 / 2 : ℝ) := by rw [one_mul]

theorem norm_term_le_half {c : HeightOneSpectrum (𝓞 K) → ℂ} (hc : ∀ v, ‖c v‖ ≤ 1) {s : ℂ}
    (hs : 1 ≤ s.re) (v : HeightOneSpectrum (𝓞 K)) : ‖c v * nC v ^ (-s)‖ ≤ 1 / 2 := by
  rw [norm_mul]
  calc ‖c v‖ * ‖nC v ^ (-s)‖ ≤ 1 * (1 / 2) :=
        mul_le_mul (hc v) (norm_nC_cpow_neg_le_half hs v) (norm_nonneg _) zero_le_one
    _ = 1 / 2 := one_mul _

theorem one_sub_term_ne_zero {c : HeightOneSpectrum (𝓞 K) → ℂ} (hc : ∀ v, ‖c v‖ ≤ 1) {s : ℂ}
    (hs : 1 ≤ s.re) (v : HeightOneSpectrum (𝓞 K)) : (1 : ℂ) - c v * nC v ^ (-s) ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  have := norm_term_le_half hc hs v
  rw [← h, norm_one] at this
  norm_num at this

theorem summable_norm_term {c : HeightOneSpectrum (𝓞 K) → ℂ} (hc : ∀ v, ‖c v‖ ≤ 1) {s : ℂ}
    (hs : 1 < s.re) : Summable fun v : HeightOneSpectrum (𝓞 K) => ‖c v * nC v ^ (-s)‖ := by
  refine Summable.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => ?_)
    (NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt K hs)
  rw [norm_mul, ← norm_nC_cpow_neg]
  calc ‖c v‖ * ‖nC v ^ (-s)‖ ≤ 1 * ‖nC v ^ (-s)‖ :=
        mul_le_mul_of_nonneg_right (hc v) (norm_nonneg _)
    _ = ‖nC v ^ (-s)‖ := one_mul _

theorem hasProd_subtype {c : HeightOneSpectrum (𝓞 K) → ℂ} (hc : ∀ v, ‖c v‖ ≤ 1) {s : ℂ}
    (hs : 1 < s.re) (S : Set (HeightOneSpectrum (𝓞 K))) :
    HasProd (fun v : S => (1 - c v.1 * nC v.1 ^ (-s))⁻¹)
      (cexp (∑' v : S, -log (1 - c v.1 * nC v.1 ^ (-s)))) := by
  have hne : ∀ v : HeightOneSpectrum (𝓞 K), (1 : ℂ) - c v * nC v ^ (-s) ≠ 0 :=
    one_sub_term_ne_zero hc hs.le
  have hsub : Summable fun v : S => c v.1 * nC v.1 ^ (-s) :=
    ((summable_norm_term hc hs).subtype S).of_norm
  have hg : Summable fun v : S => -log (1 - c v.1 * nC v.1 ^ (-s)) := hsub.clog_one_sub.neg
  have H := hg.hasSum.cexp
  have hcongr : (cexp ∘ fun v : S => -log (1 - c v.1 * nC v.1 ^ (-s))) =
      fun v => (1 - c v.1 * nC v.1 ^ (-s))⁻¹ := by
    funext v
    simp only [Function.comp_apply, exp_neg, exp_log (hne v.1)]
  rw [hcongr] at H
  exact H

theorem tprod_compl_eq {c : HeightOneSpectrum (𝓞 K) → ℂ} (hc : ∀ v, ‖c v‖ ≤ 1) {s : ℂ}
    (hs : 1 < s.re) (T : Finset (HeightOneSpectrum (𝓞 K))) :
    (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}, (1 - c v.1 * nC v.1 ^ (-s))⁻¹) =
      (∏ v ∈ T, (1 - c v * nC v ^ (-s))) *
        ∏' v : HeightOneSpectrum (𝓞 K), (1 - c v * nC v ^ (-s))⁻¹ := by
  set f : HeightOneSpectrum (𝓞 K) → ℂ := fun v => (1 - c v * nC v ^ (-s))⁻¹ with hf
  set E : ℂ := cexp (∑' v : ((↑T : Set (HeightOneSpectrum (𝓞 K)))ᶜ : Set (HeightOneSpectrum (𝓞 K))),
    -log (1 - c v.1 * nC v.1 ^ (-s))) with hE
  have hP : HasProd (f ∘ (↑) : ((↑T : Set (HeightOneSpectrum (𝓞 K)))ᶜ : Set _) → ℂ) E :=
    hasProd_subtype hc hs _
  have hEq : (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}, (1 - c v.1 * nC v.1 ^ (-s))⁻¹) = E :=
    hP.tprod_eq
  have hG : HasProd (f ∘ (↑) : (↑T : Set (HeightOneSpectrum (𝓞 K))) → ℂ) (∏ v ∈ T, f v) :=
    Finset.hasProd T _
  have hall : HasProd f ((∏ v ∈ T, f v) * E) := hG.mul_isCompl isCompl_compl hP
  have htot : (∏' v : HeightOneSpectrum (𝓞 K), f v) = (∏ v ∈ T, f v) * E := hall.tprod_eq
  have hne : (∏ v ∈ T, (1 - c v * nC v ^ (-s))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun v _ => one_sub_term_ne_zero hc hs.le v
  have hinv : (∏ v ∈ T, f v) = (∏ v ∈ T, (1 - c v * nC v ^ (-s)))⁻¹ := by
    simp only [hf]; exact Finset.prod_inv_distrib _
  rw [hEq]
  show E = (∏ v ∈ T, (1 - c v * nC v ^ (-s))) * ∏' v : HeightOneSpectrum (𝓞 K), f v
  rw [htot, hinv, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]

def M₁ (K : Type) [Field K] [NumberField K] : ℝ :=
  Real.exp (2 * ∑' v : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))

theorem M₁_pos : 0 < M₁ K := Real.exp_pos _

theorem norm_tprod_le (c : HeightOneSpectrum (𝓞 K) → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1) (s : ℂ)
    (hs : 3 / 2 ≤ s.re) :
    ‖∏' v : HeightOneSpectrum (𝓞 K), (1 - c v * nC v ^ (-s))⁻¹‖ ≤ M₁ K := by
  have hs1 : 1 < s.re := by linarith
  have hsum := NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt K hs1
  have h := EulerProduct.norm_tprod_inv_one_sub_mul_natCast_cpow_neg_le_exp
    (fun v : HeightOneSpectrum (𝓞 K) => Ideal.absNorm v.asIdeal)
    (fun v => two_le_absNorm v) c hc s hs1.le hsum
  refine h.trans ?_
  unfold M₁
  rw [Real.exp_le_exp]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine Summable.tsum_le_tsum (fun v => ?_) hsum
    (NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt K (by norm_num))
  exact Real.rpow_le_rpow_of_exponent_le (one_le_nR v) (by linarith)

end euler

section datum
open scoped Classical
variable {K : Type} [Field K] [NumberField K]
variable (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
  (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
  (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)

theorem euler_eval (v : HeightOneSpectrum (𝓞 K)) (q : ℂ) :
    ((heckeDatum K χ uR aR uC kC).euler v).eval q = 1 - coef χ v * q := by
  classical
  simp only [heckeDatum, coef]
  split_ifs <;> simp

theorem dual_eval (v : HeightOneSpectrum (𝓞 K)) (q : ℂ) :
    ((heckeDatum K χ uR aR uC kC).dual v).eval q = 1 - coefD χ v * q := by
  classical
  simp only [heckeDatum, coefD]
  split_ifs <;> simp

theorem LFun_eq (s : ℂ) :
    (heckeDatum K χ uR aR uC kC).LFun s =
      ∏' v : HeightOneSpectrum (𝓞 K), (1 - coef χ v * nC v ^ (-s))⁻¹ := by
  unfold LDatum.LFun
  refine tprod_congr fun v => ?_
  rw [euler_eval]
  rfl

theorem LFunDual_eq (s : ℂ) :
    (heckeDatum K χ uR aR uC kC).LFunDual s =
      ∏' v : HeightOneSpectrum (𝓞 K), (1 - coefD χ v * nC v ^ (-s))⁻¹ := by
  unfold LDatum.LFunDual
  refine tprod_congr fun v => ?_
  rw [dual_eval]
  rfl

def μR (w : {w : InfinitePlace K // w.IsReal}) : ℂ := uR w.1 w.2 + signShift (aR w.1 w.2)

def μC (w : {w : InfinitePlace K // w.IsComplex}) : ℂ := uC w.1 w.2 + ((kC w.1 w.2).natAbs : ℂ) / 2

theorem prod_map_sum_singleton {ι : Type} (S : Finset ι) (x : ι → ℂ) (g : ℂ → ℂ) :
    ((∑ i ∈ S, ({x i} : Multiset ℂ)).map g).prod = ∏ i ∈ S, g (x i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, Multiset.map_add,
      Multiset.prod_add, ih, Multiset.map_singleton, Multiset.prod_singleton]

theorem archFactor_eq (s : ℂ) :
    (heckeDatum K χ uR aR uC kC).archFactor s =
      (∏ w : {w : InfinitePlace K // w.IsReal}, Gammaℝ (s + μR uR aR w)) *
        ∏ w : {w : InfinitePlace K // w.IsComplex}, Gammaℂ (s + μC uC kC w) := by
  simp only [LDatum.archFactor, heckeDatum]
  rw [prod_map_sum_singleton, prod_map_sum_singleton]
  rfl

theorem archFactorDual_eq (s : ℂ) :
    (heckeDatum K χ uR aR uC kC).archFactorDual s =
      (∏ w : {w : InfinitePlace K // w.IsReal}, Gammaℝ (s + (-uR w.1 w.2 + signShift (aR w.1 w.2)))) *
        ∏ w : {w : InfinitePlace K // w.IsComplex},
          Gammaℂ (s + (-uC w.1 w.2 + ((-kC w.1 w.2).natAbs : ℂ) / 2)) := by
  simp only [LDatum.archFactorDual, heckeDatum]
  rw [prod_map_sum_singleton, prod_map_sum_singleton]

def invArch (s : ℂ) : ℂ :=
  (∏ w : {w : InfinitePlace K // w.IsReal}, (Gammaℝ (s + μR uR aR w))⁻¹) *
    ∏ w : {w : InfinitePlace K // w.IsComplex}, (Gammaℂ (s + μC uC kC w))⁻¹

theorem differentiable_invArch : Differentiable ℂ (invArch uR aR uC kC) := by
  unfold invArch
  refine (Differentiable.fun_finsetProd fun w _ => ?_).mul (Differentiable.fun_finsetProd fun w _ => ?_)
  · exact differentiable_Gammaℝ_inv.comp (differentiable_id.add_const _)
  · exact differentiable_Gammaℂ_inv.comp (differentiable_id.add_const _)

theorem archFactor_mul_invArch {s : ℂ}
    (hR : ∀ w : {w : InfinitePlace K // w.IsReal}, Gammaℝ (s + μR uR aR w) ≠ 0)
    (hC : ∀ w : {w : InfinitePlace K // w.IsComplex}, Gammaℂ (s + μC uC kC w) ≠ 0) :
    (heckeDatum K χ uR aR uC kC).archFactor s * invArch uR aR uC kC s = 1 := by
  rw [archFactor_eq, invArch, mul_mul_mul_comm, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    Finset.prod_eq_one fun w _ => mul_inv_cancel₀ (hR w), Finset.prod_eq_one fun w _ => mul_inv_cancel₀ (hC w),
    one_mul]

end datum

theorem eq_of_agree_of_one_lt_re (L G : ℂ → ℂ) (hL : Differentiable ℂ L) (hG : Differentiable ℂ G)
    (h : ∀ s : ℂ, 1 < s.re → L s = G s) : L = G := by
  have hLa : AnalyticOnNhd ℂ L univ := hL.differentiableOn.analyticOnNhd isOpen_univ
  have hGa : AnalyticOnNhd ℂ G univ := hG.differentiableOn.analyticOnNhd isOpen_univ
  have hVopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  have hev : L =ᶠ[𝓝 (2 : ℂ)] G :=
    Filter.eventuallyEq_of_mem (hVopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)) fun z hz => h z hz
  exact hLa.eq_of_eventuallyEq hGa hev

section arch
variable {K : Type} [Field K]

theorem norm_extensionEmbedding (w : InfinitePlace K) (x : w.Completion) :
    ‖Completion.extensionEmbedding w x‖ = ‖x‖ := by
  have := (Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x
  exact this

theorem exists_unit_of_isReal {w : InfinitePlace K} (hw : w.IsReal) (r : ℝ) (hr : 0 < r) :
    ∃ ρ : (w.Completion)ˣ, Completion.extensionEmbedding w (ρ : w.Completion) = (r : ℂ) := by
  obtain ⟨y, hy⟩ := Completion.surjective_extensionEmbeddingOfIsReal hw r
  have hy' : Completion.extensionEmbedding w y = (r : ℂ) := by
    rw [← Completion.extensionEmbeddingOfIsReal_apply hw, hy]
  have hy0 : y ≠ 0 := by
    intro h; rw [h, map_zero] at hy'
    exact hr.ne' (by exact_mod_cast hy'.symm)
  exact ⟨Units.mk0 y hy0, hy'⟩

theorem exists_unit_of_isComplex {w : InfinitePlace K} (hw : w.IsComplex) (z : ℂ) (hz : z ≠ 0) :
    ∃ ρ : (w.Completion)ˣ, Completion.extensionEmbedding w (ρ : w.Completion) = z := by
  obtain ⟨y, hy⟩ := Completion.surjective_extensionEmbedding_of_isComplex hw z
  have hy0 : y ≠ 0 := by
    intro h; rw [h, map_zero] at hy; exact hz hy.symm
  exact ⟨Units.mk0 y hy0, hy⟩

theorem zpow_eq_zpow_val_of_sq_eq_one {σ : ℂ} (hσ : σ ^ 2 = 1) (k : ℤ) :
    σ ^ k = σ ^ (((k : ZMod 2)).val : ℤ) := by
  have hσ0 : σ ≠ 0 := by
    intro h; rw [h] at hσ; norm_num at hσ
  have hval : (((k : ZMod 2)).val : ℤ) = k % 2 := ZMod.val_intCast k
  rw [hval]
  conv_lhs => rw [← Int.emod_add_mul_ediv k 2]
  rw [zpow_add₀ hσ0, zpow_mul, zpow_ofNat, hσ, one_zpow, mul_one]

variable [NumberField K]
variable (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (φ : InfinitePlace K → ℝ) (k : InfinitePlace K → ℤ)
  (hφ : ∀ (w : InfinitePlace K) (a : (w.Completion)ˣ) (r : ℝ), 0 < r →
      Completion.extensionEmbedding w (a : w.Completion) = (r : ℂ) →
      ((archLocalChar χ w a : ℂˣ) : ℂ) = (r : ℂ) ^ (Complex.I * φ w))
  (hk : ∀ (w : InfinitePlace K) (a : (w.Completion)ˣ),
      ‖Completion.extensionEmbedding w (a : w.Completion)‖ = 1 →
      ((archLocalChar χ w a : ℂˣ) : ℂ) = (Completion.extensionEmbedding w (a : w.Completion)) ^ (k w))
include hφ hk

theorem archLocalChar_eq (w : InfinitePlace K) (x : (w.Completion)ˣ)
    (ρ : (w.Completion)ˣ)
    (hρ : Completion.extensionEmbedding w (ρ : w.Completion) = ((‖(x : w.Completion)‖ : ℝ) : ℂ)) :
    ((archLocalChar χ w x : ℂˣ) : ℂ) =
      ((‖(x : w.Completion)‖ : ℝ) : ℂ) ^ (Complex.I * φ w) *
        (Completion.extensionEmbedding w (x : w.Completion) / ((‖(x : w.Completion)‖ : ℝ) : ℂ)) ^ (k w) := by
  set e := Completion.extensionEmbedding w with he
  set r : ℝ := ‖(x : w.Completion)‖ with hr
  have hr0 : 0 < r := norm_pos_iff.mpr x.ne_zero
  have hrC : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr0.ne'
  set u : (w.Completion)ˣ := x * ρ⁻¹ with hu
  have heu : e (u : w.Completion) = e (x : w.Completion) / (r : ℂ) := by
    rw [hu, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hρ, div_eq_mul_inv]
  have hnu : ‖e (u : w.Completion)‖ = 1 := by
    rw [heu, norm_div, norm_extensionEmbedding, Complex.norm_real, Real.norm_of_nonneg hr0.le, ← hr,
      div_self hr0.ne']
  have hx : x = u * ρ := by rw [hu, inv_mul_cancel_right]
  have h1 := hφ w ρ r hr0 hρ
  have h2 := hk w u hnu
  calc ((archLocalChar χ w x : ℂˣ) : ℂ) = ((archLocalChar χ w u : ℂˣ) : ℂ) * ((archLocalChar χ w ρ : ℂˣ) : ℂ) := by
        rw [hx, map_mul, Units.val_mul]
    _ = (e (x : w.Completion) / (r : ℂ)) ^ (k w) * (r : ℂ) ^ (Complex.I * φ w) := by rw [h2, h1, heu]
    _ = _ := by rw [mul_comm]

theorem isArchCompAt_of_isReal (w : InfinitePlace K) (hw : w.IsReal) :
    IsArchCompAt K χ w (Complex.I * φ w) ((((k w : ℤ) : ZMod 2)).val : ℤ) := by
  intro x
  set r : ℝ := ‖(x : w.Completion)‖ with hr
  have hr0 : 0 < r := norm_pos_iff.mpr x.ne_zero
  obtain ⟨ρ, hρ⟩ := exists_unit_of_isReal hw r hr0
  rw [archLocalChar_eq χ φ k hφ hk w x ρ hρ]
  have hmult : (w.mult : ℂ) = 1 := by
    rw [show w.mult = 1 from mult_isReal ⟨w, hw⟩, Nat.cast_one]
  rw [hmult, one_mul]
  congr 1

  set σ : ℂ := Completion.extensionEmbedding w (x : w.Completion) / ((r : ℝ) : ℂ) with hσ
  have hreal : ((Completion.extensionEmbeddingOfIsReal hw (x : w.Completion) : ℝ) : ℂ) =
      Completion.extensionEmbedding w (x : w.Completion) := Completion.extensionEmbeddingOfIsReal_apply hw _
  set a : ℝ := Completion.extensionEmbeddingOfIsReal hw (x : w.Completion) with ha
  have habs : |a| = r := by
    have h1 : ‖(a : ℂ)‖ = r := by rw [hreal, norm_extensionEmbedding]
    rwa [Complex.norm_real, Real.norm_eq_abs] at h1
  have hσsq : σ ^ 2 = 1 := by
    rw [hσ, ← hreal, div_pow]
    have : ((a : ℂ)) ^ 2 = ((r : ℝ) : ℂ) ^ 2 := by
      rw [← habs, ← Complex.ofReal_pow, ← Complex.ofReal_pow, sq_abs]
    rw [this, div_self]
    exact pow_ne_zero 2 (ofReal_ne_zero.mpr hr0.ne')
  exact zpow_eq_zpow_val_of_sq_eq_one hσsq (k w)

theorem isArchCompAt_of_isComplex (w : InfinitePlace K) (hw : w.IsComplex) :
    IsArchCompAt K χ w (Complex.I * φ w / 2) (k w) := by
  intro x
  set r : ℝ := ‖(x : w.Completion)‖ with hr
  have hr0 : 0 < r := norm_pos_iff.mpr x.ne_zero
  obtain ⟨ρ, hρ⟩ := exists_unit_of_isComplex hw (r : ℂ) (ofReal_ne_zero.mpr hr0.ne')
  rw [archLocalChar_eq χ φ k hφ hk w x ρ hρ]
  have hmult : (w.mult : ℂ) = 2 := by
    rw [show w.mult = 2 from mult_isComplex ⟨w, hw⟩, Nat.cast_ofNat]
  rw [hmult]
  congr 2
  ring

end arch

section localdata
open scoped Classical
open NumberField.StandardAddChar NumberField.AdelicLevel HeckeCharacter
variable {K : Type} [Field K] [NumberField K]

theorem localChar_eq_one_of_admitsModulus (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 K))
    (hmod : AdmitsModulus K χ 𝔣) (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ)
    (ht : t ∈ higherUnitsAt K v (idealMultiplicity K v 𝔣)) : localChar χ v t = 1 := by
  rw [localChar_apply]
  apply hmod
  · rw [Units.coe_map]; rfl
  · intro w
    rw [Units.coe_map]
    change Valued.v (((localUnit (𝓞 K) K v t : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w) = 1 ∧
      Valued.v (((localUnit (𝓞 K) K v t : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w - 1) ≤ _
    by_cases hw : w = v
    · subst hw
      rw [localUnit_apply_self]
      obtain ⟨hval, hball⟩ := ht
      refine ⟨hval, ?_⟩
      rcases hball with h0 | hle
      · rw [h0, Nat.cast_zero, neg_zero, WithZero.exp_zero]
        calc Valued.v ((t : w.adicCompletion K) - 1)
            ≤ max (Valued.v (t : w.adicCompletion K)) (Valued.v (1 : w.adicCompletion K)) := Valuation.map_sub _ _ _
          _ = 1 := by rw [hval, map_one, max_self]
      · exact hle
    · rw [localUnit_apply_of_ne (𝓞 K) K v t hw]
      refine ⟨map_one _, ?_⟩
      rw [sub_self, map_zero]
      exact zero_le'

theorem exists_hasConductorExponentAt_le (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 K))
    (hmod : AdmitsModulus K χ 𝔣) (v : HeightOneSpectrum (𝓞 K)) :
    ∃ c : ℕ, c ≤ idealMultiplicity K v 𝔣 ∧ HasConductorExponentAt K v (localChar χ v) c := by
  have hex : ∃ c : ℕ, ∀ u ∈ higherUnitsAt K v c, localChar χ v u = 1 :=
    ⟨idealMultiplicity K v 𝔣, fun u hu => localChar_eq_one_of_admitsModulus χ 𝔣 hmod v u hu⟩
  refine ⟨Nat.find hex, Nat.find_min' hex fun u hu => localChar_eq_one_of_admitsModulus χ 𝔣 hmod v u hu,
    Nat.find_spec hex, fun m hm => ?_⟩
  have := Nat.find_min hex hm
  push Not at this
  exact this

theorem conductorExponentAt_le (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 K))
    (hmod : AdmitsModulus K χ 𝔣) (v : HeightOneSpectrum (𝓞 K)) :
    conductorExponentAt K v (localChar χ v) ≤ idealMultiplicity K v 𝔣 := by
  obtain ⟨c, hc, h⟩ := exists_hasConductorExponentAt_le χ 𝔣 hmod v
  rw [conductorExponentAt_eq_of_hasConductorExponentAt K v h]
  exact hc

theorem norm_localChar {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hχu : IsUnitaryChar (𝓞 K) K χ)
    (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    ‖((localChar χ v t : ℂˣ) : ℂ)‖ = 1 := by
  rw [localChar_apply]; exact hχu _

theorem norm_heckeRootNumber (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 K))
    (hmod : AdmitsModulus K χ 𝔣) (hχu : IsUnitaryChar (𝓞 K) K χ)
    (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ) :
    ‖heckeRootNumber K χ aR kC‖ = 1 := by
  unfold heckeRootNumber
  rw [norm_mul, norm_mul, norm_prod, norm_prod]
  have h1 : ∏ w : {w : InfinitePlace K // w.IsReal}, ‖signEpsilon (aR w.1 w.2)‖ = 1 :=
    Finset.prod_eq_one fun w _ => by unfold signEpsilon; split_ifs <;> simp
  have h2 : ∏ w : {w : InfinitePlace K // w.IsComplex}, ‖Complex.I ^ (kC w.1 w.2).natAbs‖ = 1 :=
    Finset.prod_eq_one fun w _ => by rw [norm_pow, Complex.norm_I, one_pow]
  have h3 : ‖∏ᶠ v : HeightOneSpectrum (𝓞 K), stdRootNumberAt K v (localChar χ v)‖ = 1 := by
    refine finprod_induction (fun x : ℂ => ‖x‖ = 1) norm_one
      (fun x y hx hy => by rw [norm_mul, hx, hy, one_mul]) fun v => ?_
    obtain ⟨c, -, hc⟩ := exists_hasConductorExponentAt_le χ 𝔣 hmod v
    exact LanglandsTunnell.TateLocal.norm_stdRootNumberAt_eq_one_of_hasConductorExponentAt K v (localChar χ v)
      c hc (norm_localChar hχu v)
  rw [h1, h2, h3, one_mul, one_mul]

def nD (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : ℤ :=
  FractionalIdeal.count K v ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) :
    FractionalIdeal (nonZeroDivisors (𝓞 K)) K)

theorem nD_nonneg (v : HeightOneSpectrum (𝓞 K)) : 0 ≤ nD K v :=
  FractionalIdeal.count_coe_nonneg K v _

theorem finite_nD_ne_zero (K : Type) [Field K] [NumberField K] :
    {v : HeightOneSpectrum (𝓞 K) | nD K v ≠ 0}.Finite := by
  have := FractionalIdeal.finite_factors (K := K)
    ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
  exact Filter.eventually_cofinite.mp this

theorem finite_mult_ne_zero (𝔣 : Ideal (𝓞 K)) :
    {v : HeightOneSpectrum (𝓞 K) | idealMultiplicity K v 𝔣 ≠ 0}.Finite := by
  by_cases h𝔣 : 𝔣 = ⊥
  · subst h𝔣
    have : {v : HeightOneSpectrum (𝓞 K) | idealMultiplicity K v (⊥ : Ideal (𝓞 K)) ≠ 0} = ∅ := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not, idealMultiplicity,
        Submodule.zero_eq_bot.symm, Associates.mk_zero, Associates.factors_zero]
      unfold Associates.count
      split_ifs <;> rfl
    rw [this]; exact Set.finite_empty
  · refine (Ideal.finite_factors h𝔣).subset fun v hv => ?_
    simp only [Set.mem_setOf_eq, idealMultiplicity] at hv ⊢
    exact (Associates.count_ne_zero_iff_dvd h𝔣 v.irreducible).mp hv

def levelSet (𝔣 : Ideal (𝓞 K)) : Finset (HeightOneSpectrum (𝓞 K)) :=
  (finite_mult_ne_zero 𝔣).toFinset ∪ (finite_nD_ne_zero K).toFinset

def Nf (𝔣 : Ideal (𝓞 K)) : ℝ :=
  ∏ v ∈ levelSet 𝔣, (Ideal.absNorm v.asIdeal : ℝ) ^ ((idealMultiplicity K v 𝔣 : ℤ) + nD K v)

theorem Nf_pos (𝔣 : Ideal (𝓞 K)) : 0 < Nf (K := K) 𝔣 :=
  Finset.prod_pos fun v _ => zpow_pos (by exact_mod_cast nC_pos v) _

theorem pinnedExp_eq (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) :
    pinnedExp K χ v = (conductorExponentAt K v (localChar χ v) : ℤ) + nD K v := by
  unfold pinnedExp nD
  rw [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_eq_count_differentIdeal K v]

theorem heckeConductor_le (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 K))
    (hmod : AdmitsModulus K χ 𝔣) : heckeConductor K χ ≤ Nf 𝔣 := by
  unfold heckeConductor Nf
  have hsupp : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) =>
      (Ideal.absNorm v.asIdeal : ℝ) ^ (pinnedExp K χ v)) ⊆ ↑(levelSet 𝔣) := by
    intro v hv
    rw [Function.mem_mulSupport] at hv
    by_contra hnot
    apply hv
    have hm : idealMultiplicity K v 𝔣 = 0 := by
      by_contra h
      exact hnot (Finset.mem_coe.mpr (Finset.mem_union_left _ ((finite_mult_ne_zero 𝔣).mem_toFinset.mpr h)))
    have hn : nD K v = 0 := by
      by_contra h
      exact hnot (Finset.mem_coe.mpr (Finset.mem_union_right _ ((finite_nD_ne_zero K).mem_toFinset.mpr h)))
    have hc : conductorExponentAt K v (localChar χ v) = 0 := by
      have := conductorExponentAt_le χ 𝔣 hmod v
      omega
    rw [pinnedExp_eq, hc, hn]
    simp
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp]
  refine Finset.prod_le_prod (fun v _ => (zpow_pos (by exact_mod_cast nC_pos v) _).le) fun v _ => ?_
  rw [pinnedExp_eq]
  refine zpow_le_zpow_right₀ (one_le_nR v) ?_
  have := conductorExponentAt_le χ 𝔣 hmod v
  omega

end localdata

section main
open scoped Classical
open HeckeCharacter
variable {K : Type} [Field K] [NumberField K]

theorem conj_eq_of_re {s : ℂ} (hs : s.re = -1 / 2) : conj s = -1 - s := by
  apply Complex.ext
  · simp [hs]; norm_num
  · simp

theorem conj_signShift (a : ZMod 2) : conj (signShift a) = signShift a := by
  unfold signShift; split_ifs <;> simp

theorem norm_signShift_le (a : ZMod 2) : ‖signShift a‖ ≤ 1 := by
  unfold signShift; split_ifs <;> simp

theorem norm_le_of_re {s : ℂ} (hs : s.re = -1 / 2) : ‖s‖ ≤ 1 / 2 + |s.im| := by
  have h := norm_le_abs_re_add_abs_im s
  rw [hs] at h
  norm_num at h
  linarith

theorem arch_ratio_le (φ : InfinitePlace K → ℝ) (k : InfinitePlace K → ℤ) (s : ℂ) (hs : s.re = -1 / 2)
    (q : ℝ) (hq0 : 0 ≤ q) (hq : ∀ w : InfinitePlace K, 2 + |s.im| + |φ w| + |(k w : ℝ)| ≤ q) :
    ‖(∏ w : {w : InfinitePlace K // w.IsReal},
        Gammaℝ (1 - s + (-(Complex.I * φ w.1) + signShift (((k w.1 : ℤ) : ZMod 2))))) *
      ∏ w : {w : InfinitePlace K // w.IsComplex},
        Gammaℂ (1 - s + (-(Complex.I * φ w.1 / 2) + ((-k w.1).natAbs : ℂ) / 2))‖ *
    ‖invArch (fun w _ => Complex.I * φ w) (fun w _ => ((k w : ℤ) : ZMod 2))
        (fun w _ => Complex.I * φ w / 2) (fun w _ => k w) s‖ ≤
      q ^ (Fintype.card {w : InfinitePlace K // w.IsReal}) *
        (q * q) ^ (Fintype.card {w : InfinitePlace K // w.IsComplex}) := by
  have hsn := norm_le_of_re hs
  unfold invArch μR μC
  rw [norm_mul, norm_mul, mul_mul_mul_comm, norm_prod, norm_prod, norm_prod, norm_prod,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun w _ => by positivity) (pow_nonneg hq0 _)
  ·
    refine (Finset.prod_le_prod (fun w _ => by positivity) fun w _ => ?_).trans_eq
      (by rw [Finset.prod_const, Finset.card_univ])
    set z : ℂ := s + (Complex.I * φ w.1 + signShift (((k w.1 : ℤ) : ZMod 2))) with hz
    have harg : 1 - s + (-(Complex.I * φ w.1) + signShift (((k w.1 : ℤ) : ZMod 2))) = conj z + 2 := by
      rw [hz, map_add, map_add, conj_eq_of_re hs, map_mul, Complex.conj_I, Complex.conj_ofReal, conj_signShift]
      ring
    rw [harg]
    refine (norm_Gammaℝ_conj_add_two_mul_inv_le z).trans ?_
    calc ‖z‖ ≤ ‖s‖ + (‖Complex.I * φ w.1‖ + ‖signShift (((k w.1 : ℤ) : ZMod 2))‖) :=
          norm_add_le_of_le (le_refl _) (norm_add_le _ _)
      _ ≤ (1 / 2 + |s.im|) + (|φ w.1| + 1) := by
          gcongr
          · rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
          · exact norm_signShift_le _
      _ ≤ q := by have := hq w.1; have := abs_nonneg (k w.1 : ℝ); linarith
  ·
    refine (Finset.prod_le_prod (fun w _ => by positivity) fun w _ => ?_).trans_eq
      (by rw [Finset.prod_const, Finset.card_univ])
    set z : ℂ := s + (Complex.I * φ w.1 / 2 + ((k w.1).natAbs : ℂ) / 2) with hz
    have harg : 1 - s + (-(Complex.I * φ w.1 / 2) + ((-k w.1).natAbs : ℂ) / 2) = conj z + 2 := by
      rw [hz, map_add, map_add, conj_eq_of_re hs, map_div₀, map_div₀, map_mul, Complex.conj_I,
        Complex.conj_ofReal, map_natCast, conj_two, Int.natAbs_neg]
      ring
    rw [harg]
    refine (norm_Gammaℂ_conj_add_two_mul_inv_le z).trans ?_
    have hk : ‖((k w.1).natAbs : ℂ) / 2‖ ≤ |(k w.1 : ℝ)| := by
      rw [norm_div, Complex.norm_natCast, Complex.norm_ofNat, Nat.cast_natAbs, Int.cast_abs]
      have := abs_nonneg (k w.1 : ℝ)
      linarith
    have hφ : ‖Complex.I * φ w.1 / 2‖ ≤ |φ w.1| := by
      rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat]
      have := abs_nonneg (φ w.1)
      linarith
    have hz1 : ‖z‖ ≤ 1 / 2 + |s.im| + |φ w.1| + |(k w.1 : ℝ)| := by
      calc ‖z‖ ≤ ‖s‖ + (‖Complex.I * φ w.1 / 2‖ + ‖((k w.1).natAbs : ℂ) / 2‖) :=
            norm_add_le_of_le (le_refl _) (norm_add_le _ _)
        _ ≤ (1 / 2 + |s.im|) + (|φ w.1| + |(k w.1 : ℝ)|) := by gcongr
        _ = _ := by ring
    have hz2 : ‖z + 1‖ ≤ 3 / 2 + |s.im| + |φ w.1| + |(k w.1 : ℝ)| := by
      calc ‖z + 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ ≤ (1 / 2 + |s.im| + |φ w.1| + |(k w.1 : ℝ)|) + 1 := by rw [norm_one]; gcongr
        _ = _ := by ring
    have hqw := hq w.1
    exact mul_le_mul (by linarith) (by linarith) (norm_nonneg _) hq0

theorem signShift_re_nonneg (a : ZMod 2) : 0 ≤ (signShift a).re := by
  unfold signShift; split_ifs <;> simp

theorem main (T : Finset (HeightOneSpectrum (𝓞 K))) (𝔣 : Ideal (𝓞 K)) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ), IsIdeleClassChar (𝓞 K) K χ → Continuous χ →
        IsUnitaryChar (𝓞 K) K χ → (∃ x ∈ normOneIdeles K, χ x ≠ 1) →
        HeckeCharacter.AdmitsModulus K χ 𝔣 → (∀ v ∉ T, IsUnramifiedCharAt χ v) →
      ∀ (φ : InfinitePlace K → ℝ) (k : InfinitePlace K → ℤ),
        (∀ (w : InfinitePlace K) (a : (w.Completion)ˣ) (r : ℝ), 0 < r →
            Completion.extensionEmbedding w (a : w.Completion) = (r : ℂ) →
            ((archLocalChar χ w a : ℂˣ) : ℂ) = (r : ℂ) ^ (Complex.I * φ w)) →
        (∀ (w : InfinitePlace K) (a : (w.Completion)ˣ),
            ‖Completion.extensionEmbedding w (a : w.Completion)‖ = 1 →
            ((archLocalChar χ w a : ℂˣ) : ℂ) = (Completion.extensionEmbedding w (a : w.Completion)) ^ (k w)) →
      ∀ (L : ℂ → ℂ), Differentiable ℂ L →
        (∀ s : ℂ, 1 < s.re → L s = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
            (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
              (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) →
      ∀ s : ℂ, s.re = -1 / 2 →
        ‖L s‖ ≤ C * (2 + |s.im| + ∑ w : InfinitePlace K, (|φ w| + |(k w : ℝ)|)) ^ A := by
  set r₁ : ℕ := Fintype.card {w : InfinitePlace K // w.IsReal} with hr₁
  set r₂ : ℕ := Fintype.card {w : InfinitePlace K // w.IsComplex} with hr₂
  refine ⟨Nf 𝔣 * M₁ K * PT T, ((r₁ + 2 * r₂ : ℕ) : ℝ), mul_pos (mul_pos (Nf_pos 𝔣) M₁_pos) (PT_pos T), ?_, ?_⟩
  · have h : r₁ + 2 * r₂ = Module.finrank ℚ K := by
      rw [hr₁, hr₂]
      convert NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
    have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
    exact_mod_cast (h ▸ hpos : 0 < r₁ + 2 * r₂)
  intro χ hχ hχc hχu hχ1 hmod hunr φ k hφ hk L hL hLT s hs

  set uR : ∀ w : InfinitePlace K, w.IsReal → ℂ := fun w _ => Complex.I * φ w with huR
  set aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2 := fun w _ => ((k w : ℤ) : ZMod 2) with haR
  set uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ := fun w _ => Complex.I * φ w / 2 with huC
  set kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ := fun w _ => k w with hkC
  have hR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K χ w (uR w hw) ((aR w hw).val : ℤ) :=
    fun w hw => isArchCompAt_of_isReal χ φ k hφ hk w hw
  have hC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K χ w (uC w hw) (kC w hw) :=
    fun w hw => isArchCompAt_of_isComplex χ φ k hφ hk w hw
  have hadm : IsAdmissibleTwist K χ := ⟨hχ, hχc, hχu⟩
  obtain ⟨hWF, hConv, hNpos, Λ, Λd, hΛ, hΛd, hBΛ, hBΛd, hΛeq, hΛdeq, hFE⟩ :=
    LanglandsTunnell.HeckeTate.isNicePinned_heckeDatum K χ hadm hχ1 uR aR uC kC hR hC
  set D := heckeDatum K χ uR aR uC kC with hD
  have habs : D.abscissa = 1 := rfl
  have hcen : D.center = 1 / 2 := rfl

  have hcoef : ∀ v, ‖coef χ v‖ ≤ 1 := norm_coef_le_one hχu
  have hLid : L = fun z => Λ z * invArch uR aR uC kC z * corr χ T z := by
    refine eq_of_agree_of_one_lt_re L _ hL
      ((hΛ.mul (differentiable_invArch uR aR uC kC)).mul (differentiable_corr χ T)) fun z hz => ?_
    have h1 : Λ z = D.archFactor z * D.LFun z := by
      have := hΛeq z (by rw [habs]; exact hz); simpa using this
    have h2 : D.LFun z = ∏' v : HeightOneSpectrum (𝓞 K), (1 - coef χ v * nC v ^ (-z))⁻¹ := LFun_eq χ uR aR uC kC z
    have h3 : L z = corr χ T z * ∏' v : HeightOneSpectrum (𝓞 K), (1 - coef χ v * nC v ^ (-z))⁻¹ := by
      rw [hLT z hz]; exact tprod_compl_eq hcoef hz T
    have hΓR : ∀ w : {w : InfinitePlace K // w.IsReal}, Gammaℝ (z + μR uR aR w) ≠ 0 := fun w => by
      refine Gammaℝ_ne_zero_of_re_pos ?_
      have := signShift_re_nonneg (aR w.1 w.2)
      simp only [μR, huR, add_re, mul_re, Complex.I_re, Complex.ofReal_re, zero_mul, Complex.I_im,
        Complex.ofReal_im, mul_zero, sub_zero, zero_add]
      linarith
    have hΓC : ∀ w : {w : InfinitePlace K // w.IsComplex}, Gammaℂ (z + μC uC kC w) ≠ 0 := fun w => by
      refine Gammaℂ_ne_zero_of_re_pos ?_
      simp only [μC, huC, add_re, div_re, mul_re, Complex.I_re, Complex.ofReal_re, zero_mul, Complex.I_im,
        Complex.ofReal_im, mul_zero, sub_zero, Complex.natCast_re, Complex.normSq_ofNat, Complex.re_ofNat,
        Complex.natCast_im, Complex.im_ofNat]
      positivity
    have h4 := archFactor_mul_invArch χ uR aR uC kC hΓR hΓC
    show L z = Λ z * invArch uR aR uC kC z * corr χ T z
    rw [h3, h1, h2]
    calc corr χ T z * ∏' v : HeightOneSpectrum (𝓞 K), (1 - coef χ v * nC v ^ (-z))⁻¹
        = (D.archFactor z * invArch uR aR uC kC z) *
            (∏' v : HeightOneSpectrum (𝓞 K), (1 - coef χ v * nC v ^ (-z))⁻¹) * corr χ T z := by
          rw [h4, one_mul, mul_comm]
      _ = _ := by ring

  have h1s : (2 : ℂ) * ((D.center : ℝ) : ℂ) - s = 1 - s := by rw [hcen]; push_cast; ring
  have hre1 : (1 - s).re = 3 / 2 := by simp [hs]; norm_num
  have hFEs : Λ s = heckeRootNumber K χ aR kC * ((heckeConductor K χ : ℝ) : ℂ) ^ (((D.center : ℝ) : ℂ) - s) *
      Λd (1 - s) := by rw [← h1s]; exact hFE s
  have hΛd1 : Λd (1 - s) = D.archFactorDual (1 - s) * D.LFunDual (1 - s) := by
    have := hΛdeq (1 - s) (by rw [habs, hre1]; norm_num); simpa using this
  have hN : ‖((heckeConductor K χ : ℝ) : ℂ) ^ (((D.center : ℝ) : ℂ) - s)‖ = heckeConductor K χ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hNpos, hcen]
    have : ((((1 / 2 : ℝ) : ℂ)) - s).re = 1 := by simp [hs]; norm_num
    rw [this, Real.rpow_one]
  have hW : ‖heckeRootNumber K χ aR kC‖ = 1 := norm_heckeRootNumber χ 𝔣 hmod hχu aR kC
  have hdual : ‖D.LFunDual (1 - s)‖ ≤ M₁ K := by
    rw [LFunDual_eq]
    exact norm_tprod_le (coefD χ) (norm_coefD_le_one hχu) (1 - s) (by rw [hre1])

  set Q : ℝ := ∑ w : InfinitePlace K, (|φ w| + |(k w : ℝ)|) with hQ
  set q : ℝ := 2 + |s.im| + Q with hq
  have hQw : ∀ w : InfinitePlace K, |φ w| + |(k w : ℝ)| ≤ Q := fun w =>
    Finset.single_le_sum (f := fun w => |φ w| + |(k w : ℝ)|) (fun w _ => by positivity) (Finset.mem_univ w)
  have hqw : ∀ w : InfinitePlace K, 2 + |s.im| + |φ w| + |(k w : ℝ)| ≤ q := fun w => by
    have := hQw w; rw [hq]; linarith
  have hq1 : 1 ≤ q := by
    have : 0 ≤ Q := Finset.sum_nonneg fun w _ => by positivity
    have := abs_nonneg s.im; rw [hq]; linarith
  have harch := arch_ratio_le φ k s hs q (by linarith) hqw
  rw [← archFactorDual_eq χ uR aR uC kC (1 - s)] at harch

  have hLs : L s = Λ s * invArch uR aR uC kC s * corr χ T s := congrFun hLid s
  have hcorr : ‖corr χ T s‖ ≤ PT T := norm_corr_le hχu T (by rw [hs])
  have hcond : heckeConductor K χ ≤ Nf 𝔣 := heckeConductor_le χ 𝔣 hmod
  have hpow : q ^ r₁ * (q * q) ^ r₂ = q ^ (((r₁ + 2 * r₂ : ℕ) : ℝ)) := by
    rw [Real.rpow_natCast, pow_add, pow_mul, sq]
  have hA : heckeConductor K χ * ‖D.LFunDual (1 - s)‖ ≤ Nf 𝔣 * M₁ K :=
    mul_le_mul hcond hdual (norm_nonneg _) (Nf_pos 𝔣).le
  have hq0 : 0 ≤ q := by linarith
  calc ‖L s‖ = ‖Λ s‖ * ‖invArch uR aR uC kC s‖ * ‖corr χ T s‖ := by rw [hLs, norm_mul, norm_mul]
    _ = heckeConductor K χ * ‖D.LFunDual (1 - s)‖ *
          (‖D.archFactorDual (1 - s)‖ * ‖invArch uR aR uC kC s‖) * ‖corr χ T s‖ := by
        rw [hFEs, hΛd1, norm_mul, norm_mul, norm_mul, hW, hN, one_mul]; ring
    _ ≤ Nf 𝔣 * M₁ K * (q ^ r₁ * (q * q) ^ r₂) * PT T := by
        refine mul_le_mul (mul_le_mul hA harch (by positivity) (mul_pos (Nf_pos 𝔣) M₁_pos).le) hcorr
          (norm_nonneg _) ?_
        exact mul_nonneg (mul_pos (Nf_pos 𝔣) M₁_pos).le (by positivity)
    _ = Nf 𝔣 * M₁ K * PT T * q ^ (((r₁ + 2 * r₂ : ℕ) : ℝ)) := by rw [hpow]; ring

end main

end R4G2b

end

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal NumberField.InfinitePlace in
open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (T : Finset (HeightOneSpectrum (𝓞 K))) (𝔣 : Ideal (𝓞 K)) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ), IsIdeleClassChar (𝓞 K) K χ → Continuous χ →
        IsUnitaryChar (𝓞 K) K χ → (∃ x ∈ normOneIdeles K, χ x ≠ 1) →
        HeckeCharacter.AdmitsModulus K χ 𝔣 → (∀ v ∉ T, IsUnramifiedCharAt χ v) →
      ∀ (φ : InfinitePlace K → ℝ) (k : InfinitePlace K → ℤ),
        (∀ (w : InfinitePlace K) (a : (w.Completion)ˣ) (r : ℝ), 0 < r →
            Completion.extensionEmbedding w (a : w.Completion) = (r : ℂ) →
            ((archLocalChar χ w a : ℂˣ) : ℂ) = (r : ℂ) ^ (Complex.I * φ w)) →
        (∀ (w : InfinitePlace K) (a : (w.Completion)ˣ),
            ‖Completion.extensionEmbedding w (a : w.Completion)‖ = 1 →
            ((archLocalChar χ w a : ℂˣ) : ℂ) = (Completion.extensionEmbedding w (a : w.Completion)) ^ (k w)) →
      ∀ (L : ℂ → ℂ), Differentiable ℂ L →
        (∀ s : ℂ, 1 < s.re → L s = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
            (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
              (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) →
      ∀ s : ℂ, s.re = -1 / 2 →
        ‖L s‖ ≤ C * (2 + |s.im| + ∑ w : InfinitePlace K, (|φ w| + |(k w : ℝ)|)) ^ A :=
  R4G2b.main T 𝔣

end S_NumberField_TateGlobal_exists_forall_norm_partialEulerProduct_continuation_le_rpow_on_re_eq_neg_half_of_admitsModulus
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_forall_norm_partialEulerProduct_continuation_le_rpow_on_re_eq_neg_half_of_admitsModulus (solution)
