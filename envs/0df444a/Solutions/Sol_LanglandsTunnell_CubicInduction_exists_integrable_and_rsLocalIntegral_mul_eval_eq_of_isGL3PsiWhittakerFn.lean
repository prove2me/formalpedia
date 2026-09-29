-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/7cf89169-2ab3-5811-9136-163bb1dab86f

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_Completion_Finite
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_apply_iotaGL_diagZ_mul_scalarPi_zpow_eq_sum_of_isGL3PsiWhittakerFn
import Theorems.Thm_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral
import Theorems.Thm_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out
import Theorems.Thm_HaarQuotient_lintegral_density_mul_eq_one
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RankinSelberg.hasSum_cell_terms_rsLocalIntegral TateLocal.addCharLevel_psiLocal_rat TateLocal.psiLocal_ne_one TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel TateLocal.psiLocal_eq_one_of_mem_integers TateLocal.modulus_adicCompletion_eq_nnnorm"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply gl3CyclicSubspace transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL iotaGL_unipotentGL2 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply exists_forall_apply_iotaGL_diagZ_mul_scalarPi_zpow_eq_sum_of_isGL3PsiWhittakerFn"
namespace LocalPairingSeries
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private abbrev G2 (v : HeightOneSpectrum (𝓞 ℚ)) : Type := GL (Fin 2) (v.adicCompletion ℚ)

private abbrev unif (v : HeightOneSpectrum (𝓞 ℚ)) (ϖ : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ :=
  algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ

private abbrev Nr (v : HeightOneSpectrum (𝓞 ℚ)) : Subgroup (G2 v) :=
  (unipotentGL2Hom (R := v.adicCompletion ℚ)).range

private abbrev Kmax (v : HeightOneSpectrum (𝓞 ℚ)) : Subgroup (G2 v) := AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤

private abbrev tor (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ} (hπ : unif v ϖ ≠ 0)
    (p : ℤ × ℤ) : G2 v :=
  diagZ (unif v ϖ) hπ (p.1 - p.2) * scalarPi (unif v ϖ) hπ ^ p.2

private abbrev detModulus (v : HeightOneSpectrum (𝓞 ℚ)) (g : G2 v) : ℝ :=
  (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ)

private abbrev wMeasure (v : HeightOneSpectrum (𝓞 ℚ)) [MeasurableSpace (G2 v)] (μ₂ : Measure (G2 v))
    (μN : Measure (Nr v)) : Measure (G2 v) :=
  μ₂.withDensity (HaarQuotient.density (Nr v) μN)

private abbrev cellOne (v : HeightOneSpectrum (𝓞 ℚ)) : Set (G2 v) :=
  {g : G2 v | ∃ n ∈ Nr v, ∃ k ∈ Kmax v, g = n * k}

private abbrev cellTerm (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ} (hπ : unif v ϖ ≠ 0)
    (vol : ℂ) (δ : G2 v → ℝ) (s : ℂ) (W F : G2 v → ℂ) (p : ℤ × ℤ) : ℂ :=
  vol * ((Ideal.absNorm v.asIdeal : ℂ) ^ (p.1 - p.2)) *
    ((W (tor v hπ p) * F (tor v hπ p)) * ((δ (tor v hπ p) : ℝ) : ℂ) ^ (s - 1 / 2))

end LanglandsTunnell.CubicInduction.LocalPairingSeries

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RankinSelberg.hasSum_cell_terms_rsLocalIntegral TateLocal.addCharLevel_psiLocal_rat TateLocal.psiLocal_ne_one TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel TateLocal.psiLocal_eq_one_of_mem_integers TateLocal.modulus_adicCompletion_eq_nnnorm"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply gl3CyclicSubspace transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL iotaGL_unipotentGL2 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply exists_forall_apply_iotaGL_diagZ_mul_scalarPi_zpow_eq_sum_of_isGL3PsiWhittakerFn"
namespace LocalPairingSeries
namespace TorusConj
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable {K : Type*} [Field K]

private theorem diagZ_coe (π : K) (hπ : π ≠ 0) (m : ℤ) :
    (UnramifiedWhittaker.diagZ π hπ m : Matrix (Fin 2) (Fin 2) K) = !![π ^ m, 0; 0, 1] := rfl

private theorem scalarPi_coe (π : K) (hπ : π ≠ 0) :
    (UnramifiedWhittaker.scalarPi π hπ : Matrix (Fin 2) (Fin 2) K) = !![π, 0; 0, π] := rfl

private theorem diagZ_mul_unipotentGL2 (π : K) (hπ : π ≠ 0) (m : ℤ) (x : K) :
    UnramifiedWhittaker.diagZ π hπ m * AutomorphicForm.unipotentGL2 x =
      AutomorphicForm.unipotentGL2 (π ^ m * x) * UnramifiedWhittaker.diagZ π hπ m := by
  apply Units.ext
  simp only [Units.val_mul, diagZ_coe, AutomorphicForm.unipotentGL2_coe]
  simp

private theorem scalarPi_commute_unipotentGL2 (π : K) (hπ : π ≠ 0) (x : K) :
    Commute (UnramifiedWhittaker.scalarPi π hπ) (AutomorphicForm.unipotentGL2 x) := by
  apply Units.ext
  simp only [Units.val_mul, scalarPi_coe, AutomorphicForm.unipotentGL2_coe]
  simp [mul_comm]

private theorem torus_mul_unipotentGL2 (π : K) (hπ : π ≠ 0) (p : ℤ × ℤ) (x : K) :
    UnramifiedWhittaker.diagZ π hπ (p.1 - p.2) * UnramifiedWhittaker.scalarPi π hπ ^ p.2 *
        AutomorphicForm.unipotentGL2 x =
      AutomorphicForm.unipotentGL2 (π ^ (p.1 - p.2) * x) *
        (UnramifiedWhittaker.diagZ π hπ (p.1 - p.2) * UnramifiedWhittaker.scalarPi π hπ ^ p.2) := by
  have hc : Commute (UnramifiedWhittaker.scalarPi π hπ ^ p.2) (AutomorphicForm.unipotentGL2 x) :=
    (scalarPi_commute_unipotentGL2 π hπ x).zpow_left p.2
  calc UnramifiedWhittaker.diagZ π hπ (p.1 - p.2) * UnramifiedWhittaker.scalarPi π hπ ^ p.2 *
          AutomorphicForm.unipotentGL2 x
      = UnramifiedWhittaker.diagZ π hπ (p.1 - p.2) *
          (AutomorphicForm.unipotentGL2 x * UnramifiedWhittaker.scalarPi π hπ ^ p.2) := by
        rw [mul_assoc, hc.eq]
    _ = (UnramifiedWhittaker.diagZ π hπ (p.1 - p.2) * AutomorphicForm.unipotentGL2 x) *
          UnramifiedWhittaker.scalarPi π hπ ^ p.2 := by
        rw [mul_assoc]
    _ = AutomorphicForm.unipotentGL2 (π ^ (p.1 - p.2) * x) *
          (UnramifiedWhittaker.diagZ π hπ (p.1 - p.2) * UnramifiedWhittaker.scalarPi π hπ ^ p.2) := by
        rw [diagZ_mul_unipotentGL2, mul_assoc]

private theorem scalarPi_pow_coe (π : K) (hπ : π ≠ 0) (n : ℕ) :
    ((UnramifiedWhittaker.scalarPi π hπ ^ n : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![π ^ n, 0; 0, π ^ n] := by
  induction n with
  | zero => simp [Matrix.one_fin_two]
  | succ n ih =>
    rw [pow_succ, Units.val_mul, ih, scalarPi_coe]
    simp [pow_succ]

private theorem scalarPi_inv (π : K) (hπ : π ≠ 0) :
    (UnramifiedWhittaker.scalarPi π hπ)⁻¹ = UnramifiedWhittaker.scalarPi π⁻¹ (inv_ne_zero hπ) := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  rw [Units.val_mul, scalarPi_coe, scalarPi_coe, Units.val_one]
  simp [mul_inv_cancel₀ hπ, Matrix.one_fin_two]

private theorem scalarPi_zpow_coe (π : K) (hπ : π ≠ 0) (m : ℤ) :
    ((UnramifiedWhittaker.scalarPi π hπ ^ m : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![π ^ m, 0; 0, π ^ m] := by
  cases m with
  | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast, scalarPi_pow_coe]; simp
  | negSucc n =>
    rw [zpow_negSucc, ← inv_pow, scalarPi_inv, scalarPi_pow_coe]
    simp [zpow_negSucc, inv_pow]

private theorem torus_coe (π : K) (hπ : π ≠ 0) (m₁ m₂ : ℤ) :
    ((UnramifiedWhittaker.diagZ π hπ (m₁ - m₂) * UnramifiedWhittaker.scalarPi π hπ ^ m₂ :
        GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![π ^ m₁, 0; 0, π ^ m₂] := by
  have h : π ^ (m₁ - m₂) * π ^ m₂ = π ^ m₁ := by rw [← zpow_add₀ hπ, sub_add_cancel]
  rw [Units.val_mul, diagZ_coe, scalarPi_zpow_coe]
  simp [h]

private theorem torus_coe_pair (π : K) (hπ : π ≠ 0) (p : ℤ × ℤ) :
    ((UnramifiedWhittaker.diagZ π hπ (p.1 - p.2) * UnramifiedWhittaker.scalarPi π hπ ^ p.2 :
        GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![π ^ p.1, 0; 0, π ^ p.2] :=
  torus_coe π hπ p.1 p.2

section Disjoint

open scoped WithZero

variable {F : Type*} [Field F] [Valued F ℤᵐ⁰]

private theorem valued_zpow_of_uniformizer {π : F} (hπ1 : Valued.v π = WithZero.exp (-1 : ℤ)) (m : ℤ) :
    Valued.v (π ^ m) = WithZero.exp (-m) := by
  rw [map_zpow₀, hπ1, ← WithZero.exp_zsmul]
  simp

private theorem mul_max_eq (c a b : ℤᵐ⁰) : max (c * a) (c * b) = c * max a b := by
  have hm : Monotone (fun t : ℤᵐ⁰ => c * t) := fun _ _ h => mul_le_mul_right h c
  exact (Monotone.map_max hm).symm

private theorem max_bottom_row_eq_one (k : Matrix (Fin 2) (Fin 2) F)
    (hk : ∀ i j, Valued.v (k i j) ≤ 1) (hdet : Valued.v k.det = 1) :
    max (Valued.v (k 1 0)) (Valued.v (k 1 1)) = 1 := by
  refine le_antisymm (max_le (hk 1 0) (hk 1 1)) ?_
  by_contra hlt
  rw [not_le, max_lt_iff] at hlt
  obtain ⟨h10, h11⟩ := hlt
  have h00 := hk 0 0
  have h01 := hk 0 1
  have h1 : Valued.v (k 0 0 * k 1 1) < 1 := by
    rw [map_mul]
    calc Valued.v (k 0 0) * Valued.v (k 1 1) ≤ 1 * Valued.v (k 1 1) := by gcongr
      _ < 1 := by rw [one_mul]; exact h11
  have h2 : Valued.v (k 0 1 * k 1 0) < 1 := by
    rw [map_mul]
    calc Valued.v (k 0 1) * Valued.v (k 1 0) ≤ 1 * Valued.v (k 1 0) := by gcongr
      _ < 1 := by rw [one_mul]; exact h10
  have hd : Valued.v k.det < 1 := by
    rw [Matrix.det_fin_two]
    exact lt_of_le_of_lt (Valued.v.map_sub _ _) (max_lt h1 h2)
  rw [hdet] at hd
  exact lt_irrefl _ hd

variable (π : F) (hπ : π ≠ 0)

omit [Valued F ℤᵐ⁰] in

private theorem cell_bottom_row (p : ℤ × ℤ) (x : F) (k : GL (Fin 2) F) (j : Fin 2) :
    ((AutomorphicForm.unipotentGL2 x *
        (UnramifiedWhittaker.diagZ π hπ (p.1 - p.2) * UnramifiedWhittaker.scalarPi π hπ ^ p.2) * k :
        GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j =
      π ^ p.2 * (k : Matrix (Fin 2) (Fin 2) F) 1 j := by
  rw [Units.val_mul, Units.val_mul, AutomorphicForm.unipotentGL2_coe, torus_coe_pair]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem valued_det_cell (hπ1 : Valued.v π = WithZero.exp (-1 : ℤ)) (p : ℤ × ℤ) (x : F) (k : GL (Fin 2) F)
    (hdet : Valued.v (k : Matrix (Fin 2) (Fin 2) F).det = 1) :
    Valued.v ((AutomorphicForm.unipotentGL2 x *
        (UnramifiedWhittaker.diagZ π hπ (p.1 - p.2) * UnramifiedWhittaker.scalarPi π hπ ^ p.2) * k :
        GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = WithZero.exp (-(p.1 + p.2)) := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, AutomorphicForm.unipotentGL2_coe,
    torus_coe_pair, map_mul, map_mul, hdet]
  simp only [Matrix.det_fin_two_of, mul_zero, sub_zero, mul_one, one_mul, map_mul, map_one,
    valued_zpow_of_uniformizer hπ1, ← WithZero.exp_add, neg_add]

private theorem max_valued_bottom_row_cell (hπ1 : Valued.v π = WithZero.exp (-1 : ℤ)) (p : ℤ × ℤ) (x : F)
    (k : GL (Fin 2) F) (hk : ∀ i j, Valued.v ((k : Matrix (Fin 2) (Fin 2) F) i j) ≤ 1)
    (hdet : Valued.v (k : Matrix (Fin 2) (Fin 2) F).det = 1) :
    max (Valued.v (((AutomorphicForm.unipotentGL2 x *
          (UnramifiedWhittaker.diagZ π hπ (p.1 - p.2) * UnramifiedWhittaker.scalarPi π hπ ^ p.2) * k :
          GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0))
        (Valued.v (((AutomorphicForm.unipotentGL2 x *
          (UnramifiedWhittaker.diagZ π hπ (p.1 - p.2) * UnramifiedWhittaker.scalarPi π hπ ^ p.2) * k :
          GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1)) =
      WithZero.exp (-p.2) := by
  rw [cell_bottom_row, cell_bottom_row, map_mul, map_mul, mul_max_eq, max_bottom_row_eq_one _ hk hdet,
    mul_one, valued_zpow_of_uniformizer hπ1]

private theorem cell_index_eq (hπ1 : Valued.v π = WithZero.exp (-1 : ℤ)) {p p' : ℤ × ℤ} {x x' : F}
    {k k' : GL (Fin 2) F} (hk : ∀ i j, Valued.v ((k : Matrix (Fin 2) (Fin 2) F) i j) ≤ 1)
    (hdet : Valued.v (k : Matrix (Fin 2) (Fin 2) F).det = 1)
    (hk' : ∀ i j, Valued.v ((k' : Matrix (Fin 2) (Fin 2) F) i j) ≤ 1)
    (hdet' : Valued.v (k' : Matrix (Fin 2) (Fin 2) F).det = 1)
    (h : AutomorphicForm.unipotentGL2 x *
          (UnramifiedWhittaker.diagZ π hπ (p.1 - p.2) * UnramifiedWhittaker.scalarPi π hπ ^ p.2) * k =
        AutomorphicForm.unipotentGL2 x' *
          (UnramifiedWhittaker.diagZ π hπ (p'.1 - p'.2) * UnramifiedWhittaker.scalarPi π hπ ^ p'.2) * k') :
    p = p' := by
  have h1 := valued_det_cell π hπ hπ1 p x k hdet
  have h2 := max_valued_bottom_row_cell π hπ hπ1 p x k hk hdet
  rw [h] at h1 h2
  rw [valued_det_cell π hπ hπ1 p' x' k' hdet', WithZero.exp_inj] at h1
  rw [max_valued_bottom_row_cell π hπ hπ1 p' x' k' hk' hdet', WithZero.exp_inj] at h2
  exact Prod.ext (by omega) (by omega)

end Disjoint

section Factorisation

open scoped WithZero
open IsDedekindDomain NumberField

variable {v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)}

private theorem exists_zpow_mul_unit {ϖ : v.adicCompletion ℚ} (hϖ1 : Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (x : v.adicCompletion ℚ) (hx : x ≠ 0) :
    ∃ (m : ℤ) (u : (v.adicCompletionIntegers ℚ)ˣ),
      x = ϖ ^ m * ((u : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) := by
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hϖ1
    exact WithZero.exp_ne_zero hϖ1.symm
  have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  set m : ℤ := -WithZero.log (Valued.v x) with hm
  have hpow : Valued.v (ϖ ^ m) = Valued.v x := by
    rw [map_zpow₀, hϖ1, ← WithZero.exp_zsmul, ← WithZero.exp_log hvx]
    congr 1
    rw [hm]
    simp
  have hpow0 : ϖ ^ m ≠ 0 := zpow_ne_zero m hϖ0
  set w : v.adicCompletion ℚ := x / ϖ ^ m with hw
  have hvw : Valued.v w = 1 := by
    rw [hw, map_div₀, hpow, div_self hvx]
  have hwmem : w ∈ v.adicCompletionIntegers ℚ := by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, hvw]
  have hunit : IsUnit (⟨w, hwmem⟩ : v.adicCompletionIntegers ℚ) :=
    IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hvw
  obtain ⟨u, hu⟩ := hunit
  refine ⟨m, u, ?_⟩
  rw [hu]
  show x = ϖ ^ m * w
  rw [hw, mul_div_cancel₀ x hpow0]

end Factorisation

end LanglandsTunnell.CubicInduction.LocalPairingSeries.TorusConj

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RankinSelberg.hasSum_cell_terms_rsLocalIntegral TateLocal.addCharLevel_psiLocal_rat TateLocal.psiLocal_ne_one TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel TateLocal.psiLocal_eq_one_of_mem_integers TateLocal.modulus_adicCompletion_eq_nnnorm"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply gl3CyclicSubspace transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL iotaGL_unipotentGL2 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply exists_forall_apply_iotaGL_diagZ_mul_scalarPi_zpow_eq_sum_of_isGL3PsiWhittakerFn"
namespace LocalPairingSeries
namespace UnipotentMass
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open IsDedekindDomain NumberField
open scoped WithZero

open MeasureTheory Matrix AutomorphicForm
open scoped ENNReal Pointwise

section Entry

variable {F : Type*} [Field F]

set_option quotPrecheck false in
local notation "N" => (AutomorphicForm.unipotentGL2Hom (R := F)).range

private def entry (n : N) : F := ((n : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1

private theorem unipotentGL2_mem (x : F) : unipotentGL2 x ∈ N := ⟨Multiplicative.ofAdd x, rfl⟩

private def up (x : F) : N := ⟨unipotentGL2 x, unipotentGL2_mem x⟩

@[scoped simp] private theorem entry_up (x : F) : entry (up x) = x := by
  simp [entry, up]

private theorem up_entry (n : N) : up (entry n) = n := by
  obtain ⟨g, y, rfl⟩ := n
  apply Subtype.ext
  show unipotentGL2 _ = unipotentGL2Hom y
  simp only [entry]
  rfl

private theorem entry_injective : Function.Injective (entry (F := F)) := fun n m h => by
  rw [← up_entry n, ← up_entry m, h]

private theorem up_add (x y : F) : up (x + y) = up x * up y :=
  Subtype.ext (unipotentGL2_add x y)

private theorem entry_mul (n m : N) : entry (n * m) = entry n + entry m := by
  rw [← up_entry n, ← up_entry m, ← up_add, entry_up, entry_up, entry_up]

variable [TopologicalSpace F]

private theorem continuous_entry : Continuous (entry (F := F)) :=
  (Units.continuous_val.comp continuous_subtype_val).matrix_elem 0 1

variable [IsTopologicalRing F]

private theorem continuous_unipotentGL2 : Continuous (unipotentGL2 (R := F)) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2] <;> fun_prop

private theorem continuous_up : Continuous (up (F := F)) :=
  continuous_unipotentGL2.subtype_mk _

private def upHomeomorph : F ≃ₜ N where
  toFun := up
  invFun := entry
  left_inv := entry_up
  right_inv := up_entry
  continuous_toFun := continuous_up
  continuous_invFun := continuous_entry

private def scaleEntry (a : F) (ha : a ≠ 0) : N ≃ₜ* N where
  toFun n := up (a * entry n)
  invFun n := up (a⁻¹ * entry n)
  left_inv n := by simp [ha, up_entry]
  right_inv n := by simp [ha, up_entry]
  map_mul' n m := by
    rw [entry_mul, mul_add, up_add]
  continuous_toFun := continuous_up.comp (continuous_const.mul continuous_entry)
  continuous_invFun := continuous_up.comp (continuous_const.mul continuous_entry)

@[scoped simp] private theorem scaleEntry_apply (a : F) (ha : a ≠ 0) (n : N) : scaleEntry a ha n = up (a * entry n) := rfl

private theorem entry_scaleEntry (a : F) (ha : a ≠ 0) (n : N) : entry (scaleEntry a ha n) = a * entry n := by
  simp

end Entry

section Generic

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

private theorem map_eq_smul_of_conj (μX : Measure X) (μY : Measure Y) {e : X → Y} (he : Measurable e)
    (hμY : μX.map e = μY)
    {ψ : X → X} (hψ : Measurable ψ) {φ : Y → Y} (hφ : Measurable φ) (hconj : φ ∘ e = e ∘ ψ) (c : ℝ≥0∞)
    (hscale : μX.map ψ = c • μX) : μY.map φ = c • μY := by
  rw [← hμY, Measure.map_map hφ he, hconj, ← Measure.map_map he hψ, hscale, Measure.map_smul]

end Generic

section GenericGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

private theorem map_eq_smul_of_apply (μ : Measure G) [μ.IsHaarMeasure] (φ : G ≃ₜ* G) {U : Set G} (hU : MeasurableSet U)
    (hU0 : μ U ≠ 0) (hUtop : μ U ≠ ⊤) (c : ℝ≥0∞) (hc : μ ((φ : G → G) ⁻¹' U) = c * μ U) :
    μ.map (φ : G → G) = c • μ := by
  haveI : (μ.map (φ : G → G)).IsHaarMeasure := φ.isHaarMeasure_map μ
  have hφm : Measurable (φ : G → G) := φ.continuous.measurable
  have hd : μ.map (φ : G → G) = (((μ.map (φ : G → G)).haarScalarFactor μ : NNReal) : ℝ≥0∞) • μ :=
    Measure.isMulLeftInvariant_eq_smul _ μ
  have hmapU : (μ.map (φ : G → G)) U = c * μ U := by
    rw [Measure.map_apply hφm hU, hc]
  rw [hd, Measure.smul_apply, smul_eq_mul] at hmapU
  have hdc : ((((μ.map (φ : G → G)).haarScalarFactor μ : NNReal)) : ℝ≥0∞) = c :=
    (ENNReal.mul_left_inj hU0 hUtop).mp hmapU
  rw [hd, hdc]

end GenericGroup

end LanglandsTunnell.CubicInduction.LocalPairingSeries.UnipotentMass
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries.UnipotentMass"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RankinSelberg.hasSum_cell_terms_rsLocalIntegral TateLocal.addCharLevel_psiLocal_rat TateLocal.psiLocal_ne_one TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel TateLocal.psiLocal_eq_one_of_mem_integers TateLocal.modulus_adicCompletion_eq_nnnorm"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply gl3CyclicSubspace transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL iotaGL_unipotentGL2 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply exists_forall_apply_iotaGL_diagZ_mul_scalarPi_zpow_eq_sum_of_isGL3PsiWhittakerFn"
namespace LocalPairingSeries
namespace IwasawaCover
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open Matrix NumberField

variable {F : Type*} [Field F] (O : ValuationSubring F)

private def IsIntegralUnit (k : GL (Fin 2) F) : Prop :=
  (∀ i j, (k : Matrix (Fin 2) (Fin 2) F) i j ∈ O) ∧ ∀ i j, ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j ∈ O

variable {O}

private def mkUnit (m n : Matrix (Fin 2) (Fin 2) F) (h₁ : m * n = 1) (h₂ : n * m = 1) : GL (Fin 2) F :=
  ⟨m, n, h₁, h₂⟩

private theorem mkUnit_coe (m n : Matrix (Fin 2) (Fin 2) F) (h₁ : m * n = 1) (h₂ : n * m = 1) :
    ((mkUnit m n h₁ h₂ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = m := rfl

private theorem mkUnit_inv_coe (m n : Matrix (Fin 2) (Fin 2) F) (h₁ : m * n = 1) (h₂ : n * m = 1) :
    (((mkUnit m n h₁ h₂)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = n := rfl

private def shear (y : F) : GL (Fin 2) F :=
  mkUnit !![1, 0; y, 1] !![1, 0; -y, 1]
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two])
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two])

private theorem shear_isIntegralUnit {y : F} (hy : y ∈ O) : IsIntegralUnit O (shear y) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · simp only [shear, mkUnit_coe]
    fin_cases i <;> fin_cases j <;> simp [hy]
  · simp only [shear, mkUnit_inv_coe]
    fin_cases i <;> fin_cases j <;> simp [neg_mem hy]

private def swap : GL (Fin 2) F :=
  mkUnit !![0, 1; 1, 0] !![0, 1; 1, 0]
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two])
    (by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two])

private theorem swap_isIntegralUnit : IsIntegralUnit O (swap (F := F)) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · simp only [swap, mkUnit_coe]
    fin_cases i <;> fin_cases j <;> simp
  · simp only [swap, mkUnit_inv_coe]
    fin_cases i <;> fin_cases j <;> simp

private def diagUnits (u₁ u₂ : Oˣ) : GL (Fin 2) F :=
  mkUnit !![((u₁ : O) : F), 0; 0, ((u₂ : O) : F)] !![((u₁⁻¹ : Oˣ) : O), 0; 0, ((u₂⁻¹ : Oˣ) : O)]
    (by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        first
        | exact_mod_cast (congrArg (fun x : O => (x : F)) (Units.mul_inv u₁))
        | exact_mod_cast (congrArg (fun x : O => (x : F)) (Units.mul_inv u₂)))
    (by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        first
        | exact_mod_cast (congrArg (fun x : O => (x : F)) (Units.inv_mul u₁))
        | exact_mod_cast (congrArg (fun x : O => (x : F)) (Units.inv_mul u₂)))

private theorem diagUnits_isIntegralUnit (u₁ u₂ : Oˣ) : IsIntegralUnit O (diagUnits u₁ u₂) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · simp only [diagUnits, mkUnit_coe]
    fin_cases i <;> fin_cases j <;> simp
  · simp only [diagUnits, mkUnit_inv_coe]
    fin_cases i <;> fin_cases j <;> simp

private theorem isOpen_setOf_isIntegralUnit [TopologicalSpace F] [IsTopologicalRing F] (hO : IsOpen (O : Set F)) :
    IsOpen {k : GL (Fin 2) F | IsIntegralUnit O k} := by
  have h1 : ∀ i j : Fin 2, IsOpen {k : GL (Fin 2) F | (k : Matrix (Fin 2) (Fin 2) F) i j ∈ O} := fun i j =>
    hO.preimage (Units.continuous_val.matrix_elem i j)
  have h2 : ∀ i j : Fin 2, IsOpen {k : GL (Fin 2) F | ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j ∈ O} :=
    fun i j => hO.preimage (Units.continuous_coe_inv.matrix_elem i j)
  have hset : {k : GL (Fin 2) F | IsIntegralUnit O k} =
      (⋂ i, ⋂ j, {k : GL (Fin 2) F | (k : Matrix (Fin 2) (Fin 2) F) i j ∈ O}) ∩
        ⋂ i, ⋂ j, {k : GL (Fin 2) F | ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j ∈ O} := by
    ext k
    simp only [IsIntegralUnit, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hset]
  exact (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => h1 i j).inter
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => h2 i j)

private theorem det_mem {m : Matrix (Fin 2) (Fin 2) F} (hm : ∀ i j, m i j ∈ O) : m.det ∈ O := by
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem (hm 0 0) (hm 1 1)) (mul_mem (hm 0 1) (hm 1 0))

private theorem det_mul_det_inv (k : GL (Fin 2) F) :
    (k : Matrix (Fin 2) (Fin 2) F).det * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]

private theorem eq_one_of_mul_eq_one_of_le_one {Γ : Type*} [LinearOrderedCommMonoidWithZero Γ] {a b : Γ} (ha : a ≤ 1)
    (hb : b ≤ 1) (hab : a * b = 1) : a = 1 :=
  le_antisymm ha (by calc (1 : Γ) = a * b := hab.symm
    _ ≤ a * 1 := mul_le_mul_right hb a
    _ = a := mul_one a)

section Cover

variable (O)

private theorem exists_triangular (K : Subgroup (GL (Fin 2) F)) (hK : ∀ k, k ∈ K ↔ IsIntegralUnit O k)
    (g : GL (Fin 2) F) :
    ∃ k₁ ∈ K, ∃ α β δ : F, α ≠ 0 ∧ δ ≠ 0 ∧ ((g * k₁ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![α, β; 0, δ] := by
  set a : F := (g : Matrix (Fin 2) (Fin 2) F) 0 0 with ha
  set b : F := (g : Matrix (Fin 2) (Fin 2) F) 0 1 with hb
  set c : F := (g : Matrix (Fin 2) (Fin 2) F) 1 0 with hc
  set d : F := (g : Matrix (Fin 2) (Fin 2) F) 1 1 with hd
  have hg : (g : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] := Matrix.eta_fin_two _
  have hdet : a * d - b * c ≠ 0 := by
    have h := (Matrix.isUnits_det_units g).ne_zero
    rwa [hg, Matrix.det_fin_two_of] at h
  by_cases hd0 : d = 0
  ·
    have hc0 : c ≠ 0 := by
      intro hc0
      apply hdet
      rw [hd0, hc0]
      ring
    have hb0 : b ≠ 0 := by
      intro hb0
      apply hdet
      rw [hd0, hb0]
      ring
    refine ⟨swap, (hK _).mpr swap_isIntegralUnit, b, a, c, hb0, hc0, ?_⟩
    rw [Units.val_mul, hg, hd0]
    simp only [swap, mkUnit_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · by_cases hcd : c / d ∈ O
    ·
      refine ⟨shear (-(c / d)), (hK _).mpr (shear_isIntegralUnit (neg_mem hcd)), a - b * (c / d), b, d, ?_, hd0, ?_⟩
      · intro h0
        apply hdet
        have : a - b * (c / d) = (a * d - b * c) / d := by
          field_simp
        rw [this, div_eq_zero_iff] at h0
        exact h0.resolve_right hd0
      · rw [Units.val_mul, hg]
        simp only [shear, mkUnit_coe]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
    ·
      have hdc : (c / d)⁻¹ ∈ O := (O.mem_or_inv_mem (c / d)).resolve_left hcd
      have hc0 : c ≠ 0 := by
        intro hc0
        apply hcd
        rw [hc0, zero_div]
        exact zero_mem _
      rw [inv_div] at hdc
      refine ⟨swap * shear (-(d / c)), K.mul_mem ((hK _).mpr swap_isIntegralUnit)
        ((hK _).mpr (shear_isIntegralUnit (neg_mem hdc))), b - a * (d / c), a, c, ?_, hc0, ?_⟩
      · intro h0
        apply hdet
        have : b - a * (d / c) = -(a * d - b * c) / c := by
          field_simp
          ring
        rw [this, div_eq_zero_iff, neg_eq_zero] at h0
        exact h0.resolve_right hc0
      · rw [← mul_assoc, Units.val_mul, Units.val_mul, hg]
        simp only [swap, shear, mkUnit_coe]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

private theorem exists_cover (K : Subgroup (GL (Fin 2) F)) (hK : ∀ k, k ∈ K ↔ IsIntegralUnit O k) {ϖ : F}
    (hfac : ∀ x : F, x ≠ 0 → ∃ (m : ℤ) (u : Oˣ), x = ϖ ^ m * ((u : O) : F)) (g : GL (Fin 2) F) :
    ∃ (x : F) (m : ℤ × ℤ) (k : GL (Fin 2) F), k ∈ K ∧
      (g : Matrix (Fin 2) (Fin 2) F) =
        !![1, x; 0, 1] * !![ϖ ^ m.1, 0; 0, ϖ ^ m.2] * (k : Matrix (Fin 2) (Fin 2) F) := by
  obtain ⟨k₁, hk₁, α, β, δ, hα, hδ, htri⟩ := exists_triangular O K hK g
  obtain ⟨m₁, u₁, hu₁⟩ := hfac α hα
  obtain ⟨m₂, u₂, hu₂⟩ := hfac δ hδ
  refine ⟨β / δ, (m₁, m₂), diagUnits u₁ u₂ * k₁⁻¹,
    K.mul_mem ((hK _).mpr (diagUnits_isIntegralUnit u₁ u₂)) (K.inv_mem hk₁), ?_⟩

  have hfactor : !![α, β; 0, δ] =
      !![1, β / δ; 0, 1] * !![ϖ ^ m₁, 0; 0, ϖ ^ m₂] *
        ((diagUnits u₁ u₂ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    have hϖ₂ : ϖ ^ m₂ ≠ 0 := left_ne_zero_of_mul (hu₂ ▸ hδ)
    simp only [diagUnits, mkUnit_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hu₁, hu₂]
    field_simp
  have hg : (g : Matrix (Fin 2) (Fin 2) F) =
      ((g * k₁ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * ((k₁⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    rw [← Units.val_mul, mul_inv_cancel_right]
  rw [hg, htri, hfactor, Units.val_mul, Matrix.mul_assoc]

end Cover
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries.UnipotentMass"

section Bench

open IsDedekindDomain AdelicDock

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem isLocalLevelOne_top_iff (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :
    IsLocalLevelOne (𝓞 ℚ) ℚ v ⊤ m ↔ ∀ i j, m i j ∈ v.adicCompletionIntegers ℚ := by
  refine ⟨fun h => h.integral, fun h => ⟨h, ?_, ?_⟩⟩
  · rw [AdelicLevel.idealBound_top]
    have := h 1 0
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at this
  · rw [AdelicLevel.idealBound_top]
    have := sub_mem (h 1 1) (one_mem (v.adicCompletionIntegers ℚ))
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at this

private theorem mem_localLevelOne_top_iff (k : GL (Fin 2) (v.adicCompletion ℚ)) :
    k ∈ localLevelOne (𝓞 ℚ) ℚ v ⊤ ↔ IsIntegralUnit (v.adicCompletionIntegers ℚ) k := by
  rw [mem_localLevelOne_iff, isLocalLevelOne_top_iff, isLocalLevelOne_top_iff]
  exact Iff.rfl

private theorem valued_apply_le_one_of_mem {k : GL (Fin 2) (v.adicCompletion ℚ)} (hk : k ∈ localLevelOne (𝓞 ℚ) ℚ v ⊤)
    (i j : Fin 2) : Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1 := by
  have := ((mem_localLevelOne_top_iff v k).mp hk).1 i j
  rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at this

private theorem valued_det_eq_one_of_mem {k : GL (Fin 2) (v.adicCompletion ℚ)} (hk : k ∈ localLevelOne (𝓞 ℚ) ℚ v ⊤) :
    Valued.v (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det = 1 := by
  obtain ⟨h₁, h₂⟩ := (mem_localLevelOne_top_iff v k).mp hk
  have hd₁ := det_mem h₁
  have hd₂ := det_mem h₂
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hd₁ hd₂
  exact eq_one_of_mul_eq_one_of_le_one hd₁ hd₂ (by rw [← map_mul, det_mul_det_inv, map_one])

private theorem exists_cover_localLevelOne {ϖ : v.adicCompletion ℚ}
    (hfac : ∀ x : v.adicCompletion ℚ, x ≠ 0 → ∃ (m : ℤ) (u : (v.adicCompletionIntegers ℚ)ˣ),
      x = ϖ ^ m * ((u : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ))
    (g : GL (Fin 2) (v.adicCompletion ℚ)) :
    ∃ (x : v.adicCompletion ℚ) (m : ℤ × ℤ) (k : GL (Fin 2) (v.adicCompletion ℚ)), k ∈ localLevelOne (𝓞 ℚ) ℚ v ⊤ ∧
      (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) =
        !![1, x; 0, 1] * !![ϖ ^ m.1, 0; 0, ϖ ^ m.2] * (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :=
  exists_cover (v.adicCompletionIntegers ℚ) _ (mem_localLevelOne_top_iff v) hfac g

end Bench
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries.UnipotentMass"

end LanglandsTunnell.CubicInduction.LocalPairingSeries.IwasawaCover
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries.UnipotentMass"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries.UnipotentMass"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries.UnipotentMass"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries.UnipotentMass"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RankinSelberg.hasSum_cell_terms_rsLocalIntegral TateLocal.addCharLevel_psiLocal_rat TateLocal.psiLocal_ne_one TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel TateLocal.psiLocal_eq_one_of_mem_integers TateLocal.modulus_adicCompletion_eq_nnnorm"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "IsGL3PsiWhittakerFn gl3AmbientRightTranslate gl3AmbientRightTranslate_apply gl3CyclicSubspace transposeInv3 upperUnipotent3 upperUnipotent3_coe embedMat2 iotaGL iotaGL_unipotentGL2 valued_mul_apply_le3 localMaximalCompact3 LocalGL3 longWeyl3 longWeyl3_coe dualWhittakerFn3 dualWhittakerFn3_apply exists_forall_apply_iotaGL_diagZ_mul_scalarPi_zpow_eq_sum_of_isGL3PsiWhittakerFn"
namespace LocalPairingSeries
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open MeasureTheory NumberField IsDedekindDomain UnramifiedWhittaker AutomorphicForm
open scoped ENNReal Pointwise
open IwasawaCover TorusConj UnipotentMass

section Assembly

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem sigmaCompactSpace_of_isClosed {G : Type*} [Group G] [TopologicalSpace G] [SigmaCompactSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) : SigmaCompactSpace H :=
  hH.sigmaCompactSpace

private theorem sfinite_of_isHaarMeasure {H : Type*} [Group H] [TopologicalSpace H] [SigmaCompactSpace H]
    [MeasurableSpace H] (ν : Measure H) [ν.IsHaarMeasure] : SFinite ν :=
  inferInstance

section Unipotent

variable {R : Type*} [CommRing R] [TopologicalSpace R] [T2Space R]

omit [TopologicalSpace R] [T2Space R] in

private theorem coe_range_unipotentGL2Hom :
    ((unipotentGL2Hom (R := R)).range : Set (GL (Fin 2) R)) =
      {g : GL (Fin 2) R | Units.val g 0 0 = 1 ∧ Units.val g 1 0 = 0 ∧ Units.val g 1 1 = 1} := by
  ext g
  constructor
  · rintro ⟨y, rfl⟩
    change Units.val (unipotentGL2 y.toAdd) 0 0 = 1 ∧ Units.val (unipotentGL2 y.toAdd) 1 0 = 0 ∧
      Units.val (unipotentGL2 y.toAdd) 1 1 = 1
    simp [unipotentGL2]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨Multiplicative.ofAdd (Units.val g 0 1), ?_⟩
    change unipotentGL2 (Units.val g 0 1) = g
    refine Units.ext ?_
    rw [unipotentGL2_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]

private theorem isClosed_range_unipotentGL2Hom :
    IsClosed ((unipotentGL2Hom (R := R)).range : Set (GL (Fin 2) R)) := by
  rw [coe_range_unipotentGL2Hom]
  have hc : Continuous fun g : GL (Fin 2) R => Units.val g := Units.continuous_val
  exact (isClosed_eq (hc.matrix_elem 0 0) continuous_const).inter
    ((isClosed_eq (hc.matrix_elem 1 0) continuous_const).inter
      (isClosed_eq (hc.matrix_elem 1 1) continuous_const))

end Unipotent
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries.UnipotentMass"

section Density

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]

private theorem measurable_weight (H : Subgroup G) (μH : Measure H) : Measurable (HaarQuotient.weight H μH) := by
  unfold HaarQuotient.weight
  split_ifs with h
  · refine Measurable.tsum fun n => ?_
    exact (measurable_const.indicator isOpen_interior.measurableSet).const_mul _
  · exact measurable_const

private theorem measurable_lintegral_weight_mul [BorelSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    (H : Subgroup G) (μH : Measure H) [SFinite μH] :
    Measurable fun g : G => ∫⁻ x : H, HaarQuotient.weight H μH ((x : G) * g) ∂μH := by
  have hm : Measurable fun p : H × G => HaarQuotient.weight H μH ((p.1 : G) * p.2) :=
    (measurable_weight H μH).comp ((measurable_subtype_coe.comp measurable_fst).mul measurable_snd)
  exact hm.lintegral_prod_left

private theorem measurable_density [BorelSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] (H : Subgroup G)
    (μH : Measure H) [SFinite μH] : Measurable (HaarQuotient.density H μH) := by
  unfold HaarQuotient.density
  exact (measurable_weight H μH).div (measurable_lintegral_weight_mul H μH)

end Density
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries.UnipotentMass"

private theorem isOpen_localLevelOne_top :
    IsOpen ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) :
      Set (GL (Fin 2) (v.adicCompletion ℚ))) := by
  have hset : ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) :
      Set (GL (Fin 2) (v.adicCompletion ℚ))) =
        {k : GL (Fin 2) (v.adicCompletion ℚ) | IsIntegralUnit (v.adicCompletionIntegers ℚ) k} := by
    ext k
    exact mem_localLevelOne_top_iff v k
  rw [hset]
  exact isOpen_setOf_isIntegralUnit ((AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 ℚ) ℚ).out v)

end Assembly
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries.UnipotentMass"

section Cells

open IwasawaCover TorusConj UnipotentMass
open scoped ENNReal Pointwise

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem tor_coe {ϖ : v.adicCompletionIntegers ℚ} (hπ : unif v ϖ ≠ 0) (p : ℤ × ℤ) :
    ((tor v hπ p : G2 v) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = !![unif v ϖ ^ p.1, 0; 0, unif v ϖ ^ p.2] :=
  torus_coe_pair _ hπ p

private def cell {ϖ : v.adicCompletionIntegers ℚ} (hπ : unif v ϖ ≠ 0) (p : ℤ × ℤ) : Set (G2 v) :=
  ((Nr v : Set (G2 v)) * {tor v hπ p}) * (Kmax v : Set (G2 v))

private theorem setBuilder_eq_mul {G : Type*} [Group G] (H K : Subgroup G) :
    {g : G | ∃ n ∈ H, ∃ k ∈ K, g = n * k} = (H : Set G) * (K : Set G) := by
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_mul, SetLike.mem_coe]
  constructor
  · rintro ⟨n, hn, k, hk, rfl⟩
    exact ⟨n, hn, k, hk, rfl⟩
  · rintro ⟨n, hn, k, hk, rfl⟩
    exact ⟨n, hn, k, hk, rfl⟩

private theorem mem_mul_singleton_mul {G : Type*} [Group G] {H K : Subgroup G} {t g : G} :
    g ∈ ((H : Set G) * {t}) * (K : Set G) ↔ ∃ n ∈ H, ∃ k ∈ K, g = n * t * k := by
  simp only [Set.mem_mul, Set.mem_singleton_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨_, ⟨n, hn, _, rfl, rfl⟩, k, hk, rfl⟩
    exact ⟨n, hn, k, hk, rfl⟩
  · rintro ⟨n, hn, k, hk, rfl⟩
    exact ⟨n * t, ⟨n, hn, t, rfl, rfl⟩, k, hk, rfl⟩

private theorem mem_cell_iff {ϖ : v.adicCompletionIntegers ℚ} (hπ : unif v ϖ ≠ 0) (p : ℤ × ℤ) (g : G2 v) :
    g ∈ cell v hπ p ↔ ∃ n ∈ Nr v, ∃ k ∈ Kmax v, g = n * tor v hπ p * k :=
  mem_mul_singleton_mul

private theorem tor_mem_cell {ϖ : v.adicCompletionIntegers ℚ} (hπ : unif v ϖ ≠ 0) (p : ℤ × ℤ) :
    tor v hπ p ∈ cell v hπ p :=
  (mem_cell_iff v hπ p _).mpr ⟨1, one_mem _, 1, one_mem _, by rw [one_mul, mul_one]⟩

private theorem cellOne_eq : cellOne v = (Nr v : Set (G2 v)) * (Kmax v : Set (G2 v)) :=
  setBuilder_eq_mul (Nr v) (Kmax v)

private theorem mul_mem_cell {ϖ : v.adicCompletionIntegers ℚ} (hπ : unif v ϖ ≠ 0) (p : ℤ × ℤ) {n g : G2 v}
    (hn : n ∈ Nr v) (hg : g ∈ cell v hπ p) : n * g ∈ cell v hπ p := by
  obtain ⟨n', hn', k, hk, rfl⟩ := (mem_cell_iff v hπ p g).mp hg
  exact (mem_cell_iff v hπ p _).mpr ⟨n * n', mul_mem hn hn', k, hk, by
    rw [mul_assoc (n * n') (tor v hπ p) k, mul_assoc n n' (tor v hπ p * k), mul_assoc n' (tor v hπ p) k]⟩

private theorem mem_cell_mul {ϖ : v.adicCompletionIntegers ℚ} (hπ : unif v ϖ ≠ 0) (p : ℤ × ℤ) {k g : G2 v}
    (hk : k ∈ Kmax v) (hg : g ∈ cell v hπ p) : g * k ∈ cell v hπ p := by
  obtain ⟨n, hn, k', hk', rfl⟩ := (mem_cell_iff v hπ p g).mp hg
  exact (mem_cell_iff v hπ p _).mpr ⟨n, hn, k' * k, mul_mem hk' hk, by rw [mul_assoc]⟩

private theorem isOpen_cell {ϖ : v.adicCompletionIntegers ℚ} (hπ : unif v ϖ ≠ 0) (p : ℤ × ℤ) :
    IsOpen (cell v hπ p) :=
  (isOpen_localLevelOne_top v).mul_left

private theorem isOpen_cellOne : IsOpen (cellOne v) := by
  rw [cellOne_eq]
  exact (isOpen_localLevelOne_top v).mul_left

private theorem coe_eq_unipotentGL2_entry (x : Nr v) : (x : G2 v) = AutomorphicForm.unipotentGL2 (entry x) := by
  conv_lhs => rw [← up_entry x]
  rfl

private theorem pairwise_disjoint_cell {ϖ : v.adicCompletionIntegers ℚ} (hπ : unif v ϖ ≠ 0)
    (hϖ : Valued.v (unif v ϖ) = WithZero.exp (-1 : ℤ)) : Pairwise (Function.onFun Disjoint (cell v hπ)) := by
  intro p p' hpp'
  rw [Function.onFun, Set.disjoint_left]
  intro g hg hg'
  obtain ⟨n, hn, k, hk, rfl⟩ := (mem_cell_iff v hπ p g).mp hg
  obtain ⟨n', hn', k', hk', heq⟩ := (mem_cell_iff v hπ p' _).mp hg'
  apply hpp'
  have h1 := coe_eq_unipotentGL2_entry v ⟨n, hn⟩
  have h1' := coe_eq_unipotentGL2_entry v ⟨n', hn'⟩
  dsimp only at h1 h1'
  rw [h1, h1'] at heq
  exact cell_index_eq _ hπ hϖ (valued_apply_le_one_of_mem v hk) (valued_det_eq_one_of_mem v hk)
    (valued_apply_le_one_of_mem v hk') (valued_det_eq_one_of_mem v hk') heq

private theorem eq_of_mem_cell {ϖ : v.adicCompletionIntegers ℚ} (hπ : unif v ϖ ≠ 0)
    (hϖ : Valued.v (unif v ϖ) = WithZero.exp (-1 : ℤ)) {p p' : ℤ × ℤ} {g : G2 v} (hg : g ∈ cell v hπ p)
    (hg' : g ∈ cell v hπ p') : p = p' := by
  by_contra h
  exact Set.disjoint_left.mp (pairwise_disjoint_cell v hπ hϖ h) hg hg'

private theorem iUnion_cell {ϖ : v.adicCompletionIntegers ℚ} (hπ : unif v ϖ ≠ 0)
    (hϖ : Valued.v (unif v ϖ) = WithZero.exp (-1 : ℤ)) : (⋃ p, cell v hπ p) = Set.univ := by
  refine Set.eq_univ_of_forall fun g => Set.mem_iUnion.mpr ?_
  obtain ⟨x, m, k, hk, hg⟩ := exists_cover_localLevelOne v (fun y hy => exists_zpow_mul_unit hϖ y hy) g
  refine ⟨m, (mem_cell_iff v hπ m g).mpr ⟨unipotentGL2 x, unipotentGL2_mem x, k, hk, ?_⟩⟩
  apply Units.ext
  rw [hg, Units.val_mul, Units.val_mul, unipotentGL2_coe, tor_coe]

private theorem exists_unique_mem_cell {ϖ : v.adicCompletionIntegers ℚ} (hπ : unif v ϖ ≠ 0)
    (hϖ : Valued.v (unif v ϖ) = WithZero.exp (-1 : ℤ)) (g : G2 v) : ∃! p : ℤ × ℤ, g ∈ cell v hπ p := by
  have hg : g ∈ ⋃ p, cell v hπ p := by rw [iUnion_cell v hπ hϖ]; exact Set.mem_univ g
  obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hg
  exact ⟨p, hp, fun p' hp' => eq_of_mem_cell v hπ hϖ hp' hp⟩

private theorem apply_eq_apply_tor_of_mem_cell {X : Type*} {ϖ : v.adicCompletionIntegers ℚ} (hπ : unif v ϖ ≠ 0)
    (f : G2 v → X) (hN : ∀ n ∈ Nr v, ∀ g : G2 v, f (n * g) = f g) (hK : ∀ k ∈ Kmax v, ∀ g : G2 v, f (g * k) = f g)
    {p : ℤ × ℤ} {g : G2 v} (hg : g ∈ cell v hπ p) : f g = f (tor v hπ p) := by
  obtain ⟨n, hn, k, hk, rfl⟩ := (mem_cell_iff v hπ p g).mp hg
  rw [hK k hk, hN n hn]

private theorem measurable_of_invariant [MeasurableSpace (G2 v)] [BorelSpace (G2 v)] {X : Type*}
    [MeasurableSpace X] {ϖ : v.adicCompletionIntegers ℚ} (hπ : unif v ϖ ≠ 0)
    (hϖ : Valued.v (unif v ϖ) = WithZero.exp (-1 : ℤ)) (f : G2 v → X)
    (hN : ∀ n ∈ Nr v, ∀ g : G2 v, f (n * g) = f g) (hK : ∀ k ∈ Kmax v, ∀ g : G2 v, f (g * k) = f g) :
    Measurable f := by
  intro s _
  have hpre : f ⁻¹' s = ⋃ p ∈ {p : ℤ × ℤ | f (tor v hπ p) ∈ s}, cell v hπ p := by
    ext g
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    obtain ⟨p, hp, -⟩ := exists_unique_mem_cell v hπ hϖ g
    constructor
    · intro hg
      exact ⟨p, by rwa [← apply_eq_apply_tor_of_mem_cell v hπ f hN hK hp], hp⟩
    · rintro ⟨p', hp', hg'⟩
      rwa [apply_eq_apply_tor_of_mem_cell v hπ f hN hK hg']
  rw [hpre]
  exact MeasurableSet.biUnion (Set.to_countable _) fun p _ => (isOpen_cell v hπ p).measurableSet

end Cells
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries.UnipotentMass"

section Functional

open IwasawaCover TorusConj UnipotentMass AutomorphicForm
open scoped ENNReal Pointwise

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem secondCountable_G2 : SecondCountableTopology (G2 v) := by
  haveI : SecondCountableTopology (v.adicCompletion ℚ) := inferInstance
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → v.adicCompletion ℚ))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))).symm.isInducing
      |>.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

private theorem coe_Kmax_eq_localIntegralSet : (Kmax v : Set (G2 v)) = localIntegralSet ℚ v := by
  ext k
  rw [SetLike.mem_coe, mem_localLevelOne_top_iff v k, mem_localIntegralSet]
  exact Iff.rfl

private theorem isCompact_Kmax : IsCompact (Kmax v : Set (G2 v)) := by
  rw [coe_Kmax_eq_localIntegralSet]
  exact isCompact_localIntegralSet ℚ v

private theorem isClosed_Nr : IsClosed (Nr v : Set (G2 v)) := isClosed_range_unipotentGL2Hom

private theorem mul_comm_Nr (x y : Nr v) : x * y = y * x :=
  entry_injective (by rw [entry_mul, entry_mul, add_comm])

private theorem isMulRightInvariant_Nr [MeasurableSpace (G2 v)] [BorelSpace (G2 v)] (μN : Measure (Nr v))
    [μN.IsMulLeftInvariant] : μN.IsMulRightInvariant := by
  constructor
  intro x
  have h : (fun y : Nr v => y * x) = fun y => x * y := funext fun y => mul_comm_Nr v y x
  rw [h]
  exact map_mul_left_eq_self μN x

private def conjEquiv (k : G2 v) : G2 v ≃ₜ* G2 v where
  toFun g := k⁻¹ * g * k
  invFun g := k * g * k⁻¹
  left_inv g := by group
  right_inv g := by group
  map_mul' g h := by group
  continuous_toFun := (continuous_const.mul continuous_id).mul continuous_const
  continuous_invFun := (continuous_const.mul continuous_id).mul continuous_const

private theorem conjEquiv_apply (k g : G2 v) : conjEquiv v k g = k⁻¹ * g * k := rfl

private theorem map_mul_right_eq_self_of_mem [MeasurableSpace (G2 v)] [BorelSpace (G2 v)] (μ₂ : Measure (G2 v))
    [μ₂.IsHaarMeasure] {k : G2 v} (hk : k ∈ Kmax v) : μ₂.map (fun g => g * k) = μ₂ := by
  haveI : LocallyCompactSpace (G2 v) := locallyCompactSpace_localGL ℚ v
  haveI : SecondCountableTopology (G2 v) := secondCountable_G2 v
  have hKm : MeasurableSet (Kmax v : Set (G2 v)) := (isOpen_localLevelOne_top v).measurableSet
  have hK0 : μ₂ (Kmax v : Set (G2 v)) ≠ 0 := (isOpen_localLevelOne_top v).measure_ne_zero μ₂ ⟨1, one_mem _⟩
  have hKt : μ₂ (Kmax v : Set (G2 v)) ≠ ⊤ := (isCompact_Kmax v).measure_lt_top.ne
  have hpre : (conjEquiv v k : G2 v → G2 v) ⁻¹' (Kmax v : Set (G2 v)) = Kmax v := by
    ext g
    simp only [Set.mem_preimage, SetLike.mem_coe, conjEquiv_apply]
    constructor
    · intro h
      have h' : k * (k⁻¹ * g * k) * k⁻¹ ∈ Kmax v := mul_mem (mul_mem hk h) (inv_mem hk)
      have hg : k * (k⁻¹ * g * k) * k⁻¹ = g := by group
      rwa [hg] at h'
    · intro h
      exact mul_mem (mul_mem (inv_mem hk) h) hk
  have hmap : μ₂.map (conjEquiv v k : G2 v → G2 v) = (1 : ℝ≥0∞) • μ₂ :=
    map_eq_smul_of_apply μ₂ (conjEquiv v k) hKm hK0 hKt 1 (by rw [hpre, one_mul])
  have hcomp : (fun g : G2 v => g * k) = (fun g : G2 v => k * g) ∘ (conjEquiv v k : G2 v → G2 v) := by
    funext g
    simp only [Function.comp_apply, conjEquiv_apply]
    group
  have hmeas : Measurable (⇑(conjEquiv v k)) := (conjEquiv v k).continuous.measurable
  rw [hcomp, ← Measure.map_map (measurable_const_mul k) hmeas, hmap, one_smul, map_mul_left_eq_self]

private theorem lintegral_eq_lintegral_quotient [MeasurableSpace (G2 v)] [BorelSpace (G2 v)] (μ₂ : Measure (G2 v))
    [μ₂.IsHaarMeasure] (μN : Measure (Nr v)) [μN.IsHaarMeasure] (F : G2 v → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ g, F g ∂μ₂ = ∫⁻ q, (∫⁻ x : Nr v, F ((x : G2 v) * q.out) ∂μN) ∂(HaarQuotient.measure μ₂ (Nr v) μN) := by
  haveI : LocallyCompactSpace (G2 v) := locallyCompactSpace_localGL ℚ v
  haveI : SecondCountableTopology (G2 v) := secondCountable_G2 v
  haveI : SigmaCompactSpace (G2 v) := inferInstance
  haveI := sfinite_of_isHaarMeasure μ₂
  haveI := isMulRightInvariant_Nr v μN
  exact HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out μ₂ (Nr v) (isClosed_Nr v) μN F hF

private theorem lintegral_density_mul [MeasurableSpace (G2 v)] [BorelSpace (G2 v)] (μN : Measure (Nr v))
    [μN.IsHaarMeasure] (g : G2 v) :
    ∫⁻ x : Nr v, HaarQuotient.density (Nr v) μN ((x : G2 v) * g) ∂μN = 1 := by
  haveI : LocallyCompactSpace (G2 v) := locallyCompactSpace_localGL ℚ v
  haveI : SecondCountableTopology (G2 v) := secondCountable_G2 v
  haveI := isMulRightInvariant_Nr v μN
  exact HaarQuotient.lintegral_density_mul_eq_one (Nr v) (isClosed_Nr v) μN g

private theorem measurable_density_Nr [MeasurableSpace (G2 v)] [BorelSpace (G2 v)] (μN : Measure (Nr v))
    [μN.IsHaarMeasure] : Measurable (HaarQuotient.density (Nr v) μN) := by
  haveI : SecondCountableTopology (G2 v) := secondCountable_G2 v
  haveI : SigmaCompactSpace (Nr v) := by
    haveI : LocallyCompactSpace (G2 v) := locallyCompactSpace_localGL ℚ v
    haveI : SigmaCompactSpace (G2 v) := inferInstance
    exact sigmaCompactSpace_of_isClosed _ (isClosed_Nr v)
  haveI := sfinite_of_isHaarMeasure μN
  exact measurable_density _ μN

private theorem lintegral_comp_mul_right_eq [MeasurableSpace (G2 v)] [BorelSpace (G2 v)] (μ₂ : Measure (G2 v))
    [μ₂.IsHaarMeasure] (μN : Measure (Nr v)) [μN.IsHaarMeasure] (f : G2 v → ℝ≥0∞)
    (hf : ∀ n ∈ Nr v, ∀ g : G2 v, f (n * g) = f g) (hfm : Measurable f) {k : G2 v} (hk : k ∈ Kmax v) :
    ∫⁻ g, f (g * k) ∂(wMeasure v μ₂ μN) = ∫⁻ g, f g ∂(wMeasure v μ₂ μN) := by
  set ρ := HaarQuotient.density (Nr v) μN with hρ_def
  have hρ : Measurable ρ := measurable_density_Nr v μN
  have hfk : Measurable fun g : G2 v => f (g * k) := hfm.comp (measurable_mul_const k)
  have hρk : Measurable fun g : G2 v => ρ (g * k⁻¹) := hρ.comp (measurable_mul_const k⁻¹)

  rw [show wMeasure v μ₂ μN = μ₂.withDensity ρ from rfl, lintegral_withDensity_eq_lintegral_mul μ₂ hρ hfk,
    lintegral_withDensity_eq_lintegral_mul μ₂ hρ hfm]

  have hstep : ∫⁻ g, (ρ * fun g => f (g * k)) g ∂μ₂ = ∫⁻ g, ρ (g * k⁻¹) * f g ∂μ₂ := by
    have hm : Measurable fun g : G2 v => ρ (g * k⁻¹) * f g := hρk.mul hfm
    calc ∫⁻ g, (ρ * fun g => f (g * k)) g ∂μ₂
        = ∫⁻ g, (fun g' => ρ (g' * k⁻¹) * f g') (g * k) ∂μ₂ := by
          refine lintegral_congr fun g => ?_
          simp only [Pi.mul_apply, mul_inv_cancel_right]
      _ = ∫⁻ g, ρ (g * k⁻¹) * f g ∂(μ₂.map fun g => g * k) := (lintegral_map hm (measurable_mul_const k)).symm
      _ = ∫⁻ g, ρ (g * k⁻¹) * f g ∂μ₂ := by rw [map_mul_right_eq_self_of_mem v μ₂ hk]
  rw [hstep]

  rw [lintegral_eq_lintegral_quotient v μ₂ μN (fun g => ρ (g * k⁻¹) * f g) (hρk.mul hfm),
    lintegral_eq_lintegral_quotient v μ₂ μN (ρ * f) (hρ.mul hfm)]
  refine lintegral_congr fun q => ?_
  have h1 : ∫⁻ x : Nr v, ρ ((x : G2 v) * q.out * k⁻¹) * f ((x : G2 v) * q.out) ∂μN = f q.out := by
    calc ∫⁻ x : Nr v, ρ ((x : G2 v) * q.out * k⁻¹) * f ((x : G2 v) * q.out) ∂μN
        = ∫⁻ x : Nr v, ρ ((x : G2 v) * (q.out * k⁻¹)) * f q.out ∂μN := by
          refine lintegral_congr fun x => ?_
          rw [mul_assoc, hf _ x.2]
      _ = (∫⁻ x : Nr v, ρ ((x : G2 v) * (q.out * k⁻¹)) ∂μN) * f q.out :=
          lintegral_mul_const _ (hρ.comp ((measurable_subtype_coe.mul_const _)))
      _ = f q.out := by rw [hρ_def, lintegral_density_mul v μN, one_mul]
  have h2 : ∫⁻ x : Nr v, (ρ * f) ((x : G2 v) * q.out) ∂μN = f q.out := by
    calc ∫⁻ x : Nr v, (ρ * f) ((x : G2 v) * q.out) ∂μN
        = ∫⁻ x : Nr v, ρ ((x : G2 v) * q.out) * f q.out ∂μN := by
          refine lintegral_congr fun x => ?_
          rw [Pi.mul_apply, hf _ x.2]
      _ = (∫⁻ x : Nr v, ρ ((x : G2 v) * q.out) ∂μN) * f q.out :=
          lintegral_mul_const _ (hρ.comp ((measurable_subtype_coe.mul_const _)))
      _ = f q.out := by rw [hρ_def, lintegral_density_mul v μN, one_mul]
  simp only [Pi.mul_apply] at h2 ⊢
  rw [h2]
  convert h1 using 1

private theorem integral_comp_mul_right_eq [MeasurableSpace (G2 v)] [BorelSpace (G2 v)] (μ₂ : Measure (G2 v))
    [μ₂.IsHaarMeasure] (μN : Measure (Nr v)) [μN.IsHaarMeasure] (f : G2 v → ℂ)
    (hf : ∀ n ∈ Nr v, ∀ g : G2 v, f (n * g) = f g) (hfm : Measurable f) {k : G2 v} (hk : k ∈ Kmax v) :
    (Integrable (fun g => f (g * k)) (wMeasure v μ₂ μN) ↔ Integrable f (wMeasure v μ₂ μN)) ∧
      ∫ g, f (g * k) ∂(wMeasure v μ₂ μN) = ∫ g, f g ∂(wMeasure v μ₂ μN) := by
  set μ' := wMeasure v μ₂ μN with hμ'
  have hfk : Measurable fun g : G2 v => f (g * k) := hfm.comp (measurable_mul_const k)

  have key : ∀ (φ : ℂ → ℝ≥0∞), Measurable φ →
      ∫⁻ g, φ (f (g * k)) ∂μ' = ∫⁻ g, φ (f g) ∂μ' := fun φ hφ =>
    lintegral_comp_mul_right_eq v μ₂ μN (fun g => φ (f g)) (fun n hn g => by simp only [hf n hn g])
      (hφ.comp hfm) hk
  have hint : Integrable (fun g => f (g * k)) μ' ↔ Integrable f μ' := by
    simp only [Integrable, hfk.aestronglyMeasurable, hfm.aestronglyMeasurable, true_and, hasFiniteIntegral_iff_enorm]
    rw [key (fun z => ‖z‖ₑ) measurable_enorm]
  refine ⟨hint, ?_⟩
  by_cases hI : Integrable f μ'
  · have hIk : Integrable (fun g => f (g * k)) μ' := hint.mpr hI
    apply Complex.ext
    · rw [← RCLike.re_eq_complex_re, ← integral_re hIk, ← integral_re hI,
        integral_eq_lintegral_pos_part_sub_lintegral_neg_part hIk.re,
        integral_eq_lintegral_pos_part_sub_lintegral_neg_part hI.re]
      simp only [RCLike.re_eq_complex_re]
      rw [key (fun z => ENNReal.ofReal z.re) (ENNReal.measurable_ofReal.comp Complex.measurable_re),
        key (fun z => ENNReal.ofReal (-z.re)) (ENNReal.measurable_ofReal.comp Complex.measurable_re.neg)]
    · rw [← RCLike.im_eq_complex_im, ← integral_im hIk, ← integral_im hI,
        integral_eq_lintegral_pos_part_sub_lintegral_neg_part hIk.im,
        integral_eq_lintegral_pos_part_sub_lintegral_neg_part hI.im]
      simp only [RCLike.im_eq_complex_im]
      rw [key (fun z => ENNReal.ofReal z.im) (ENNReal.measurable_ofReal.comp Complex.measurable_im),
        key (fun z => ENNReal.ofReal (-z.im)) (ENNReal.measurable_ofReal.comp Complex.measurable_im.neg)]
  · rw [integral_undef hI, integral_undef (fun h => hI (hint.mp h))]

private theorem wMeasure_mul_lt_top [MeasurableSpace (G2 v)] [BorelSpace (G2 v)] (μ₂ : Measure (G2 v))
    [μ₂.IsHaarMeasure] (μN : Measure (Nr v)) [μN.IsHaarMeasure] {C : Set (G2 v)} (hC : IsCompact C) :
    wMeasure v μ₂ μN ((Nr v : Set (G2 v)) * C) < ∞ := by
  haveI : LocallyCompactSpace (G2 v) := locallyCompactSpace_localGL ℚ v
  haveI : LocallyCompactSpace (Nr v) := (isClosed_Nr v).locallyCompactSpace
  haveI := isMulRightInvariant_Nr v μN
  set ρ := HaarQuotient.density (Nr v) μN with hρ_def
  have hρ : Measurable ρ := measurable_density_Nr v μN

  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : Nr v)
  have hV0 : μN V ≠ 0 := (Measure.measure_pos_of_mem_nhds μN hV1).ne'
  have hVt : μN V ≠ ∞ := hVc.measure_lt_top.ne

  set S : Set (G2 v) := (((↑) : Nr v → G2 v) '' V) * C with hS_def
  have hSc : IsCompact S := (hVc.image continuous_subtype_val).mul hC
  have hSm : MeasurableSet S := hSc.isClosed.measurableSet
  have hNC : MeasurableSet ((Nr v : Set (G2 v)) * C) := ((isClosed_Nr v).mul_right_of_isCompact hC).measurableSet

  have hmass : wMeasure v μ₂ μN ((Nr v : Set (G2 v)) * C) =
      ∫⁻ q, ((Nr v : Set (G2 v)) * C).indicator 1 q.out ∂(HaarQuotient.measure μ₂ (Nr v) μN) := by
    rw [show wMeasure v μ₂ μN = μ₂.withDensity ρ from rfl, ← lintegral_indicator_one hNC,
      lintegral_withDensity_eq_lintegral_mul μ₂ hρ (measurable_one.indicator hNC),
      lintegral_eq_lintegral_quotient v μ₂ μN (ρ * ((Nr v : Set (G2 v)) * C).indicator (1 : G2 v → ℝ≥0∞))
        (hρ.mul (measurable_one.indicator hNC))]
    refine lintegral_congr fun q => ?_
    have hind : ∀ x : Nr v, ((Nr v : Set (G2 v)) * C).indicator (1 : G2 v → ℝ≥0∞) ((x : G2 v) * q.out) =
        ((Nr v : Set (G2 v)) * C).indicator 1 q.out := by
      intro x
      by_cases hq : q.out ∈ (Nr v : Set (G2 v)) * C
      · have hxq : (x : G2 v) * q.out ∈ (Nr v : Set (G2 v)) * C := by
          obtain ⟨n, hn, c, hc, hq'⟩ := Set.mem_mul.mp hq
          exact Set.mem_mul.mpr ⟨x * n, mul_mem x.2 hn, c, hc, by rw [← hq', mul_assoc]⟩
        rw [Set.indicator_of_mem hq, Set.indicator_of_mem hxq]
        rfl
      · have hxq : (x : G2 v) * q.out ∉ (Nr v : Set (G2 v)) * C := by
          intro h
          apply hq
          obtain ⟨n, hn, c, hc, h'⟩ := Set.mem_mul.mp h
          refine Set.mem_mul.mpr ⟨(x : G2 v)⁻¹ * n, mul_mem (inv_mem x.2) hn, c, hc, ?_⟩
          rw [mul_assoc, h', inv_mul_cancel_left]
        rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hxq]
    calc ∫⁻ x : Nr v, (ρ * ((Nr v : Set (G2 v)) * C).indicator (1 : G2 v → ℝ≥0∞)) ((x : G2 v) * q.out) ∂μN
        = ∫⁻ x : Nr v, ρ ((x : G2 v) * q.out) * ((Nr v : Set (G2 v)) * C).indicator 1 q.out ∂μN := by
          refine lintegral_congr fun x => ?_
          rw [Pi.mul_apply, hind x]
      _ = (∫⁻ x : Nr v, ρ ((x : G2 v) * q.out) ∂μN) * ((Nr v : Set (G2 v)) * C).indicator 1 q.out :=
          lintegral_mul_const _ (hρ.comp (measurable_subtype_coe.mul_const _))
      _ = ((Nr v : Set (G2 v)) * C).indicator 1 q.out := by rw [hρ_def, lintegral_density_mul v μN, one_mul]

  have hptw : ∀ q : MulAction.orbitRel.Quotient (Nr v) (G2 v),
      μN V * ((Nr v : Set (G2 v)) * C).indicator 1 q.out ≤ ∫⁻ x : Nr v, S.indicator 1 ((x : G2 v) * q.out) ∂μN := by
    intro q
    by_cases hq : q.out ∈ (Nr v : Set (G2 v)) * C
    · obtain ⟨n, hn, c, hc, hq'⟩ := Set.mem_mul.mp hq
      rw [Set.indicator_of_mem hq, Pi.one_apply, mul_one]

      have hsub : (fun x : Nr v => x * (⟨n, hn⟩ : Nr v)⁻¹) '' V ⊆
          {x : Nr v | (x : G2 v) * q.out ∈ S} := by
        rintro _ ⟨y, hy, rfl⟩
        simp only [Set.mem_setOf_eq]
        rw [← hq', Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, ← mul_assoc ((n : G2 v))⁻¹, inv_mul_cancel,
          one_mul]
        exact Set.mul_mem_mul ⟨y, hy, rfl⟩ hc
      calc μN V = μN ((fun x : Nr v => x * (⟨n, hn⟩ : Nr v)⁻¹) '' V) := by
            rw [Set.image_mul_right, measure_preimage_mul_right]

        _ ≤ μN {x : Nr v | (x : G2 v) * q.out ∈ S} := measure_mono hsub
        _ = ∫⁻ x : Nr v, S.indicator 1 ((x : G2 v) * q.out) ∂μN := by
            change μN ((fun x : Nr v => (x : G2 v) * q.out) ⁻¹' S) = _
            rw [← lintegral_indicator_one (hSm.preimage (measurable_subtype_coe.mul_const q.out))]
            exact lintegral_congr fun x => rfl
    · rw [Set.indicator_of_notMem hq, mul_zero]
      exact zero_le

  have hle : μN V * wMeasure v μ₂ μN ((Nr v : Set (G2 v)) * C) ≤ μ₂ S := by
    calc μN V * wMeasure v μ₂ μN ((Nr v : Set (G2 v)) * C)
        = ∫⁻ q, μN V * ((Nr v : Set (G2 v)) * C).indicator 1 q.out ∂(HaarQuotient.measure μ₂ (Nr v) μN) := by
          rw [hmass, lintegral_const_mul' _ _ hVt]
      _ ≤ ∫⁻ q, (∫⁻ x : Nr v, S.indicator 1 ((x : G2 v) * q.out) ∂μN) ∂(HaarQuotient.measure μ₂ (Nr v) μN) :=
          lintegral_mono hptw
      _ = ∫⁻ g, S.indicator 1 g ∂μ₂ :=
          (lintegral_eq_lintegral_quotient v μ₂ μN (S.indicator 1) (measurable_one.indicator hSm)).symm
      _ = μ₂ S := lintegral_indicator_one hSm
  have hSt : μ₂ S < ∞ := hSc.measure_lt_top
  have hfin : μN V * wMeasure v μ₂ μN ((Nr v : Set (G2 v)) * C) < ∞ := lt_of_le_of_lt hle hSt
  exact (ENNReal.mul_lt_top_iff.mp hfin).elim (fun h => h.2) fun h => h.elim (fun h0 => (hV0 h0).elim)
    fun h0 => by rw [h0]; exact ENNReal.zero_lt_top

end Functional
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries.UnipotentMass"

section Expansion

open IwasawaCover TorusConj UnipotentMass AutomorphicForm
open scoped ENNReal NNReal Pointwise

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem mul_mem_cell_iff {ϖ : v.adicCompletionIntegers ℚ} (hπ : unif v ϖ ≠ 0) (p : ℤ × ℤ) {n : G2 v}
    (hn : n ∈ Nr v) (g : G2 v) : n * g ∈ cell v hπ p ↔ g ∈ cell v hπ p := by
  refine ⟨fun h => ?_, mul_mem_cell v hπ p hn⟩
  have h' := mul_mem_cell v hπ p (inv_mem hn) h
  rwa [inv_mul_cancel_left] at h'

private theorem mem_cell_mul_iff {ϖ : v.adicCompletionIntegers ℚ} (hπ : unif v ϖ ≠ 0) (p : ℤ × ℤ) {k : G2 v}
    (hk : k ∈ Kmax v) (g : G2 v) : g * k ∈ cell v hπ p ↔ g ∈ cell v hπ p := by
  refine ⟨fun h => ?_, mem_cell_mul v hπ p hk⟩
  have h' := mem_cell_mul v hπ p (inv_mem hk) h
  rwa [mul_inv_cancel_right] at h'

private theorem wMeasure_cell_lt_top [MeasurableSpace (G2 v)] [BorelSpace (G2 v)] (μ₂ : Measure (G2 v))
    [μ₂.IsHaarMeasure] (μN : Measure (Nr v)) [μN.IsHaarMeasure] {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : unif v ϖ ≠ 0) (p : ℤ × ℤ) : wMeasure v μ₂ μN (cell v hπ p) < ∞ := by
  have hsub : cell v hπ p ⊆ (Nr v : Set (G2 v)) * (tor v hπ p • (Kmax v : Set (G2 v))) := by
    intro g hg
    obtain ⟨n, hn, k, hk, rfl⟩ := (mem_cell_iff v hπ p g).mp hg
    rw [mul_assoc]
    exact Set.mul_mem_mul hn (Set.smul_mem_smul_set hk)
  exact lt_of_le_of_lt (measure_mono hsub)
    (wMeasure_mul_lt_top v μ₂ μN ((isCompact_Kmax v).smul (tor v hπ p)))

private theorem wMeasure_cellOne_lt_top [MeasurableSpace (G2 v)] [BorelSpace (G2 v)] (μ₂ : Measure (G2 v))
    [μ₂.IsHaarMeasure] (μN : Measure (Nr v)) [μN.IsHaarMeasure] : wMeasure v μ₂ μN (cellOne v) < ∞ := by
  rw [cellOne_eq]
  exact wMeasure_mul_lt_top v μ₂ μN (isCompact_Kmax v)

private theorem norm_absNorm_zpow (z : ℤ) :
    ‖((Ideal.absNorm v.asIdeal : ℂ)) ^ z‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ z := by
  rw [norm_zpow, Complex.norm_natCast]

private theorem absNorm_asIdeal_ne_zero : Ideal.absNorm v.asIdeal ≠ 0 := by
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact v.ne_bot

private theorem ofReal_absNorm_zpow (z : ℤ) :
    ENNReal.ofReal ((Ideal.absNorm v.asIdeal : ℝ) ^ z) = (Ideal.absNorm v.asIdeal : ℝ≥0∞) ^ z := by
  have hN0 : (Ideal.absNorm v.asIdeal : ℝ≥0) ≠ 0 := by exact_mod_cast absNorm_asIdeal_ne_zero v
  rw [← NNReal.coe_natCast, ← NNReal.coe_zpow, ENNReal.ofReal_coe_nnreal, ENNReal.coe_zpow hN0, ENNReal.coe_natCast]

private theorem wMeasure_cell {ϖ : v.adicCompletionIntegers ℚ} (hπ : unif v ϖ ≠ 0)
    (hϖ : Valued.v (unif v ϖ) = WithZero.exp (-1 : ℤ)) :
    letI : MeasurableSpace (G2 v) := borel (G2 v)
    ∀ (μ₂ : Measure (G2 v)) [μ₂.IsHaarMeasure] (μN : Measure (Nr v)) [μN.IsHaarMeasure] (p : ℤ × ℤ),
      wMeasure v μ₂ μN (cell v hπ p) =
        (Ideal.absNorm v.asIdeal : ℝ≥0∞) ^ (p.1 - p.2) * wMeasure v μ₂ μN (cellOne v) := by
  letI : MeasurableSpace (G2 v) := borel (G2 v)
  haveI : BorelSpace (G2 v) := ⟨rfl⟩
  intro μ₂ _ μN _ p
  haveI : LocallyCompactSpace (G2 v) := locallyCompactSpace_localGL ℚ v
  haveI : SecondCountableTopology (G2 v) := secondCountable_G2 v
  set μ' := wMeasure v μ₂ μN with hμ'
  have hcm : MeasurableSet (cell v hπ p) := (isOpen_cell v hπ p).measurableSet
  have hfin : μ' (cell v hπ p) < ∞ := wMeasure_cell_lt_top v μ₂ μN hπ p
  have hfin1 : μ' (cellOne v) < ∞ := wMeasure_cellOne_lt_top v μ₂ μN
  have hN0 : (Ideal.absNorm v.asIdeal : ℝ≥0∞) ≠ 0 := by exact_mod_cast absNorm_asIdeal_ne_zero v

  set χ : G2 v → ℂ := (cell v hπ p).indicator fun _ => (1 : ℂ) with hχ
  have hχN : ∀ n ∈ Nr v, ∀ g : G2 v, χ (n * g) * (1 : ℂ) = χ g * 1 := by
    intro n hn g
    by_cases hg : g ∈ cell v hπ p
    · rw [hχ, Set.indicator_of_mem hg, Set.indicator_of_mem ((mul_mem_cell_iff v hπ p hn g).mpr hg)]
    · rw [hχ, Set.indicator_of_notMem hg, Set.indicator_of_notMem (mt (mul_mem_cell_iff v hπ p hn g).mp hg)]
  have hχK : ∀ k ∈ Kmax v, ∀ g : G2 v, χ (g * k) * (1 : ℂ) = χ g * 1 := by
    intro k hk g
    by_cases hg : g ∈ cell v hπ p
    · rw [hχ, Set.indicator_of_mem hg, Set.indicator_of_mem ((mem_cell_mul_iff v hπ p hk g).mpr hg)]
    · rw [hχ, Set.indicator_of_notMem hg, Set.indicator_of_notMem (mt (mem_cell_mul_iff v hπ p hk g).mp hg)]
  have h0 : (1 / 2 : ℂ) - 1 / 2 = 0 := sub_self _
  have hfun : (fun g : G2 v => (χ g * (fun _ => (1 : ℂ)) g) *
      (((fun _ => (1 : ℝ)) g : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - 1 / 2)) =
      χ := by
    funext g
    simp only [h0, Complex.cpow_zero, mul_one]
  have hint : Integrable (fun g : G2 v => (χ g * (fun _ => (1 : ℂ)) g) *
      (((fun _ => (1 : ℝ)) g : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - 1 / 2)) μ' := by
    rw [hfun, hχ, integrable_indicator_iff hcm]
    exact integrableOn_const hfin.ne
  haveI := isMulRightInvariant_Nr v μN
  have hrow := LanglandsTunnell.RankinSelberg.hasSum_cell_terms_rsLocalIntegral v hπ hϖ μ₂ μN (fun _ => (1 : ℝ))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (1 / 2) χ (fun _ => 1) hχN hχK hint

  have hI : RSCarrier.rsLocalIntegral μ₂ (Nr v) μN (fun _ => (1 : ℝ)) (1 / 2) χ (fun _ => 1) =
      ((μ' (cell v hπ p)).toReal : ℂ) := by
    simp only [RSCarrier.rsLocalIntegral, h0, Complex.cpow_zero, mul_one]
    rw [hχ, integral_indicator_const (1 : ℂ) hcm, Complex.real_smul, mul_one, measureReal_def, hμ']

  have hterm : ∀ p' : ℤ × ℤ, p' ≠ p →
      ((μ' (cellOne v)).toReal : ℂ) * ((Ideal.absNorm v.asIdeal : ℂ) ^ (p'.1 - p'.2)) *
        ((χ (tor v hπ p') * (fun _ => (1 : ℂ)) (tor v hπ p')) *
          (((fun _ => (1 : ℝ)) (tor v hπ p') : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - 1 / 2)) = 0 := by
    intro p' hp'
    have hnot : tor v hπ p' ∉ cell v hπ p := fun h => hp' (eq_of_mem_cell v hπ hϖ (tor_mem_cell v hπ p') h)
    rw [hχ, Set.indicator_of_notMem hnot, zero_mul, zero_mul, mul_zero]
  have hsingle := (hasSum_single p hterm).unique hrow
  rw [hI, hχ, Set.indicator_of_mem (tor_mem_cell v hπ p)] at hsingle
  simp only [h0, Complex.cpow_zero, mul_one] at hsingle

  have hreal : (μ' (cellOne v)).toReal * (Ideal.absNorm v.asIdeal : ℝ) ^ (p.1 - p.2) = (μ' (cell v hπ p)).toReal := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_zpow, ← Complex.ofReal_mul] at hsingle
    exact Complex.ofReal_injective hsingle
  rw [mul_comm]
  refine (ENNReal.toReal_eq_toReal_iff' hfin.ne (ENNReal.mul_ne_top hfin1.ne
    (ENNReal.zpow_ne_top hN0 (ENNReal.natCast_ne_top _) _))).mp ?_
  rw [← hreal, ENNReal.toReal_mul, ← ofReal_absNorm_zpow v, ENNReal.toReal_ofReal (zpow_nonneg (Nat.cast_nonneg _) _)]

private theorem lintegral_eq_tsum_cell {ϖ : v.adicCompletionIntegers ℚ} (hπ : unif v ϖ ≠ 0)
    (hϖ : Valued.v (unif v ϖ) = WithZero.exp (-1 : ℤ)) :
    letI : MeasurableSpace (G2 v) := borel (G2 v)
    ∀ (μ₂ : Measure (G2 v)) [μ₂.IsHaarMeasure] (μN : Measure (Nr v)) [μN.IsHaarMeasure] (φ : G2 v → ℝ≥0∞)
      (_ : ∀ n ∈ Nr v, ∀ g : G2 v, φ (n * g) = φ g) (_ : ∀ k ∈ Kmax v, ∀ g : G2 v, φ (g * k) = φ g),
      ∫⁻ g, φ g ∂(wMeasure v μ₂ μN) = ∑' p : ℤ × ℤ,
        wMeasure v μ₂ μN (cellOne v) * (Ideal.absNorm v.asIdeal : ℝ≥0∞) ^ (p.1 - p.2) * φ (tor v hπ p) := by
  letI : MeasurableSpace (G2 v) := borel (G2 v)
  haveI : BorelSpace (G2 v) := ⟨rfl⟩
  intro μ₂ _ μN _ φ hN hK
  set μ' := wMeasure v μ₂ μN with hμ'
  have hcm : ∀ p, MeasurableSet (cell v hπ p) := fun p => (isOpen_cell v hπ p).measurableSet
  calc ∫⁻ g, φ g ∂μ' = ∫⁻ g in ⋃ p, cell v hπ p, φ g ∂μ' := by
        rw [iUnion_cell v hπ hϖ, Measure.restrict_univ]
    _ = ∑' p, ∫⁻ g in cell v hπ p, φ g ∂μ' := lintegral_iUnion hcm (pairwise_disjoint_cell v hπ hϖ) φ
    _ = ∑' p, φ (tor v hπ p) * μ' (cell v hπ p) := by
        refine tsum_congr fun p => ?_
        rw [setLIntegral_congr_fun (hcm p) (g := fun _ => φ (tor v hπ p))
          (fun g hg => apply_eq_apply_tor_of_mem_cell v hπ φ hN hK hg), setLIntegral_const]
    _ = ∑' p : ℤ × ℤ, μ' (cellOne v) * (Ideal.absNorm v.asIdeal : ℝ≥0∞) ^ (p.1 - p.2) * φ (tor v hπ p) := by
        refine tsum_congr fun p => ?_
        rw [wMeasure_cell v hπ hϖ μ₂ μN p]
        ring

private theorem integrable_and_hasSum_of_summable {ϖ : v.adicCompletionIntegers ℚ} (hπ : unif v ϖ ≠ 0)
    (hϖ : Valued.v (unif v ϖ) = WithZero.exp (-1 : ℤ)) :
    letI : MeasurableSpace (G2 v) := borel (G2 v)
    ∀ (μ₂ : Measure (G2 v)) [μ₂.IsHaarMeasure] (μN : Measure (Nr v)) [μN.IsHaarMeasure]
      (δ : G2 v → ℝ) (_ : ∀ n ∈ Nr v, ∀ g : G2 v, δ (n * g) = δ g) (_ : ∀ k ∈ Kmax v, ∀ g : G2 v, δ (g * k) = δ g)
      (s : ℂ) (W F : G2 v → ℂ) (_ : ∀ n ∈ Nr v, ∀ g : G2 v, W (n * g) * F (n * g) = W g * F g)
      (_ : ∀ k ∈ Kmax v, ∀ g : G2 v, W (g * k) * F (g * k) = W g * F g)
      (_ : Summable fun p : ℤ × ℤ => ‖cellTerm v hπ (((wMeasure v μ₂ μN) (cellOne v)).toReal : ℂ) δ s W F p‖),
      Integrable (fun g : G2 v => (W g * F g) * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2)) (wMeasure v μ₂ μN) ∧
        HasSum (fun p : ℤ × ℤ => cellTerm v hπ (((wMeasure v μ₂ μN) (cellOne v)).toReal : ℂ) δ s W F p)
          (RSCarrier.rsLocalIntegral μ₂ (Nr v) μN δ s W F) := by
  letI : MeasurableSpace (G2 v) := borel (G2 v)
  haveI : BorelSpace (G2 v) := ⟨rfl⟩
  intro μ₂ _ μN _ δ hδN hδK s W F hN hK hsum
  haveI : LocallyCompactSpace (G2 v) := locallyCompactSpace_localGL ℚ v
  haveI : SecondCountableTopology (G2 v) := secondCountable_G2 v
  set μ' := wMeasure v μ₂ μN with hμ'
  set f : G2 v → ℂ := fun g => (W g * F g) * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2) with hf
  have hfN : ∀ n ∈ Nr v, ∀ g : G2 v, f (n * g) = f g := by
    intro n hn g
    simp only [hf, hN n hn g, hδN n hn g]
  have hfK : ∀ k ∈ Kmax v, ∀ g : G2 v, f (g * k) = f g := by
    intro k hk g
    simp only [hf, hK k hk g, hδK k hk g]
  have hfm : Measurable f := measurable_of_invariant v hπ hϖ f hfN hfK
  have hfin1 : μ' (cellOne v) < ∞ := wMeasure_cellOne_lt_top v μ₂ μN

  have hterm : ∀ p : ℤ × ℤ, μ' (cellOne v) * (Ideal.absNorm v.asIdeal : ℝ≥0∞) ^ (p.1 - p.2) * ‖f (tor v hπ p)‖ₑ =
      ENNReal.ofReal ‖cellTerm v hπ ((μ' (cellOne v)).toReal : ℂ) δ s W F p‖ := by
    intro p
    have hexp : cellTerm v hπ ((μ' (cellOne v)).toReal : ℂ) δ s W F p =
        ((μ' (cellOne v)).toReal : ℂ) * ((Ideal.absNorm v.asIdeal : ℂ) ^ (p.1 - p.2)) * f (tor v hπ p) := rfl
    rw [hexp, norm_mul, norm_mul, norm_absNorm_zpow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_mul (mul_nonneg ENNReal.toReal_nonneg (zpow_nonneg (Nat.cast_nonneg _) _)),
      ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin1.ne, ofReal_norm,
      ofReal_absNorm_zpow v]
  have hlin : ∫⁻ g, ‖f g‖ₑ ∂μ' =
      ∑' p : ℤ × ℤ, ENNReal.ofReal ‖cellTerm v hπ ((μ' (cellOne v)).toReal : ℂ) δ s W F p‖ := by
    rw [lintegral_eq_tsum_cell v hπ hϖ μ₂ μN (fun g => ‖f g‖ₑ) (fun n hn g => by simp only [hfN n hn g])
      (fun k hk g => by simp only [hfK k hk g])]
    exact tsum_congr hterm
  have hfinI : HasFiniteIntegral f μ' := by
    rw [hasFiniteIntegral_iff_enorm, hlin, ← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hsum]
    exact ENNReal.ofReal_lt_top
  have hint : Integrable f μ' := ⟨hfm.aestronglyMeasurable, hfinI⟩
  haveI := isMulRightInvariant_Nr v μN
  exact ⟨hint, LanglandsTunnell.RankinSelberg.hasSum_cell_terms_rsLocalIntegral v hπ hϖ μ₂ μN δ hδN hδK s W F hN hK
    hint⟩

end Expansion
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries.UnipotentMass"

private theorem exists_valued_le_exp_one_and_psiLocal_ne_one (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧
      NumberField.StandardAddChar.psiLocal ℚ v x ≠ 1 := by
  have h := LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ v
    (NumberField.StandardAddChar.psiLocal ℚ v)
    ⟨0, fun x hx => LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers ℚ v x (by
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
      simpa using hx)⟩
    (LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ v)
  rw [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat v] at h
  obtain ⟨x, hx, hne⟩ := h.2
  exact ⟨x, by simpa using hx, hne⟩

private theorem not_forall_apply_eq_one_of_eq_psiLocal (v : HeightOneSpectrum (𝓞 ℚ))
    (η : AddChar (v.adicCompletion ℚ) ℂ)
    (hη : η = NumberField.StandardAddChar.psiLocal ℚ v ∨ η = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹) :
    ¬ ∀ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (1 : ℤ) → η x = 1 := by
  intro hall
  obtain ⟨x, hx, hne⟩ := exists_valued_le_exp_one_and_psiLocal_ne_one v
  rcases hη with rfl | rfl
  · exact hne (hall x hx)
  · apply hne
    have h := hall (-x) (by rwa [Valuation.map_neg])
    rwa [AddChar.inv_apply, neg_neg] at h

private theorem exists_nat_forall_valued_sub_le_imp_mem (v : HeightOneSpectrum (𝓞 ℚ))
    {x : v.adicCompletion ℚ} {t : Set (v.adicCompletion ℚ)} (ht : t ∈ nhds x) :
    ∃ L : ℕ, ∀ y : v.adicCompletion ℚ, Valued.v (y - x) ≤ WithZero.exp (-(L : ℤ)) → y ∈ t := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 ht
  have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by
    exact (map_ne_zero _).2 γ.ne_zero
  refine ⟨(1 - WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)).toNat, fun y hy => hγ ?_⟩
  show Valuation.restrict Valued.v (y - x) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  refine lt_of_le_of_lt hy ?_
  conv_rhs => rw [← WithZero.exp_log hne]
  rw [WithZero.exp_lt_exp]
  omega

private theorem exists_nat_forall_row_mem (v : HeightOneSpectrum (𝓞 ℚ)) {r : Fin 3 → v.adicCompletion ℚ}
    {t : Set (Fin 3 → v.adicCompletion ℚ)} (ht : t ∈ nhds r) :
    ∃ L : ℕ, ∀ r' : Fin 3 → v.adicCompletion ℚ,
      (∀ j, Valued.v (r' j - r j) ≤ WithZero.exp (-(L : ℤ))) → r' ∈ t := by
  rw [nhds_pi] at ht
  obtain ⟨I, -, u, hu, hsub⟩ := Filter.mem_pi.1 ht
  choose Lf hLf using fun j => exists_nat_forall_valued_sub_le_imp_mem v (hu j)
  refine ⟨∑ j, Lf j, fun r' hr' => hsub fun j _ => hLf j (r' j) (le_trans (hr' j) ?_)⟩
  rw [WithZero.exp_le_exp]
  have : Lf j ≤ ∑ i, Lf i := Finset.single_le_sum (fun i _ => Nat.zero_le (Lf i)) (Finset.mem_univ j)
  omega

private theorem exists_nat_forall_matrix_mem (v : HeightOneSpectrum (𝓞 ℚ))
    {a : Fin 3 → Fin 3 → v.adicCompletion ℚ} {t : Set (Fin 3 → Fin 3 → v.adicCompletion ℚ)}
    (ht : t ∈ nhds a) :
    ∃ L : ℕ, ∀ b : Fin 3 → Fin 3 → v.adicCompletion ℚ,
      (∀ i j, Valued.v (b i j - a i j) ≤ WithZero.exp (-(L : ℤ))) → b ∈ t := by
  rw [nhds_pi] at ht
  obtain ⟨I, -, u, hu, hsub⟩ := Filter.mem_pi.1 ht
  choose Lf hLf using fun i => exists_nat_forall_row_mem v (hu i)
  refine ⟨∑ i, Lf i, fun b hb => hsub fun i _ => hLf i (b i) fun j => le_trans (hb i j) ?_⟩
  rw [WithZero.exp_le_exp]
  have : Lf i ≤ ∑ l, Lf l := Finset.single_le_sum (fun l _ => Nat.zero_le (Lf l)) (Finset.mem_univ i)
  omega

private theorem valued_inv_sub_one_le (v : HeightOneSpectrum (𝓞 ℚ)) {C : WithZero (Multiplicative ℤ)}
    (k : LocalGL3 v) (hk : k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (hkC : ∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
      (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ C) (i j : Fin 3) :
    Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
      (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ C := by
  have hk' : (∀ i j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ 1) ∧
      (∀ i j, Valued.v (((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ 1) := hk
  have hmul : (1 - (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) *
      ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
        ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) - 1 := by
    rw [sub_mul, one_mul, Units.mul_inv]
  rw [← Matrix.sub_apply, ← hmul]
  refine valued_mul_apply_le3 (𝓞 ℚ) ℚ v (fun l => ?_) (fun l => hk'.2 l j)
  rw [Matrix.sub_apply, Valuation.map_sub_swap]
  exact hkC i l

private theorem exists_nat_forall_mem_of_isOpen (v : HeightOneSpectrum (𝓞 ℚ)) (V₀ : Subgroup (LocalGL3 v))
    (hV₀ : IsOpen (V₀ : Set (LocalGL3 v))) :
    ∃ L : ℕ, ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v,
      (∀ i j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
        (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(L : ℤ))) → k ∈ V₀ := by
  have h1 : (V₀ : Set (LocalGL3 v)) ∈ nhds (1 : LocalGL3 v) := hV₀.mem_nhds V₀.one_mem
  rw [Units.isInducing_embedProduct.nhds_eq_comap] at h1
  obtain ⟨T, hT, hTsub⟩ := Filter.mem_comap.1 h1
  have hpt : Units.embedProduct (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) (1 : LocalGL3 v) =
      ((1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)),
        MulOpposite.op (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) := by
    rfl
  rw [hpt, nhds_prod_eq] at hT
  obtain ⟨A, hA, B, hB, hAB⟩ := Filter.mem_prod_iff.1 hT
  have hB' : (MulOpposite.op ⁻¹' B : Set (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) ∈
      nhds (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) := by
    have h : (MulOpposite.op ⁻¹' B : Set (Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))) ∈
        Filter.comap MulOpposite.op (nhds (MulOpposite.op (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))) :=
      Filter.preimage_mem_comap hB
    rwa [MulOpposite.comap_op_nhds, MulOpposite.unop_op] at h
  obtain ⟨L, hL⟩ := exists_nat_forall_matrix_mem v (Filter.inter_mem hA hB')
  refine ⟨L, fun k hk hkL => hTsub ?_⟩
  have hkval := hL (k : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) hkL
  have hkinv := hL ((k⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))
    (fun i j => valued_inv_sub_one_le v k hk hkL i j)
  exact hAB ⟨hkval.1, hkinv.2⟩

private theorem val_det_diagZ {K : Type*} [Field K] (π : K) (hπ : π ≠ 0) (k : ℤ) :
    ((Matrix.GeneralLinearGroup.det (diagZ π hπ k) : Kˣ) : K) = π ^ k := by
  simp [diagZ, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two_of]

private theorem val_det_scalarPi {K : Type*} [Field K] (π : K) (hπ : π ≠ 0) :
    ((Matrix.GeneralLinearGroup.det (scalarPi π hπ) : Kˣ) : K) = π * π := by
  simp [scalarPi, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two_of]

private theorem valued_det_tor (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : unif v ϖ ≠ 0) (hϖ : Valued.v (unif v ϖ) = WithZero.exp (-1 : ℤ)) (p : ℤ × ℤ) :
    Valued.v ((Matrix.GeneralLinearGroup.det (tor v hπ p) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) =
      WithZero.exp (-(p.1 + p.2)) := by
  have h : Valued.v ((Matrix.GeneralLinearGroup.det (tor v hπ p) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) =
      Valued.v (unif v ϖ) ^ (p.1 - p.2) * (Valued.v (unif v ϖ) * Valued.v (unif v ϖ)) ^ p.2 := by
    simp only [tor, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, val_det_diagZ, val_det_scalarPi,
      map_zpow₀]
  rw [h, hϖ, ← WithZero.exp_add, ← WithZero.exp_zsmul, ← WithZero.exp_zsmul, ← WithZero.exp_add]
  congr 1
  push_cast
  ring

private theorem toNNReal_exp {e : NNReal} (he : e ≠ 0) (n : ℤ) :
    WithZeroMulInt.toNNReal he (WithZero.exp n) = e ^ n := by
  rw [WithZeroMulInt.toNNReal_neg_apply he WithZero.exp_ne_zero]
  congr 1

private theorem detModulus_eq (v : HeightOneSpectrum (𝓞 ℚ)) (g : G2 v) :
    detModulus v g = ((WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero (v := v))
      (Valued.v ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)) : NNReal) : ℝ) := by
  rw [detModulus, LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ v, coe_nnnorm,
    NumberField.FinitePlace.norm_def]

private theorem detModulus_eq_one_of_valued_det_eq_one (v : HeightOneSpectrum (𝓞 ℚ)) (g : G2 v)
    (h : Valued.v ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1) :
    detModulus v g = 1 := by
  rw [detModulus_eq, h, map_one, NNReal.coe_one]

private theorem detModulus_tor (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : unif v ϖ ≠ 0) (hϖ : Valued.v (unif v ϖ) = WithZero.exp (-1 : ℤ)) (p : ℤ × ℤ) :
    detModulus v (tor v hπ p) = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(p.1 + p.2)) := by
  rw [detModulus_eq, valued_det_tor v hπ hϖ p, toNNReal_exp, NNReal.coe_zpow, NNReal.coe_natCast]

private theorem one_lt_absNorm_real (v : HeightOneSpectrum (𝓞 ℚ)) : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm (v := v)

private theorem apply_mul_scalarPi_zpow (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : unif v ϖ ≠ 0) {c : ℂ} (hc : c ≠ 0) (W₂ : G2 v → ℂ)
    (hW₂Z : ∀ g : G2 v, W₂ (g * scalarPi (unif v ϖ) hπ) = c * W₂ g) (g : G2 v) (m : ℤ) :
    W₂ (g * scalarPi (unif v ϖ) hπ ^ m) = c ^ m * W₂ g := by
  induction m using Int.induction_on with
  | zero => simp
  | succ i ih =>
    rw [zpow_add_one, ← mul_assoc, hW₂Z, ih, zpow_add_one₀ hc]
    ring
  | pred i ih =>
    have h := hW₂Z (g * scalarPi (unif v ϖ) hπ ^ (-(i : ℤ) - 1))
    rw [mul_assoc, ← zpow_add_one, sub_add_cancel, ih] at h
    rw [zpow_sub_one₀ hc]
    calc W₂ (g * scalarPi (unif v ϖ) hπ ^ (-(i : ℤ) - 1))
        = c⁻¹ * (c * W₂ (g * scalarPi (unif v ϖ) hπ ^ (-(i : ℤ) - 1))) := by
          rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
      _ = c ^ (-(i : ℤ)) * c⁻¹ * W₂ g := by rw [← h]; ring

private theorem apply_tor (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ} (hπ : unif v ϖ ≠ 0)
    (b : ℂ) {c : ℂ} (hc : c ≠ 0) (W₂ : G2 v → ℂ)
    (hW₂Z : ∀ g : G2 v, W₂ (g * scalarPi (unif v ϖ) hπ) = c * W₂ g)
    (hW₂T : ∀ m : ℤ, W₂ (diagZ (unif v ϖ) hπ m) = torusFactor (Ideal.absNorm v.asIdeal : ℂ) b c m) (p : ℤ × ℤ) :
    W₂ (tor v hπ p) = c ^ p.2 * torusFactor (Ideal.absNorm v.asIdeal : ℂ) b c (p.1 - p.2) := by
  rw [tor, apply_mul_scalarPi_zpow v hπ hc W₂ hW₂Z, hW₂T]

private theorem exists_norm_heckeRecursionSeq_le (N lam om : ℂ) (hN : N ≠ 0) :
    ∃ A ρ : ℝ, 0 ≤ A ∧ 1 ≤ ρ ∧ ∀ n : ℕ, ‖heckeRecursionSeq N lam om n‖ ≤ A * ρ ^ n := by
  have hN' : 0 < ‖N‖ := norm_pos_iff.2 hN
  refine ⟨max 1 (‖lam‖ / ‖N‖), max 1 ((‖lam‖ + ‖om‖) / ‖N‖), le_trans zero_le_one (le_max_left _ _),
    le_max_left _ _, fun n => ?_⟩
  refine Nat.strong_induction_on n ?_
  intro n ih
  · rcases n with _ | _ | n
    · simp [heckeRecursionSeq]
    · show ‖heckeRecursionSeq N lam om 1‖ ≤ max 1 (‖lam‖ / ‖N‖) * max 1 ((‖lam‖ + ‖om‖) / ‖N‖) ^ 1
      have h1 : ‖heckeRecursionSeq N lam om 1‖ = ‖lam‖ / ‖N‖ := by simp [heckeRecursionSeq]
      rw [h1, pow_one]
      calc ‖lam‖ / ‖N‖ ≤ max 1 (‖lam‖ / ‖N‖) := le_max_right _ _
        _ = max 1 (‖lam‖ / ‖N‖) * 1 := (mul_one _).symm
        _ ≤ max 1 (‖lam‖ / ‖N‖) * max 1 ((‖lam‖ + ‖om‖) / ‖N‖) :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) (le_trans zero_le_one (le_max_left _ _))
    · show ‖heckeRecursionSeq N lam om (n + 2)‖ ≤ max 1 (‖lam‖ / ‖N‖) * max 1 ((‖lam‖ + ‖om‖) / ‖N‖) ^ (n + 2)
      have h0 := ih n (by omega)
      have h1 := ih (n + 1) (by omega)
      have hA : (0 : ℝ) ≤ max 1 (‖lam‖ / ‖N‖) := le_trans zero_le_one (le_max_left _ _)
      have hρ : (1 : ℝ) ≤ max 1 ((‖lam‖ + ‖om‖) / ‖N‖) := le_max_left _ _
      have hρN : ‖lam‖ + ‖om‖ ≤ max 1 ((‖lam‖ + ‖om‖) / ‖N‖) * ‖N‖ :=
        (div_le_iff₀ hN').1 (le_max_right _ _)
      have hpow : (0 : ℝ) ≤ max 1 ((‖lam‖ + ‖om‖) / ‖N‖) ^ n := pow_nonneg (le_trans zero_le_one hρ) n
      have hpow' : max 1 ((‖lam‖ + ‖om‖) / ‖N‖) ^ n ≤ max 1 ((‖lam‖ + ‖om‖) / ‖N‖) ^ (n + 1) :=
        pow_le_pow_right₀ hρ (Nat.le_succ n)
      have hu0 : ‖heckeRecursionSeq N lam om n‖ ≤ max 1 (‖lam‖ / ‖N‖) * max 1 ((‖lam‖ + ‖om‖) / ‖N‖) ^ (n + 1) :=
        h0.trans (mul_le_mul_of_nonneg_left hpow' hA)
      have hstep : ‖heckeRecursionSeq N lam om (n + 2)‖ =
          ‖lam * heckeRecursionSeq N lam om (n + 1) - om * heckeRecursionSeq N lam om n‖ / ‖N‖ := by
        simp [heckeRecursionSeq]
      rw [hstep, div_le_iff₀ hN']
      calc ‖lam * heckeRecursionSeq N lam om (n + 1) - om * heckeRecursionSeq N lam om n‖
          ≤ ‖lam‖ * ‖heckeRecursionSeq N lam om (n + 1)‖ + ‖om‖ * ‖heckeRecursionSeq N lam om n‖ := by
            refine (norm_sub_le _ _).trans ?_
            rw [norm_mul, norm_mul]
        _ ≤ ‖lam‖ * (max 1 (‖lam‖ / ‖N‖) * max 1 ((‖lam‖ + ‖om‖) / ‖N‖) ^ (n + 1)) +
              ‖om‖ * (max 1 (‖lam‖ / ‖N‖) * max 1 ((‖lam‖ + ‖om‖) / ‖N‖) ^ (n + 1)) :=
            add_le_add (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) (mul_le_mul_of_nonneg_left hu0 (norm_nonneg _))
        _ = (‖lam‖ + ‖om‖) * (max 1 (‖lam‖ / ‖N‖) * max 1 ((‖lam‖ + ‖om‖) / ‖N‖) ^ (n + 1)) := by ring
        _ ≤ (max 1 ((‖lam‖ + ‖om‖) / ‖N‖) * ‖N‖) *
              (max 1 (‖lam‖ / ‖N‖) * max 1 ((‖lam‖ + ‖om‖) / ‖N‖) ^ (n + 1)) :=
            mul_le_mul_of_nonneg_right hρN (mul_nonneg hA (pow_nonneg (le_trans zero_le_one hρ) _))
        _ = max 1 (‖lam‖ / ‖N‖) * max 1 ((‖lam‖ + ‖om‖) / ‖N‖) ^ (n + 2) * ‖N‖ := by ring

private theorem exists_norm_torusFactor_le (N lam om : ℂ) (hN : N ≠ 0) :
    ∃ A ρ : ℝ, 0 ≤ A ∧ 1 ≤ ρ ∧ ∀ k : ℤ, ‖torusFactor N lam om k‖ ≤ A * ρ ^ k.toNat := by
  obtain ⟨A, ρ, hA, hρ, h⟩ := exists_norm_heckeRecursionSeq_le N lam om hN
  refine ⟨A, ρ, hA, hρ, fun k => ?_⟩
  unfold torusFactor
  split_ifs with hk
  · exact h k.toNat
  · rw [norm_zero]
    exact mul_nonneg hA (pow_nonneg (le_trans zero_le_one hρ) _)

private def cellWeight (L : ℕ) (r : ℝ) (j : ℤ) : ℝ := if -(L : ℤ) ≤ j then r ^ (j + L).toNat else 0

private theorem cellWeight_of_le {L : ℕ} {r : ℝ} {j : ℤ} (h : -(L : ℤ) ≤ j) :
    cellWeight L r j = r ^ (j + L).toNat := by
  unfold cellWeight
  exact if_pos h

private theorem cellWeight_of_lt {L : ℕ} {r : ℝ} {j : ℤ} (h : j < -(L : ℤ)) : cellWeight L r j = 0 := by
  unfold cellWeight
  exact if_neg (not_le.2 h)

private theorem cellWeight_nonneg {L : ℕ} {r : ℝ} (hr0 : 0 ≤ r) (j : ℤ) : 0 ≤ cellWeight L r j := by
  unfold cellWeight
  split_ifs
  · exact pow_nonneg hr0 _
  · exact le_rfl

private theorem cellWeight_nonneg' {L : ℕ} {r : ℝ} (hr0 : 0 ≤ r) : 0 ≤ cellWeight L r :=
  fun j => cellWeight_nonneg hr0 j

attribute [irreducible] cellWeight

private theorem summable_shift_geometric (L : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) : Summable (cellWeight L r) := by
  have hinj : Function.Injective fun n : ℕ => (n : ℤ) - L := by
    intro a b hab
    simpa using hab
  have hzero : ∀ j ∉ Set.range fun n : ℕ => (n : ℤ) - L, cellWeight L r j = 0 := by
    intro j hj
    refine cellWeight_of_lt ?_
    by_contra hle
    rw [not_lt] at hle
    exact hj ⟨(j + L).toNat, show (((j + L).toNat : ℕ) : ℤ) - L = j by omega⟩
  have hgeo : Summable (cellWeight L r ∘ fun n : ℕ => (n : ℤ) - L) := by
    refine (summable_geometric_of_lt_one hr0 hr1).congr fun n => ?_
    have h2 : ((n : ℤ) - L + L).toNat = n := by omega
    rw [Function.comp_apply, cellWeight_of_le (by omega), h2]
  exact (hinj.summable_iff hzero).1 hgeo

private theorem summable_cells_core (w₁ w₂ : ℤ → ℝ) (h₁ : Summable w₁) (h₂ : Summable w₂) (n₁ : 0 ≤ w₁)
    (n₂ : 0 ≤ w₂) : Summable fun p : ℤ × ℤ => w₁ (p.1 - p.2) * w₂ p.2 := by
  have h : Summable fun x : ℤ × ℤ => w₁ x.1 * w₂ x.2 := h₁.mul_of_nonneg h₂ n₁ n₂
  have hinj : Function.Injective fun p : ℤ × ℤ => (p.1 - p.2, p.2) := by
    intro p q hpq
    simp only [Prod.mk.injEq] at hpq
    exact Prod.ext (by omega) hpq.2
  have h2 := h.comp_injective hinj
  exact h2

private theorem summable_cells (L : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun p : ℤ × ℤ => cellWeight L r (p.1 - p.2) * cellWeight L r p.2 :=
  summable_cells_core (cellWeight L r) (cellWeight L r) (summable_shift_geometric L hr0 hr1)
    (summable_shift_geometric L hr0 hr1) (cellWeight_nonneg' hr0) (cellWeight_nonneg' hr0)

private theorem zpow_rpow_comm {x : ℝ} (hx : 0 < x) (j : ℤ) (y : ℝ) : (x ^ j) ^ y = (x ^ y) ^ j := by
  rw [← Real.rpow_intCast x j, ← Real.rpow_mul hx.le, mul_comm, Real.rpow_mul hx.le, Real.rpow_intCast]

private theorem re_sub_half (s : ℂ) : (s - 1 / 2 : ℂ).re = s.re - 1 / 2 := by
  simp

private theorem exists_forall_summable_majorant (L : ℕ) {N : ℝ} (hN1 : 1 < N) {C R A ρ : ℝ} (hC : 0 ≤ C)
    (hR : 1 ≤ R) (hA : 0 ≤ A) (hρ : 1 ≤ ρ) {c₀ : ℝ} (hc₀ : 0 < c₀) {V : ℝ} (hV : 0 ≤ V) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → Summable fun p : ℤ × ℤ =>
      if -(L : ℤ) ≤ p.1 - p.2 ∧ -(L : ℤ) ≤ p.2 then
        V * N ^ (p.1 - p.2) * (((C * R ^ ((p.1 - p.2 + L).toNat + (p.2 + L).toNat)) *
          (c₀ ^ p.2 * (A * ρ ^ ((p.1 - p.2 + L).toNat + (p.2 + L).toNat)))) *
            (N ^ (-(p.1 + p.2))) ^ (s.re - 1 / 2))
      else 0 := by
  have hN0 : 0 < N := zero_lt_one.trans hN1
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hρ0 : 0 ≤ ρ := zero_le_one.trans hρ
  have hc₁ : (1 : ℝ) ≤ max 1 c₀ := le_max_left _ _
  have hD0 : 0 < N * max 1 c₀ * ρ * R := by positivity
  obtain ⟨n₀, hn₀⟩ := pow_unbounded_of_one_lt (N * max 1 c₀ * ρ * R) hN1
  refine ⟨(n₀ : ℝ) + 1 / 2, fun s hs => ?_⟩
  have hσ'n₀ : (n₀ : ℝ) ≤ s.re - 1 / 2 := by linarith
  have hσ'0 : 0 ≤ s.re - 1 / 2 := le_trans (Nat.cast_nonneg n₀) hσ'n₀
  have hM1 : 1 ≤ N ^ (s.re - 1 / 2) := Real.one_le_rpow hN1.le hσ'0
  have hM0 : 0 < N ^ (s.re - 1 / 2) := zero_lt_one.trans_le hM1
  have hDM : N * max 1 c₀ * ρ * R < N ^ (s.re - 1 / 2) := by
    calc N * max 1 c₀ * ρ * R < N ^ n₀ := hn₀
      _ = N ^ (n₀ : ℝ) := (Real.rpow_natCast N n₀).symm
      _ ≤ N ^ (s.re - 1 / 2) := Real.rpow_le_rpow_of_exponent_le hN1.le hσ'n₀
  have hr0 : 0 ≤ N * max 1 c₀ * ρ * R / N ^ (s.re - 1 / 2) := div_nonneg hD0.le hM0.le
  have hr1 : N * max 1 c₀ * ρ * R / N ^ (s.re - 1 / 2) < 1 := (div_lt_one hM0).2 hDM
  have hK₀ : 0 ≤ V * (N ^ (-(L : ℤ)) * c₀ ^ (-(L : ℤ)) * (N ^ (s.re - 1 / 2)) ^ (3 * (L : ℤ))) * (A * C) := by
    positivity
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) ((summable_cells L hr0 hr1).mul_left
    (V * (N ^ (-(L : ℤ)) * c₀ ^ (-(L : ℤ)) * (N ^ (s.re - 1 / 2)) ^ (3 * (L : ℤ))) * (A * C)))
  · skip
    split_ifs
    · positivity
    · exact le_rfl
  · obtain ⟨p₁, p₂⟩ := p
    dsimp only
    by_cases hin : -(L : ℤ) ≤ p₁ - p₂ ∧ -(L : ℤ) ≤ p₂
    · have hk : -(L : ℤ) ≤ p₁ - p₂ := hin.1
      have hm : -(L : ℤ) ≤ p₂ := hin.2
      rw [if_pos hin, cellWeight_of_le hk, cellWeight_of_le hm, zpow_rpow_comm hN0]
      have hNk : N ^ (p₁ - p₂) ≤ N ^ (-(L : ℤ)) * N ^ ((p₁ - p₂ + L).toNat + (p₂ + L).toNat) := by
        have hsplit : N ^ (p₁ - p₂) = N ^ (-(L : ℤ)) * N ^ (p₁ - p₂ + L).toNat := by
          rw [← zpow_natCast, ← zpow_add₀ hN0.ne']
          congr 1
          omega
        rw [hsplit]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hN1.le (Nat.le_add_right (p₁ - p₂ + L).toNat (p₂ + L).toNat)) (zpow_pos hN0 _).le
      have hcm : c₀ ^ p₂ ≤ c₀ ^ (-(L : ℤ)) * max 1 c₀ ^ ((p₁ - p₂ + L).toNat + (p₂ + L).toNat) := by
        have hsplit : c₀ ^ p₂ = c₀ ^ (-(L : ℤ)) * c₀ ^ (p₂ + L).toNat := by
          rw [← zpow_natCast, ← zpow_add₀ hc₀.ne']
          congr 1
          omega
        rw [hsplit]
        refine mul_le_mul_of_nonneg_left ?_ (zpow_pos hc₀ _).le
        exact (pow_le_pow_left₀ hc₀.le (le_max_right 1 c₀) (p₂ + L).toNat).trans
          (pow_le_pow_right₀ hc₁ (Nat.le_add_left (p₂ + L).toNat (p₁ - p₂ + L).toNat))
      have hMj : (N ^ (s.re - 1 / 2)) ^ (-(p₁ + p₂)) ≤
          (N ^ (s.re - 1 / 2)) ^ (3 * (L : ℤ)) * (N ^ (s.re - 1 / 2))⁻¹ ^ ((p₁ - p₂ + L).toNat + (p₂ + L).toNat) := by
        rw [inv_pow, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hM0.ne']
        exact zpow_le_zpow_right₀ hM1 (by omega)
      have hfac : V * (N ^ (-(L : ℤ)) * N ^ ((p₁ - p₂ + L).toNat + (p₂ + L).toNat)) *
          ((C * R ^ ((p₁ - p₂ + L).toNat + (p₂ + L).toNat)) *
            ((c₀ ^ (-(L : ℤ)) * max 1 c₀ ^ ((p₁ - p₂ + L).toNat + (p₂ + L).toNat)) *
              (A * ρ ^ ((p₁ - p₂ + L).toNat + (p₂ + L).toNat))) *
            ((N ^ (s.re - 1 / 2)) ^ (3 * (L : ℤ)) *
              (N ^ (s.re - 1 / 2))⁻¹ ^ ((p₁ - p₂ + L).toNat + (p₂ + L).toNat))) =
          V * (N ^ (-(L : ℤ)) * c₀ ^ (-(L : ℤ)) * (N ^ (s.re - 1 / 2)) ^ (3 * (L : ℤ))) * (A * C) *
            ((N * max 1 c₀ * ρ * R / N ^ (s.re - 1 / 2)) ^ (p₁ - p₂ + L).toNat *
              (N * max 1 c₀ * ρ * R / N ^ (s.re - 1 / 2)) ^ (p₂ + L).toNat) := by
        rw [← pow_add, div_pow, mul_pow, mul_pow, mul_pow, inv_pow]
        ring
      rw [← hfac]
      have h2 : c₀ ^ p₂ * (A * ρ ^ ((p₁ - p₂ + L).toNat + (p₂ + L).toNat)) ≤
          (c₀ ^ (-(L : ℤ)) * max 1 c₀ ^ ((p₁ - p₂ + L).toNat + (p₂ + L).toNat)) *
            (A * ρ ^ ((p₁ - p₂ + L).toNat + (p₂ + L).toNat)) :=
        mul_le_mul_of_nonneg_right hcm (by positivity)
      have h3 : (C * R ^ ((p₁ - p₂ + L).toNat + (p₂ + L).toNat)) *
            (c₀ ^ p₂ * (A * ρ ^ ((p₁ - p₂ + L).toNat + (p₂ + L).toNat))) ≤
          (C * R ^ ((p₁ - p₂ + L).toNat + (p₂ + L).toNat)) *
            ((c₀ ^ (-(L : ℤ)) * max 1 c₀ ^ ((p₁ - p₂ + L).toNat + (p₂ + L).toNat)) *
              (A * ρ ^ ((p₁ - p₂ + L).toNat + (p₂ + L).toNat))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      have h5 : V * N ^ (p₁ - p₂) ≤ V * (N ^ (-(L : ℤ)) * N ^ ((p₁ - p₂ + L).toNat + (p₂ + L).toNat)) :=
        mul_le_mul_of_nonneg_left hNk hV
      have hinner : (C * R ^ ((p₁ - p₂ + L).toNat + (p₂ + L).toNat)) *
            (c₀ ^ p₂ * (A * ρ ^ ((p₁ - p₂ + L).toNat + (p₂ + L).toNat))) * (N ^ (s.re - 1 / 2)) ^ (-(p₁ + p₂)) ≤
          (C * R ^ ((p₁ - p₂ + L).toNat + (p₂ + L).toNat)) *
            ((c₀ ^ (-(L : ℤ)) * max 1 c₀ ^ ((p₁ - p₂ + L).toNat + (p₂ + L).toNat)) *
              (A * ρ ^ ((p₁ - p₂ + L).toNat + (p₂ + L).toNat))) *
            ((N ^ (s.re - 1 / 2)) ^ (3 * (L : ℤ)) *
              (N ^ (s.re - 1 / 2))⁻¹ ^ ((p₁ - p₂ + L).toNat + (p₂ + L).toNat)) :=
        mul_le_mul h3 hMj (zpow_pos hM0 _).le (by positivity)
      exact mul_le_mul h5 hinner (by positivity) (by positivity)
    · rw [if_neg hin]
      exact mul_nonneg hK₀ (mul_nonneg (cellWeight_nonneg hr0 _) (cellWeight_nonneg hr0 _))

private theorem exists_abscissa_summable_of_member (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : unif v ϖ ≠ 0) (hϖ : Valued.v (unif v ϖ) = WithZero.exp (-1 : ℤ)) (F : LocalGL3 v → ℂ) (L : ℕ)
    (hsupp : ∀ k m : ℤ, k < -(L : ℤ) ∨ m < -(L : ℤ) →
      F (iotaGL (diagZ (unif v ϖ) hπ k * scalarPi (unif v ϖ) hπ ^ m)) = 0)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 1 ≤ R)
    (hgrowth : ∀ k m : ℤ, -(L : ℤ) ≤ k → -(L : ℤ) ≤ m →
      ‖F (iotaGL (diagZ (unif v ϖ) hπ k * scalarPi (unif v ϖ) hπ ^ m))‖ ≤ C * R ^ ((k + L).toNat + (m + L).toNat))
    (b c : ℂ) (hc : c ≠ 0) (W₂ : G2 v → ℂ)
    (hW₂Z : ∀ g : G2 v, W₂ (g * scalarPi (unif v ϖ) hπ) = c * W₂ g)
    (hW₂T : ∀ m : ℤ, W₂ (diagZ (unif v ϖ) hπ m) = torusFactor (Ideal.absNorm v.asIdeal : ℂ) b c m) (vol : ℂ) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Summable fun p : ℤ × ℤ => ‖cellTerm v hπ vol (detModulus v) s (fun g => F (iotaGL g)) W₂ p‖ := by
  have hN1 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := one_lt_absNorm_real v
  have hN0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := zero_lt_one.trans hN1
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hNC : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
    have h : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := (zero_lt_one.trans hN1).ne'
    exact_mod_cast (show (Ideal.absNorm v.asIdeal : ℕ) ≠ 0 by exact_mod_cast h)
  obtain ⟨A, ρ, hA, hρ, htf⟩ := exists_norm_torusFactor_le (Ideal.absNorm v.asIdeal : ℂ) b c hNC
  have hc0 : 0 < ‖c‖ := norm_pos_iff.2 hc
  obtain ⟨σ, hσ⟩ := exists_forall_summable_majorant L hN1 hC hR hA hρ hc0 (norm_nonneg vol)
  refine ⟨σ, fun s hs => Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_) (hσ s hs)⟩
  obtain ⟨p₁, p₂⟩ := p
  dsimp only
  have hW := apply_tor v hπ b hc W₂ hW₂Z hW₂T (p₁, p₂)
  have hδ := detModulus_tor v hπ hϖ (p₁, p₂)
  dsimp only at hW hδ
  by_cases hin : -(L : ℤ) ≤ p₁ - p₂ ∧ -(L : ℤ) ≤ p₂
  · rw [if_pos hin]
    have hδpos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) ^ (-(p₁ + p₂)) := zpow_pos (zero_lt_one.trans hN1) _
    have hnorm : ‖cellTerm v hπ vol (detModulus v) s (fun g => F (iotaGL g)) W₂ (p₁, p₂)‖ =
        ‖vol‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (p₁ - p₂) *
          ((‖F (iotaGL (tor v hπ (p₁, p₂)))‖ *
            (‖c‖ ^ p₂ * ‖torusFactor (Ideal.absNorm v.asIdeal : ℂ) b c (p₁ - p₂)‖)) *
              ((Ideal.absNorm v.asIdeal : ℝ) ^ (-(p₁ + p₂))) ^ (s.re - 1 / 2)) := by
      simp only [cellTerm, norm_mul, norm_zpow, Complex.norm_natCast, hW, hδ]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hδpos, re_sub_half]
    rw [hnorm]
    have hFt : ‖F (iotaGL (tor v hπ (p₁, p₂)))‖ ≤ C * R ^ ((p₁ - p₂ + L).toNat + (p₂ + L).toNat) :=
      hgrowth (p₁ - p₂) p₂ hin.1 hin.2
    have htf' : ‖torusFactor (Ideal.absNorm v.asIdeal : ℂ) b c (p₁ - p₂)‖ ≤
        A * ρ ^ ((p₁ - p₂ + L).toNat + (p₂ + L).toNat) :=
      (htf (p₁ - p₂)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hρ (by omega)) hA)
    have hmid : ‖F (iotaGL (tor v hπ (p₁, p₂)))‖ *
          (‖c‖ ^ p₂ * ‖torusFactor (Ideal.absNorm v.asIdeal : ℂ) b c (p₁ - p₂)‖) ≤
        (C * R ^ ((p₁ - p₂ + L).toNat + (p₂ + L).toNat)) *
          (‖c‖ ^ p₂ * (A * ρ ^ ((p₁ - p₂ + L).toNat + (p₂ + L).toNat))) :=
      mul_le_mul hFt (mul_le_mul_of_nonneg_left htf' (zpow_pos hc0 _).le)
        (mul_nonneg (zpow_pos hc0 _).le (norm_nonneg _)) (by positivity)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul_of_nonneg_right hmid (Real.rpow_nonneg hδpos.le _)
  · rw [if_neg hin]
    have hzero : F (iotaGL (tor v hπ (p₁, p₂))) = 0 := hsupp (p₁ - p₂) p₂ (by omega)
    have hterm : cellTerm v hπ vol (detModulus v) s (fun g => F (iotaGL g)) W₂ (p₁, p₂) = 0 := by
      simp only [cellTerm]
      rw [hzero]
      ring
    rw [hterm, norm_zero]

private theorem tsum_mul_sum_eq_of_shift_relation {z : ℕ → ℂ} {Z : ℂ} (hZ : Z ≠ 0)
    (hz : Summable fun n => z n * Z ^ n) {M : ℕ} (α : Fin M → ℂ)
    (hrel : ∀ n : ℕ, ∑ i : Fin M, α i * z (n + i) = 0) :
    (∑' n, z n * Z ^ n) * ∑ i : Fin M, α i * Z ^ (M - 1 - (i : ℕ)) =
      ∑ i : Fin M, α i * ∑ n ∈ Finset.range i, z n * Z ^ (n + (M - 1 - (i : ℕ))) := by
  have hshift : ∀ i : ℕ, Summable fun n => z (n + i) * Z ^ (n + i) := fun i =>
    (summable_nat_add_iff (f := fun n => z n * Z ^ n) i).2 hz
  have hZi : ∀ i : ℕ, Z ^ i * Z⁻¹ ^ i = 1 := fun i => by rw [← mul_pow, mul_inv_cancel₀ hZ, one_pow]
  have hg : ∀ i : Fin M, Summable fun n => α i * z (n + i) * Z ^ n := fun i =>
    ((hshift i).mul_right (α i * Z⁻¹ ^ (i : ℕ))).congr fun n => by
      rw [pow_add]
      linear_combination (α i * z (n + i) * Z ^ n) * hZi i
  have key : ∀ i : Fin M, (∑' n, z n * Z ^ n) * (α i * Z ^ (M - 1 - (i : ℕ))) =
      α i * (∑ n ∈ Finset.range i, z n * Z ^ (n + (M - 1 - (i : ℕ)))) +
        Z ^ (M - 1) * ∑' n, α i * z (n + i) * Z ^ n := by
    intro i
    have hi : (i : ℕ) < M := i.isLt
    rw [← hz.sum_add_tsum_nat_add (i : ℕ), add_mul, Finset.sum_mul, Finset.mul_sum, ← tsum_mul_right,
      ← tsum_mul_left]
    congr 1
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [pow_add]
      ring
    · refine tsum_congr fun n => ?_
      have hpow : Z ^ (n + (i : ℕ)) * Z ^ (M - 1 - (i : ℕ)) = Z ^ (M - 1) * Z ^ n := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      linear_combination (z (n + i) * α i) * hpow
  rw [Finset.mul_sum]
  simp only [key]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hzero : (∑ i : Fin M, ∑' n, α i * z (n + i) * Z ^ n) = 0 := by
    rw [← (hasSum_sum fun i _ => (hg i).hasSum).tsum_eq]
    show ∑' n : ℕ, ∑ i : Fin M, α i * z (n + i) * Z ^ n = 0
    refine (tsum_congr fun n => ?_).trans tsum_zero
    rw [← Finset.sum_mul, hrel n, zero_mul]
  rw [hzero, mul_zero, add_zero]

private abbrev shiftSeq {E : Type*} (t : ℕ) (f : ℕ → E) : ℕ → E := fun n => f (n + t)

private theorem shiftSeq_mem_span {E : Type*} [AddCommGroup E] [Module ℂ E] {D : ℕ} (cf : Fin D → ℂ)
    (f : ℕ → E) (hf : ∀ n : ℕ, f (n + D) = ∑ i : Fin D, cf i • f (n + i)) (t : ℕ) :
    shiftSeq t f ∈ Submodule.span ℂ (Set.range fun i : Fin D => shiftSeq (i : ℕ) f) := by
  refine Nat.strong_induction_on t ?_
  intro t ih
  by_cases ht : t < D
  · exact Submodule.subset_span ⟨⟨t, ht⟩, rfl⟩
  · obtain ⟨u, rfl⟩ : ∃ u, t = u + D := ⟨t - D, by omega⟩
    have hexp : shiftSeq (u + D) f = ∑ i : Fin D, cf i • shiftSeq (u + (i : ℕ)) f := by
      funext n
      simp only [shiftSeq, Finset.sum_apply, Pi.smul_apply]
      rw [show n + (u + D) = (n + u) + D by omega, hf (n + u)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show n + u + (i : ℕ) = n + (u + (i : ℕ)) by omega]
    rw [hexp]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (ih (u + (i : ℕ)) ?_)
    have := i.isLt
    omega

private abbrev mulSeq {E : Type*} [AddCommGroup E] [Module ℂ E] (x : ℕ → ℂ) (y : ℕ → E) : ℕ → E :=
  fun n => x n • y n

private theorem shiftSeq_mulSeq_mem_span {E : Type*} [AddCommGroup E] [Module ℂ E] {D₁ D₂ : ℕ}
    (cx : Fin D₁ → ℂ) (x : ℕ → ℂ) (hx : ∀ n : ℕ, x (n + D₁) = ∑ i : Fin D₁, cx i • x (n + i))
    (cy : Fin D₂ → ℂ) (y : ℕ → E) (hy : ∀ n : ℕ, y (n + D₂) = ∑ j : Fin D₂, cy j • y (n + j)) (t : ℕ) :
    shiftSeq t (mulSeq x y) ∈ Submodule.span ℂ
      (Set.range fun ij : Fin D₁ × Fin D₂ => mulSeq (shiftSeq (ij.1 : ℕ) x) (shiftSeq (ij.2 : ℕ) y)) := by
  obtain ⟨lam, hlam⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (shiftSeq_mem_span cx x hx t)
  obtain ⟨mu, hmu⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (shiftSeq_mem_span cy y hy t)
  have hexp : shiftSeq t (mulSeq x y) = ∑ ij : Fin D₁ × Fin D₂,
      (lam ij.1 * mu ij.2) • mulSeq (shiftSeq (ij.1 : ℕ) x) (shiftSeq (ij.2 : ℕ) y) := by
    funext n
    have h1 : x (n + t) = ∑ i : Fin D₁, lam i * x (n + i) := by
      have := congrFun hlam n
      simp only [shiftSeq, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      exact this.symm
    have h2 : y (n + t) = ∑ j : Fin D₂, mu j • y (n + j) := by
      have := congrFun hmu n
      simp only [shiftSeq, Finset.sum_apply, Pi.smul_apply] at this
      exact this.symm
    simp only [shiftSeq, mulSeq, Finset.sum_apply, Pi.smul_apply, Fintype.sum_prod_type]
    rw [h1, h2, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, smul_smul]
    congr 1
    ring
  rw [hexp]
  exact Submodule.sum_mem _ fun ij _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨ij, rfl⟩)

private theorem exists_shift_relation_mulSeq {E : Type*} [AddCommGroup E] [Module ℂ E] {D₁ D₂ : ℕ}
    (cx : Fin D₁ → ℂ) (x : ℕ → ℂ) (hx : ∀ n : ℕ, x (n + D₁) = ∑ i : Fin D₁, cx i • x (n + i))
    (cy : Fin D₂ → ℂ) (y : ℕ → E) (hy : ∀ n : ℕ, y (n + D₂) = ∑ j : Fin D₂, cy j • y (n + j)) :
    ∃ α : Fin (D₁ * D₂ + 1) → ℂ, (∃ i, α i ≠ 0) ∧
      ∀ n : ℕ, ∑ i : Fin (D₁ * D₂ + 1), α i • (x (n + i) • y (n + i)) = 0 := by
  set W := Submodule.span ℂ
    (Set.range fun ij : Fin D₁ × Fin D₂ => mulSeq (shiftSeq (ij.1 : ℕ) x) (shiftSeq (ij.2 : ℕ) y)) with hW
  haveI : Module.Finite ℂ W := Module.Finite.span_of_finite ℂ (Set.finite_range _)
  have hrank : Module.finrank ℂ W ≤ D₁ * D₂ := by
    refine (finrank_range_le_card _).trans ?_
    simp [Fintype.card_prod]
  let w : Fin (D₁ * D₂ + 1) → W := fun i => ⟨shiftSeq (i : ℕ) (mulSeq x y), shiftSeq_mulSeq_mem_span cx x hx cy y hy i⟩
  have hdep : ¬ LinearIndependent ℂ w := fun hli => by
    have := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin] at this
    omega
  obtain ⟨α, hsum, hne⟩ := Fintype.not_linearIndependent_iff.1 hdep
  refine ⟨α, hne, fun n => ?_⟩
  have hval := congrArg Subtype.val hsum
  simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero, w] at hval
  have := congrFun hval n
  simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, shiftSeq, mulSeq] using this

private abbrev uZ (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ} (hπ : unif v ϖ ≠ 0)
    (U : LocalGL3 v → ℂ) (k m : ℤ) : ℂ :=
  U (iotaGL (diagZ (unif v ϖ) hπ k * scalarPi (unif v ϖ) hπ ^ m))

private abbrev nuHalf (v : HeightOneSpectrum (𝓞 ℚ)) : ℂ :=
  Complex.exp ((Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℂ) / 2)

private theorem nuHalf_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) : nuHalf v ≠ 0 := Complex.exp_ne_zero _

private theorem absNorm_complex_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
  have h : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := zero_lt_one.trans (one_lt_absNorm_real v)
  exact_mod_cast (show (Ideal.absNorm v.asIdeal : ℕ) ≠ 0 by exact_mod_cast h.ne')

private theorem absNorm_cpow_neg_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) (s : ℂ) :
    (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero (absNorm_complex_ne_zero v)]
  exact Complex.exp_ne_zero _

private theorem ofReal_zpow_cpow_eq (v : HeightOneSpectrum (𝓞 ℚ)) (j : ℤ) (s : ℂ) :
    ((((Ideal.absNorm v.asIdeal : ℝ) ^ (-j) : ℝ)) : ℂ) ^ (s - 1 / 2) =
      (nuHalf v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ j := by
  have hN0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := zero_lt_one.trans (one_lt_absNorm_real v)
  have hδ0 : ((((Ideal.absNorm v.asIdeal : ℝ) ^ (-j) : ℝ)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (zpow_pos hN0 _).ne'
  have hlogN : Complex.log (Ideal.absNorm v.asIdeal : ℂ) = (Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _)]
  rw [Complex.cpow_def_of_ne_zero hδ0, Complex.cpow_def_of_ne_zero (absNorm_complex_ne_zero v), nuHalf,
    ← Complex.exp_add, ← Complex.exp_int_mul, ← Complex.ofReal_log (zpow_pos hN0 _).le, Real.log_zpow, hlogN]
  congr 1
  push_cast
  ring

private abbrev Z1p (v : HeightOneSpectrum (𝓞 ℚ)) : Polynomial ℂ :=
  Polynomial.C ((Ideal.absNorm v.asIdeal : ℂ) * nuHalf v) * Polynomial.X

private abbrev Z2p (v : HeightOneSpectrum (𝓞 ℚ)) (c : ℂ) : Polynomial ℂ :=
  Polynomial.C (c * (nuHalf v * nuHalf v)) * Polynomial.X ^ 2

private theorem Z1p_eval (v : HeightOneSpectrum (𝓞 ℚ)) (Y : ℂ) :
    (Z1p v).eval Y = (Ideal.absNorm v.asIdeal : ℂ) * nuHalf v * Y := by
  simp [Z1p]

private theorem Z2p_eval (v : HeightOneSpectrum (𝓞 ℚ)) (c Y : ℂ) :
    (Z2p v c).eval Y = c * (nuHalf v * nuHalf v) * Y ^ 2 := by
  simp [Z2p]

private theorem Z1p_eval_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) {Y : ℂ} (hY : Y ≠ 0) : (Z1p v).eval Y ≠ 0 := by
  rw [Z1p_eval]
  exact mul_ne_zero (mul_ne_zero (absNorm_complex_ne_zero v) (nuHalf_ne_zero v)) hY

private theorem Z2p_eval_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) {c : ℂ} (hc : c ≠ 0) {Y : ℂ} (hY : Y ≠ 0) :
    (Z2p v c).eval Y ≠ 0 := by
  rw [Z2p_eval]
  exact mul_ne_zero (mul_ne_zero hc (mul_ne_zero (nuHalf_ne_zero v) (nuHalf_ne_zero v))) (pow_ne_zero 2 hY)

private theorem Z1p_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) : Z1p v ≠ 0 := by
  intro h
  have := congrArg (Polynomial.eval 1) h
  rw [Z1p_eval, Polynomial.eval_zero, mul_one] at this
  exact mul_ne_zero (absNorm_complex_ne_zero v) (nuHalf_ne_zero v) this

private theorem Z2p_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) {c : ℂ} (hc : c ≠ 0) : Z2p v c ≠ 0 := by
  intro h
  have := congrArg (Polynomial.eval 1) h
  rw [Z2p_eval, Polynomial.eval_zero, one_pow, mul_one] at this
  exact mul_ne_zero hc (mul_ne_zero (nuHalf_ne_zero v) (nuHalf_ne_zero v)) this

private abbrev relPoly {M : ℕ} (α : Fin M → ℂ) (Zp : Polynomial ℂ) : Polynomial ℂ :=
  ∑ i : Fin M, Polynomial.C (α i) * Zp ^ (M - 1 - (i : ℕ))

private theorem relPoly_eval {M : ℕ} (α : Fin M → ℂ) (Zp : Polynomial ℂ) (Y : ℂ) :
    (relPoly α Zp).eval Y = ∑ i : Fin M, α i * (Zp.eval Y) ^ (M - 1 - (i : ℕ)) := by
  simp [relPoly, Polynomial.eval_finsetSum]

private theorem relPoly_eval_zero {M : ℕ} (hM : 0 < M) (α : Fin M → ℂ) (Zp : Polynomial ℂ) (hZp : Zp.eval 0 = 0) :
    (relPoly α Zp).eval 0 = α ⟨M - 1, by omega⟩ := by
  rw [relPoly_eval, hZp]
  rw [Finset.sum_eq_single ⟨M - 1, by omega⟩]
  · simp
  · intro i _ hi
    have hne : M - 1 - (i : ℕ) ≠ 0 := by
      intro h0
      apply hi
      rw [Fin.ext_iff]
      show (i : ℕ) = M - 1
      have := i.isLt
      omega
    rw [zero_pow hne, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem relPoly_ne_zero {M : ℕ} (hM : 0 < M) (α : Fin M → ℂ) (hlast : α ⟨M - 1, by omega⟩ ≠ 0)
    (Zp : Polynomial ℂ) (hZp : Zp.eval 0 = 0) : relPoly α Zp ≠ 0 := by
  intro h
  have := relPoly_eval_zero hM α Zp hZp
  rw [h, Polynomial.eval_zero] at this
  exact hlast this.symm

private theorem exists_relation_last_ne_zero {E : Type*} [AddCommGroup E] [Module ℂ E] (w : ℕ → E) :
    ∀ (M : ℕ) (α : Fin M → ℂ), (∃ i, α i ≠ 0) → (∀ n : ℕ, ∑ i : Fin M, α i • w (n + i) = 0) →
      ∃ (M' : ℕ) (hM' : 0 < M') (α' : Fin M' → ℂ), α' ⟨M' - 1, by omega⟩ ≠ 0 ∧
        ∀ n : ℕ, ∑ i : Fin M', α' i • w (n + i) = 0 := by
  intro M
  induction M with
  | zero => intro α hα _; obtain ⟨i, _⟩ := hα; exact i.elim0
  | succ M ih =>
    intro α hα hrel
    by_cases hlast : α (Fin.last M) = 0
    · have hrel' : ∀ n : ℕ, ∑ i : Fin M, α (Fin.castSucc i) • w (n + i) = 0 := by
        intro n
        have := hrel n
        rw [Fin.sum_univ_castSucc, hlast, zero_smul, add_zero] at this
        simpa using this
      have hα' : ∃ i : Fin M, α (Fin.castSucc i) ≠ 0 := by
        obtain ⟨i, hi⟩ := hα
        induction i using Fin.lastCases with
        | last => exact absurd hlast hi
        | cast j => exact ⟨j, hi⟩
      exact ih (fun i => α (Fin.castSucc i)) hα' hrel'
    · exact ⟨M + 1, Nat.succ_pos M, α, by simpa [Fin.last] using hlast, hrel⟩

private theorem torusFactor_natCast (N lam om : ℂ) (t : ℕ) :
    torusFactor N lam om (t : ℤ) = heckeRecursionSeq N lam om t := by
  simp [torusFactor]

private theorem torusFactor_neg_of_lt (N lam om : ℂ) {k : ℤ} (hk : k < 0) : torusFactor N lam om k = 0 := by
  simp [torusFactor, not_le.2 hk]

private theorem heckeRecursionSeq_rec (N lam om : ℂ) (t : ℕ) :
    heckeRecursionSeq N lam om (t + 2) =
      ∑ i : Fin 2, (![-om / N, lam / N] : Fin 2 → ℂ) i • heckeRecursionSeq N lam om (t + i) := by
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, add_zero, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one, heckeRecursionSeq]
  ring

private abbrev quadIndex (L : ℕ) (q : ℕ × ℕ) : ℤ × ℤ := (((q.1 : ℤ) - L) + ((q.2 : ℤ) - L), (q.2 : ℤ) - L)

private theorem quadIndex_injective (L : ℕ) : Function.Injective (quadIndex L) := by
  intro q q' h
  simp only [quadIndex, Prod.mk.injEq] at h
  ext <;> omega

private theorem cellTerm_quadIndex (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : unif v ϖ ≠ 0) (hϖ : Valued.v (unif v ϖ) = WithZero.exp (-1 : ℤ)) (U : LocalGL3 v → ℂ) (L : ℕ)
    (b : ℂ) {c : ℂ} (hc : c ≠ 0) (W₂ : G2 v → ℂ)
    (hW₂Z : ∀ g : G2 v, W₂ (g * scalarPi (unif v ϖ) hπ) = c * W₂ g)
    (hW₂T : ∀ m : ℤ, W₂ (diagZ (unif v ϖ) hπ m) = torusFactor (Ideal.absNorm v.asIdeal : ℂ) b c m)
    (vol : ℂ) (s : ℂ) (q : ℕ × ℕ) :
    cellTerm v hπ vol (detModulus v) s (fun g => U (iotaGL g)) W₂ (quadIndex L q) =
      vol * (uZ v hπ U ((q.1 : ℤ) - L) ((q.2 : ℤ) - L) *
          torusFactor (Ideal.absNorm v.asIdeal : ℂ) b c ((q.1 : ℤ) - L)) *
        ((Z1p v).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ ((q.1 : ℤ) - L) *
          (Z2p v c).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ ((q.2 : ℤ) - L)) := by
  have hW := apply_tor v hπ b hc W₂ hW₂Z hW₂T (quadIndex L q)
  have hδ := detModulus_tor v hπ hϖ (quadIndex L q)
  have hYZ : nuHalf v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) ≠ 0 :=
    mul_ne_zero (nuHalf_ne_zero v) (absNorm_cpow_neg_ne_zero v s)
  simp only [tor, add_sub_cancel_right] at hW hδ
  simp only [cellTerm, tor, add_sub_cancel_right, hW, hδ, ofReal_zpow_cpow_eq, Z1p_eval, Z2p_eval, uZ]
  rw [show (q.1 : ℤ) - L + ((q.2 : ℤ) - L) + ((q.2 : ℤ) - L) = ((q.1 : ℤ) - L) + 2 * ((q.2 : ℤ) - L) by ring,
    zpow_add₀ hYZ, zpow_mul, zpow_two, pow_two]
  simp only [mul_zpow]
  ring

private theorem support_cellTerm_subset (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : unif v ϖ ≠ 0) (U : LocalGL3 v → ℂ) (L : ℕ)
    (hsupp : ∀ k m : ℤ, k < -(L : ℤ) ∨ m < -(L : ℤ) →
      U (iotaGL (diagZ (unif v ϖ) hπ k * scalarPi (unif v ϖ) hπ ^ m)) = 0)
    (W₂ : G2 v → ℂ) (vol : ℂ) (s : ℂ) :
    Function.support (cellTerm v hπ vol (detModulus v) s (fun g => U (iotaGL g)) W₂) ⊆ Set.range (quadIndex L) := by
  intro p hp
  obtain ⟨p₁, p₂⟩ := p
  rw [Function.mem_support] at hp
  by_contra hout
  apply hp
  have hk : p₁ - p₂ < -(L : ℤ) ∨ p₂ < -(L : ℤ) := by
    by_contra hin
    push Not at hin
    exact hout ⟨((p₁ - p₂ + L).toNat, (p₂ + L).toNat), by simp only [quadIndex, Prod.mk.injEq]; omega⟩
  have hzero : U (iotaGL (tor v hπ (p₁, p₂))) = 0 := hsupp (p₁ - p₂) p₂ hk
  simp only [cellTerm]
  rw [hzero]
  ring

private theorem tsum_mul_rel_mul_rel_eq {L M₂ : ℕ} (α₂ : Fin M₂ → ℂ) (u : ℕ → ℕ → ℂ)
    (hu₂ : ∀ a n : ℕ, ∑ i : Fin M₂, α₂ i * u a (n + i) = 0) (tf' : ℕ → ℂ) (htf0 : ∀ a : ℕ, a < L → tf' a = 0)
    {M₁ : ℕ} (α₁ : Fin M₁ → ℂ)
    (hrel₁ : ∀ n t : ℕ, ∑ i : Fin M₁, α₁ i * (tf' (t + i + L) * u (t + i + L) n) = 0)
    {vol : ℂ} (hvol : vol ≠ 0) {Z₁ Z₂ : ℂ} (hZ₁ : Z₁ ≠ 0) (hZ₂ : Z₂ ≠ 0)
    (hF : Summable fun q : ℕ × ℕ => vol * (u q.1 q.2 * tf' q.1) * (Z₁ ^ q.1 * Z₂ ^ q.2)) :
    (∑' q : ℕ × ℕ, vol * (u q.1 q.2 * tf' q.1) * (Z₁ ^ q.1 * Z₂ ^ q.2)) *
        (∑ i : Fin M₂, α₂ i * Z₂ ^ (M₂ - 1 - (i : ℕ))) * (∑ i : Fin M₁, α₁ i * Z₁ ^ (M₁ - 1 - (i : ℕ))) =
      ∑ i : Fin M₂, ∑ n ∈ Finset.range i, (α₂ i * Z₂ ^ (n + (M₂ - 1 - (i : ℕ)))) *
        (vol * Z₁ ^ L * ∑ i' : Fin M₁, α₁ i' *
          ∑ t ∈ Finset.range i', (tf' (t + L) * u (t + L) n) * Z₁ ^ (t + (M₁ - 1 - (i' : ℕ)))) := by

  have hg : ∀ n : ℕ, Summable fun a : ℕ => vol * (tf' a * u a n) * Z₁ ^ a := by
    intro n
    have h1 := hF.prod_symm.prod_factor n
    refine (h1.mul_left (Z₂ ^ n)⁻¹).congr fun a => ?_
    simp only [Prod.swap_prod_mk]
    rw [show vol * (u a n * tf' a) * (Z₁ ^ a * Z₂ ^ n) = Z₂ ^ n * (vol * (tf' a * u a n) * Z₁ ^ a) by ring,
      inv_mul_cancel_left₀ (pow_ne_zero n hZ₂)]

  have hinner : ∀ a : ℕ, (∑' n : ℕ, vol * (u a n * tf' a) * (Z₁ ^ a * Z₂ ^ n)) *
      (∑ i : Fin M₂, α₂ i * Z₂ ^ (M₂ - 1 - (i : ℕ))) =
        ∑ i : Fin M₂, ∑ n ∈ Finset.range i,
          (α₂ i * Z₂ ^ (n + (M₂ - 1 - (i : ℕ)))) * (vol * (tf' a * u a n) * Z₁ ^ a) := by
    intro a
    have hterm : ∀ n : ℕ, vol * (u a n * tf' a) * (Z₁ ^ a * Z₂ ^ n) = (vol * tf' a * Z₁ ^ a) * (u a n * Z₂ ^ n) :=
      fun n => by ring
    simp only [hterm]
    by_cases hK : vol * tf' a * Z₁ ^ a = 0
    · have hta : tf' a = 0 := by simpa [hvol, hZ₁] using hK
      simp [hta]
    · have hz : Summable fun n : ℕ => u a n * Z₂ ^ n := by
        refine ((hF.prod_factor a).mul_left (vol * tf' a * Z₁ ^ a)⁻¹).congr fun n => ?_
        simp only [hterm]
        rw [inv_mul_cancel_left₀ hK]
      rw [tsum_mul_left, mul_assoc (vol * tf' a * Z₁ ^ a), tsum_mul_sum_eq_of_shift_relation hZ₂ hz α₂ (hu₂ a),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      ring

  have hcol : ∀ n : ℕ, (∑' a : ℕ, vol * (tf' a * u a n) * Z₁ ^ a) * (∑ i : Fin M₁, α₁ i * Z₁ ^ (M₁ - 1 - (i : ℕ))) =
      vol * Z₁ ^ L * ∑ i' : Fin M₁, α₁ i' *
        ∑ t ∈ Finset.range i', (tf' (t + L) * u (t + L) n) * Z₁ ^ (t + (M₁ - 1 - (i' : ℕ))) := by
    intro n
    have hshift : Summable fun t : ℕ => vol * (tf' (t + L) * u (t + L) n) * Z₁ ^ (t + L) :=
      (summable_nat_add_iff (f := fun a : ℕ => vol * (tf' a * u a n) * Z₁ ^ a) L).2 (hg n)
    have hz : Summable fun t : ℕ => (tf' (t + L) * u (t + L) n) * Z₁ ^ t := by
      refine (hshift.mul_left (vol * Z₁ ^ L)⁻¹).congr fun t => ?_
      rw [pow_add, show vol * (tf' (t + L) * u (t + L) n) * (Z₁ ^ t * Z₁ ^ L) =
          (vol * Z₁ ^ L) * ((tf' (t + L) * u (t + L) n) * Z₁ ^ t) by ring,
        inv_mul_cancel_left₀ (mul_ne_zero hvol (pow_ne_zero L hZ₁))]
    have hdrop : (∑' a : ℕ, vol * (tf' a * u a n) * Z₁ ^ a) =
        vol * Z₁ ^ L * ∑' t : ℕ, (tf' (t + L) * u (t + L) n) * Z₁ ^ t := by
      rw [← (hg n).sum_add_tsum_nat_add L, Finset.sum_eq_zero, zero_add, ← tsum_mul_left]
      · refine tsum_congr fun t => ?_
        rw [pow_add]
        ring
      · intro a ha
        rw [htf0 a (Finset.mem_range.1 ha), zero_mul, mul_zero, zero_mul]
    rw [hdrop, mul_assoc (vol * Z₁ ^ L), tsum_mul_sum_eq_of_shift_relation hZ₁ hz α₁ (hrel₁ n)]

  rw [hF.tsum_prod]
  simp only
  rw [← tsum_mul_right]
  simp only [hinner]
  have hrows : HasSum (fun a : ℕ => ∑ i : Fin M₂, ∑ n ∈ Finset.range i,
      (α₂ i * Z₂ ^ (n + (M₂ - 1 - (i : ℕ)))) * (vol * (tf' a * u a n) * Z₁ ^ a))
      (∑ i : Fin M₂, ∑ n ∈ Finset.range i,
        (α₂ i * Z₂ ^ (n + (M₂ - 1 - (i : ℕ)))) * ∑' a : ℕ, vol * (tf' a * u a n) * Z₁ ^ a) :=
    hasSum_sum fun i _ => hasSum_sum fun n _ => (hg n).hasSum.mul_left _
  rw [hrows.tsum_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [mul_assoc, hcol n]

private theorem exists_torusData (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : unif v ϖ ≠ 0) (hϖ : Valued.v (unif v ϖ) = WithZero.exp (-1 : ℤ))
    (η : AddChar (v.adicCompletion ℚ) ℂ)
    (hη : η = NumberField.StandardAddChar.psiLocal ℚ v ∨ η = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn η W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (fam : Finset (LocalGL3 v → ℂ)) (hfam : ∀ F ∈ fam, F ∈ gl3CyclicSubspace W)
    (hV₀ : ∃ V₀ : Subgroup (LocalGL3 v), IsOpen (V₀ : Set (LocalGL3 v)) ∧
      ∀ F ∈ fam, ∀ k ∈ V₀, ∀ g : LocalGL3 v, F (g * k) = F g) :
    ∃ (L : ℕ) (d₁ : ℕ) (c₁ : Fin d₁ → ℂ) (d₂ : ℕ) (c₂ : Fin d₂ → ℂ), ∀ F ∈ fam,
      (∀ k m : ℤ, k < -(L : ℤ) ∨ m < -(L : ℤ) →
        F (iotaGL (diagZ (unif v ϖ) hπ k * scalarPi (unif v ϖ) hπ ^ m)) = 0) ∧
      (∀ k m : ℤ, -(L : ℤ) ≤ k → -(L : ℤ) ≤ m →
        F (iotaGL (diagZ (unif v ϖ) hπ (k + d₁) * scalarPi (unif v ϖ) hπ ^ m)) =
            ∑ i : Fin d₁, c₁ i * F (iotaGL (diagZ (unif v ϖ) hπ (k + (i : ℕ)) * scalarPi (unif v ϖ) hπ ^ m)) ∧
          F (iotaGL (diagZ (unif v ϖ) hπ k * scalarPi (unif v ϖ) hπ ^ (m + d₂))) =
            ∑ i : Fin d₂, c₂ i * F (iotaGL (diagZ (unif v ϖ) hπ k * scalarPi (unif v ϖ) hπ ^ (m + (i : ℕ))))) ∧
      ∃ C R : ℝ, 0 ≤ C ∧ 1 ≤ R ∧ ∀ k m : ℤ, -(L : ℤ) ≤ k → -(L : ℤ) ≤ m →
        ‖F (iotaGL (diagZ (unif v ϖ) hπ k * scalarPi (unif v ϖ) hπ ^ m))‖ ≤
          C * R ^ ((k + L).toNat + (m + L).toNat) := by
  obtain ⟨V₀, hV₀open, hV₀inv⟩ := hV₀
  obtain ⟨L, hL⟩ := exists_nat_forall_mem_of_isOpen v V₀ hV₀open
  obtain ⟨d₁, c₁, d₂, c₂, hE⟩ :=
    exists_forall_apply_iotaGL_diagZ_mul_scalarPi_zpow_eq_sum_of_isGL3PsiWhittakerFn v hπ hϖ η
      (not_forall_apply_eq_one_of_eq_psiLocal v η hη) W hW hsm hadm L
  refine ⟨L, d₁, c₁, d₂, c₂, fun F hF => ?_⟩
  exact hE F (hfam F hF) fun k hk hkL g => hV₀inv F hF k (hL k hk hkL) g

private theorem exists_abscissa_summable (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : unif v ϖ ≠ 0) (hϖ : Valued.v (unif v ϖ) = WithZero.exp (-1 : ℤ))
    (fam : Finset (LocalGL3 v → ℂ)) (L : ℕ) (d₁ : ℕ) (c₁ : Fin d₁ → ℂ) (d₂ : ℕ) (c₂ : Fin d₂ → ℂ)
    (hdata : ∀ F ∈ fam,
      (∀ k m : ℤ, k < -(L : ℤ) ∨ m < -(L : ℤ) →
        F (iotaGL (diagZ (unif v ϖ) hπ k * scalarPi (unif v ϖ) hπ ^ m)) = 0) ∧
      ∃ C R : ℝ, 0 ≤ C ∧ 1 ≤ R ∧ ∀ k m : ℤ, -(L : ℤ) ≤ k → -(L : ℤ) ≤ m →
        ‖F (iotaGL (diagZ (unif v ϖ) hπ k * scalarPi (unif v ϖ) hπ ^ m))‖ ≤
          C * R ^ ((k + L).toNat + (m + L).toNat))
    (b c : ℂ) (hc : c ≠ 0) (W₂ : G2 v → ℂ)
    (hW₂Z : ∀ g : G2 v, W₂ (g * scalarPi (unif v ϖ) hπ) = c * W₂ g)
    (hW₂T : ∀ m : ℤ, W₂ (diagZ (unif v ϖ) hπ m) = torusFactor (Ideal.absNorm v.asIdeal : ℂ) b c m)
    (vol : ℂ) :
    ∃ σ : ℝ, ∀ F ∈ fam, ∀ s : ℂ, σ < s.re →
      Summable fun p : ℤ × ℤ => ‖cellTerm v hπ vol (detModulus v) s (fun g => F (iotaGL g)) W₂ p‖ := by
  have _ := c₁
  have _ := c₂
  have hmem : ∀ F ∈ fam, ∃ σF : ℝ, ∀ s : ℂ, σF < s.re →
      Summable fun p : ℤ × ℤ => ‖cellTerm v hπ vol (detModulus v) s (fun g => F (iotaGL g)) W₂ p‖ := by
    intro F hF
    obtain ⟨hsupp, C, R, hC, hR, hgrowth⟩ := hdata F hF
    exact exists_abscissa_summable_of_member v hπ hϖ F L hsupp hC hR hgrowth b c hc W₂ hW₂Z hW₂T vol
  choose! σf hσf using hmem
  obtain ⟨σ, hσ⟩ := (fam.image σf).exists_le
  refine ⟨σ, fun F hF s hs => hσf F hF s (lt_of_le_of_lt ?_ hs)⟩
  exact hσ _ (Finset.mem_image_of_mem σf hF)

private theorem exists_polynomial_tsum_cellTerm_eq (v : HeightOneSpectrum (𝓞 ℚ))
    {ϖ : v.adicCompletionIntegers ℚ} (hπ : unif v ϖ ≠ 0) (hϖ : Valued.v (unif v ϖ) = WithZero.exp (-1 : ℤ))
    (U : LocalGL3 v → ℂ) (L : ℕ) (d₁ : ℕ) (c₁ : Fin d₁ → ℂ) (d₂ : ℕ) (c₂ : Fin d₂ → ℂ)
    (hsupp : ∀ k m : ℤ, k < -(L : ℤ) ∨ m < -(L : ℤ) →
      U (iotaGL (diagZ (unif v ϖ) hπ k * scalarPi (unif v ϖ) hπ ^ m)) = 0)
    (hrec : ∀ k m : ℤ, -(L : ℤ) ≤ k → -(L : ℤ) ≤ m →
      U (iotaGL (diagZ (unif v ϖ) hπ (k + d₁) * scalarPi (unif v ϖ) hπ ^ m)) =
          ∑ i : Fin d₁, c₁ i * U (iotaGL (diagZ (unif v ϖ) hπ (k + (i : ℕ)) * scalarPi (unif v ϖ) hπ ^ m)) ∧
        U (iotaGL (diagZ (unif v ϖ) hπ k * scalarPi (unif v ϖ) hπ ^ (m + d₂))) =
          ∑ i : Fin d₂, c₂ i * U (iotaGL (diagZ (unif v ϖ) hπ k * scalarPi (unif v ϖ) hπ ^ (m + (i : ℕ)))))
    (b c : ℂ) (hc : c ≠ 0) (W₂ : G2 v → ℂ)
    (hW₂Z : ∀ g : G2 v, W₂ (g * scalarPi (unif v ϖ) hπ) = c * W₂ g)
    (hW₂T : ∀ m : ℤ, W₂ (diagZ (unif v ϖ) hπ m) = torusFactor (Ideal.absNorm v.asIdeal : ℂ) b c m)
    (vol : ℂ) (σ : ℝ)
    (hsum : ∀ s : ℂ, σ < s.re →
      Summable fun p : ℤ × ℤ => ‖cellTerm v hπ vol (detModulus v) s (fun g => U (iotaGL g)) W₂ p‖) :
    ∃ (p q : Polynomial ℂ), q ≠ 0 ∧ ∀ s : ℂ, σ < s.re →
      (∑' r : ℤ × ℤ, cellTerm v hπ vol (detModulus v) s (fun g => U (iotaGL g)) W₂ r) *
          q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) = p.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by
  by_cases hvol : vol = 0
  · refine ⟨0, 1, one_ne_zero, fun s _ => ?_⟩
    simp [cellTerm, hvol]

  obtain ⟨α₂, hα₂⟩ : ∃ α₂ : Fin (d₂ + 1) → ℂ,
      α₂ = fun i => Fin.lastCases (motive := fun _ => ℂ) (-1) c₂ i := ⟨_, rfl⟩
  have hα₂last : α₂ ⟨d₂ + 1 - 1, by omega⟩ ≠ 0 := by
    have hidx : (⟨d₂ + 1 - 1, by omega⟩ : Fin (d₂ + 1)) = Fin.last d₂ := by
      rw [Fin.ext_iff]
      simp
    rw [hidx, hα₂]
    simp
  have hu₂ : ∀ a n : ℕ,
      ∑ i : Fin (d₂ + 1), α₂ i * uZ v hπ U ((a : ℤ) - L) (((n + (i : ℕ) : ℕ) : ℤ) - L) = 0 := by
    intro a n
    have h := (hrec ((a : ℤ) - L) ((n : ℤ) - L) (by omega) (by omega)).2
    have hc : ∀ i : Fin d₂, ((n : ℤ) - L) + (i : ℕ) = ((n + (i : ℕ) : ℕ) : ℤ) - L := fun i => by omega
    have hd : ((n : ℤ) - L) + d₂ = ((n + d₂ : ℕ) : ℤ) - L := by omega
    simp only [hc, hd] at h
    rw [Fin.sum_univ_castSucc]
    simp only [hα₂, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, Fin.val_last, uZ]
    rw [h]
    ring

  have hx : ∀ t : ℕ, heckeRecursionSeq (Ideal.absNorm v.asIdeal : ℂ) b c (t + 2) =
      ∑ i : Fin 2, (![-c / (Ideal.absNorm v.asIdeal : ℂ), b / (Ideal.absNorm v.asIdeal : ℂ)] : Fin 2 → ℂ) i •
        heckeRecursionSeq (Ideal.absNorm v.asIdeal : ℂ) b c (t + i) :=
    heckeRecursionSeq_rec (Ideal.absNorm v.asIdeal : ℂ) b c
  have hy : ∀ t : ℕ, (fun t : ℕ => fun n : ℕ => uZ v hπ U (t : ℤ) ((n : ℤ) - L)) (t + d₁) =
      ∑ j : Fin d₁, c₁ j • (fun t : ℕ => fun n : ℕ => uZ v hπ U (t : ℤ) ((n : ℤ) - L)) (t + j) := by
    intro t
    funext n
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have h := (hrec (t : ℤ) ((n : ℤ) - L) (by omega) (by omega)).1
    push_cast
    exact h
  obtain ⟨α₀, hα₀, hrel₀⟩ := exists_shift_relation_mulSeq _ (heckeRecursionSeq (Ideal.absNorm v.asIdeal : ℂ) b c) hx
    c₁ (fun t : ℕ => fun n : ℕ => uZ v hπ U (t : ℤ) ((n : ℤ) - L)) hy
  obtain ⟨M₁, hM₁, α₁, hα₁last, hrel₁⟩ := exists_relation_last_ne_zero
    (fun t : ℕ => heckeRecursionSeq (Ideal.absNorm v.asIdeal : ℂ) b c t •
      (fun t : ℕ => fun n : ℕ => uZ v hπ U (t : ℤ) ((n : ℤ) - L)) t) _ α₀ hα₀ hrel₀
  have hrel₁' : ∀ n t : ℕ, ∑ i : Fin M₁, α₁ i *
      (torusFactor (Ideal.absNorm v.asIdeal : ℂ) b c (((t + (i : ℕ) + L : ℕ) : ℤ) - L) *
        uZ v hπ U (((t + (i : ℕ) + L : ℕ) : ℤ) - L) ((n : ℤ) - L)) = 0 := by
    intro n t
    have hcomp := congrFun (hrel₁ t) n
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hcomp
    have hcast : ∀ i : Fin M₁, (((t + (i : ℕ) + L : ℕ)) : ℤ) - L = ((t + (i : ℕ) : ℕ) : ℤ) := fun i => by omega
    simp only [hcast, torusFactor_natCast]
    exact hcomp

  refine ⟨∑ i : Fin (d₂ + 1), ∑ n ∈ Finset.range i,
      (Polynomial.C (α₂ i) * Z2p v c ^ (n + (d₂ + 1 - 1 - (i : ℕ)))) *
        (Polynomial.C vol * Z1p v ^ L * ∑ i' : Fin M₁, Polynomial.C (α₁ i') *
          ∑ t ∈ Finset.range i',
            Polynomial.C (torusFactor (Ideal.absNorm v.asIdeal : ℂ) b c (((t + L : ℕ) : ℤ) - L) *
              uZ v hπ U (((t + L : ℕ) : ℤ) - L) ((n : ℤ) - L)) * Z1p v ^ (t + (M₁ - 1 - (i' : ℕ)))),
    Z1p v ^ L * Z2p v c ^ L * relPoly α₂ (Z2p v c) * relPoly α₁ (Z1p v), ?_, fun s hs => ?_⟩
  · refine mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero L (Z1p_ne_zero v)) (pow_ne_zero L (Z2p_ne_zero v hc)))
      (relPoly_ne_zero (Nat.succ_pos d₂) α₂ hα₂last _ ?_)) (relPoly_ne_zero hM₁ α₁ hα₁last _ ?_)
    · rw [Z2p_eval]; ring
    · rw [Z1p_eval]; ring

  have hY : (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) ≠ 0 := absNorm_cpow_neg_ne_zero v s
  obtain ⟨Z₁, hZ₁def⟩ : ∃ Z₁ : ℂ,
      Z₁ = (Ideal.absNorm v.asIdeal : ℂ) * nuHalf v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) := ⟨_, rfl⟩
  obtain ⟨Z₂, hZ₂def⟩ : ∃ Z₂ : ℂ, Z₂ = c * (nuHalf v * nuHalf v) * ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ 2 :=
    ⟨_, rfl⟩
  have hZ₁ : Z₁ ≠ 0 := by
    rw [hZ₁def]
    exact mul_ne_zero (mul_ne_zero (absNorm_complex_ne_zero v) (nuHalf_ne_zero v)) hY
  have hZ₂ : Z₂ ≠ 0 := by
    rw [hZ₂def]
    exact mul_ne_zero (mul_ne_zero hc (mul_ne_zero (nuHalf_ne_zero v) (nuHalf_ne_zero v))) (pow_ne_zero 2 hY)

  have hq : ∀ q : ℕ × ℕ,
      cellTerm v hπ vol (detModulus v) s (fun g => U (iotaGL g)) W₂ (quadIndex L q) * (Z₁ ^ L * Z₂ ^ L) =
        vol * (uZ v hπ U ((q.1 : ℤ) - L) ((q.2 : ℤ) - L) *
            torusFactor (Ideal.absNorm v.asIdeal : ℂ) b c ((q.1 : ℤ) - L)) *
          (Z₁ ^ q.1 * Z₂ ^ q.2) := by
    intro q
    rw [cellTerm_quadIndex v hπ hϖ U L b hc W₂ hW₂Z hW₂T vol s q, Z1p_eval, Z2p_eval, ← hZ₁def, ← hZ₂def]
    have e1 : Z₁ ^ ((q.1 : ℤ) - L) * Z₁ ^ L = Z₁ ^ q.1 := by
      rw [← zpow_natCast Z₁ L, ← zpow_add₀ hZ₁, sub_add_cancel, zpow_natCast]
    have e2 : Z₂ ^ ((q.2 : ℤ) - L) * Z₂ ^ L = Z₂ ^ q.2 := by
      rw [← zpow_natCast Z₂ L, ← zpow_add₀ hZ₂, sub_add_cancel, zpow_natCast]
    rw [← e1, ← e2]
    ring
  have hF : Summable fun q : ℕ × ℕ =>
      vol * (uZ v hπ U ((q.1 : ℤ) - L) ((q.2 : ℤ) - L) *
          torusFactor (Ideal.absNorm v.asIdeal : ℂ) b c ((q.1 : ℤ) - L)) *
        (Z₁ ^ q.1 * Z₂ ^ q.2) :=
    (((hsum s hs).of_norm.comp_injective (quadIndex_injective L)).mul_right (Z₁ ^ L * Z₂ ^ L)).congr hq
  have hclear : (∑' q : ℕ × ℕ, cellTerm v hπ vol (detModulus v) s (fun g => U (iotaGL g)) W₂ (quadIndex L q)) *
      (Z₁ ^ L * Z₂ ^ L) = ∑' q : ℕ × ℕ,
        vol * (uZ v hπ U ((q.1 : ℤ) - L) ((q.2 : ℤ) - L) *
            torusFactor (Ideal.absNorm v.asIdeal : ℂ) b c ((q.1 : ℤ) - L)) *
          (Z₁ ^ q.1 * Z₂ ^ q.2) := by
    rw [← tsum_mul_right]
    exact tsum_congr hq
  have htf0 : ∀ a : ℕ, a < L → torusFactor (Ideal.absNorm v.asIdeal : ℂ) b c ((a : ℤ) - L) = 0 := fun a ha =>
    torusFactor_neg_of_lt _ _ _ (by omega)
  have key := tsum_mul_rel_mul_rel_eq (L := L) α₂ (fun a n => uZ v hπ U ((a : ℤ) - L) ((n : ℤ) - L)) hu₂
    (fun a => torusFactor (Ideal.absNorm v.asIdeal : ℂ) b c ((a : ℤ) - L)) htf0 α₁ hrel₁' hvol hZ₁ hZ₂ hF
  rw [← hclear] at key
  have hre : (∑' q : ℕ × ℕ, cellTerm v hπ vol (detModulus v) s (fun g => U (iotaGL g)) W₂ (quadIndex L q)) =
      ∑' r : ℤ × ℤ, cellTerm v hπ vol (detModulus v) s (fun g => U (iotaGL g)) W₂ r :=
    (quadIndex_injective L).tsum_eq (support_cellTerm_subset v hπ U L hsupp W₂ vol s)
  rw [← hre]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]
  rw [← hZ₁def, ← hZ₂def, ← mul_assoc, ← mul_assoc]
  exact key

section Average

open scoped Pointwise

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem continuous_iotaGL : Continuous (iotaGL : G2 v → LocalGL3 v) := by
  have hval : Continuous fun h : G2 v => embedMat2 ((h : G2 v) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp only [embedMat2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.empty_val'] <;>
      first | exact continuous_const | exact Units.continuous_val.matrix_elem _ _
  have hinv : Continuous fun h : G2 v =>
      embedMat2 (((h⁻¹ : G2 v) : G2 v) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp only [embedMat2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.empty_val'] <;>
      first | exact continuous_const | exact Units.continuous_coe_inv.matrix_elem _ _
  exact Units.continuous_iff.mpr ⟨hval, hinv⟩

private theorem isOpen_map_conj (U : Subgroup (LocalGL3 v)) (hU : IsOpen (U : Set (LocalGL3 v))) (x : LocalGL3 v) :
    IsOpen ((U.map (MulAut.conj x).toMonoidHom : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) := by
  have hset : ((U.map (MulAut.conj x).toMonoidHom : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) =
      (fun u => x⁻¹ * u * x) ⁻¹' (U : Set (LocalGL3 v)) := by
    ext u
    simp only [Subgroup.coe_map, Set.mem_image, Set.mem_preimage, SetLike.mem_coe, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have h : x⁻¹ * (x * w * x⁻¹) * x = w := by group
      rwa [h]
    · intro h
      exact ⟨x⁻¹ * u * x, h, by group⟩
  rw [hset]
  exact hU.preimage ((continuous_const.mul continuous_id).mul continuous_const)

private theorem exists_average (W : LocalGL3 v → ℂ)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g) :
    ∃ (n : ℕ) (ks : Fin n → G2 v), 0 < n ∧ (∀ i, ks i ∈ Kmax v) ∧
      (∃ V₀ : Subgroup (LocalGL3 v), IsOpen (V₀ : Set (LocalGL3 v)) ∧
        ∀ i, ∀ u ∈ V₀, ∀ g : LocalGL3 v, W (g * u * iotaGL (ks i)) = W (g * iotaGL (ks i))) ∧
      (∀ k ∈ Kmax v, ∀ g : G2 v,
        (∑ i, W (iotaGL (g * k) * iotaGL (ks i))) = ∑ i, W (iotaGL g * iotaGL (ks i))) ∧
      (∀ k ∈ Kmax v, ∀ g : G2 v,
        (∑ i, ‖W (iotaGL (g * k) * iotaGL (ks i))‖) = ∑ i, ‖W (iotaGL g * iotaGL (ks i))‖) := by
  obtain ⟨Uv, hUo, hUv⟩ := hsm

  set H : Subgroup (Kmax v) := (Uv.comap (iotaGL : G2 v →* LocalGL3 v)).subgroupOf (Kmax v) with hH
  have hHo : IsOpen (H : Set (Kmax v)) :=
    ((hUo.preimage (continuous_iotaGL v)).preimage continuous_subtype_val)
  haveI : CompactSpace (Kmax v) := isCompact_iff_compactSpace.mp (isCompact_Kmax v)
  haveI : DiscreteTopology ((Kmax v) ⧸ H) := QuotientGroup.discreteTopology hHo
  haveI : Finite ((Kmax v) ⧸ H) := finite_of_compact_of_discrete
  letI : Fintype ((Kmax v) ⧸ H) := Fintype.ofFinite _
  have hmemH : ∀ h : Kmax v, h ∈ H → iotaGL ((h : Kmax v) : G2 v) ∈ Uv := fun h hh => by
    simpa [hH, Subgroup.mem_subgroupOf, Subgroup.mem_comap] using hh

  set n : ℕ := Fintype.card ((Kmax v) ⧸ H) with hn
  set e : ((Kmax v) ⧸ H) ≃ Fin n := Fintype.equivFin _ with he
  set ks : Fin n → G2 v := fun i => (((e.symm i).out : Kmax v) : G2 v) with hks

  have hcoset : ∀ {X : Type} (φ : LocalGL3 v → X), (∀ u ∈ Uv, ∀ x : LocalGL3 v, φ (x * u) = φ x) →
      ∀ (kk : Kmax v) (x : LocalGL3 v) (q : (Kmax v) ⧸ H),
        φ (x * iotaGL ((kk : G2 v) * ((q.out : Kmax v) : G2 v))) =
          φ (x * iotaGL (((QuotientGroup.mk (kk * q.out) : (Kmax v) ⧸ H).out : Kmax v) : G2 v)) := by
    intro X φ hφ kk x q
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (s := H) (kk * q.out)
    have e : (((kk * q.out * (h : Kmax v) : Kmax v)) : G2 v) =
        ((kk : G2 v) * ((q.out : Kmax v) : G2 v)) * ((h : Kmax v) : G2 v) := rfl
    rw [hh, e, map_mul iotaGL ((kk : G2 v) * ((q.out : Kmax v) : G2 v)) ((h : Kmax v) : G2 v),
      ← mul_assoc x _ (iotaGL ((h : Kmax v) : G2 v)), hφ _ (hmemH h h.2)]

  have hperm : ∀ {X : Type} [AddCommMonoid X] (φ : LocalGL3 v → X),
      (∀ u ∈ Uv, ∀ x : LocalGL3 v, φ (x * u) = φ x) → ∀ (kk : Kmax v) (x : LocalGL3 v),
        (∑ i, φ (x * iotaGL (kk : G2 v) * iotaGL (ks i))) = ∑ i, φ (x * iotaGL (ks i)) := by
    intro X _ φ hφ kk x

    have hsum : ∀ (F : G2 v → X), (∑ i, F (ks i)) = ∑ q : (Kmax v) ⧸ H, F ((q.out : Kmax v) : G2 v) := by
      intro F
      exact (Fintype.sum_equiv e.symm _ _ fun _ => rfl)
    rw [hsum (fun y => φ (x * iotaGL (kk : G2 v) * iotaGL y)), hsum (fun y => φ (x * iotaGL y))]

    let σ : ((Kmax v) ⧸ H) ≃ ((Kmax v) ⧸ H) :=
      { toFun := fun q => QuotientGroup.mk (kk * q.out)
        invFun := fun q => QuotientGroup.mk (kk⁻¹ * q.out)
        left_inv := fun q => by
          obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (s := H) (kk * q.out)
          simp only
          rw [hh, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, QuotientGroup.mk_mul_of_mem _ h.2,
            QuotientGroup.out_eq']
        right_inv := fun q => by
          obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (s := H) (kk⁻¹ * q.out)
          simp only
          rw [hh, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, QuotientGroup.mk_mul_of_mem _ h.2,
            QuotientGroup.out_eq'] }
    calc (∑ q : (Kmax v) ⧸ H, φ (x * iotaGL (kk : G2 v) * iotaGL ((q.out : Kmax v) : G2 v)))
        = ∑ q : (Kmax v) ⧸ H, φ (x * iotaGL (((σ q).out : Kmax v) : G2 v)) := by
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [mul_assoc, ← map_mul]
          exact hcoset φ hφ kk x q
      _ = ∑ q : (Kmax v) ⧸ H, φ (x * iotaGL ((q.out : Kmax v) : G2 v)) :=
          Equiv.sum_comp σ (fun q => φ (x * iotaGL ((q.out : Kmax v) : G2 v)))
  refine ⟨n, ks, ?_, fun i => ((e.symm i).out : Kmax v).2, ?_, ?_, ?_⟩
  · exact Fintype.card_pos_iff.mpr ⟨QuotientGroup.mk 1⟩
  ·
    refine ⟨⨅ i : Fin n, Uv.map (MulAut.conj (iotaGL (ks i))).toMonoidHom, ?_, ?_⟩
    · rw [Subgroup.coe_iInf]
      exact isOpen_iInter_of_finite fun i => isOpen_map_conj v Uv hUo _
    · intro i u hu g
      have hu' : u ∈ Uv.map (MulAut.conj (iotaGL (ks i))).toMonoidHom := (Subgroup.mem_iInf.mp hu) i
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hu'
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show g * (iotaGL (ks i) * w * (iotaGL (ks i))⁻¹) * iotaGL (ks i) = g * iotaGL (ks i) * w by group]
      exact hUv w hw _
  · intro k hk g
    have h := hperm (X := ℂ) W hUv ⟨k, hk⟩ (iotaGL g)
    simpa only [map_mul] using h
  · intro k hk g
    have h := hperm (X := ℝ) (fun x => ‖W x‖) (fun u hu x => by simp only [hUv u hu x]) ⟨k, hk⟩ (iotaGL g)
    simpa only [map_mul] using h

end Average
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries.UnipotentMass"

section Dual

open Matrix

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def tinvHom : LocalGL3 v →* LocalGL3 v where
  toFun := transposeInv3
  map_one' := Units.ext (by
    show ((((1 : LocalGL3 v)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))ᵀ = 1
    rw [inv_one, Units.val_one, Matrix.transpose_one])
  map_mul' g h := Units.ext (by
    show ((((g * h)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))ᵀ =
      (((g⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))ᵀ *
        (((h⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))ᵀ
    rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul])

private theorem tinvHom_apply (g : LocalGL3 v) : tinvHom v g = transposeInv3 g := rfl

private theorem transposeInv3_transposeInv3 (g : LocalGL3 v) : transposeInv3 (transposeInv3 g) = g :=
  Units.ext (by
    show ((((transposeInv3 g)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))ᵀ = g
    exact Matrix.transpose_transpose _)

private theorem continuous_transposeInv3 : Continuous (transposeInv3 : LocalGL3 v → LocalGL3 v) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun g : LocalGL3 v => (((g⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))ᵀ
    exact Units.continuous_coe_inv.matrix_transpose
  · show Continuous fun g : LocalGL3 v => ((g : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ))ᵀ
    exact Units.continuous_val.matrix_transpose

private def dualAut (z : LocalGL3 v) : LocalGL3 v →* LocalGL3 v :=
  (tinvHom v).comp (MulAut.conj z⁻¹).toMonoidHom

private theorem dualAut_apply (z k : LocalGL3 v) : dualAut v z k = transposeInv3 (z⁻¹ * k * z) := by
  simp [dualAut, tinvHom_apply]

private theorem continuous_dualAut (z : LocalGL3 v) : Continuous (dualAut v z) := by
  have h : (dualAut v z : LocalGL3 v → LocalGL3 v) = fun k => transposeInv3 (z⁻¹ * k * z) := funext (dualAut_apply v z)
  rw [h]
  exact (continuous_transposeInv3 v).comp ((continuous_const.mul continuous_id).mul continuous_const)

private def dualAutInv (z : LocalGL3 v) : LocalGL3 v →* LocalGL3 v :=
  (MulAut.conj z).toMonoidHom.comp (tinvHom v)

private theorem dualAutInv_apply (z k : LocalGL3 v) : dualAutInv v z k = z * transposeInv3 k * z⁻¹ := by
  simp [dualAutInv, tinvHom_apply]

private theorem continuous_dualAutInv (z : LocalGL3 v) : Continuous (dualAutInv v z) := by
  have h : (dualAutInv v z : LocalGL3 v → LocalGL3 v) = fun k => z * transposeInv3 k * z⁻¹ :=
    funext (dualAutInv_apply v z)
  rw [h]
  exact (continuous_const.mul (continuous_transposeInv3 v)).mul continuous_const

private theorem dualAut_dualAutInv (z k : LocalGL3 v) : dualAut v z (dualAutInv v z k) = k := by
  rw [dualAut_apply, dualAutInv_apply, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, inv_mul_cancel_right,
    transposeInv3_transposeInv3]

private theorem longWeyl3_mul_transposeInv3_mul (z x k : LocalGL3 v) :
    (longWeyl3 : LocalGL3 v) * transposeInv3 (x * k * z) = longWeyl3 * transposeInv3 (x * z) * dualAut v z k := by
  rw [dualAut_apply, mul_assoc (longWeyl3 : LocalGL3 v), ← tinvHom_apply, ← tinvHom_apply, ← tinvHom_apply, ← map_mul]
  congr 2
  group

private theorem exists_longWeyl3_mul_transposeInv3_eq (z y : LocalGL3 v) :
    ∃ x : LocalGL3 v, (longWeyl3 : LocalGL3 v) * transposeInv3 (x * z) = y := by
  refine ⟨transposeInv3 ((longWeyl3 : LocalGL3 v)⁻¹ * y) * z⁻¹, ?_⟩
  rw [inv_mul_cancel_right, transposeInv3_transposeInv3, mul_inv_cancel_left]

private theorem longWeyl3_mul_transposeInv3_upperUnipotent3 (x y z : v.adicCompletion ℚ) :
    (longWeyl3 : LocalGL3 v) * transposeInv3 (upperUnipotent3 x y z) =
      upperUnipotent3 (-y) (-x) (x * y - z) * longWeyl3 := by
  apply Units.ext
  have hinv : (((upperUnipotent3 x y z)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      !![1, -x, x * y - z; 0, 1, -y; 0, 0, 1] := rfl
  rw [Units.val_mul, Units.val_mul,
    show ((transposeInv3 (upperUnipotent3 x y z) : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      ((((upperUnipotent3 x y z)⁻¹ : LocalGL3 v) : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)))ᵀ from rfl,
    hinv, upperUnipotent3_coe, longWeyl3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]

private theorem isGL3PsiWhittakerFn_dual (η : AddChar (v.adicCompletion ℚ) ℂ)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn η⁻¹ W) : IsGL3PsiWhittakerFn η (dualWhittakerFn3 W) := by
  intro x y z g
  rw [dualWhittakerFn3_apply, dualWhittakerFn3_apply, ← tinvHom_apply, map_mul, tinvHom_apply, tinvHom_apply,
    ← mul_assoc, longWeyl3_mul_transposeInv3_upperUnipotent3, mul_assoc, hW, AddChar.inv_apply,
    show -(-y + -x) = x + y by ring]

private theorem dual_translate_hsm_hadm (W : LocalGL3 v → ℂ) (z : LocalGL3 v)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ))) :
    (∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, dualWhittakerFn3 W (g * k * z) = dualWhittakerFn3 W (g * z)) ∧
    (∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace (fun g => dualWhittakerFn3 W (g * z)),
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ))) := by
  classical

  set D : (LocalGL3 v → ℂ) →ₗ[ℂ] (LocalGL3 v → ℂ) :=
    { toFun := fun Φ x => Φ ((longWeyl3 : LocalGL3 v) * transposeInv3 (x * z))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } with hD
  have hDapp : ∀ (Φ : LocalGL3 v → ℂ) (x : LocalGL3 v), D Φ x = Φ ((longWeyl3 : LocalGL3 v) * transposeInv3 (x * z)) :=
    fun _ _ => rfl
  have hDW : (fun g => dualWhittakerFn3 W (g * z)) = D W := by
    funext x
    rw [hDapp, dualWhittakerFn3_apply]
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨Uv, hUo, hUv⟩ := hsm
    refine ⟨Uv.comap (dualAut v z), hUo.preimage (continuous_dualAut v z), fun k hk g => ?_⟩
    rw [dualWhittakerFn3_apply, dualWhittakerFn3_apply, longWeyl3_mul_transposeInv3_mul]
    exact hUv _ (Subgroup.mem_comap.mp hk) _
  ·
    intro Uv hUo

    set Uv₀ : Subgroup (LocalGL3 v) := Uv.comap (dualAutInv v z) with hUv₀
    have hUv₀o : IsOpen (Uv₀ : Set (LocalGL3 v)) := hUo.preimage (continuous_dualAutInv v z)
    obtain ⟨B, hB⟩ := hadm Uv₀ hUv₀o
    refine ⟨B.image D, fun F hF hFk => ?_⟩

    have hle : gl3CyclicSubspace (fun g => dualWhittakerFn3 W (g * z)) ≤ (gl3CyclicSubspace W).map D := by
      rw [hDW]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨h, rfl⟩
      refine ⟨gl3AmbientRightTranslate (R := ℂ) (dualAut v z h) W, Submodule.subset_span ⟨dualAut v z h, rfl⟩, ?_⟩
      funext x
      simp only [gl3AmbientRightTranslate_apply, hDapp, longWeyl3_mul_transposeInv3_mul]
    obtain ⟨F₀, hF₀, rfl⟩ := Submodule.mem_map.mp (hle hF)

    have hF₀k : ∀ k ∈ Uv₀, ∀ y : LocalGL3 v, F₀ (y * k) = F₀ y := by
      intro k hk y
      obtain ⟨x, rfl⟩ := exists_longWeyl3_mul_transposeInv3_eq v z y
      have hk' : dualAutInv v z k ∈ Uv := Subgroup.mem_comap.mp hk
      have h := hFk _ hk' x
      rw [hDapp, hDapp, longWeyl3_mul_transposeInv3_mul, dualAut_dualAutInv] at h
      exact h
    have hmem := hB F₀ hF₀ hF₀k
    rw [Finset.coe_image, ← Submodule.map_span]
    exact Submodule.mem_map_of_mem hmem

end Dual
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries.UnipotentMass"

section Delta

open IwasawaCover AutomorphicForm

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem modulus_mul_adic (a b : v.adicCompletion ℚ) : modulus (a * b) = modulus a * modulus b := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ v,
    LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ v,
    LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ v, nnnorm_mul]

private theorem modulus_eq_one_of_valued_eq_one (x : v.adicCompletion ℚ) (hx : Valued.v x = 1) : modulus x = 1 := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ v x, ← NNReal.coe_inj, coe_nnnorm,
    NumberField.FinitePlace.norm_def, hx, map_one, NNReal.coe_one]

private theorem detModulus_mul_left_of_mem : ∀ n ∈ Nr v, ∀ g : G2 v, detModulus v (n * g) = detModulus v g := by
  rintro _ ⟨y, rfl⟩ g
  have hdet : Matrix.GeneralLinearGroup.det (unipotentGL2Hom y : G2 v) = 1 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
    show ((unipotentGL2 y.toAdd : G2 v) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)).det = 1
    rw [unipotentGL2_coe, Matrix.det_fin_two_of]
    ring
  show (modulus ((Matrix.GeneralLinearGroup.det (_ * g) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) = _
  rw [map_mul, hdet, one_mul]

private theorem detModulus_mul_right_of_mem : ∀ k ∈ Kmax v, ∀ g : G2 v, detModulus v (g * k) = detModulus v g := by
  intro k hk g
  have h1 : modulus ((Matrix.GeneralLinearGroup.det k : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
    refine modulus_eq_one_of_valued_eq_one v _ ?_
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact valued_det_eq_one_of_mem v hk
  show (modulus ((Matrix.GeneralLinearGroup.det (g * k) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ) =
    (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ)
  rw [map_mul, Units.val_mul, modulus_mul_adic v, h1, mul_one]

end Delta
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries.UnipotentMass"

section Pairing

open IwasawaCover TorusConj UnipotentMass AutomorphicForm
open scoped ENNReal Pointwise

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem measurable_of_mul_right_invariant [MeasurableSpace (G2 v)] [BorelSpace (G2 v)] {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (f : G2 v → X)
    (U : Subgroup (G2 v)) (hU : IsOpen (U : Set (G2 v))) (hf : ∀ u ∈ U, ∀ g : G2 v, f (g * u) = f g) :
    Measurable f := by
  have hlc : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_exists_open]
    intro g
    refine ⟨(fun u => g * u) '' (U : Set (G2 v)), (Homeomorph.mulLeft g).isOpenMap _ hU, ⟨1, one_mem U, mul_one g⟩, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    exact hf u hu g
  exact hlc.continuous.measurable

private theorem isGL3PsiWhittakerFn_translate (η : AddChar (v.adicCompletion ℚ) ℂ) (Φ : LocalGL3 v → ℂ)
    (hΦ : IsGL3PsiWhittakerFn η Φ) (h : LocalGL3 v) : IsGL3PsiWhittakerFn η fun x => Φ (x * h) := by
  intro x y z g
  simp only [mul_assoc]
  exact hΦ x y z (g * h)

private theorem isGL3PsiWhittakerFn_sum (η : AddChar (v.adicCompletion ℚ) ℂ) {n : ℕ} (Φ : Fin n → LocalGL3 v → ℂ)
    (hΦ : ∀ i, IsGL3PsiWhittakerFn η (Φ i)) : IsGL3PsiWhittakerFn η fun x => ∑ i, Φ i x := by
  intro x y z g
  simp only [hΦ _ x y z g, ← Finset.mul_sum]

private theorem whittaker_mul_invariant_left (η η' : AddChar (v.adicCompletion ℚ) ℂ) (hηη' : ∀ x, η x * η' x = 1)
    (Φ : LocalGL3 v → ℂ) (hΦ : IsGL3PsiWhittakerFn η Φ) (W₂ : G2 v → ℂ)
    (hW₂ψ : ∀ (x : v.adicCompletion ℚ) (g : G2 v), W₂ (unipotentGL2 x * g) = η' x * W₂ g) :
    ∀ n ∈ Nr v, ∀ g : G2 v, Φ (iotaGL (n * g)) * W₂ (n * g) = Φ (iotaGL g) * W₂ g := by
  rintro _ ⟨y, rfl⟩ g
  have hn : (unipotentGL2Hom y : G2 v) = unipotentGL2 y.toAdd := rfl
  rw [hn, map_mul, iotaGL_unipotentGL2, hΦ, hW₂ψ, add_zero]
  calc η y.toAdd * Φ (iotaGL g) * (η' y.toAdd * W₂ g)
      = (η y.toAdd * η' y.toAdd) * (Φ (iotaGL g) * W₂ g) := by ring
    _ = Φ (iotaGL g) * W₂ g := by rw [hηη', one_mul]

private theorem cellWeight_mul_enorm [MeasurableSpace (G2 v)] {ϖ : v.adicCompletionIntegers ℚ} (hπ : unif v ϖ ≠ 0)
    (μ' : Measure (G2 v)) (hfin1 : μ' (cellOne v) < ∞) (δ : G2 v → ℝ) (s : ℂ) (Φ F : G2 v → ℂ) (p : ℤ × ℤ) :
    μ' (cellOne v) * (Ideal.absNorm v.asIdeal : ℝ≥0∞) ^ (p.1 - p.2) *
        ‖(Φ (tor v hπ p) * F (tor v hπ p)) * ((δ (tor v hπ p) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ =
      ENNReal.ofReal ‖cellTerm v hπ ((μ' (cellOne v)).toReal : ℂ) δ s Φ F p‖ := by
  have hexp : cellTerm v hπ ((μ' (cellOne v)).toReal : ℂ) δ s Φ F p =
      ((μ' (cellOne v)).toReal : ℂ) * ((Ideal.absNorm v.asIdeal : ℂ) ^ (p.1 - p.2)) *
        ((Φ (tor v hπ p) * F (tor v hπ p)) * ((δ (tor v hπ p) : ℝ) : ℂ) ^ (s - 1 / 2)) := rfl
  rw [hexp, norm_mul, norm_mul, norm_absNorm_zpow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_mul (mul_nonneg ENNReal.toReal_nonneg (zpow_nonneg (Nat.cast_nonneg _) _)),
    ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin1.ne, ofReal_norm,
    ofReal_absNorm_zpow v]

private theorem pairing {ϖ : v.adicCompletionIntegers ℚ} (hπ : unif v ϖ ≠ 0)
    (hϖ : Valued.v (unif v ϖ) = WithZero.exp (-1 : ℤ))
    (η η' : AddChar (v.adicCompletion ℚ) ℂ)
    (hη : η = NumberField.StandardAddChar.psiLocal ℚ v ∨ η = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹)
    (hηη' : ∀ x, η x * η' x = 1)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn η W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (lam om : ℂ) (hom : om ≠ 0) (W₂ : G2 v → ℂ)
    (hW₂ψ : ∀ (x : v.adicCompletion ℚ) (g : G2 v), W₂ (unipotentGL2 x * g) = η' x * W₂ g)
    (hW₂K : ∀ k ∈ Kmax v, ∀ g : G2 v, W₂ (g * k) = W₂ g)
    (hW₂Z : ∀ g : G2 v, W₂ (g * scalarPi (unif v ϖ) hπ) = om * W₂ g)
    (hW₂T : ∀ m : ℤ, W₂ (diagZ (unif v ϖ) hπ m) = torusFactor (Ideal.absNorm v.asIdeal : ℂ) lam om m) :
    letI : MeasurableSpace (G2 v) := borel (G2 v)
    ∀ (μ₂ : Measure (G2 v)) [μ₂.IsHaarMeasure] (μN : Measure (Nr v)) [μN.IsHaarMeasure],
      ∃ (p q : Polynomial ℂ) (σ : ℝ), q ≠ 0 ∧
        (∀ s : ℂ, σ < s.re → Integrable (fun g : G2 v =>
          (W (iotaGL g) * W₂ g) * ((detModulus v g : ℝ) : ℂ) ^ (s - 1 / 2)) (wMeasure v μ₂ μN)) ∧
        (∀ s : ℂ, σ < s.re →
          RSCarrier.rsLocalIntegral μ₂ (Nr v) μN (detModulus v) s (fun g => W (iotaGL g)) W₂ *
              q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) = p.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) := by
  letI : MeasurableSpace (G2 v) := borel (G2 v)
  haveI : BorelSpace (G2 v) := ⟨rfl⟩
  intro μ₂ _ μN _
  classical
  haveI : LocallyCompactSpace (G2 v) := locallyCompactSpace_localGL ℚ v
  haveI : SecondCountableTopology (G2 v) := secondCountable_G2 v
  set μ' := wMeasure v μ₂ μN with hμ'
  have hfin1 : μ' (cellOne v) < ∞ := wMeasure_cellOne_lt_top v μ₂ μN

  have hδN := detModulus_mul_left_of_mem v
  have hδK := detModulus_mul_right_of_mem v

  obtain ⟨n, ks, hn, hks, ⟨V₀, hV₀o, hV₀⟩, havg, havgn⟩ := exists_average v W hsm
  set T : Fin n → LocalGL3 v → ℂ := fun i x => W (x * iotaGL (ks i)) with hT
  set U : LocalGL3 v → ℂ := fun x => ∑ i, T i x with hU
  have hUι : ∀ g : G2 v, U (iotaGL g) = ∑ i, W (iotaGL g * iotaGL (ks i)) := fun g => rfl

  set fam : Finset (LocalGL3 v → ℂ) := insert U (Finset.univ.image T) with hfam_def
  have hTmem : ∀ i, T i ∈ gl3CyclicSubspace W := fun i =>
    Submodule.subset_span ⟨iotaGL (ks i), funext fun x => by simp [hT, gl3AmbientRightTranslate_apply]⟩
  have hUeq : U = ∑ i, T i := by
    funext x
    simp only [hU, Finset.sum_apply]
  have hUmem : U ∈ gl3CyclicSubspace W := by
    rw [hUeq]
    exact Submodule.sum_mem _ fun i _ => hTmem i
  have hUfam : U ∈ fam := Finset.mem_insert_self _ _
  have hTfam : ∀ i, T i ∈ fam := fun i => Finset.mem_insert_of_mem (Finset.mem_image_of_mem T (Finset.mem_univ i))
  have hfam : ∀ F ∈ fam, F ∈ gl3CyclicSubspace W := by
    intro F hF
    rcases Finset.mem_insert.mp hF with rfl | hF
    · exact hUmem
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hF
      exact hTmem i
  have hV₀T : ∀ i, ∀ u ∈ V₀, ∀ x : LocalGL3 v, T i (x * u) = T i x := fun i u hu x => hV₀ i u hu x
  have hV₀fam : ∃ V : Subgroup (LocalGL3 v), IsOpen (V : Set (LocalGL3 v)) ∧
      ∀ F ∈ fam, ∀ k ∈ V, ∀ g : LocalGL3 v, F (g * k) = F g := by
    refine ⟨V₀, hV₀o, fun F hF k hk g => ?_⟩
    rcases Finset.mem_insert.mp hF with rfl | hF
    · exact Finset.sum_congr rfl fun i _ => hV₀T i k hk g
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hF
      exact hV₀T i k hk g

  obtain ⟨L, d₁, c₁, d₂, c₂, hdata⟩ := exists_torusData v hπ hϖ η hη W hW hsm hadm fam hfam hV₀fam
  obtain ⟨σ, hσ⟩ := exists_abscissa_summable v hπ hϖ fam L d₁ c₁ d₂ c₂
    (fun F hF => ⟨(hdata F hF).1, (hdata F hF).2.2⟩) lam om hom W₂ hW₂Z hW₂T ((μ' (cellOne v)).toReal : ℂ)
  obtain ⟨p, q, hq, hpq⟩ := exists_polynomial_tsum_cellTerm_eq v hπ hϖ U L d₁ c₁ d₂ c₂ (hdata U hUfam).1
    (hdata U hUfam).2.1 lam om hom W₂ hW₂Z hW₂T ((μ' (cellOne v)).toReal : ℂ) σ (fun s hs => hσ U hUfam s hs)

  have hTW : ∀ i, IsGL3PsiWhittakerFn η (T i) := fun i => isGL3PsiWhittakerFn_translate v η W hW _
  have hUW : IsGL3PsiWhittakerFn η U := isGL3PsiWhittakerFn_sum v η T hTW
  have hNW := whittaker_mul_invariant_left v η η' hηη' W hW W₂ hW₂ψ
  have hNT := fun i => whittaker_mul_invariant_left v η η' hηη' (T i) (hTW i) W₂ hW₂ψ
  have hNU := whittaker_mul_invariant_left v η η' hηη' U hUW W₂ hW₂ψ
  have hKU : ∀ k ∈ Kmax v, ∀ g : G2 v, U (iotaGL (g * k)) * W₂ (g * k) = U (iotaGL g) * W₂ g := by
    intro k hk g
    rw [hUι, hUι, havg k hk g, hW₂K k hk g]

  obtain ⟨Uv, hUo, hUv⟩ := hsm
  have hmW : Measurable fun g : G2 v => W (iotaGL g) :=
    measurable_of_mul_right_invariant v (fun g => W (iotaGL g)) (Uv.comap (iotaGL : G2 v →* LocalGL3 v))
      (hUo.preimage (continuous_iotaGL v)) fun u hu g => by
        simp only [map_mul]
        exact hUv _ hu _
  have hmW₂ : Measurable W₂ :=
    measurable_of_mul_right_invariant v W₂ (Kmax v) (isOpen_localLevelOne_top v) hW₂K
  have hmδ : Measurable fun g : G2 v => ((detModulus v g : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (measurable_of_mul_right_invariant v (detModulus v) (Kmax v)
      (isOpen_localLevelOne_top v) hδK)

  have hInt : ∀ s : ℂ, σ < s.re →
      Integrable (fun g : G2 v => (W (iotaGL g) * W₂ g) * ((detModulus v g : ℝ) : ℂ) ^ (s - 1 / 2)) μ' := by
    intro s hs
    set f : G2 v → ℂ := fun g => (W (iotaGL g) * W₂ g) * ((detModulus v g : ℝ) : ℂ) ^ (s - 1 / 2) with hf
    have hfm : Measurable f := (hmW.mul hmW₂).mul (hmδ.pow_const _)
    have hfN : ∀ n ∈ Nr v, ∀ g : G2 v, f (n * g) = f g := fun n hn g => by
      simp only [hf, hNW n hn g, hδN n hn g]

    set φ : G2 v → ℝ≥0∞ := fun g => ∑ i, ‖f (g * ks i)‖ₑ with hφ
    have hfk : ∀ i (g : G2 v), f (g * ks i) =
        (T i (iotaGL g) * W₂ g) * ((detModulus v g : ℝ) : ℂ) ^ (s - 1 / 2) := by
      intro i g
      simp only [hf, hT, map_mul, hW₂K _ (hks i) g, hδK _ (hks i) g]
    have hφN : ∀ n ∈ Nr v, ∀ g : G2 v, φ (n * g) = φ g := by
      intro n hn g
      simp only [hφ, hfk, hNT _ n hn g, hδN n hn g]
    have hφK : ∀ k ∈ Kmax v, ∀ g : G2 v, φ (g * k) = φ g := by
      intro k hk g
      simp only [hφ, hfk, hW₂K k hk g, hδK k hk g, enorm_mul]
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      simp only [hT, ← ofReal_norm]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _),
        ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _), havgn k hk g]
    have hφfin : ∫⁻ g, φ g ∂μ' < ∞ := by
      rw [lintegral_eq_tsum_cell v hπ hϖ μ₂ μN φ hφN hφK]
      have hrw : ∀ pp : ℤ × ℤ, μ' (cellOne v) * (Ideal.absNorm v.asIdeal : ℝ≥0∞) ^ (pp.1 - pp.2) * φ (tor v hπ pp) =
          ∑ i, ENNReal.ofReal ‖cellTerm v hπ ((μ' (cellOne v)).toReal : ℂ) (detModulus v) s
            (fun g => T i (iotaGL g)) W₂ pp‖ := by
        intro pp
        simp only [hφ, Finset.mul_sum, hfk]
        exact Finset.sum_congr rfl fun i _ =>
          cellWeight_mul_enorm v hπ μ' hfin1 (detModulus v) s (fun g => T i (iotaGL g)) W₂ pp
      rw [← hμ']
      simp only [hrw]
      rw [Summable.tsum_finsetSum fun i _ => ENNReal.summable]
      refine ENNReal.sum_lt_top.mpr fun i _ => ?_
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hσ (T i) (hTfam i) s hs)]
      exact ENNReal.ofReal_lt_top

    obtain ⟨i₀⟩ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hIk : Integrable (fun g => f (g * ks i₀)) μ' := by
      refine ⟨(hfm.comp (measurable_mul_const _)).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      refine lt_of_le_of_lt (lintegral_mono fun g => ?_) hφfin
      exact Finset.single_le_sum (f := fun i => ‖f (g * ks i)‖ₑ) (fun _ _ => zero_le) (Finset.mem_univ i₀)
    exact (integral_comp_mul_right_eq v μ₂ μN f hfN hfm (hks i₀)).1.mp hIk
  refine ⟨Polynomial.C ((n : ℂ)⁻¹) * p, q, σ, hq, hInt, ?_⟩

  intro s hs
  set f : G2 v → ℂ := fun g => (W (iotaGL g) * W₂ g) * ((detModulus v g : ℝ) : ℂ) ^ (s - 1 / 2) with hf
  have hfm : Measurable f := (hmW.mul hmW₂).mul (hmδ.pow_const _)
  have hfN : ∀ n ∈ Nr v, ∀ g : G2 v, f (n * g) = f g := fun n hn g => by
    simp only [hf, hNW n hn g, hδN n hn g]
  have hfk : ∀ i (g : G2 v), f (g * ks i) =
      (T i (iotaGL g) * W₂ g) * ((detModulus v g : ℝ) : ℂ) ^ (s - 1 / 2) := by
    intro i g
    simp only [hf, hT, map_mul, hW₂K _ (hks i) g, hδK _ (hks i) g]

  obtain ⟨hintU, hsumU⟩ := integrable_and_hasSum_of_summable v hπ hϖ μ₂ μN (detModulus v) hδN hδK s
    (fun g => U (iotaGL g)) W₂ hNU hKU (hσ U hUfam s hs)

  have hfint : Integrable f μ' := hInt s hs
  have hinti : ∀ i, Integrable (fun g => f (g * ks i)) μ' := fun i =>
    (integral_comp_mul_right_eq v μ₂ μN f hfN hfm (hks i)).1.mpr hfint
  have hIi : ∀ i, ∫ g, f (g * ks i) ∂μ' = ∫ g, f g ∂μ' := fun i =>
    (integral_comp_mul_right_eq v μ₂ μN f hfN hfm (hks i)).2
  have hsumf : ∫ g, (U (iotaGL g) * W₂ g) * ((detModulus v g : ℝ) : ℂ) ^ (s - 1 / 2) ∂μ' = n * ∫ g, f g ∂μ' := by
    have hpt : ∀ g : G2 v, (U (iotaGL g) * W₂ g) * ((detModulus v g : ℝ) : ℂ) ^ (s - 1 / 2) =
        ∑ i, f (g * ks i) := by
      intro g
      simp only [hfk, hUι, hT, Finset.sum_mul]
    simp only [hpt]
    rw [integral_finsetSum _ fun i _ => hinti i]
    simp only [hIi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hRS : RSCarrier.rsLocalIntegral μ₂ (Nr v) μN (detModulus v) s (fun g => W (iotaGL g)) W₂ =
      (n : ℂ)⁻¹ * ∑' r : ℤ × ℤ, cellTerm v hπ ((μ' (cellOne v)).toReal : ℂ) (detModulus v) s
        (fun g => U (iotaGL g)) W₂ r := by
    rw [hsumU.tsum_eq]
    unfold RSCarrier.rsLocalIntegral
    rw [hsumf, ← mul_assoc, inv_mul_cancel₀ hn0, one_mul]
  rw [hRS, mul_assoc, hpq s hs, Polynomial.eval_mul, Polynomial.eval_C]

end Pairing
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries.UnipotentMass"

end LanglandsTunnell.CubicInduction.LocalPairingSeries
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries.UnipotentMass"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries.UnipotentMass"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries.UnipotentMass"

open _root_.LanglandsTunnell _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction in
theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (ℓ : ℕ) :
    ∀ (a₁ a₂ : ℂ) (ha : a₁ * a₂ ≠ 0)
    (W₂ : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hW₂ψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      W₂ (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ v x * W₂ g)
    (hW₂K : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂ (g * k) = W₂ g)
    (hW₂1 : W₂ 1 = 1)
    (hW₂Z : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
      W₂ (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) =
        a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ) * W₂ g)
    (hW₂T : ∀ m : ℤ, W₂ (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) =
      torusFactor (Ideal.absNorm v.asIdeal : ℂ) (a₁ + a₂) (a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ)) m)
    (W₂d : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hW₂dψ : ∀ (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)),
      W₂d (unipotent x * g) = (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ x * W₂d g)
    (hW₂dK : ∀ (k g : GL (Fin 2) (v.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W₂d (g * k) = W₂d g)
    (hW₂d1 : W₂d 1 = 1)
    (hW₂dZ : ∀ g : GL (Fin 2) (v.adicCompletion ℚ),
      W₂d (g * scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ) =
        (Ideal.absNorm v.asIdeal : ℂ) / (a₁ * a₂) * W₂d g)
    (hW₂dT : ∀ m : ℤ, W₂d (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m) =
      torusFactor (Ideal.absNorm v.asIdeal : ℂ) ((Ideal.absNorm v.asIdeal : ℂ) * (a₁ + a₂) / (a₁ * a₂))
        ((Ideal.absNorm v.asIdeal : ℂ) / (a₁ * a₂)) m),
    letI := localGLBorel ℚ v
    haveI := borelSpace_localGLBorel ℚ v
    ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure],
    ∃ (p q pd qd : Polynomial ℂ) (σ₂ σ₃ : ℝ), q ≠ 0 ∧ qd ≠ 0 ∧
      (∀ s : ℂ, σ₂ < s.re →
        Integrable
          (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
            (W (iotaGL g) * W₂ g) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                  v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) ∧
      (∀ s : ℂ, σ₃ < (1 - s).re →
        Integrable
          (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
            (dualWhittakerFn3 (W) (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
                (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                  (-(ℓ : ℤ)))) * W₂d g) *
              ((modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) :
                  v.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 - s - 1 / 2))
          (μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))) ∧
      (∀ s : ℂ, σ₂ < s.re →
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            s (fun g => W (iotaGL g)) W₂ * q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) =
          p.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) ∧
      (∀ s : ℂ, σ₃ < (1 - s).re →
        RSCarrier.rsLocalIntegral μ₂ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN
            (fun g : GL (Fin 2) (v.adicCompletion ℚ) =>
              (modulus ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) : ℝ))
            (1 - s) (fun g => dualWhittakerFn3 (W) (iotaGL g * iotaGL (UnramifiedWhittaker.scalarPi
              (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
                (-(ℓ : ℤ))))) W₂d *
            qd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s))) =
          pd.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-(1 - s)))) := by
  intro a₁ a₂ ha W₂ hW₂ψ hW₂K _ hW₂Z hW₂T W₂d hW₂dψ hW₂dK _ hW₂dZ hW₂dT μ₂ _ μN _
  have hN0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by exact_mod_cast LocalPairingSeries.absNorm_asIdeal_ne_zero v
  set ψ := NumberField.StandardAddChar.psiLocal ℚ v with hψ
  have hψψ : ∀ x, ψ⁻¹ x * ψ x = 1 := fun x => by
    rw [AddChar.inv_apply, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have hψψ' : ∀ x, ψ x * ψ⁻¹ x = 1 := fun x => by rw [mul_comm]; exact hψψ x
  have hunip : ∀ x : v.adicCompletion ℚ,
      (unipotent x : GL (Fin 2) (v.adicCompletion ℚ)) = AutomorphicForm.unipotentGL2 x := fun x => Units.ext rfl

  obtain ⟨p, q, σ₂, hq, hI, hR⟩ := LocalPairingSeries.pairing v hπ hϖ ψ⁻¹ ψ (Or.inr rfl) hψψ W hW hsm hadm
    (a₁ + a₂) (a₁ * a₂ / (Ideal.absNorm v.asIdeal : ℂ)) (div_ne_zero ha hN0) W₂
    (fun x g => by rw [← hunip]; exact hW₂ψ x g) (fun k hk g => hW₂K k g hk) hW₂Z hW₂T μ₂ μN

  set z : LocalGL3 v :=
    iotaGL (UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^
      (-(ℓ : ℤ))) with hz
  have hWd : IsGL3PsiWhittakerFn ψ (dualWhittakerFn3 W) := LocalPairingSeries.isGL3PsiWhittakerFn_dual v ψ W hW
  have hWd' : IsGL3PsiWhittakerFn ψ (fun x => dualWhittakerFn3 W (x * z)) :=
    LocalPairingSeries.isGL3PsiWhittakerFn_translate v ψ _ hWd z
  obtain ⟨hsmd, hadmd⟩ := LocalPairingSeries.dual_translate_hsm_hadm v W z hsm hadm
  obtain ⟨pd, qd, σ₃, hqd, hId, hRd⟩ := LocalPairingSeries.pairing v hπ hϖ ψ ψ⁻¹ (Or.inl rfl) hψψ'
    (fun x => dualWhittakerFn3 W (x * z)) hWd' hsmd hadmd
    ((Ideal.absNorm v.asIdeal : ℂ) * (a₁ + a₂) / (a₁ * a₂)) ((Ideal.absNorm v.asIdeal : ℂ) / (a₁ * a₂))
    (div_ne_zero hN0 ha) W₂d (fun x g => by rw [← hunip]; exact hW₂dψ x g) (fun k hk g => hW₂dK k g hk) hW₂dZ hW₂dT
    μ₂ μN
  refine ⟨p, q, pd, qd, σ₂, σ₃, hq, hqd, hI, ?_, hR, ?_⟩
  · intro s hs
    exact hId (1 - s) hs
  · intro s hs
    exact hRd (1 - s) hs

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn.LanglandsTunnell.CubicInduction.LocalPairingSeries.UnipotentMass"

end S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_integrable_and_rsLocalIntegral_mul_eval_eq_of_isGL3PsiWhittakerFn (solution)
