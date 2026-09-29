-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_forall_localAt_eq_one_and_ne_zero_of_heckeLocal_of_levelOne_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/cffd88f7-648b-5116-8592-f741236483ef

import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_LocalGL2_iwasawa_decomposition_diag
import Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_NumberField_StandardAddChar_psiLocal_rat_eq_psiQ_adeleSingleAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_localAt_eq_one_and_ne_zero_of_heckeLocal_of_levelOne_invariant
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell
open NumberField.TateGlobal NumberField.AdelicLevel
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory
open scoped nonZeroDivisors

noncomputable section

namespace Ws23HL

section MatrixAlgebra
open Matrix UnramifiedWhittaker
variable {F : Type*} [Field F] (π : F) (hπ : π ≠ 0)

def diagU : Fˣ × Fˣ →* GL (Fin 2) F where
  toFun ab := GeneralLinearGroup.mkOfDetNeZero !![((ab.1 : Fˣ) : F), 0; 0, ((ab.2 : Fˣ) : F)]
    (by simp [det_fin_two_of])
  map_one' := by
    apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_mul' x y := by
    apply Units.ext; ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem coe_diagU (a b : Fˣ) :
    ((diagU (a, b) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![(a : F), 0; 0, (b : F)] := rfl

theorem coe_diagU_inv (a b : Fˣ) :
    (((diagU (a, b))⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![((a⁻¹ : Fˣ) : F), 0; 0, ((b⁻¹ : Fˣ) : F)] := by
  rw [← map_inv, Prod.inv_mk, coe_diagU]

theorem coe_unipotent (β : F) : ((unipotent β : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, β; 0, 1] := rfl

theorem unipotent_inv (β : F) : (unipotent β)⁻¹ = unipotent (-β) := by
  rw [inv_eq_iff_mul_eq_one]
  apply Units.ext; ext i j
  fin_cases i <;> fin_cases j <;> simp [unipotent, Matrix.mul_apply, Fin.sum_univ_two]

theorem diagZ_zero : diagZ π hπ 0 = 1 := by
  apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [diagZ]

theorem diagZ_eq_diagU (m : ℤ) : diagZ π hπ m = diagU (Units.mk0 π hπ ^ m, 1) := by
  apply Units.ext; ext i j
  fin_cases i <;> fin_cases j <;> simp [diagZ, coe_diagU, Units.val_zpow_eq_zpow_val]

theorem scalarPi_eq_diagU : scalarPi π hπ = diagU (Units.mk0 π hπ, Units.mk0 π hπ) := by
  apply Units.ext; ext i j
  fin_cases i <;> fin_cases j <;> simp [scalarPi, coe_diagU]

theorem diagZ_mul_unipotent (m : ℤ) (β : F) :
    diagZ π hπ m * unipotent β = unipotent (π ^ m * β) * diagZ π hπ m := by
  apply Units.ext; ext i j
  fin_cases i <;> fin_cases j <;> simp [diagZ, unipotent, Matrix.mul_apply, Fin.sum_univ_two]

theorem diagZ_mul_repSome (m : ℤ) (β : F) :
    diagZ π hπ m * repSome π hπ β = unipotent (π ^ m * β) * diagZ π hπ (m + 1) := by
  apply Units.ext; ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagZ, unipotent, repSome, Matrix.mul_apply, Fin.sum_univ_two, zpow_add_one₀ hπ]

theorem diagZ_mul_repInf (m : ℤ) :
    diagZ π hπ m * repInf π hπ = diagZ π hπ (m - 1) * scalarPi π hπ := by
  apply Units.ext; ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagZ, repInf, scalarPi, Matrix.mul_apply, Fin.sum_univ_two, zpow_sub_one₀ hπ, mul_assoc,
      inv_mul_cancel₀ hπ]

theorem diagU_zpow_eq (k₁ k₂ : ℤ) :
    diagU (Units.mk0 π hπ ^ k₁, Units.mk0 π hπ ^ k₂) = diagZ π hπ (k₁ - k₂) * scalarPi π hπ ^ k₂ := by
  rw [diagZ_eq_diagU, scalarPi_eq_diagU, ← map_zpow, ← map_mul]
  congr 1
  refine Prod.ext ?_ ?_
  · show Units.mk0 π hπ ^ k₁ = Units.mk0 π hπ ^ (k₁ - k₂) * (Units.mk0 π hπ, Units.mk0 π hπ).1 ^ k₂
    rw [← _root_.zpow_add, sub_add_cancel]
  · show Units.mk0 π hπ ^ k₂ = 1 * (Units.mk0 π hπ, Units.mk0 π hπ).2 ^ k₂
    rw [one_mul]

theorem eq_unipotent_mul_diagU_mul {g k : GL (Fin 2) F} {z : F} {a₁ a₂ : Fˣ}
    (h : (g : Matrix (Fin 2) (Fin 2) F) = !![1, z; 0, 1] * !![(a₁ : F), 0; 0, (a₂ : F)] * k) :
    g = unipotent z * diagU (a₁, a₂) * k := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact h

end MatrixAlgebra

section Local
open Matrix UnramifiedWhittaker

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem mem_localLevelOne_top_of_valued_le {k : GL (Fin 2) (v.adicCompletion ℚ)}
    (h1 : ∀ i j, Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1)
    (h2 : ∀ i j, Valued.v (((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) :
    k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ := by
  have hO : ∀ {x : v.adicCompletion ℚ}, Valued.v x ≤ 1 → x ∈ v.adicCompletionIntegers ℚ :=
    fun hx => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx
  have hB : ∀ {x : v.adicCompletion ℚ}, x ∈ v.adicCompletionIntegers ℚ →
      Valued.v x ≤ NumberField.AdelicLevel.idealBound (𝓞 ℚ) (⊤ : Ideal (𝓞 ℚ)) v :=
    fun hx => by
      rw [NumberField.AdelicLevel.idealBound_top]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hx
  rw [AdelicDock.mem_localLevelOne_iff]
  exact ⟨⟨fun i j => hO (h1 i j), hB (hO (h1 1 0)), hB (sub_mem (hO (h1 1 1)) (one_mem _))⟩,
    ⟨fun i j => hO (h2 i j), hB (hO (h2 1 0)), hB (sub_mem (hO (h2 1 1)) (one_mem _))⟩⟩

theorem unipotent_mem_localLevelOne {β : v.adicCompletion ℚ} (hβ : Valued.v β ≤ 1) :
    unipotent β ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ := by
  refine mem_localLevelOne_top_of_valued_le v ?_ ?_
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [coe_unipotent, hβ]
  · rw [unipotent_inv]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [coe_unipotent, Valuation.map_neg, hβ]

theorem diagU_mem_localLevelOne {u₁ u₂ : (v.adicCompletion ℚ)ˣ}
    (hu₁ : Valued.v (u₁ : v.adicCompletion ℚ) = 1) (hu₂ : Valued.v (u₂ : v.adicCompletion ℚ) = 1) :
    diagU (u₁, u₂) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ := by
  refine mem_localLevelOne_top_of_valued_le v ?_ ?_
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [coe_diagU, hu₁, hu₂]
  · rw [coe_diagU_inv]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hu₁, hu₂]

theorem mem_localLevelOne_of_mem_integralSubgroup {k : GL (Fin 2) (v.adicCompletion ℚ)}
    (hk : k ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) :
    k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ := by
  obtain ⟨y, rfl⟩ := hk
  have hint : ∀ (z : GL (Fin 2) (v.adicCompletionIntegers ℚ)) (i j : Fin 2),
      Valued.v ((((Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) z) :
          GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1 :=
    fun z i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1
      ((z : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers ℚ)) i j).2
  refine mem_localLevelOne_top_of_valued_le v (hint y) ?_
  rw [← map_inv]
  exact hint y⁻¹

variable (ϖ : v.adicCompletion ℚ) (hπ : ϖ ≠ 0) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
  (ψ : v.adicCompletion ℚ → ℂ) (hψ0 : ∀ x, Valued.v x ≤ 1 → ψ x = 1)
  (hψ1 : ∃ x, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧ ψ x ≠ 1)
  {ι : Type} [Fintype ι] [Nonempty ι] (β : ι → v.adicCompletion ℚ) (hβ : ∀ i, Valued.v (β i) ≤ 1)
  (a c : ℂ) (hc : c ≠ 0)
  (w : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
  (hN : ∀ (x : v.adicCompletion ℚ) (y : GL (Fin 2) (v.adicCompletion ℚ)), w (unipotent x * y) = ψ x * w y)
  (hK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, ∀ y : GL (Fin 2) (v.adicCompletion ℚ), w (y * k) = w y)
  (hT : ∀ y : GL (Fin 2) (v.adicCompletion ℚ),
    ∑ i, w (y * repSome ϖ hπ (β i)) + w (y * repInf ϖ hπ) = a * w y)
  (hZ : ∀ y : GL (Fin 2) (v.adicCompletion ℚ), w (y * scalarPi ϖ hπ) = c * w y)

include hϖ in
theorem valued_zpow (m : ℤ) : Valued.v (ϖ ^ m) = WithZero.exp (-m) := by
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one]

include hϖ in

theorem exists_unit_mul_zpow (a : (v.adicCompletion ℚ)ˣ) :
    ∃ (u : (v.adicCompletion ℚ)ˣ) (m : ℤ), Valued.v (u : v.adicCompletion ℚ) = 1 ∧ a = Units.mk0 ϖ hπ ^ m * u := by
  set n : ℤ := WithZero.log (Valued.v (a : v.adicCompletion ℚ)) with hn
  have ha : Valued.v (a : v.adicCompletion ℚ) = WithZero.exp n := by
    rw [hn, WithZero.exp_log]
    exact (Valuation.ne_zero_iff _).2 a.ne_zero
  refine ⟨a * Units.mk0 ϖ hπ ^ n, -n, ?_, ?_⟩
  · rw [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, map_mul, valued_zpow v ϖ hϖ, ha,
      ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
  · rw [mul_left_comm, ← _root_.zpow_add, neg_add_cancel, zpow_zero, mul_one]

include hϖ hψ1 hN hK in

theorem torus_neg {m : ℤ} (hm : m < 0) : w (diagZ ϖ hπ m) = 0 := by
  obtain ⟨x₀, hx₀, hne⟩ := hψ1
  have hβ : Valued.v (ϖ ^ (-m) * x₀) ≤ 1 := by
    rw [map_mul, valued_zpow v ϖ hϖ, neg_neg]
    calc WithZero.exp m * Valued.v x₀ ≤ WithZero.exp m * WithZero.exp (1 : ℤ) := mul_le_mul_right hx₀ _
      _ = WithZero.exp (m + 1) := (WithZero.exp_add _ _).symm
      _ ≤ WithZero.exp 0 := WithZero.exp_le_exp.2 (by omega)
      _ = 1 := WithZero.exp_zero
  have h := hK _ (unipotent_mem_localLevelOne v hβ) (diagZ ϖ hπ m)
  rw [diagZ_mul_unipotent, hN, ← mul_assoc, ← zpow_add₀ hπ, add_neg_cancel, zpow_zero, one_mul] at h

  have h' : (ψ x₀ - 1) * w (diagZ ϖ hπ m) = 0 := by rw [sub_mul, one_mul, h, sub_self]
  exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 hne)

omit [Nonempty ι] in
include hϖ hψ0 hβ hN hT hZ in

theorem torus_rec {m : ℤ} (hm : 0 ≤ m) :
    (Fintype.card ι : ℂ) * w (diagZ ϖ hπ (m + 1)) + c * w (diagZ ϖ hπ (m - 1)) = a * w (diagZ ϖ hπ m) := by
  have h := hT (diagZ ϖ hπ m)
  have hs : ∀ i, w (diagZ ϖ hπ m * repSome ϖ hπ (β i)) = w (diagZ ϖ hπ (m + 1)) := fun i => by
    rw [diagZ_mul_repSome, hN, hψ0 _ ?_, one_mul]
    rw [map_mul, valued_zpow v ϖ hϖ]
    calc WithZero.exp (-m) * Valued.v (β i) ≤ WithZero.exp (-m) * 1 := mul_le_mul_right (hβ i) _
      _ ≤ WithZero.exp 0 * 1 := mul_le_mul_left (WithZero.exp_le_exp.2 (by omega)) _
      _ = 1 := by rw [WithZero.exp_zero, one_mul]
  rw [Finset.sum_congr rfl fun i _ => hs i, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    diagZ_mul_repInf, hZ] at h
  exact h

include hϖ hψ0 hψ1 hβ hN hK hT hZ in

theorem torus_zero (h1 : w 1 = 0) (m : ℤ) : w (diagZ ϖ hπ m) = 0 := by
  have hN0 : (Fintype.card ι : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have key : ∀ n : ℕ, w (diagZ ϖ hπ n) = 0 ∧ w (diagZ ϖ hπ ((n : ℤ) - 1)) = 0 := by
    intro n
    induction n with
    | zero =>
      refine ⟨by rw [Nat.cast_zero, diagZ_zero]; exact h1, ?_⟩
      exact torus_neg v ϖ hπ hϖ ψ hψ1 w hN hK (by norm_num)
    | succ n ih =>
      have hr := torus_rec v ϖ hπ hϖ ψ hψ0 β hβ a c w hN hT hZ (m := (n : ℤ)) (by positivity)
      rw [ih.1, ih.2, mul_zero, mul_zero, add_zero] at hr
      refine ⟨?_, ?_⟩
      · rw [Nat.cast_succ]
        exact (mul_eq_zero.1 hr).resolve_left hN0
      · rw [Nat.cast_succ, add_sub_cancel_right]
        exact ih.1
  rcases lt_or_ge m 0 with hm | hm
  · exact torus_neg v ϖ hπ hϖ ψ hψ1 w hN hK hm
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    exact (key n).1

include hc hZ in

theorem zero_iff_scalar_zpow (m : ℤ) (y : GL (Fin 2) (v.adicCompletion ℚ)) :
    w (y * scalarPi ϖ hπ ^ m) = 0 ↔ w y = 0 := by
  induction m using Int.induction_on generalizing y with
  | zero => rw [zpow_zero, mul_one]
  | succ n ih => rw [_root_.zpow_add_one, ← mul_assoc, hZ, mul_eq_zero, or_iff_right hc, ih]
  | pred n ih =>
    have e : y * scalarPi ϖ hπ ^ (-(n : ℤ) - 1) * scalarPi ϖ hπ = y * scalarPi ϖ hπ ^ (-(n : ℤ)) := by
      rw [mul_assoc, ← _root_.zpow_add_one, sub_add_cancel]
    rw [← ih y, ← e, hZ, mul_eq_zero, or_iff_right hc]

include hϖ hψ0 hψ1 hβ hc hN hK hT hZ in

theorem local_vanish (h1 : w 1 = 0) (y : GL (Fin 2) (v.adicCompletion ℚ)) : w y = 0 := by
  obtain ⟨z, a₁, a₂, k, hk, hy⟩ :=
    LocalGL2.iwasawa_decomposition_diag (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) y
  rw [eq_unipotent_mul_diagU_mul hy, hK k (mem_localLevelOne_of_mem_integralSubgroup v hk), hN]
  refine mul_eq_zero_of_right _ ?_
  obtain ⟨u₁, m₁, hu₁, rfl⟩ := exists_unit_mul_zpow v ϖ hπ hϖ a₁
  obtain ⟨u₂, m₂, hu₂, rfl⟩ := exists_unit_mul_zpow v ϖ hπ hϖ a₂
  rw [show (Units.mk0 ϖ hπ ^ m₁ * u₁, Units.mk0 ϖ hπ ^ m₂ * u₂) =
      (Units.mk0 ϖ hπ ^ m₁, Units.mk0 ϖ hπ ^ m₂) * (u₁, u₂) from rfl, map_mul,
    hK _ (diagU_mem_localLevelOne v hu₁ hu₂), diagU_zpow_eq, zero_iff_scalar_zpow v ϖ hπ c hc w hZ]
  exact torus_zero v ϖ hπ hϖ ψ hψ0 hψ1 β hβ a c w hN hK hT hZ h1 _

end Local

section Adelic
open UnramifiedWhittaker AdelicDock

abbrev G2 : Type := AdelicGL2 (𝓞 ℚ) ℚ
abbrev Gf : Type := ↥(finiteAdelicGL2Subgroup ℚ)

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem localAt_placeEmbed_self (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    localAt ℚ v (placeEmbed ℚ v x) = x := by
  show AdelicLevel.finComponent (𝓞 ℚ) ℚ v (AdelicLevel.glFin (𝓞 ℚ) ℚ (AdelicDock.finEmbed (𝓞 ℚ) ℚ
    (AdelicDock.localEmbed (𝓞 ℚ) ℚ v x))) = x
  rw [AdelicDock.glFin_finEmbed, AdelicDock.finComponent_localEmbed_self]

theorem localAt_placeEmbed_of_ne (x : GL (Fin 2) (v.adicCompletion ℚ)) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) :
    localAt ℚ w (placeEmbed ℚ v x) = 1 := by
  show AdelicLevel.finComponent (𝓞 ℚ) ℚ w (AdelicLevel.glFin (𝓞 ℚ) ℚ (AdelicDock.finEmbed (𝓞 ℚ) ℚ
    (AdelicDock.localEmbed (𝓞 ℚ) ℚ v x))) = 1
  rw [AdelicDock.glFin_finEmbed, AdelicDock.finComponent_localEmbed_of_ne _ _ _ _ hw]

theorem placeEmbed_mem_fin (x : GL (Fin 2) (v.adicCompletion ℚ)) : placeEmbed ℚ v x ∈ finiteAdelicGL2Subgroup ℚ := by
  rw [mem_finiteAdelicGL2Subgroup_iff]
  exact AdelicDock.glArch_finEmbed _ _ _

theorem eventually_mem_localLevelOne (g : G2) :
    ∀ᶠ w in Filter.cofinite, localAt ℚ w g ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ w ⊤ := by
  have h1 : ∀ i j : Fin 2, ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
      ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 w ∈ w.adicCompletionIntegers ℚ :=
    fun i j => ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2.2
  have h2 : ∀ i j : Fin 2, ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
      (((g⁻¹ : G2) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 w ∈ w.adicCompletionIntegers ℚ :=
    fun i j => (((g⁻¹ : G2) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2.2
  have hall := (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => h1 i j).and
    (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => h2 i j)
  refine hall.mono fun w hw => ?_
  have hint : ∀ {x : w.adicCompletion ℚ}, x ∈ w.adicCompletionIntegers ℚ →
      Valued.v x ≤ NumberField.AdelicLevel.idealBound (𝓞 ℚ) (⊤ : Ideal (𝓞 ℚ)) w :=
    fun hx => by
      rw [NumberField.AdelicLevel.idealBound_top]
      exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hx
  rw [AdelicDock.mem_localLevelOne_iff, ← map_inv]
  exact ⟨⟨fun i j => hw.1 i j, hint (hw.1 1 0), hint (sub_mem (hw.1 1 1) (one_mem _))⟩,
    ⟨fun i j => hw.2 i j, hint (hw.2 1 0), hint (sub_mem (hw.2 1 1) (one_mem _))⟩⟩

theorem placeEmbed_mul_comm {g : G2} (hg : localAt ℚ v g = 1)
    (x : GL (Fin 2) (v.adicCompletion ℚ)) : placeEmbed ℚ v x * g = g * placeEmbed ℚ v x := by
  have hgp : (finAdeleEval (𝓞 ℚ) ℚ v).mapMatrix ((adeleFin (𝓞 ℚ) ℚ).mapMatrix
      (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))) = 1 := congrArg Units.val hg
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  show finMat (𝓞 ℚ) ℚ (localMat (𝓞 ℚ) ℚ v x) * _ = _ * finMat (𝓞 ℚ) ℚ (localMat (𝓞 ℚ) ℚ v x)
  refine matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 ℚ) ℚ ?_ ?_
  · rw [map_mul, map_mul, mapMatrix_arch_finMat, one_mul, mul_one]
  · rw [map_mul, map_mul, mapMatrix_fin_finMat]
    refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 ℚ) ℚ fun w => ?_
    rw [map_mul, map_mul]
    by_cases hw : w = v
    · subst hw
      rw [hgp, mul_one, one_mul]
    · rw [mapMatrix_localMat_of_ne (𝓞 ℚ) ℚ v _ hw, one_mul, mul_one]

theorem coe_finFactor (g : G2) :
    (RSCarrier.finFactor g : G2) =
      (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 g))⁻¹ * g := rfl

theorem ratArchGL2_of_mem {g : G2} (hg : g ∈ finiteAdelicGL2Subgroup ℚ) : ratArchGL2 g = 1 := by
  unfold LanglandsTunnell.ratArchGL2
  rw [(mem_finiteAdelicGL2Subgroup_iff ℚ g).1 hg, map_one, map_one]

theorem finFactor_coe (gf : Gf) : RSCarrier.finFactor (gf : G2) = gf := by
  refine Subtype.ext ?_
  rw [coe_finFactor, ratArchGL2_of_mem gf.2, map_one, inv_one, one_mul]

def E : GL (Fin 2) (v.adicCompletion ℚ) →* Gf :=
  (placeEmbed ℚ v).codRestrict _ (placeEmbed_mem_fin v)

theorem coe_mul_E (g : Gf) (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    ((g * E v x : Gf) : G2) = (g : G2) * placeEmbed ℚ v x := rfl

theorem finFactor_mul_placeEmbed (g : Gf) (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    RSCarrier.finFactor ((g : G2) * placeEmbed ℚ v x) = g * E v x :=
  finFactor_coe (g * E v x)

theorem localAt_mul_E_self (g : Gf) (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    localAt ℚ v ((g * E v x : Gf) : G2) = localAt ℚ v (g : G2) * x := by
  rw [coe_mul_E, map_mul, localAt_placeEmbed_self]

theorem localAt_mul_E_of_ne (g : Gf) (x : GL (Fin 2) (v.adicCompletion ℚ)) {w : HeightOneSpectrum (𝓞 ℚ)}
    (hw : w ≠ v) : localAt ℚ w ((g * E v x : Gf) : G2) = localAt ℚ w (g : G2) := by
  rw [coe_mul_E, map_mul, localAt_placeEmbed_of_ne v _ hw, mul_one]

theorem psi_level_zero :
    (∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → psiLoc NumberField.StandardAddChar.psiQ v x = 1) ∧
      ∃ x : v.adicCompletion ℚ, Valued.v x ≤ WithZero.exp (1 : ℤ) ∧
        psiLoc NumberField.StandardAddChar.psiQ v x ≠ 1 := by
  have hloc : ∀ x : v.adicCompletion ℚ,
      psiLoc NumberField.StandardAddChar.psiQ v x = NumberField.StandardAddChar.psiLocal ℚ v x :=
    fun x => (NumberField.StandardAddChar.psiLocal_rat_eq_psiQ_adeleSingleAt v x).symm
  have h0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → NumberField.StandardAddChar.psiLocal ℚ v x = 1 :=
    fun x hx => LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers ℚ v x
      ((IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx)
  have h := LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel ℚ v
    (NumberField.StandardAddChar.psiLocal ℚ v) ⟨0, fun x hx => h0 x (by rwa [WithZero.exp_zero] at hx)⟩
    (LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ v)
  rw [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat, zero_add] at h
  obtain ⟨x, hx, hne⟩ := h.2
  exact ⟨fun x hx => (hloc x).trans (h0 x hx), x, hx, fun e => hne ((hloc x).symm.trans e)⟩

theorem key
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    [hIfin : ∀ p : HeightOneSpectrum (𝓞 ℚ), Fintype (𝓞 ℚ ⧸ p.asIdeal)]
    (ϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p.adicCompletionIntegers ℚ)
    (hπ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p) ≠ 0)
    (hϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) = WithZero.exp (-1 : ℤ))
    (aev bev : HeightOneSpectrum (𝓞 ℚ) → ℂ) (hbev : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → bev v ≠ 0)
    (W : finiteAdelicGL2Subgroup ℚ → ℂ)
    (hHL :         (∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ SQ → ∀ (x : q.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          W (RSCarrier.finFactor (UnramifiedWhittaker.placeEmbed ℚ q (UnramifiedWhittaker.unipotent x) * g)) =
            psiLoc NumberField.StandardAddChar.psiQ q x * W (RSCarrier.finFactor g)) ∧
        (∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ SQ →
          ∀ (x : GL (Fin 2) (q.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
            x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ q ⊤ →
              W (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ q x)) = W (RSCarrier.finFactor g)) ∧
        (∀ q : HeightOneSpectrum (𝓞 ℚ), ∀ hq : q ∉ SQ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          (∑ r, W (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ q (UnramifiedWhittaker.repSome
              (algebraMap (q.adicCompletionIntegers ℚ) (q.adicCompletion ℚ) (ϖ q)) (hπ q hq)
              (algebraMap (q.adicCompletionIntegers ℚ) (q.adicCompletion ℚ)
                (algebraMap (𝓞 ℚ) (q.adicCompletionIntegers ℚ) (Quotient.out (r : 𝓞 ℚ ⧸ q.asIdeal)))))))) +
            W (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ q (UnramifiedWhittaker.repInf
              (algebraMap (q.adicCompletionIntegers ℚ) (q.adicCompletion ℚ) (ϖ q)) (hπ q hq)))) =
            aev q * W (RSCarrier.finFactor g)) ∧
        (∀ q : HeightOneSpectrum (𝓞 ℚ), ∀ hq : q ∉ SQ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          W (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ q (UnramifiedWhittaker.scalarPi
            (algebraMap (q.adicCompletionIntegers ℚ) (q.adicCompletion ℚ) (ϖ q)) (hπ q hq)))) =
            (bev q / (Ideal.absNorm q.asIdeal : ℂ)) * W (RSCarrier.finFactor g)))
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∉ SQ) (h : Gf) (hh : localAt ℚ v (h : G2) = 1) (hW0 : W h = 0)
    (y : GL (Fin 2) (v.adicCompletion ℚ)) : W (h * E v y) = 0 := by
  obtain ⟨hHN, hHK, hHT, hHZ⟩ := hHL
  have hfin : ∀ z : GL (Fin 2) (v.adicCompletion ℚ),
      RSCarrier.finFactor ((h : G2) * placeEmbed ℚ v z) = h * E v z := finFactor_mul_placeEmbed v h
  obtain ⟨hψ0, hψ1⟩ := psi_level_zero v
  haveI : Nonempty (𝓞 ℚ ⧸ v.asIdeal) := ⟨0⟩
  have hNv : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h0 => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  refine local_vanish v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) (hϖ v hv)
    (fun x => psiLoc NumberField.StandardAddChar.psiQ v x) hψ0 hψ1
    (fun r : 𝓞 ℚ ⧸ v.asIdeal => algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)
      (algebraMap (𝓞 ℚ) (v.adicCompletionIntegers ℚ) (Quotient.out r)))
    (fun r => (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1
      (algebraMap (𝓞 ℚ) (v.adicCompletionIntegers ℚ) (Quotient.out r)).2)
    (aev v) (bev v / (Ideal.absNorm v.asIdeal : ℂ)) (div_ne_zero (hbev v hv) hNv)
    (fun y => W (h * E v y)) ?_ ?_ ?_ ?_ ?_ y
  · intro x y
    have e := hHN v hv x ((h : G2) * placeEmbed ℚ v y)
    rw [← mul_assoc, placeEmbed_mul_comm v hh, mul_assoc, ← map_mul, hfin, hfin] at e
    exact e
  · intro k hk y
    have e := hHK v hv k ((h : G2) * placeEmbed ℚ v y) hk
    rw [mul_assoc, ← map_mul, hfin, hfin] at e
    exact e
  · intro y
    have e := hHT v hv ((h : G2) * placeEmbed ℚ v y)
    simp only [mul_assoc, ← map_mul, hfin] at e
    exact e
  · intro y
    have e := hHZ v hv ((h : G2) * placeEmbed ℚ v y)
    rw [mul_assoc, ← map_mul, hfin, hfin] at e
    exact e
  · show W (h * E v 1) = 0
    rw [map_one, mul_one]
    exact hW0

theorem exists_strip (C : Finset (HeightOneSpectrum (𝓞 ℚ))) (g : Gf) :
    ∃ k : Gf, (∀ w ∈ C, localAt ℚ w (k : G2) = 1) ∧ (∀ w, w ∉ C → localAt ℚ w (k : G2) = localAt ℚ w (g : G2)) := by
  classical
  induction C using Finset.induction_on with
  | empty => exact ⟨g, fun w hw => absurd hw (Finset.notMem_empty w), fun w _ => rfl⟩
  | @insert v C hvC ih =>
    obtain ⟨k, hk1, hk2⟩ := ih
    refine ⟨k * E v (localAt ℚ v (k : G2))⁻¹, ?_, ?_⟩
    · intro w hw
      rcases Finset.mem_insert.1 hw with rfl | hw
      · rw [localAt_mul_E_self, mul_inv_cancel]
      · have hwv : w ≠ v := fun e => hvC (e ▸ hw)
        rw [localAt_mul_E_of_ne v _ _ hwv, hk1 w hw]
    · intro w hw
      have hwv : w ≠ v := fun e => hw (e ▸ Finset.mem_insert_self v C)
      have hwC : w ∉ C := fun e => hw (Finset.mem_insert_of_mem e)
      rw [localAt_mul_E_of_ne v _ _ hwv, hk2 w hwC]

theorem descend (SQ : Finset (HeightOneSpectrum (𝓞 ℚ))) (W : Gf → ℂ)
    (hkey : ∀ v, v ∉ SQ → ∀ h : Gf, localAt ℚ v (h : G2) = 1 → W h = 0 →
      ∀ y : GL (Fin 2) (v.adicCompletion ℚ), W (h * E v y) = 0) :
    ∀ (D : Finset (HeightOneSpectrum (𝓞 ℚ))) (g : Gf),
      (∀ w, w ∉ D → w ∉ SQ → localAt ℚ w (g : G2) = 1) → W g ≠ 0 →
        ∃ g' : Gf, (∀ w, w ∉ SQ → localAt ℚ w (g' : G2) = 1) ∧ W g' ≠ 0 := by
  classical
  intro D
  induction D using Finset.induction_on with
  | empty =>
    intro g hg hW
    exact ⟨g, fun w hw => hg w (Finset.notMem_empty w) hw, hW⟩
  | @insert v D hvD ih =>
    intro g hg hW
    by_cases hv : v ∈ SQ
    · exact ih g (fun w hwD hwSQ => hg w
        (fun e => (Finset.mem_insert.1 e).elim (fun e' => hwSQ (e' ▸ hv)) hwD) hwSQ) hW
    · set h : Gf := g * E v (localAt ℚ v (g : G2))⁻¹ with hdef
      have hh : localAt ℚ v (h : G2) = 1 := by rw [hdef, localAt_mul_E_self, mul_inv_cancel]
      have hg' : g = h * E v (localAt ℚ v (g : G2)) := by
        rw [hdef, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
      have hWh : W h ≠ 0 := fun h0 => hW (by rw [hg']; exact hkey v hv h hh h0 _)
      refine ih h (fun w hwD hwSQ => ?_) hWh
      by_cases hwv : w = v
      · subst hwv; exact hh
      · rw [hdef, localAt_mul_E_of_ne v _ _ hwv]
        exact hg w (fun e => (Finset.mem_insert.1 e).elim hwv hwD) hwSQ

end Adelic

end Ws23HL

open Ws23HL in
theorem solution
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    [hIfin : ∀ p : HeightOneSpectrum (𝓞 ℚ), Fintype (𝓞 ℚ ⧸ p.asIdeal)]
    (ϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p.adicCompletionIntegers ℚ)
    (hπ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p) ≠ 0)
    (hϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) = WithZero.exp (-1 : ℤ))
    (aev bev : HeightOneSpectrum (𝓞 ℚ) → ℂ) (hbev : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → bev v ≠ 0)
    (W : finiteAdelicGL2Subgroup ℚ → ℂ)

    (hHL :         (∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ SQ → ∀ (x : q.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          W (RSCarrier.finFactor (UnramifiedWhittaker.placeEmbed ℚ q (UnramifiedWhittaker.unipotent x) * g)) =
            psiLoc NumberField.StandardAddChar.psiQ q x * W (RSCarrier.finFactor g)) ∧
        (∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ SQ →
          ∀ (x : GL (Fin 2) (q.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
            x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ q ⊤ →
              W (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ q x)) = W (RSCarrier.finFactor g)) ∧
        (∀ q : HeightOneSpectrum (𝓞 ℚ), ∀ hq : q ∉ SQ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          (∑ r, W (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ q (UnramifiedWhittaker.repSome
              (algebraMap (q.adicCompletionIntegers ℚ) (q.adicCompletion ℚ) (ϖ q)) (hπ q hq)
              (algebraMap (q.adicCompletionIntegers ℚ) (q.adicCompletion ℚ)
                (algebraMap (𝓞 ℚ) (q.adicCompletionIntegers ℚ) (Quotient.out (r : 𝓞 ℚ ⧸ q.asIdeal)))))))) +
            W (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ q (UnramifiedWhittaker.repInf
              (algebraMap (q.adicCompletionIntegers ℚ) (q.adicCompletion ℚ) (ϖ q)) (hπ q hq)))) =
            aev q * W (RSCarrier.finFactor g)) ∧
        (∀ q : HeightOneSpectrum (𝓞 ℚ), ∀ hq : q ∉ SQ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          W (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ q (UnramifiedWhittaker.scalarPi
            (algebraMap (q.adicCompletionIntegers ℚ) (q.adicCompletion ℚ) (ϖ q)) (hπ q hq)))) =
            (bev q / (Ideal.absNorm q.asIdeal : ℂ)) * W (RSCarrier.finFactor g)))

    (hK : ∀ k : finiteAdelicGL2Subgroup ℚ,
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
        localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) →
      (∀ v ∈ SQ, localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1) →
      ∀ g : finiteAdelicGL2Subgroup ℚ, W (g * k) = W g)
    (hne : ∃ g : finiteAdelicGL2Subgroup ℚ, W g ≠ 0) :
    ∃ g : finiteAdelicGL2Subgroup ℚ,
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = 1) ∧ W g ≠ 0 := by
  classical
  obtain ⟨g₀, hg₀⟩ := hne
  obtain ⟨T, hT⟩ : ∃ T : Finset (HeightOneSpectrum (𝓞 ℚ)), ∀ v, v ∉ T →
      localAt ℚ v (g₀ : AdelicGL2 (𝓞 ℚ) ℚ) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ := by
    have h := Ws23HL.eventually_mem_localLevelOne (g₀ : AdelicGL2 (𝓞 ℚ) ℚ)
    rw [Filter.eventually_cofinite] at h
    exact ⟨h.toFinset, fun v hv => by_contra fun h' => hv (h.mem_toFinset.2 h')⟩
  obtain ⟨k, hk1, hk2⟩ := Ws23HL.exists_strip (SQ ∪ T) g₀
  have hkK := hK k
    (fun v hv => by
      by_cases hvT : v ∈ T
      · rw [hk1 v (Finset.mem_union_right _ hvT)]; exact one_mem _
      · rw [hk2 v (fun e => (Finset.mem_union.1 e).elim hv hvT)]; exact hT v hvT)
    (fun v hv => hk1 v (Finset.mem_union_left _ hv)) (g₀ * k⁻¹)
  rw [inv_mul_cancel_right] at hkK
  refine Ws23HL.descend SQ W (Ws23HL.key SQ ϖ hπ hϖ aev bev hbev W hHL) (SQ ∪ T) (g₀ * k⁻¹)
    (fun v hvC _ => ?_) (by rw [← hkK]; exact hg₀)
  show localAt ℚ v ((g₀ : AdelicGL2 (𝓞 ℚ) ℚ) * (k : AdelicGL2 (𝓞 ℚ) ℚ)⁻¹) = 1
  rw [map_mul, map_inv, hk2 v hvC, mul_inv_cancel]

#print axioms solution

end
end S_LanglandsTunnell_RankinSelberg_exists_forall_localAt_eq_one_and_ne_zero_of_heckeLocal_of_levelOne_invariant
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_localAt_eq_one_and_ne_zero_of_heckeLocal_of_levelOne_invariant (solution)
