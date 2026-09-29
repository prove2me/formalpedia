-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_forall_exists_localZetaDual31_ne_zero_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/1bf3128d-a2b6-5de1-b11b-35e33c7be257

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_localZeta30_selfDual_ne_zero_of_isGL3PsiWhittakerFn_of_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_exists_localZetaDual31_ne_zero_of_irreducible
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open IsDedekindDomain NumberField NumberField.TateGlobal LanglandsTunnell.TateLocal MeasureTheory
open scoped NNReal ENNReal Topology Pointwise Matrix

noncomputable section

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

namespace LTZeta31NV

open LanglandsTunnell.CubicInduction

section Algebra

variable {A : Type*} [CommRing A]

theorem transposeInv3_coe (g : GL (Fin 3) A) :
    ((transposeInv3 g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      (((g⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ := rfl

theorem transposeInv3_mul (g h : GL (Fin 3) A) :
    transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  refine Units.ext ?_
  rw [Units.val_mul, transposeInv3_coe, transposeInv3_coe, transposeInv3_coe, mul_inv_rev, Units.val_mul,
    Matrix.transpose_mul]

theorem transposeInv3_one : transposeInv3 (1 : GL (Fin 3) A) = 1 := by
  refine Units.ext ?_
  rw [transposeInv3_coe, inv_one, Units.val_one, Matrix.transpose_one]

theorem transposeInv3_transposeInv3 (g : GL (Fin 3) A) : transposeInv3 (transposeInv3 g) = g := by
  refine Units.ext ?_
  show ((((g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A))ᵀ)ᵀ = _
  exact Matrix.transpose_transpose _

def tIHom : GL (Fin 3) A →* GL (Fin 3) A where
  toFun := transposeInv3
  map_one' := transposeInv3_one
  map_mul' := transposeInv3_mul

@[scoped simp] theorem tIHom_apply (g : GL (Fin 3) A) : tIHom g = transposeInv3 g := rfl

theorem longWeyl3_mul_self : (longWeyl3 : GL (Fin 3) A) * longWeyl3 = 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

theorem longWeyl3_inv : (longWeyl3 : GL (Fin 3) A)⁻¹ = longWeyl3 :=
  inv_eq_of_mul_eq_one_right longWeyl3_mul_self

theorem coe_inv_upperUnipotent3 (x y z : A) :
    (((upperUnipotent3 x y z)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      !![1, -x, x * y - z; 0, 1, -y; 0, 0, 1] := rfl

theorem coe_transposeInv3_upperUnipotent3 (x y z : A) :
    ((transposeInv3 (upperUnipotent3 x y z) : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      !![1, 0, 0; -x, 1, 0; x * y - z, -y, 1] := by
  rw [transposeInv3_coe, coe_inv_upperUnipotent3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]

theorem longWeyl3_mul_transposeInv3_upperUnipotent3_mul_longWeyl3 (x y z : A) :
    (longWeyl3 : GL (Fin 3) A) * transposeInv3 (upperUnipotent3 x y z) * longWeyl3 =
      upperUnipotent3 (-y) (-x) (x * y - z) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_transposeInv3_upperUnipotent3, longWeyl3_coe,
    upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem isGL3PsiWhittakerFn_dualWhittakerFn3 {R : Type*} [CommRing R] {ψ : AddChar A R}
    {W : GL (Fin 3) A → R} (hW : IsGL3PsiWhittakerFn ψ⁻¹ W) :
    IsGL3PsiWhittakerFn ψ (dualWhittakerFn3 W) := by
  intro x y z g
  rw [dualWhittakerFn3_apply, dualWhittakerFn3_apply, transposeInv3_mul]
  have h : (longWeyl3 : GL (Fin 3) A) * (transposeInv3 (upperUnipotent3 x y z) * transposeInv3 g) =
      upperUnipotent3 (-y) (-x) (x * y - z) * (longWeyl3 * transposeInv3 g) := by
    rw [← longWeyl3_mul_transposeInv3_upperUnipotent3_mul_longWeyl3]
    have : (longWeyl3 : GL (Fin 3) A) * (transposeInv3 (upperUnipotent3 x y z) * transposeInv3 g) =
        longWeyl3 * transposeInv3 (upperUnipotent3 x y z) * longWeyl3⁻¹ * (longWeyl3 * transposeInv3 g) := by
      group
    rw [this, longWeyl3_inv]
  rw [h, hW, AddChar.inv_apply]
  congr 2
  ring

theorem iotaDiag_mul_lower_mul_upper (a : Aˣ) (x z : A) :
    iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * upperUnipotent3 0 0 z =
      upperUnipotent3 0 (x * z) ((a : A) * z) * (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x) := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, embedMat2]

theorem apply_iotaDiag_lower_upper {R : Type*} [CommRing R] {ψ : AddChar A R} {W : GL (Fin 3) A → R}
    (hW : IsGL3PsiWhittakerFn ψ W) (a : Aˣ) (x z : A) (h : GL (Fin 3) A) :
    W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (upperUnipotent3 0 0 z * h)) =
      ψ (x * z) * W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h) := by
  have : iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (upperUnipotent3 0 0 z * h) =
      upperUnipotent3 0 (x * z) ((a : A) * z) * (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h) := by
    rw [← mul_assoc, iotaDiag_mul_lower_mul_upper, mul_assoc]
  rw [this, hW, zero_add]

theorem upperUnipotent3_zero_zero_add (z e : A) :
    upperUnipotent3 (0 : A) 0 (z + e) = upperUnipotent3 0 0 z * upperUnipotent3 0 0 e := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, add_comm]

theorem lowerUnipotent21_zero : lowerUnipotent21 (0 : A) = 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end Algebra

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v

theorem surjV : Function.Surjective (Valued.v : 𝕂 → WithZero (Multiplicative ℤ)) :=
  HeightOneSpectrum.valuedAdicCompletion_surjective ℚ v

theorem isClopen_le {γ : WithZero (Multiplicative ℤ)} (hγ : γ ≠ 0) :
    IsClopen {x : 𝕂 | Valued.v x ≤ γ} := by
  obtain ⟨y, hy⟩ := surjV v γ
  have h : {x : 𝕂 | Valued.v x ≤ γ} = {x : 𝕂 | Valued.v.restrict x ≤ Valued.v.restrict y} := by
    ext x; simp [Valuation.restrict_le_iff, hy]
  rw [h]
  have hy0 : y ≠ 0 := by
    intro h0; rw [h0, Valuation.map_zero] at hy; exact hγ hy.symm
  exact Valued.isClopen_closedBall _ ((Valuation.ne_zero_iff _).mpr hy0)

theorem exists_ball_sub_of_mem_nhds {s : Set 𝕂} {x : 𝕂} (h : s ∈ 𝓝 x) :
    ∃ n : ℤ, ∀ y : 𝕂, Valued.v (y - x) ≤ WithZero.exp n → y ∈ s := by
  rw [Valued.mem_nhds] at h
  obtain ⟨γ, hγ⟩ := h
  set g : WithZero (Multiplicative ℤ) :=
    MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hg
  have hg0 : g ≠ 0 := by
    rw [hg]
    exact (map_ne_zero _).mpr γ.ne_zero
  refine ⟨WithZero.log g - 1, fun y hy => hγ ?_⟩
  show Valued.v.restrict (y - x) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding, ← hg]
  calc Valued.v (y - x) ≤ WithZero.exp (WithZero.log g - 1) := hy
    _ < WithZero.exp (WithZero.log g) := by
        rw [WithZero.exp_lt_exp]; omega
    _ = g := WithZero.exp_log hg0

def lat (n : ℤ) : Set 𝕂 := {x : 𝕂 | Valued.v x ≤ WithZero.exp n}

theorem mem_lat {n : ℤ} {x : 𝕂} : x ∈ lat v n ↔ Valued.v x ≤ WithZero.exp n := Iff.rfl

theorem zero_mem_lat (n : ℤ) : (0 : 𝕂) ∈ lat v n := by simp [mem_lat]

theorem add_mem_lat {n : ℤ} {x y : 𝕂} (hx : x ∈ lat v n) (hy : y ∈ lat v n) : x + y ∈ lat v n := by
  rw [mem_lat] at hx hy ⊢
  exact le_trans (Valued.v.map_add x y) (max_le hx hy)

theorem neg_mem_lat {n : ℤ} {x : 𝕂} (hx : x ∈ lat v n) : -x ∈ lat v n := by
  rw [mem_lat, Valuation.map_neg]; exact hx

theorem sub_mem_lat {n : ℤ} {x y : 𝕂} (hx : x ∈ lat v n) (hy : y ∈ lat v n) : x - y ∈ lat v n := by
  rw [sub_eq_add_neg]; exact add_mem_lat v hx (neg_mem_lat v hy)

theorem lat_mono {m n : ℤ} (h : m ≤ n) : lat v m ⊆ lat v n := fun _ hx =>
  le_trans hx (WithZero.exp_le_exp.mpr h)

theorem mul_mem_lat {k m : ℤ} {a x : 𝕂} (ha : Valued.v a ≤ WithZero.exp k) (hx : x ∈ lat v m) :
    a * x ∈ lat v (k + m) := by
  rw [mem_lat, Valuation.map_mul, WithZero.exp_add]
  exact mul_le_mul' ha hx

theorem isClopen_lat (n : ℤ) : IsClopen (lat v n) := isClopen_le v WithZero.exp_ne_zero

theorem isOpen_lat (n : ℤ) : IsOpen (lat v n) := (isClopen_lat v n).isOpen

theorem measurableSet_lat (n : ℤ) : MeasurableSet (lat v n) := (isOpen_lat v n).measurableSet

theorem lat_zero_eq : lat v 0 = (v.adicCompletionIntegers ℚ : Set 𝕂) := by
  ext x
  rw [mem_lat, WithZero.exp_zero]
  exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).symm

theorem isCompact_lat (n : ℤ) : IsCompact (lat v n) := by
  have h0 : IsCompact (lat v 0) := by
    rw [lat_zero_eq]
    exact isCompact_iff_compactSpace.mpr
      (show CompactSpace (v.adicCompletionIntegers ℚ) from inferInstance)
  obtain ⟨y, hy⟩ := surjV v (WithZero.exp n)
  have hy0 : y ≠ 0 := by
    intro h; rw [h, Valuation.map_zero] at hy; exact WithZero.exp_ne_zero hy.symm
  have hset : lat v n = (fun x => y * x) '' lat v 0 := by
    ext x
    constructor
    · intro hx
      refine ⟨y⁻¹ * x, ?_, by field_simp⟩
      rw [mem_lat, Valuation.map_mul, map_inv₀, hy, WithZero.exp_zero]
      rw [mem_lat] at hx
      calc (WithZero.exp n)⁻¹ * Valued.v x ≤ (WithZero.exp n)⁻¹ * WithZero.exp n :=
            mul_le_mul' le_rfl hx
        _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
    · rintro ⟨z, hz, rfl⟩
      rw [mem_lat, Valuation.map_mul, hy]
      rw [mem_lat, WithZero.exp_zero] at hz
      calc WithZero.exp n * Valued.v z ≤ WithZero.exp n * 1 := mul_le_mul' le_rfl hz
        _ = WithZero.exp n := mul_one _
  rw [hset]
  exact h0.image (continuous_const.mul continuous_id)

theorem isOpen_ball (a : 𝕂) (j : ℤ) : IsOpen {y : 𝕂 | y - a ∈ lat v j} :=
  (isOpen_lat v j).preimage (continuous_id.sub continuous_const)

theorem v_natCast_le_one (k : ℕ) : Valued.v ((k : 𝕂)) ≤ 1 := by
  have : ((k : 𝕂)) ∈ (v.adicCompletionIntegers ℚ : Set 𝕂) := by
    have h := natCast_mem (v.adicCompletionIntegers ℚ) k
    exact_mod_cast h
  exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mp this

section AddChar

variable {v}
variable (ψ : AddChar (HeightOneSpectrum.adicCompletion ℚ v) ℂ)

theorem norm_apply_eq_one (hc : Continuous ψ) (z : 𝕂) : ‖ψ z‖ = 1 := by
  have key : ∀ z : 𝕂, ‖ψ z‖ ≤ 1 := by
    intro z
    by_cases hz : z = 0
    · rw [hz, AddChar.map_zero_eq_one, norm_one]
    have hvz : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).mpr hz
    set n := WithZero.log (Valued.v z) with hn
    have hzn : z ∈ lat v n := by
      rw [mem_lat, hn, WithZero.exp_log hvz]
    obtain ⟨C, hC⟩ := (isCompact_lat v n).exists_bound_of_continuousOn hc.continuousOn
    have hpow : ∀ k : ℕ, ‖ψ z‖ ^ k ≤ C := by
      intro k
      have hkz : (k • z) ∈ lat v n := by
        rw [nsmul_eq_mul, mem_lat, Valuation.map_mul]
        calc Valued.v (k : 𝕂) * Valued.v z ≤ 1 * Valued.v z :=
              mul_le_mul' (v_natCast_le_one v k) le_rfl
          _ = Valued.v z := one_mul _
          _ ≤ WithZero.exp n := hzn
      have := hC _ hkz
      rwa [AddChar.map_nsmul_eq_pow, norm_pow] at this
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C hlt
    exact absurd (hpow k) (not_le.mpr hk)
  have h1 : ‖ψ z‖ * ‖ψ (-z)‖ = 1 := by
    rw [← norm_mul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, norm_one]
  have hz := key z
  have hnz := key (-z)
  by_contra hne
  have hlt : ‖ψ z‖ < 1 := lt_of_le_of_ne hz hne
  have : ‖ψ z‖ * ‖ψ (-z)‖ < 1 := by
    calc ‖ψ z‖ * ‖ψ (-z)‖ ≤ ‖ψ z‖ * 1 := mul_le_mul_of_nonneg_left hnz (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hlt
  exact absurd h1 (ne_of_lt this)

theorem exists_level (hψ : ψ ≠ 1) {n₀ : ℤ} (hker : ∀ x ∈ lat v n₀, ψ x = 1) :
    ∃ d : ℤ, (∀ x ∈ lat v d, ψ x = 1) ∧ ∃ t ∈ lat v (d + 1), ψ t ≠ 1 := by
  obtain ⟨t, ht⟩ := AddChar.ne_one_iff.mp hψ
  have ht0 : t ≠ 0 := by
    intro h; rw [h, AddChar.map_zero_eq_one] at ht; exact ht rfl
  have hvt : Valued.v t ≠ 0 := (Valuation.ne_zero_iff _).mpr ht0
  have hbdd : ∃ b : ℤ, ∀ z : ℤ, (∀ x ∈ lat v z, ψ x = 1) → z ≤ b := by
    refine ⟨WithZero.log (Valued.v t), fun z hz => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    have : t ∈ lat v z := by
      rw [mem_lat, ← WithZero.exp_log hvt]
      exact WithZero.exp_le_exp.mpr hlt.le
    exact ht (hz t this)
  obtain ⟨d, hd, hmax⟩ := Int.exists_greatest_of_bdd hbdd ⟨n₀, hker⟩
  refine ⟨d, hd, ?_⟩
  by_contra h
  push Not at h
  have := hmax (d + 1) h
  omega

variable (μ : Measure (HeightOneSpectrum.adicCompletion ℚ v))

theorem setIntegral_lat_char_of_forall_eq_one {m : ℤ} {b : 𝕂}
    (h : ∀ x ∈ lat v m, ψ (b * x) = 1) :
    ∫ x in lat v m, ψ (b * x) ∂μ = (μ.real (lat v m) : ℂ) := by
  rw [setIntegral_congr_fun (measurableSet_lat v m) (fun x hx => h x hx), setIntegral_const]
  simp

theorem setIntegral_lat_char_eq_zero [μ.IsAddHaarMeasure] {m : ℤ} {b : 𝕂} {x₀ : 𝕂} (hx₀ : x₀ ∈ lat v m)
    (h : ψ (b * x₀) ≠ 1) :
    ∫ x in lat v m, ψ (b * x) ∂μ = 0 := by
  set I := ∫ x in lat v m, ψ (b * x) ∂μ with hI
  have hind : I = ∫ x, (lat v m).indicator (fun x => ψ (b * x)) x ∂μ := by
    rw [hI, integral_indicator (measurableSet_lat v m)]
  have htrans : ∫ x, (lat v m).indicator (fun x => ψ (b * x)) (x₀ + x) ∂μ =
      ∫ x, (lat v m).indicator (fun x => ψ (b * x)) x ∂μ :=
    integral_add_left_eq_self _ x₀
  have hpt : ∀ x, (lat v m).indicator (fun x => ψ (b * x)) (x₀ + x) =
      ψ (b * x₀) * (lat v m).indicator (fun x => ψ (b * x)) x := by
    intro x
    by_cases hx : x ∈ lat v m
    · have hx' : x₀ + x ∈ lat v m := add_mem_lat v hx₀ hx
      rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx, mul_add, AddChar.map_add_eq_mul]
    · have hx' : x₀ + x ∉ lat v m := by
        intro h'
        apply hx
        have : x = (x₀ + x) - x₀ := by ring
        rw [this]; exact sub_mem_lat v h' hx₀
      rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem hx, mul_zero]
  simp_rw [hpt] at htrans
  rw [integral_const_mul, ← hind] at htrans
  have : (ψ (b * x₀) - 1) * I = 0 := by rw [sub_mul, one_mul, htrans, sub_self]
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) h
  · exact h1

theorem forall_lat_char_eq_one_iff {d : ℤ} (hd : ∀ x ∈ lat v d, ψ x = 1) {t : 𝕂}
    (ht : t ∈ lat v (d + 1)) (hψt : ψ t ≠ 1) (m : ℤ) (b : 𝕂) :
    (∀ x ∈ lat v m, ψ (b * x) = 1) ↔ Valued.v b ≤ WithZero.exp (d - m) := by
  constructor
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    have hb0 : b ≠ 0 := by
      intro hb; rw [hb, Valuation.map_zero] at hlt; exact not_lt_of_ge zero_le' hlt
    have hvb : Valued.v b ≠ 0 := (Valuation.ne_zero_iff _).mpr hb0
    have hle : WithZero.exp (d - m + 1) ≤ Valued.v b := by
      rw [← WithZero.exp_log hvb] at hlt ⊢
      rw [WithZero.exp_lt_exp] at hlt
      rw [WithZero.exp_le_exp]
      omega
    have hx : b⁻¹ * t ∈ lat v m := by
      rw [mem_lat, Valuation.map_mul, map_inv₀]
      rw [mem_lat] at ht
      have h1 : Valued.v t ≤ Valued.v b * WithZero.exp m := by
        calc Valued.v t ≤ WithZero.exp (d + 1) := ht
          _ = WithZero.exp (d - m + 1) * WithZero.exp m := by
              rw [← WithZero.exp_add]; congr 1; ring
          _ ≤ Valued.v b * WithZero.exp m := mul_le_mul' hle le_rfl
      calc (Valued.v b)⁻¹ * Valued.v t ≤ (Valued.v b)⁻¹ * (Valued.v b * WithZero.exp m) :=
            mul_le_mul' le_rfl h1
        _ = WithZero.exp m := by rw [← mul_assoc, inv_mul_cancel₀ hvb, one_mul]
    have := h _ hx
    rw [← mul_assoc, mul_inv_cancel₀ hb0, one_mul] at this
    exact hψt this
  · intro hb x hx
    apply hd
    have := mul_mem_lat v hb hx
    rwa [sub_add_cancel] at this

end AddChar

section Measures

theorem measurableEmbedding_val : MeasurableEmbedding (Units.val : 𝕂ˣ → 𝕂) where
  injective := Units.val_injective
  measurable := comap_measurable Units.val
  measurableSet_image' := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    have : Units.val '' (Units.val ⁻¹' t) = t ∩ {x : 𝕂 | x ≠ 0} := by
      ext x
      constructor
      · rintro ⟨u, hu, rfl⟩; exact ⟨hu, u.ne_zero⟩
      · rintro ⟨hx, hx0⟩; exact ⟨Units.mk0 x hx0, hx, rfl⟩
    rw [this]
    exact ht.inter (measurableSet_singleton (0 : 𝕂)).compl

theorem sFinite_comap_val (ρ : Measure 𝕂) [SFinite ρ] :
    SFinite (Measure.comap Units.val ρ : Measure 𝕂ˣ) := by
  have hme := measurableEmbedding_val v
  refine ⟨⟨fun n => Measure.comap Units.val (sfiniteSeq ρ n), fun n => ⟨?_⟩, ?_⟩⟩
  · rw [hme.comap_apply]
    exact measure_lt_top _ _
  · ext s hs
    rw [Measure.sum_apply _ hs, hme.comap_apply]
    simp_rw [hme.comap_apply]
    rw [← Measure.sum_apply _ (hme.measurableSet_image' hs), sum_sfiniteSeq]

theorem isAddHaarMeasure_selfDualHaarAt : (selfDualHaarAt ℚ v).IsAddHaarMeasure := by
  set c : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0) ^
    (-(addCharLevel (NumberField.StandardAddChar.psiLocal ℚ v) : ℝ) / 2) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.rpow_pos (pos_iff_ne_zero.mpr (HeightOneSpectrum.absNorm_ne_zero v))).ne'
  have hdef : selfDualHaarAt ℚ v = c • Measure.addHaarMeasure (integersPositiveCompacts ℚ v) := rfl
  have h : selfDualHaarAt ℚ v = (c : ℝ≥0∞) • Measure.addHaarMeasure (integersPositiveCompacts ℚ v) := by
    rw [hdef]
    ext s _
    rw [Measure.coe_nnreal_smul_apply, Measure.smul_apply, smul_eq_mul]
  rw [h]
  exact Measure.IsAddHaarMeasure.smul _ (ENNReal.coe_ne_zero.mpr hc0) ENNReal.coe_ne_top

end Measures

section Unipotents

variable {v}

theorem continuous_upperUnipotent3_left :
    Continuous fun y : 𝕂 => (upperUnipotent3 y 0 0 : LocalGL3 v) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun y : 𝕂 => ((upperUnipotent3 y 0 0 : LocalGL3 v) : Matrix (Fin 3) (Fin 3) 𝕂)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3] <;> fun_prop
  · change Continuous fun y : 𝕂 => (upperUnipotent3 y 0 0 : LocalGL3 v).inv
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3] <;> fun_prop

theorem continuous_upperUnipotent3_right :
    Continuous fun z : 𝕂 => (upperUnipotent3 0 0 z : LocalGL3 v) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun z : 𝕂 => ((upperUnipotent3 0 0 z : LocalGL3 v) : Matrix (Fin 3) (Fin 3) 𝕂)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3] <;> fun_prop
  · change Continuous fun z : 𝕂 => (upperUnipotent3 0 0 z : LocalGL3 v).inv
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3] <;> fun_prop

theorem continuous_lowerUnipotent21 :
    Continuous fun x : 𝕂 => (lowerUnipotent21 x : LocalGL3 v) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun x : 𝕂 => ((lowerUnipotent21 x : LocalGL3 v) : Matrix (Fin 3) (Fin 3) 𝕂)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [lowerUnipotent21] <;> fun_prop
  · change Continuous fun x : 𝕂 => (lowerUnipotent21 x : LocalGL3 v).inv
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [lowerUnipotent21] <;> fun_prop

theorem continuous_transposeInv3 : Continuous fun g : LocalGL3 v => transposeInv3 g := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun g : LocalGL3 v => ((transposeInv3 g : LocalGL3 v) : Matrix (Fin 3) (Fin 3) 𝕂)
    simp_rw [transposeInv3_coe]
    exact Units.continuous_coe_inv.matrix_transpose
  · change Continuous fun g : LocalGL3 v => (((g : LocalGL3 v) : Matrix (Fin 3) (Fin 3) 𝕂))ᵀ
    exact Units.continuous_val.matrix_transpose

theorem exists_lat_conj_mem {f : 𝕂 → LocalGL3 v} (hf : Continuous f) (hf0 : f 0 = 1)
    {U : Subgroup (LocalGL3 v)} (hU : IsOpen (U : Set (LocalGL3 v))) (g : LocalGL3 v) :
    ∃ n : ℤ, ∀ y ∈ lat v n, g⁻¹ * f y * g ∈ U := by
  have hc : Continuous fun y : 𝕂 => g⁻¹ * f y * g :=
    (continuous_const.mul hf).mul continuous_const
  have hmem : (fun y : 𝕂 => g⁻¹ * f y * g) ⁻¹' (U : Set (LocalGL3 v)) ∈ 𝓝 (0 : 𝕂) := by
    refine (hU.preimage hc).mem_nhds ?_
    simp [hf0, U.one_mem]
  obtain ⟨n, hn⟩ := exists_ball_sub_of_mem_nhds v hmem
  refine ⟨n, fun y hy => hn y ?_⟩
  rw [sub_zero]; exact hy

variable {ψ : AddChar (HeightOneSpectrum.adicCompletion ℚ v) ℂ} {W : LocalGL3 v → ℂ}
  {U : Subgroup (LocalGL3 v)}

theorem exists_lat_psi_eq_one (hW : IsGL3PsiWhittakerFn ψ W) (hU : IsOpen (U : Set (LocalGL3 v)))
    (hUW : ∀ k ∈ U, ∀ g : LocalGL3 v, W (g * k) = W g) {g₀ : LocalGL3 v} (hg₀ : W g₀ ≠ 0) :
    ∃ n₀ : ℤ, ∀ y ∈ lat v n₀, ψ y = 1 := by
  obtain ⟨n, hn⟩ := exists_lat_conj_mem continuous_upperUnipotent3_left upperUnipotent3_zero hU g₀
  refine ⟨n, fun y hy => ?_⟩
  have h1 := hUW _ (hn y hy) g₀
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, hW, add_zero] at h1
  have : (ψ y - 1) * W g₀ = 0 := by rw [sub_mul, one_mul, h1, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hg₀

end Unipotents

end LTZeta31NV
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_exists_localZetaDual31_ne_zero_of_irreducible.LTZeta31NV"

open LanglandsTunnell.CubicInduction LTZeta31NV

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (W : LocalGL3 p → ℂ)
    (_hWlaw : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W)
    (_hWsm : ∃ Uv : Subgroup (LocalGL3 p), IsOpen (Uv : Set (LocalGL3 p)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 p, W (g * k) = W g)
    (_hWne : W ≠ 0)
    (_hWirr : ∀ W' ∈ gl3CyclicSubspace W, W' ≠ 0 → W ∈ gl3CyclicSubspace W')
    (η : (p.adicCompletion ℚ)ˣ →* ℂˣ) (cη : ℕ) (_hη : HasConductorExponentAt ℚ p η cη)
    (_hconv : ∀ g : LocalGL3 p,
      letI := localBorel ℚ p
      ∃ σ₁ : ℝ, IsLocalZeta31ConvergentAbove p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))
        (selfDualHaarAt ℚ p) (dualWhittakerFn3 W) η⁻¹ (weylPrime3 * transposeInv3 g) σ₁) :
    letI := localBorel ℚ p
    ∃ g : LocalGL3 p, ∀ σ : ℝ, ∃ t : ℝ, σ < t ∧
      localZetaDual31 p (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) (selfDualHaarAt ℚ p)
        W η (t : ℂ) g ≠ 0 := by
  classical
  obtain ⟨U, hUo, hUW⟩ := _hWsm

  set ψ₀ : AddChar (p.adicCompletion ℚ) ℂ := NumberField.StandardAddChar.psiLocal ℚ p with hψ₀def
  have hψ₀ : ψ₀ ≠ 1 := LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ p
  have hψc : Continuous ψ₀ := NumberField.StandardAddChar.continuous_psiLocal ℚ p

  set ν : Measure (p.adicCompletion ℚ) := selfDualHaarAt ℚ p with hν
  haveI : ν.IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt p
  haveI : SFinite (mulMeasure ν) := by unfold mulMeasure; infer_instance
  set μ : Measure (p.adicCompletion ℚ)ˣ := Measure.comap Units.val (mulMeasure ν) with hμ
  haveI : SFinite μ := sFinite_comap_val p (mulMeasure ν)

  set Wd : LocalGL3 p → ℂ := dualWhittakerFn3 W with hWd
  have hWdlaw : IsGL3PsiWhittakerFn ψ₀ Wd := isGL3PsiWhittakerFn_dualWhittakerFn3 _hWlaw
  set Ud : Subgroup (LocalGL3 p) := U.comap (tIHom : LocalGL3 p →* LocalGL3 p) with hUd
  have hUdo : IsOpen (Ud : Set (LocalGL3 p)) := hUo.preimage continuous_transposeInv3
  have hUdW : ∀ k ∈ Ud, ∀ g : LocalGL3 p, Wd (g * k) = Wd g := by
    intro k hk g
    show W (longWeyl3 * transposeInv3 (g * k)) = W (longWeyl3 * transposeInv3 g)
    rw [transposeInv3_mul, ← mul_assoc]
    exact hUW _ hk _
  have hWdne : Wd ≠ 0 := by
    intro h0
    apply _hWne
    funext g
    have := congr_fun h0 (transposeInv3 (longWeyl3⁻¹ * g))
    simp only [Pi.zero_apply] at this ⊢
    rw [← this]
    show W g = W (longWeyl3 * transposeInv3 (transposeInv3 (longWeyl3⁻¹ * g)))
    rw [transposeInv3_transposeInv3, mul_inv_cancel_left]
  set χ : (p.adicCompletion ℚ)ˣ →* ℂˣ := η⁻¹ with hχ

  have hsurj : ∀ h : LocalGL3 p, weylPrime3 * transposeInv3 (transposeInv3 (weylPrime3⁻¹ * h)) = h := by
    intro h
    rw [transposeInv3_transposeInv3, mul_inv_cancel_left]

  have hconv31 : ∀ h : LocalGL3 p, ∃ σ₁ : ℝ, IsLocalZeta31ConvergentAbove p μ ν Wd χ h σ₁ := by
    intro h
    obtain ⟨σ₁, hσ₁⟩ := _hconv (transposeInv3 (weylPrime3⁻¹ * h))
    rw [hsurj] at hσ₁
    exact ⟨σ₁, hσ₁⟩

  have hconv30 : ∀ h : LocalGL3 p, ∃ σ : ℝ, IsLocalZeta30ConvergentAbove p μ Wd χ h σ := by
    intro h
    obtain ⟨σ₁, hσ₁⟩ := hconv31 h
    obtain ⟨n₁, hn₁⟩ := exists_lat_conj_mem continuous_lowerUnipotent21 lowerUnipotent21_zero hUdo h
    refine ⟨σ₁, fun s hs => ?_⟩
    have hFs : Integrable (fun q : (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ =>
        Wd (iotaGL (diagUnitGL2 q.1) * lowerUnipotent21 q.2 * h) * ((χ q.1 : ℂˣ) : ℂ) *
          ((modulus (q.1 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) (μ.prod ν) := hσ₁ s hs
    have hae := hFs.prod_left_ae
    obtain ⟨x, hx, hxint⟩ : ∃ x ∈ lat p n₁, Integrable (fun a : (p.adicCompletion ℚ)ˣ =>
        Wd (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h) * ((χ a : ℂˣ) : ℂ) *
          ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) μ := by
      by_contra hno
      push Not at hno
      have h0 := ae_iff.mp hae
      have hsub : lat p n₁ ⊆ {x | ¬ Integrable (fun a : (p.adicCompletion ℚ)ˣ =>
          Wd (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h) * ((χ a : ℂˣ) : ℂ) *
            ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) μ} := fun x hx => hno x hx
      have hpos : 0 < ν (lat p n₁) := (isOpen_lat p n₁).measure_pos ν ⟨0, zero_mem_lat p n₁⟩
      exact absurd (measure_mono_null hsub h0) hpos.ne'
    have hpt : ∀ a : (p.adicCompletion ℚ)ˣ,
        Wd (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h) = Wd (iotaGL (diagUnitGL2 a) * h) := by
      intro a
      have : iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h =
          iotaGL (diagUnitGL2 a) * h * (h⁻¹ * lowerUnipotent21 x * h) := by group
      rw [this, hUdW _ (hn₁ x hx)]
    simpa only [hpt] using hxint

  obtain ⟨h₀, σ', -, hZ0⟩ :=
    exists_forall_localZeta30_selfDual_ne_zero_of_isGL3PsiWhittakerFn_of_ne_zero p ψ₀ hψ₀ Wd hWdlaw
      hWdne ⟨Ud, hUdo, hUdW⟩ χ hconv30

  by_contra hcon
  push Not at hcon
  have hvan : ∀ h : LocalGL3 p, ∃ σ : ℝ, ∀ t : ℝ, σ < t → localZeta31 p μ ν Wd χ (t : ℂ) h = 0 := by
    intro h
    obtain ⟨σ, hσ⟩ := hcon (transposeInv3 (weylPrime3⁻¹ * h))
    refine ⟨σ, fun t ht => ?_⟩
    have := hσ t ht
    simp only [localZetaDual31] at this
    rwa [hsurj] at this
  choose σv hσv using hvan

  obtain ⟨g₁, hg₁⟩ : ∃ g₁, Wd g₁ ≠ 0 := by
    by_contra h
    push Not at h
    exact hWdne (funext fun g => h g)
  obtain ⟨n₀, hn₀⟩ := exists_lat_psi_eq_one hWdlaw hUdo hUdW hg₁
  obtain ⟨d, hd, tψ, htψ, hψt⟩ := exists_level ψ₀ hψ₀ hn₀
  obtain ⟨nu, hnu⟩ := exists_lat_conj_mem continuous_lowerUnipotent21 lowerUnipotent21_zero hUdo h₀
  obtain ⟨nz, hnz⟩ := exists_lat_conj_mem continuous_upperUnipotent3_right upperUnipotent3_zero hUdo h₀
  set m : ℤ := d - nu with hm

  have hperpt : ∀ (z e : p.adicCompletion ℚ), e ∈ lat p nz → ∀ X : LocalGL3 p,
      Wd (X * (upperUnipotent3 0 0 (z + e) * h₀)) = Wd (X * (upperUnipotent3 0 0 z * h₀)) := by
    intro z e he X
    rw [upperUnipotent3_zero_zero_add]
    have : X * (upperUnipotent3 0 0 z * upperUnipotent3 0 0 e * h₀) =
        X * (upperUnipotent3 0 0 z * h₀) * (h₀⁻¹ * upperUnipotent3 0 0 e * h₀) := by group
    rw [this, hUdW _ (hnz e he)]
  have hper : ∀ (z e : p.adicCompletion ℚ), e ∈ lat p nz → ∀ s : ℂ,
      localZeta31 p μ ν Wd χ s (upperUnipotent3 0 0 (z + e) * h₀) =
        localZeta31 p μ ν Wd χ s (upperUnipotent3 0 0 z * h₀) := by
    intro z e he s
    simp only [localZeta31, hperpt z e he]

  obtain ⟨T, hT⟩ : ∃ T : ℝ, ∀ z ∈ lat p m, ∀ t : ℝ, T < t →
      localZeta31 p μ ν Wd χ (t : ℂ) (upperUnipotent3 0 0 z * h₀) = 0 := by
    have hcover : lat p m ⊆ ⋃ z : p.adicCompletion ℚ, {y : p.adicCompletion ℚ | y - z ∈ lat p nz} := by
      intro y _
      refine Set.mem_iUnion.mpr ⟨y, ?_⟩
      show y - y ∈ lat p nz
      rw [sub_self]; exact zero_mem_lat p nz
    obtain ⟨I, hI⟩ := (isCompact_lat p m).elim_finite_subcover
      (fun z : p.adicCompletion ℚ => {y : p.adicCompletion ℚ | y - z ∈ lat p nz})
      (fun z => isOpen_ball p z nz) hcover
    obtain ⟨T, hT⟩ := (I.image fun z => σv (upperUnipotent3 0 0 z * h₀)).bddAbove
    refine ⟨T, fun z hz t ht => ?_⟩
    have hz' := hI hz
    rw [Set.mem_iUnion₂] at hz'
    obtain ⟨zi, hziI, hzzi⟩ := hz'
    have hzzi' : z - zi ∈ lat p nz := hzzi
    have h1 : z = zi + (z - zi) := by ring
    rw [h1, hper zi (z - zi) hzzi']
    refine hσv _ t (lt_of_le_of_lt (hT ?_) ht)
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hziI)

  obtain ⟨σ₁, hσ₁⟩ := hconv31 h₀
  set t : ℝ := max (max T σ') σ₁ + 1 with htdef
  have htT : T < t := by
    have := le_max_left (max T σ') σ₁; have := le_max_left T σ'; linarith
  have htσ' : σ' < t := by
    have := le_max_left (max T σ') σ₁; have := le_max_right T σ'; linarith
  have htσ₁ : σ₁ < t := by
    have := le_max_right (max T σ') σ₁; linarith

  set Fq : (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ → ℂ := fun q =>
    Wd (iotaGL (diagUnitGL2 q.1) * lowerUnipotent21 q.2 * h₀) * ((χ q.1 : ℂˣ) : ℂ) *
      ((modulus (q.1 : p.adicCompletion ℚ) : ℝ) : ℂ) ^ ((t : ℂ) - 1) with hFq
  have hF : Integrable Fq (μ.prod ν) := hσ₁ (t : ℂ) (by simpa using htσ₁)

  set νm : Measure (p.adicCompletion ℚ) := ν.restrict (lat p m) with hνm
  haveI : IsFiniteMeasure νm := isFiniteMeasure_restrict.mpr (isCompact_lat p m).measure_lt_top.ne
  set H : p.adicCompletion ℚ × ((p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ) → ℂ :=
    fun r => ψ₀ (r.2.2 * r.1) * Fq r.2 with hH
  have hHint : Integrable H (νm.prod (μ.prod ν)) := by
    have hae : AEStronglyMeasurable H (νm.prod (μ.prod ν)) := by
      have hg : Continuous fun w : p.adicCompletion ℚ × p.adicCompletion ℚ => ψ₀ (w.2 * w.1) :=
        hψc.comp (continuous_snd.mul continuous_fst)
      have h1 : AEStronglyMeasurable
          (fun r : p.adicCompletion ℚ × ((p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ) => ψ₀ (r.2.2 * r.1))
          (νm.prod (μ.prod ν)) :=
        (hg.stronglyMeasurable.comp_measurable (measurable_fst.prodMk measurable_snd.snd)).aestronglyMeasurable
      exact h1.mul hF.1.comp_snd
    have hbound : Integrable
        (fun r : p.adicCompletion ℚ × ((p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ) => (1 : ℝ) * ‖Fq r.2‖)
        (νm.prod (μ.prod ν)) :=
      (integrable_const (1 : ℝ)).mul_prod hF.norm
    refine hbound.mono' hae (Filter.Eventually.of_forall fun r => ?_)
    show ‖ψ₀ (r.2.2 * r.1) * Fq r.2‖ ≤ 1 * ‖Fq r.2‖
    rw [norm_mul, norm_apply_eq_one ψ₀ hψc, one_mul]

  have hL : ∫ r, H r ∂(νm.prod (μ.prod ν)) = 0 := by
    rw [integral_prod H hHint]
    show ∫ z in lat p m, (∫ q, H (z, q) ∂(μ.prod ν)) ∂ν = 0
    refine setIntegral_eq_zero_of_forall_eq_zero fun z hz => ?_
    have hmz : AEStronglyMeasurable
        (fun q : (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ => ψ₀ (q.2 * z)) (μ.prod ν) :=
      ((hψc.comp (continuous_id.mul continuous_const)).stronglyMeasurable.comp_measurable
        measurable_snd).aestronglyMeasurable
    have hHz : Integrable (fun q : (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ => H (z, q)) (μ.prod ν) := by
      show Integrable (fun q : (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ => ψ₀ (q.2 * z) * Fq q) (μ.prod ν)
      exact hF.bdd_mul hmz (ae_of_all _ fun q => (norm_apply_eq_one ψ₀ hψc _).le)
    rw [integral_prod _ hHz]
    have h31 := hT z hz t htT
    simp only [localZeta31] at h31
    rw [← h31]
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    show ∫ x, ψ₀ (x * z) * Fq (a, x) ∂ν =
      (∫ x, Wd (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (upperUnipotent3 0 0 z * h₀)) ∂ν) *
        ((χ a : ℂˣ) : ℂ) * ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ ((t : ℂ) - 1)
    rw [← integral_mul_const, ← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show ψ₀ (x * z) * Fq (a, x) = _
    simp only [hFq]
    rw [apply_iotaDiag_lower_upper hWdlaw]
    ring

  have hmeasS : MeasurableSet {q : (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ | q.2 ∈ lat p nu} :=
    measurable_snd (measurableSet_lat p nu)
  have hR : ∫ r, H r ∂(νm.prod (μ.prod ν)) =
      (ν.real (lat p m) : ℂ) * ((ν.real (lat p nu) : ℂ) * localZeta30 p μ Wd χ (t : ℂ) h₀) := by
    rw [integral_prod_symm H hHint]
    have hinner : ∀ q : (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ, ∫ z, H (z, q) ∂νm =
        (ν.real (lat p m) : ℂ) *
          {q : (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ | q.2 ∈ lat p nu}.indicator Fq q := by
      intro q
      show ∫ z in lat p m, ψ₀ (q.2 * z) * Fq q ∂ν = _
      rw [integral_mul_const]
      by_cases hq : q.2 ∈ lat p nu
      · have hall : ∀ z ∈ lat p m, ψ₀ (q.2 * z) = 1 := by
          refine (forall_lat_char_eq_one_iff ψ₀ hd htψ hψt m q.2).mpr ?_
          have : d - m = nu := by rw [hm]; ring
          rw [this]; exact hq
        have hq' : q ∈ {q : (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ | q.2 ∈ lat p nu} := hq
        rw [setIntegral_lat_char_of_forall_eq_one ψ₀ ν hall, Set.indicator_of_mem hq']
      · have hex : ∃ z₀ ∈ lat p m, ψ₀ (q.2 * z₀) ≠ 1 := by
          by_contra hno
          push Not at hno
          apply hq
          have := (forall_lat_char_eq_one_iff ψ₀ hd htψ hψt m q.2).mp hno
          have h' : d - m = nu := by rw [hm]; ring
          rw [h'] at this; exact this
        obtain ⟨z₀, hz₀, hne⟩ := hex
        have hq' : q ∉ {q : (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ | q.2 ∈ lat p nu} := hq
        rw [setIntegral_lat_char_eq_zero ψ₀ ν hz₀ hne, Set.indicator_of_notMem hq', mul_zero, zero_mul]
    rw [integral_congr_ae (ae_of_all _ hinner), integral_const_mul, integral_prod _ (hF.indicator hmeasS)]
    congr 1
    rw [show localZeta30 p μ Wd χ (t : ℂ) h₀ = ∫ a, Wd (iotaGL (diagUnitGL2 a) * h₀) * ((χ a : ℂˣ) : ℂ) *
        ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ ((t : ℂ) - 1) ∂μ from rfl, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    show ∫ x, {q : (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ | q.2 ∈ lat p nu}.indicator Fq (a, x) ∂ν = _
    have hfun : (fun x => {q : (p.adicCompletion ℚ)ˣ × p.adicCompletion ℚ | q.2 ∈ lat p nu}.indicator Fq (a, x)) =
        (lat p nu).indicator (fun x => Fq (a, x)) := by
      funext x
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
    rw [hfun, integral_indicator (measurableSet_lat p nu)]
    have hEq : Set.EqOn (fun x => Fq (a, x))
        (fun _ => Wd (iotaGL (diagUnitGL2 a) * h₀) * ((χ a : ℂˣ) : ℂ) *
          ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ ((t : ℂ) - 1)) (lat p nu) := by
      intro x hx
      show Fq (a, x) = _
      rw [hFq]
      show Wd (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h₀) * ((χ a : ℂˣ) : ℂ) *
          ((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ ((t : ℂ) - 1) = _
      have : iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * h₀ =
          iotaGL (diagUnitGL2 a) * h₀ * (h₀⁻¹ * lowerUnipotent21 x * h₀) := by group
      rw [this, hUdW _ (hnu x hx)]
    rw [setIntegral_congr_fun (measurableSet_lat p nu) hEq, setIntegral_const, Complex.real_smul]

  have hm0 : (ν.real (lat p m) : ℂ) ≠ 0 := by
    have : 0 < ν.real (lat p m) :=
      ENNReal.toReal_pos ((isOpen_lat p m).measure_pos ν ⟨0, zero_mem_lat p m⟩).ne'
        (isCompact_lat p m).measure_lt_top.ne
    exact_mod_cast this.ne'
  have hnu0 : (ν.real (lat p nu) : ℂ) ≠ 0 := by
    have : 0 < ν.real (lat p nu) :=
      ENNReal.toReal_pos ((isOpen_lat p nu).measure_pos ν ⟨0, zero_mem_lat p nu⟩).ne'
        (isCompact_lat p nu).measure_lt_top.ne
    exact_mod_cast this.ne'
  have hzero : localZeta30 p μ Wd χ (t : ℂ) h₀ = 0 := by
    have h := hR.symm.trans hL
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 hm0
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 hnu0
    · exact h2
  exact hZ0 (t : ℂ) (by simpa using htσ') hzero

end
end S_LanglandsTunnell_CubicInduction_exists_forall_exists_localZetaDual31_ne_zero_of_irreducible
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_exists_localZetaDual31_ne_zero_of_irreducible (solution)
