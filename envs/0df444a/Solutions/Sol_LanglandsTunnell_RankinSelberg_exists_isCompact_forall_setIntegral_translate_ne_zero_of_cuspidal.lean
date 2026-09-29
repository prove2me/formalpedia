-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_isCompact_forall_setIntegral_translate_ne_zero_of_cuspidal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/5b956641-32a5-59c3-baf1-902ae16b6c9c

import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Theorems.Thm_AutomorphicForm_WhittakerModel_forall_mem_span_sub_unipotent_of_forall_diagOne_eq_zero_of_irreducible_of_admissible
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_translate_eq_mul_sum_linearMap_of_admissible
import Theorems.Thm_Matrix_GeneralLinearGroup_exists_eq_mul_diagonal_natCast_pow_mul_of_forall_mem_adicCompletionIntegers
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_isCompact_forall_setIntegral_translate_ne_zero_of_cuspidal
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction UnramifiedWhittaker
open NumberField.AdelicLevel (diagOne)
open scoped Classical

noncomputable section

namespace CuspCoeff

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (p.adicCompletion ℚ)
local notation "G" => (GL (Fin 2) (p.adicCompletion ℚ))
local notation "M2" => (Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))

abbrev V (w₂base : G → ℂ) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ (Set.range fun h : G => fun g : G => w₂base (g * h))

abbrev VN (w₂base : G → ℂ) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ {D : G → ℂ | ∃ W' ∈ V p w₂base, ∃ t : F, D = fun g : G => W' (g * unipotent t) - W' g}

section Generic
variable {H : Type*} [Group H]

theorem translate_mem_span (f : H → ℂ) (h : H) {W : H → ℂ}
    (hW : W ∈ Submodule.span ℂ (Set.range fun h' : H => fun g : H => f (g * h'))) :
    (fun g : H => W (g * h)) ∈ Submodule.span ℂ (Set.range fun h' : H => fun g : H => f (g * h')) := by
  induction hW using Submodule.span_induction with
  | mem W hWm =>
      obtain ⟨h', rfl⟩ := hWm
      exact Submodule.subset_span ⟨h * h', funext fun g => by simp only [mul_assoc]⟩
  | zero => exact Submodule.zero_mem _
  | add W₁ W₂ _ _ h₁ h₂ =>
      have : (fun g : H => (W₁ + W₂) (g * h)) = (fun g : H => W₁ (g * h)) + fun g : H => W₂ (g * h) := rfl
      rw [this]; exact Submodule.add_mem _ h₁ h₂
  | smul a W _ h₁ =>
      have : (fun g : H => (a • W) (g * h)) = a • fun g : H => W (g * h) := rfl
      rw [this]; exact Submodule.smul_mem _ a h₁

theorem law_of_mem_span (f : H → ℂ) (a : H) (χ : ℂ) (hf : ∀ g : H, f (a * g) = χ * f g) {W : H → ℂ}
    (hW : W ∈ Submodule.span ℂ (Set.range fun h' : H => fun g : H => f (g * h'))) :
    ∀ g : H, W (a * g) = χ * W g := by
  induction hW using Submodule.span_induction with
  | mem W hWm =>
      obtain ⟨h', rfl⟩ := hWm
      intro g
      show f (a * g * h') = χ * f (g * h')
      rw [mul_assoc, hf]
  | zero => intro g; simp
  | add W₁ W₂ _ _ h₁ h₂ => intro g; simp only [Pi.add_apply, h₁ g, h₂ g]; ring
  | smul c W _ h₁ => intro g; simp only [Pi.smul_apply, smul_eq_mul, h₁ g]; ring

variable [TopologicalSpace H] [ContinuousMul H]

theorem exists_open_stabilizer_of_mem_span (f : H → ℂ) (K : Subgroup H) (hK : IsOpen (K : Set H))
    (hf : ∀ k ∈ K, ∀ g : H, f (g * k) = f g) {W : H → ℂ}
    (hW : W ∈ Submodule.span ℂ (Set.range fun h' : H => fun g : H => f (g * h'))) :
    ∃ U : Subgroup H, IsOpen (U : Set H) ∧ ∀ k ∈ U, ∀ g : H, W (g * k) = W g := by
  induction hW using Submodule.span_induction with
  | mem W hWm =>
      obtain ⟨h, rfl⟩ := hWm
      refine ⟨K.comap (MulAut.conj h⁻¹).toMonoidHom, ?_, ?_⟩
      · have hc : Continuous fun k : H => h⁻¹ * k * h⁻¹⁻¹ :=
          (continuous_const.mul continuous_id).mul continuous_const
        have hset : ((K.comap (MulAut.conj h⁻¹).toMonoidHom : Subgroup H) : Set H) =
            (fun k : H => h⁻¹ * k * h⁻¹⁻¹) ⁻¹' (K : Set H) := by
          ext k
          simp only [Subgroup.coe_comap, Set.mem_preimage, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
            SetLike.mem_coe]
        rw [hset]
        exact hK.preimage hc
      · intro k hk g
        have hk' : h⁻¹ * k * h⁻¹⁻¹ ∈ K := by
          simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hk
        show f (g * k * h) = f (g * h)
        have := hf _ hk' (g * h)
        rw [inv_inv] at this
        calc f (g * k * h) = f (g * h * (h⁻¹ * k * h)) := by group
          _ = f (g * h) := this
  | zero => exact ⟨⊤, isOpen_univ, fun _ _ _ => rfl⟩
  | add W₁ W₂ _ _ h₁ h₂ =>
      obtain ⟨U₁, hU₁, h₁⟩ := h₁
      obtain ⟨U₂, hU₂, h₂⟩ := h₂
      exact ⟨U₁ ⊓ U₂, hU₁.inter hU₂, fun k hk g => by
        simp only [Pi.add_apply, h₁ k hk.1 g, h₂ k hk.2 g]⟩
  | smul c W _ h₁ =>
      obtain ⟨U₁, hU₁, h₁⟩ := h₁
      exact ⟨U₁, hU₁, fun k hk g => by simp only [Pi.smul_apply, h₁ k hk g]⟩

end Generic

def rho (h : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun v := fun g => v (g * h)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rho_apply (h : G) (v : G → ℂ) (g : G) : rho p h v g = v (g * h) := rfl

theorem rho_mul (a b : G) (v : G → ℂ) : rho p (a * b) v = rho p a (rho p b v) := by
  funext g; simp only [rho_apply, mul_assoc]

theorem rho_one (v : G → ℂ) : rho p 1 v = v := by
  funext g; simp only [rho_apply, mul_one]

theorem rho_mem (w₂base : G → ℂ) (h : G) {v : G → ℂ} (hv : v ∈ V p w₂base) : rho p h v ∈ V p w₂base :=
  translate_mem_span w₂base h hv

def qR : ℝ := ((Ideal.absNorm p.asIdeal : NNReal) : ℝ)

theorem one_lt_qR : 1 < qR p := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p
  unfold qR; exact_mod_cast this

theorem norm_eq_qR_zpow (y : F) (j : ℤ) (hy : Valued.v y = WithZero.exp (-j)) : ‖y‖ = qR p ^ (-j) := by
  rw [NumberField.FinitePlace.norm_def, hy, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, NNReal.coe_zpow]
  unfold qR
  congr 1

theorem norm_eq_qR_zpow_log {y : F} (hy : Valued.v y ≠ 0) : ‖y‖ = qR p ^ (WithZero.log (Valued.v y)) := by
  have h := norm_eq_qR_zpow p y (-WithZero.log (Valued.v y)) (by rw [neg_neg, WithZero.exp_log hy])
  rw [h, neg_neg]

theorem valued_natCast_lt_one {ℓ : ℕ} (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ p.asIdeal) : Valued.v ((ℓ : ℕ) : F) < 1 := by
  have h1 : ((ℓ : ℕ) : F) = algebraMap ℚ F (algebraMap (𝓞 ℚ) ℚ ((ℓ : ℕ) : 𝓞 ℚ)) := by simp only [map_natCast]
  rw [h1, NumberField.AdelicLevel.valued_algebraMap]
  exact (IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem p _).mpr hv

theorem valued_natCast_le {ℓ : ℕ} (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ p.asIdeal) :
    Valued.v ((ℓ : ℕ) : F) ≤ WithZero.exp (-1 : ℤ) := by
  have h := valued_natCast_lt_one p hv
  by_cases hx : Valued.v ((ℓ : ℕ) : F) = 0
  · rw [hx]; exact zero_le'
  · rw [← WithZero.exp_log hx, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [← WithZero.exp_log hx, WithZero.exp_le_exp]
    omega

theorem exists_forall_le_valued_pow_mul_le_one {L : F} (hL : Valued.v L ≤ WithZero.exp (-1 : ℤ)) (x : F) :
    ∃ r : ℕ, ∀ r' : ℕ, r ≤ r' → Valued.v (L ^ r' * x) ≤ 1 := by
  by_cases hx : Valued.v x = 0
  · exact ⟨0, fun r' _ => by rw [Valuation.map_mul, hx, mul_zero]; exact zero_le'⟩
  · set e : ℤ := WithZero.log (Valued.v x) with he
    have hxe : Valued.v x = WithZero.exp e := (WithZero.exp_log hx).symm
    have key : ∀ r' : ℕ, Valued.v (L ^ r' * x) ≤ WithZero.exp (e - r') := by
      intro r'
      induction r' with
      | zero => simp [hxe]
      | succ n ih =>
          rw [pow_succ', mul_assoc, Valuation.map_mul]
          calc Valued.v L * Valued.v (L ^ n * x) ≤ WithZero.exp (-1 : ℤ) * WithZero.exp (e - n) := mul_le_mul' hL ih
            _ = WithZero.exp (e - (n + 1 : ℕ)) := by rw [← WithZero.exp_add]; congr 1; push_cast; ring
    refine ⟨e.toNat, fun r' hr' => (key r').trans ?_⟩
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    have : e ≤ (r' : ℤ) := le_trans (Int.self_le_toNat e) (by exact_mod_cast hr')
    omega

theorem mem_K0_of_integral (k : G)
    (h1 : ∀ i j, (k : M2) i j ∈ p.adicCompletionIntegers ℚ)
    (h2 : ∀ i j, ((k⁻¹ : G) : M2) i j ∈ p.adicCompletionIntegers ℚ) :
    k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ := by
  have key : ∀ m : M2, (∀ i j, m i j ∈ p.adicCompletionIntegers ℚ) → AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ p ⊤ m := by
    intro m hm
    refine ⟨hm, ?_, ?_⟩
    · rw [NumberField.AdelicLevel.idealBound_top]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).mp (hm 1 0)
    · rw [NumberField.AdelicLevel.idealBound_top]
      refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
      · exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).mp (hm 1 1)
      · rw [Valuation.map_one]
  rw [AdelicDock.mem_localLevelOne_iff]
  exact ⟨key _ h1, key _ h2⟩

theorem scalar_coe' (u : Fˣ) : ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : G) : M2) = (u : F) • (1 : M2) := by
  show Matrix.scalar (Fin 2) (u : F) = _
  rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul, mul_one]

theorem exists_prime_natCast_mem_asIdeal : ∃ ℓ : ℕ, ℓ.Prime ∧ ((ℓ : ℕ) : 𝓞 ℚ) ∈ p.asIdeal := by
  haveI : p.asIdeal.IsPrime := p.isPrime
  haveI : Finite (𝓞 ℚ ⧸ p.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot p.asIdeal p.ne_bot
  haveI : IsDomain (𝓞 ℚ ⧸ p.asIdeal) := Ideal.Quotient.isDomain p.asIdeal
  obtain ⟨ℓ, hℓ⟩ := CharP.exists (𝓞 ℚ ⧸ p.asIdeal)
  refine ⟨ℓ, CharP.char_is_prime (𝓞 ℚ ⧸ p.asIdeal) ℓ, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact CharP.cast_eq_zero _ ℓ

scoped instance charZero_F : CharZero (p.adicCompletion ℚ) :=
  charZero_of_injective_algebraMap (algebraMap ℚ (p.adicCompletion ℚ)).injective

theorem natCast_ne_zero {ℓ : ℕ} (hℓ : ℓ.Prime) : ((ℓ : ℕ) : F) ≠ 0 :=
  Nat.cast_ne_zero.2 hℓ.ne_zero

theorem norm_natCast_lt_one {ℓ : ℕ} (hℓ : ℓ.Prime) (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ p.asIdeal) : ‖((ℓ : ℕ) : F)‖ < 1 := by
  have hval := valued_natCast_lt_one p hv
  have h0 : Valued.v ((ℓ : ℕ) : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr (natCast_ne_zero p hℓ)
  rw [norm_eq_qR_zpow_log p h0, ← zpow_zero (qR p), zpow_lt_zpow_iff_right₀ (one_lt_qR p)]
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hval
  exact hval

def w0 : G := ⟨!![0, 1; 1, 0], !![0, 1; 1, 0],
  by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
  by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem diagZ_mul_unipotent (π : F) (hπ : π ≠ 0) (m : ℤ) (t : F) :
    diagZ π hπ m * unipotent t = unipotent (π ^ m * t) * diagZ π hπ m := by
  apply Units.ext
  change (!![π ^ m, 0; 0, 1] : M2) * !![1, t; 0, 1] = !![1, π ^ m * t; 0, 1] * !![π ^ m, 0; 0, 1]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagZ_eq_scalar_mul_conj (π : F) (hπ : π ≠ 0) (m : ℤ) :
    diagZ π hπ m = Matrix.GeneralLinearGroup.scalar (Fin 2) ((Units.mk0 π hπ) ^ m) * (w0 p * diagZ π hπ (-m) * (w0 p)⁻¹) := by
  apply Units.ext
  have hw : (((w0 p)⁻¹ : G) : M2) = !![0, 1; 1, 0] := rfl
  rw [Units.val_mul, Units.val_mul, Units.val_mul, hw]
  change (!![π ^ m, 0; 0, 1] : M2) = Matrix.scalar (Fin 2) (((Units.mk0 π hπ) ^ m : Fˣ) : F) * (!![0, 1; 1, 0] * !![π ^ (-m), 0; 0, 1] * !![0, 1; 1, 0])
  rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar, zpow_neg, hπ, zpow_ne_zero]

theorem unipotent_coe (x : F) : ((unipotent x : G) : M2) = !![1, x; 0, 1] := rfl

theorem unipotent_zero : (unipotent (0 : F) : G) = 1 := by
  apply Units.ext
  rw [unipotent_coe, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem unipotent_mul_unipotent_neg (x : F) : (unipotent x : G) * unipotent (-x) = 1 := by
  apply Units.ext
  rw [Units.val_mul, unipotent_coe, unipotent_coe, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem unipotent_inv (x : F) : (unipotent x : G)⁻¹ = unipotent (-x) :=
  inv_eq_of_mul_eq_one_right (unipotent_mul_unipotent_neg p x)

theorem continuous_unipotent : Continuous fun x : F => (unipotent x : G) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun x : F => ((unipotent x : G) : M2)
    simp only [unipotent_coe]
    refine continuous_matrix ?_
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun x : F => (((unipotent x : G)⁻¹ : G) : M2)
    simp only [unipotent_inv, unipotent_coe]
    refine continuous_matrix ?_
    intro i j; fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem scalar_mul_comm (z : Fˣ) (g : G) :
    g * Matrix.GeneralLinearGroup.scalar (Fin 2) z = Matrix.GeneralLinearGroup.scalar (Fin 2) z * g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  show (g : M2) * Matrix.scalar (Fin 2) (z : F) = Matrix.scalar (Fin 2) (z : F) * (g : M2)
  exact (Matrix.scalar_commute (z : F) (fun _ => Commute.all _ _) (g : M2)).symm.eq

theorem rho_scalar_of_mem (θ₀ : Fˣ →* ℂˣ) (w₂base : G → ℂ)
    (hcentral : ∀ (z : Fˣ) (g : G), w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (z : Fˣ) {v : G → ℂ} (hv : v ∈ V p w₂base) :
    rho p (Matrix.GeneralLinearGroup.scalar (Fin 2) z) v = (((θ₀ z : ℂˣ) : ℂ)) • v := by
  funext g
  rw [rho_apply, scalar_mul_comm, Pi.smul_apply, smul_eq_mul]
  exact law_of_mem_span w₂base _ _ (hcentral z) hv g

theorem decay_pos (w₂base : G → ℂ) (U : Subgroup G) (hU : IsOpen (U : Set G)) (L : (G → ℂ) →ₗ[ℂ] ℂ)
    (hL : ∀ k ∈ U, ∀ v ∈ V p w₂base, L (rho p k v) = L v)
    (π : F) (hπ : π ≠ 0) (hπ1 : ‖π‖ < 1)
    (v : G → ℂ) (hv : v ∈ VN p w₂base) :
    ∃ M : ℕ, ∀ n : ℕ, M ≤ n → L (rho p (diagZ π hπ (n : ℤ)) v) = 0 := by
  induction hv using Submodule.span_induction with
  | mem D hD =>
      obtain ⟨W', hW', t, rfl⟩ := hD
      have htend : Filter.Tendsto (fun n : ℕ => (unipotent (π ^ n * t) : G)) Filter.atTop (nhds 1) := by
        have h0 : Filter.Tendsto (fun n : ℕ => π ^ n * t) Filter.atTop (nhds 0) := by
          have := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hπ1).mul_const t
          simpa only [zero_mul] using this
        rw [← unipotent_zero p]
        exact ((continuous_unipotent p).tendsto 0).comp h0
      obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 (htend (hU.mem_nhds U.one_mem))
      refine ⟨M, fun n hn => ?_⟩
      have hmem : (unipotent (π ^ n * t) : G) ∈ U := hM n hn
      have hX : rho p (diagZ π hπ (n : ℤ)) W' ∈ V p w₂base := rho_mem p w₂base _ hW'
      have key : rho p (diagZ π hπ (n : ℤ)) (fun g : G => W' (g * unipotent t) - W' g) =
          rho p (unipotent (π ^ n * t)) (rho p (diagZ π hπ (n : ℤ)) W') - rho p (diagZ π hπ (n : ℤ)) W' := by
        funext g
        simp only [rho_apply, Pi.sub_apply, mul_assoc, diagZ_mul_unipotent, zpow_natCast]
      rw [key, map_sub, hL _ hmem _ hX, sub_self]
  | zero => exact ⟨0, fun n _ => by rw [map_zero, map_zero]⟩
  | add v₁ v₂ _ _ h₁ h₂ =>
      obtain ⟨M₁, h₁⟩ := h₁
      obtain ⟨M₂, h₂⟩ := h₂
      exact ⟨max M₁ M₂, fun n hn => by
        rw [map_add, map_add, h₁ n (le_of_max_le_left hn), h₂ n (le_of_max_le_right hn), add_zero]⟩
  | smul c v _ h₁ =>
      obtain ⟨M₁, h₁⟩ := h₁
      exact ⟨M₁, fun n hn => by rw [map_smul, map_smul, h₁ n hn, smul_zero]⟩

theorem decay_neg (θ₀ : Fˣ →* ℂˣ) (w₂base : G → ℂ)
    (hcentral : ∀ (z : Fˣ) (g : G), w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (hVN : ∀ W ∈ V p w₂base, W ∈ VN p w₂base)
    (U : Subgroup G) (hU : IsOpen (U : Set G)) (L : (G → ℂ) →ₗ[ℂ] ℂ)
    (hL : ∀ k ∈ U, ∀ v ∈ V p w₂base, L (rho p k v) = L v)
    (π : F) (hπ : π ≠ 0) (hπ1 : ‖π‖ < 1)
    (v : G → ℂ) (hv : v ∈ V p w₂base) :
    ∃ M : ℕ, ∀ n : ℕ, M ≤ n → L (rho p (diagZ π hπ (-(n : ℤ))) v) = 0 := by

  set U' : Subgroup G := U.comap (MulAut.conj (w0 p)).toMonoidHom with hU'def
  have hU' : IsOpen (U' : Set G) := by
    have hc : Continuous fun k : G => w0 p * k * (w0 p)⁻¹ := (continuous_const.mul continuous_id).mul continuous_const
    have hset : (U' : Set G) = (fun k : G => w0 p * k * (w0 p)⁻¹) ⁻¹' (U : Set G) := by
      ext k
      simp only [hU'def, Subgroup.coe_comap, Set.mem_preimage, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, SetLike.mem_coe]
    rw [hset]; exact hU.preimage hc
  set L' : (G → ℂ) →ₗ[ℂ] ℂ := L.comp (rho p (w0 p)) with hL'def
  have hL' : ∀ k ∈ U', ∀ u ∈ V p w₂base, L' (rho p k u) = L' u := by
    intro k hk u hu
    have hk' : w0 p * k * (w0 p)⁻¹ ∈ U := by
      simpa only [hU'def, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hk
    show L (rho p (w0 p) (rho p k u)) = L (rho p (w0 p) u)
    rw [← rho_mul, show w0 p * k = (w0 p * k * (w0 p)⁻¹) * w0 p by group, rho_mul]
    exact hL _ hk' _ (rho_mem p w₂base _ hu)
  have hv' : rho p (w0 p)⁻¹ v ∈ VN p w₂base := hVN _ (rho_mem p w₂base _ hv)
  obtain ⟨M, hM⟩ := decay_pos p w₂base U' hU' L' hL' π hπ hπ1 _ hv'
  refine ⟨M, fun n hn => ?_⟩
  have hflip := diagZ_eq_scalar_mul_conj p π hπ (-(n : ℤ))
  rw [neg_neg] at hflip
  have hXmem : rho p (w0 p) (rho p (diagZ π hπ (n : ℤ)) (rho p (w0 p)⁻¹ v)) ∈ V p w₂base :=
    rho_mem p w₂base _ (rho_mem p w₂base _ (rho_mem p w₂base _ hv))
  rw [hflip, rho_mul, rho_mul, rho_mul, rho_scalar_of_mem p θ₀ w₂base hcentral _ hXmem, map_smul]
  have h0 : L (rho p (w0 p) (rho p (diagZ π hπ (n : ℤ)) (rho p (w0 p)⁻¹ v))) = 0 := by
    have := hM n hn
    simpa only [hL'def, LinearMap.comp_apply] using this
  rw [h0, smul_zero]

theorem exists_finset_mul_inv_mem (K : Set G) (hK : IsCompact K) (U : Subgroup G) (hU : IsOpen (U : Set G)) :
    ∃ R : Finset G, (↑R : Set G) ⊆ K ∧ ∀ k ∈ K, ∃ r ∈ R, k * r⁻¹ ∈ U := by
  let O : K → Set G := fun r => (fun g : G => g * ((r : G))⁻¹) ⁻¹' (U : Set G)
  have hO : ∀ r, IsOpen (O r) := fun r => hU.preimage (continuous_id.mul continuous_const)
  have hcov : K ⊆ ⋃ r, O r := by
    intro k hk
    refine Set.mem_iUnion.mpr ⟨⟨k, hk⟩, ?_⟩
    show k * k⁻¹ ∈ (U : Set G)
    rw [mul_inv_cancel]; exact U.one_mem
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover O hO hcov
  refine ⟨t.image Subtype.val, ?_, fun k hk => ?_⟩
  · intro r hr
    obtain ⟨r', -, rfl⟩ := Finset.mem_image.mp hr
    exact r'.2
  · obtain ⟨r, hrt, hkr⟩ := Set.mem_iUnion₂.mp (ht hk)
    exact ⟨r, Finset.mem_image.mpr ⟨r, hrt, rfl⟩, hkr⟩

theorem exists_finset_inv_mul_mem (K : Set G) (hK : IsCompact K) (U : Subgroup G) (hU : IsOpen (U : Set G)) :
    ∃ R : Finset G, (↑R : Set G) ⊆ K ∧ ∀ k ∈ K, ∃ r ∈ R, r⁻¹ * k ∈ U := by
  let O : K → Set G := fun r => (fun g : G => ((r : G))⁻¹ * g) ⁻¹' (U : Set G)
  have hO : ∀ r, IsOpen (O r) := fun r => hU.preimage (continuous_const.mul continuous_id)
  have hcov : K ⊆ ⋃ r, O r := by
    intro k hk
    refine Set.mem_iUnion.mpr ⟨⟨k, hk⟩, ?_⟩
    show k⁻¹ * k ∈ (U : Set G)
    rw [inv_mul_cancel]; exact U.one_mem
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover O hO hcov
  refine ⟨t.image Subtype.val, ?_, fun k hk => ?_⟩
  · intro r hr
    obtain ⟨r', -, rfl⟩ := Finset.mem_image.mp hr
    exact r'.2
  · obtain ⟨r, hrt, hkr⟩ := Set.mem_iUnion₂.mp (ht hk)
    exact ⟨r, Finset.mem_image.mpr ⟨r, hrt, rfl⟩, hkr⟩

set_option synthInstance.maxHeartbeats 1600000 in
theorem exists_scalar_mul_eq_cartan {ℓ : ℕ} (hℓ : ℓ.Prime) (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ p.asIdeal) (g : G) :
    ∃ (z : Fˣ) (k₁ k₂ : G) (m : ℤ), k₁ ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ ∧ k₂ ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ ∧
      Matrix.GeneralLinearGroup.scalar (Fin 2) z * g = k₁ * diagZ ((ℓ : ℕ) : F) (natCast_ne_zero p hℓ) m * k₂ := by
  have hL0 : ((ℓ : ℕ) : F) ≠ 0 := natCast_ne_zero p hℓ
  have hvL := valued_natCast_le p hv

  have hent : ∀ i j : Fin 2, ∃ r : ℕ, ∀ r' : ℕ, r ≤ r' → Valued.v (((ℓ : ℕ) : F) ^ r' * (g : M2) i j) ≤ 1 :=
    fun i j => exists_forall_le_valued_pow_mul_le_one p hvL _
  choose rf hrf using hent
  obtain ⟨r, hr_ge⟩ : ∃ r : ℕ, ∀ i j : Fin 2, rf i j ≤ r :=
    ⟨rf 0 0 + rf 0 1 + rf 1 0 + rf 1 1, fun i j => by
      fin_cases i <;> fin_cases j
      · exact Nat.le_add_right_of_le (Nat.le_add_right_of_le (Nat.le_add_right _ _))
      · exact Nat.le_add_right_of_le (Nat.le_add_right_of_le (Nat.le_add_left _ _))
      · exact Nat.le_add_right_of_le (Nat.le_add_left _ _)
      · exact Nat.le_add_left _ _⟩
  set Lu : Fˣ := Units.mk0 ((ℓ : ℕ) : F) hL0 with hLu
  set Y : G := Matrix.GeneralLinearGroup.scalar (Fin 2) (Lu ^ r) * g with hY
  have hYcoe : (Y : M2) = ((ℓ : ℕ) : F) ^ r • (g : M2) := by
    rw [hY, Units.val_mul, scalar_coe' p, Matrix.smul_mul, Matrix.one_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
  have hYint : ∀ i j, (Y : M2) i j ∈ p.adicCompletionIntegers ℚ := by
    intro i j
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hYcoe, Matrix.smul_apply, smul_eq_mul]
    exact hrf i j r (hr_ge i j)
  obtain ⟨e₁, e₂, k₁, k₂, -, hk₁, hk₁', hk₂, hk₂', hYeq, -⟩ :=
    Matrix.GeneralLinearGroup.exists_eq_mul_diagonal_natCast_pow_mul_of_forall_mem_adicCompletionIntegers p hℓ hv Y hYint
  refine ⟨Lu ^ r * (Lu ^ e₂)⁻¹, k₁, k₂, (e₁ : ℤ) - (e₂ : ℤ), mem_K0_of_integral p k₁ hk₁ hk₁',
    mem_K0_of_integral p k₂ hk₂ hk₂', ?_⟩
  apply Units.ext
  have hdiag : (Matrix.diagonal ![((ℓ : ℕ) : F) ^ e₁, ((ℓ : ℕ) : F) ^ e₂] : M2) =
      ((ℓ : ℕ) : F) ^ e₂ • ((diagZ ((ℓ : ℕ) : F) hL0 ((e₁ : ℤ) - (e₂ : ℤ)) : G) : M2) := by
    change (Matrix.diagonal ![((ℓ : ℕ) : F) ^ e₁, ((ℓ : ℕ) : F) ^ e₂] : M2) =
      ((ℓ : ℕ) : F) ^ e₂ • (!![((ℓ : ℕ) : F) ^ ((e₁ : ℤ) - (e₂ : ℤ)), 0; 0, 1] : M2)
    have hpow : ((ℓ : ℕ) : F) ^ e₂ * ((ℓ : ℕ) : F) ^ ((e₁ : ℤ) - (e₂ : ℤ)) = ((ℓ : ℕ) : F) ^ e₁ := by
      rw [← zpow_natCast (((ℓ : ℕ) : F)) e₂, ← zpow_add₀ hL0, add_sub_cancel, zpow_natCast]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, hpow]
  have hrhs : (((k₁ * diagZ ((ℓ : ℕ) : F) hL0 ((e₁ : ℤ) - (e₂ : ℤ)) * k₂ : G)) : M2) =
      (k₁ : M2) * ((diagZ ((ℓ : ℕ) : F) hL0 ((e₁ : ℤ) - (e₂ : ℤ)) : G) : M2) * (k₂ : M2) := by
    rw [Units.val_mul, Units.val_mul]
  rw [hrhs, Units.val_mul, scalar_coe' p, Matrix.smul_mul, Matrix.one_mul, Units.val_mul, Units.val_inv_eq_inv_val,
    Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_mk0, mul_comm (((ℓ : ℕ) : F) ^ r) _, mul_smul,
    ← hYcoe, hYeq, hdiag,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hL0), one_smul]

theorem isCompact_box {ℓ : ℕ} (hℓ : ℓ.Prime) (M : ℕ) :
    IsCompact {g : G | ∃ k₁ ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∃ k₂ ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
      ∃ m : ℤ, |m| ≤ M ∧ g = k₁ * diagZ ((ℓ : ℕ) : F) (natCast_ne_zero p hℓ) m * k₂} := by
  have hK : IsCompact ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup G) : Set G) :=
    (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p ⊤ (by simp)).1
  have hS : {g : G | ∃ k₁ ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∃ k₂ ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
      ∃ m : ℤ, |m| ≤ M ∧ g = k₁ * diagZ ((ℓ : ℕ) : F) (natCast_ne_zero p hℓ) m * k₂} =
      ⋃ m ∈ Finset.Icc (-(M : ℤ)) M,
        (fun kk : G × G => kk.1 * diagZ ((ℓ : ℕ) : F) (natCast_ne_zero p hℓ) m * kk.2) ''
          (((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup G) : Set G) ×ˢ
            ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Subgroup G) : Set G)) := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, Set.mem_prod, Finset.mem_Icc, exists_prop,
      SetLike.mem_coe, Prod.exists]
    constructor
    · rintro ⟨k₁, hk₁, k₂, hk₂, m, hm, rfl⟩
      exact ⟨m, abs_le.mp hm, k₁, k₂, ⟨hk₁, hk₂⟩, rfl⟩
    · rintro ⟨m, hm, k₁, k₂, ⟨hk₁, hk₂⟩, rfl⟩
      exact ⟨k₁, hk₁, k₂, hk₂, m, abs_le.mpr hm, rfl⟩
  rw [hS]
  exact (Finset.Icc _ _).isCompact_biUnion fun m _ =>
    (hK.prod hK).image ((continuous_fst.mul continuous_const).mul continuous_snd)

theorem core (θ₀ : Fˣ →* ℂˣ) (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (w₂base : G → ℂ)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : G, w₂base (g * k) = w₂base g)
    (hcentral : ∀ (z : Fˣ) (g : G), w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (hVN : ∀ W ∈ V p w₂base, W ∈ VN p w₂base)
    (Ω : Subgroup G) (hΩo : IsOpen (Ω : Set G)) (L : (G → ℂ) →ₗ[ℂ] ℂ)
    (hL : ∀ k ∈ Ω, ∀ v ∈ V p w₂base, L (rho p k v) = L v)
    (w : G → ℂ) (hw : w ∈ V p w₂base) :
    ∃ C : Set G, IsCompact C ∧ ∀ g : G, L (rho p g w) ≠ 0 → ∃ z : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 2) z * g ∈ C := by
  classical
  obtain ⟨ℓ, hℓ, hvℓ⟩ := exists_prime_natCast_mem_asIdeal p
  have hπ : ((ℓ : ℕ) : F) ≠ 0 := natCast_ne_zero p hℓ
  have hπ1 : ‖((ℓ : ℕ) : F)‖ < 1 := norm_natCast_lt_one p hℓ hvℓ

  obtain ⟨hKc, -⟩ := AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p (⊤ : Ideal (𝓞 ℚ)) top_ne_bot
  obtain ⟨-, hKNo⟩ := AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N hN
  obtain ⟨Uw, hUwo, hUw⟩ := exists_open_stabilizer_of_mem_span w₂base (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N) hKNo hw₂K hw
  obtain ⟨R₁, -, hR₁⟩ := exists_finset_mul_inv_mem p (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set G) hKc Ω hΩo
  obtain ⟨R₂, -, hR₂⟩ := exists_finset_inv_mul_mem p (AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤ : Set G) hKc Uw hUwo

  have hpair : ∀ r₁ r₂ : G, ∃ M : ℕ, ∀ m : ℤ, (M : ℤ) ≤ |m| →
      L (rho p r₁ (rho p (diagZ ((ℓ : ℕ) : F) hπ m) (rho p r₂ w))) = 0 := by
    intro r₁ r₂
    set U₁ : Subgroup G := Ω.comap (MulAut.conj r₁).toMonoidHom with hU₁def
    have hU₁ : IsOpen (U₁ : Set G) := by
      have hc : Continuous fun k : G => r₁ * k * r₁⁻¹ := (continuous_const.mul continuous_id).mul continuous_const
      have hset : (U₁ : Set G) = (fun k : G => r₁ * k * r₁⁻¹) ⁻¹' (Ω : Set G) := by
        ext k
        simp only [hU₁def, Subgroup.coe_comap, Set.mem_preimage, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, SetLike.mem_coe]
      rw [hset]; exact hΩo.preimage hc
    set L₁ : (G → ℂ) →ₗ[ℂ] ℂ := L.comp (rho p r₁) with hL₁def
    have hL₁ : ∀ k ∈ U₁, ∀ u ∈ V p w₂base, L₁ (rho p k u) = L₁ u := by
      intro k hk u hu
      have hk' : r₁ * k * r₁⁻¹ ∈ Ω := by
        simpa only [hU₁def, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hk
      show L (rho p r₁ (rho p k u)) = L (rho p r₁ u)
      rw [← rho_mul, show r₁ * k = (r₁ * k * r₁⁻¹) * r₁ by group, rho_mul]
      exact hL _ hk' _ (rho_mem p w₂base _ hu)
    have hw₂ : rho p r₂ w ∈ V p w₂base := rho_mem p w₂base _ hw
    obtain ⟨Mp, hMp⟩ := decay_pos p w₂base U₁ hU₁ L₁ hL₁ _ hπ hπ1 _ (hVN _ hw₂)
    obtain ⟨Mn, hMn⟩ := decay_neg p θ₀ w₂base hcentral hVN U₁ hU₁ L₁ hL₁ _ hπ hπ1 _ hw₂
    refine ⟨max Mp Mn, fun m hm => ?_⟩
    show L₁ (rho p (diagZ ((ℓ : ℕ) : F) hπ m) (rho p r₂ w)) = 0
    rcases le_or_gt 0 m with h0m | hm0
    · have hm' : m = ((m.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg h0m).symm
      rw [hm']
      apply hMp
      have : (max Mp Mn : ℤ) ≤ (m.toNat : ℤ) := by rw [← hm', ← abs_of_nonneg h0m]; exact_mod_cast hm
      exact le_trans (le_max_left _ _) (by exact_mod_cast this)
    · have hm' : m = -(((-m).toNat : ℕ) : ℤ) := by rw [Int.toNat_of_nonneg (by omega)]; ring
      rw [hm']
      apply hMn
      have : (max Mp Mn : ℤ) ≤ ((-m).toNat : ℤ) := by
        rw [Int.toNat_of_nonneg (by omega), ← abs_of_neg hm0]; exact_mod_cast hm
      exact le_trans (le_max_right _ _) (by exact_mod_cast this)
  choose Mf hMf using hpair
  set M : ℕ := (R₁ ×ˢ R₂).sup fun q => Mf q.1 q.2 with hMdef
  refine ⟨_, isCompact_box p hℓ M, fun g hg => ?_⟩
  obtain ⟨z, k₁, k₂, m, hk₁, hk₂, hg'⟩ := exists_scalar_mul_eq_cartan p hℓ hvℓ g
  obtain ⟨r₁, hr₁, hu₁⟩ := hR₁ k₁ hk₁
  obtain ⟨r₂, hr₂, hu₂⟩ := hR₂ k₂ hk₂
  refine ⟨z, k₁, hk₁, k₂, hk₂, m, ?_, hg'⟩

  by_contra hbig
  have hMle : (Mf r₁ r₂ : ℤ) ≤ |m| := by
    have h1 : Mf r₁ r₂ ≤ M := by
      have hmem : (r₁, r₂) ∈ R₁ ×ˢ R₂ := Finset.mem_product.2 ⟨hr₁, hr₂⟩
      have := Finset.le_sup (f := fun q : G × G => Mf q.1 q.2) hmem
      simpa only [hMdef] using this
    have h2 : (M : ℤ) < |m| := lt_of_not_ge hbig
    exact le_trans (by exact_mod_cast h1) h2.le
  have hzero := hMf r₁ r₂ m hMle

  have hgw : rho p g w ∈ V p w₂base := rho_mem p w₂base _ hw
  have hk₂w : rho p k₂ w = rho p r₂ w := by
    rw [show k₂ = r₂ * (r₂⁻¹ * k₂) by group, rho_mul]
    congr 1
    funext x; rw [rho_apply]; exact hUw _ hu₂ x
  have hval : L (rho p (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) w) =
      L (rho p r₁ (rho p (diagZ ((ℓ : ℕ) : F) hπ m) (rho p r₂ w))) := by
    rw [hg', rho_mul, rho_mul, hk₂w, show k₁ = (k₁ * r₁⁻¹) * r₁ by group, rho_mul]
    exact hL _ hu₁ _ (rho_mem p w₂base _ (rho_mem p w₂base _ (rho_mem p w₂base _ hw)))
  have hval2 : L (rho p (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) w) = ((θ₀ z : ℂˣ) : ℂ) * L (rho p g w) := by
    rw [rho_mul, rho_scalar_of_mem p θ₀ w₂base hcentral z hgw, map_smul, smul_eq_mul]
  have : ((θ₀ z : ℂˣ) : ℂ) * L (rho p g w) = 0 := by rw [← hval2, hval, hzero]
  exact hg ((mul_eq_zero.1 this).resolve_left (Units.ne_zero _))

end CuspCoeff
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_isCompact_forall_setIntegral_translate_ne_zero_of_cuspidal.CuspCoeff"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_isCompact_forall_setIntegral_translate_ne_zero_of_cuspidal.CuspCoeff"

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    (hcusp : ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ N₀ : ℤ, ∀ y : (p.adicCompletion ℚ)ˣ, Valued.v (y : (p.adicCompletion ℚ)) ≤ WithZero.exp N₀ → v (diagOne y) = 0)
    :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (Ω : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))), IsOpen (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) → IsCompact (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∀ (g₀ : GL (Fin 2) (p.adicCompletion ℚ)),
      ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∃ C : Set (GL (Fin 2) (p.adicCompletion ℚ)), IsCompact C ∧
          ∀ g : GL (Fin 2) (p.adicCompletion ℚ), (∫ k in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (g₀ * k * g) ∂μ₂) ≠ 0 →
            ∃ z : (p.adicCompletion ℚ)ˣ, Matrix.GeneralLinearGroup.scalar (Fin 2) z * g ∈ C := by
  letI := localGLBorel ℚ p
  haveI := borelSpace_localGLBorel ℚ p
  intro μ₂ _ Ω hΩo hΩc g₀ w hw
  classical
  obtain ⟨n, wj, ℓ, hwjV, hwjlc, hℓinv, hℓlc, hexp⟩ :=
    LanglandsTunnell.RankinSelberg.exists_forall_setIntegral_translate_eq_mul_sum_linearMap_of_admissible p N hN w₂base
      hw₂K hw₂adm μ₂ Ω hΩo hΩc w hw
  have hVN := AutomorphicForm.WhittakerModel.forall_mem_span_sub_unipotent_of_forall_diagOne_eq_zero_of_irreducible_of_admissible
    p N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcusp
  have hcore : ∀ j : Fin n, ∃ C : Set (GL (Fin 2) (p.adicCompletion ℚ)), IsCompact C ∧
      ∀ g : GL (Fin 2) (p.adicCompletion ℚ), ℓ j (CuspCoeff.rho p g w) ≠ 0 →
        ∃ z : (p.adicCompletion ℚ)ˣ, Matrix.GeneralLinearGroup.scalar (Fin 2) z * g ∈ C :=
    fun j => CuspCoeff.core p θ₀ N hN w₂base hw₂K hcentral hVN Ω hΩo (ℓ j) (fun k hk v hv => hℓinv j k hk v hv) w hw
  choose C hC using hcore
  refine ⟨⋃ j, C j, isCompact_iUnion (fun j => (hC j).1), fun g hg => ?_⟩
  by_contra hno
  apply hg
  rw [hexp g₀ g]
  have hzero : ∀ j : Fin n, ℓ j (fun x : GL (Fin 2) (p.adicCompletion ℚ) => w (x * g)) = 0 := by
    intro j
    by_contra hj
    obtain ⟨z, hz⟩ := (hC j).2 g hj
    exact hno ⟨z, Set.mem_iUnion.2 ⟨j, hz⟩⟩
  simp [hzero]

end S_LanglandsTunnell_RankinSelberg_exists_isCompact_forall_setIntegral_translate_ne_zero_of_cuspidal
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_isCompact_forall_setIntegral_translate_ne_zero_of_cuspidal (solution)
