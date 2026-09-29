-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_flatSection_jacquetIntegral_eq_finsum_cpow_of_embedding_principalSeries2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/a5389bd6-6f9d-5ef9-9203-cddf07da38c7

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_CubicInduction_flatSection_mem_principalSeries2_and_iwasawaHeight_mul_eq
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_finset_forall_setIntegral_flatSection_antidiagonal_unipotentGL2_addChar_eq_sum_cpow
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_linearMap_stabilised_jacquetIntegral_principalSeries2
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_eq_smul_of_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_linearMap_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul_and_apply_eq_of_forall_mem
import Theorems.Thm_LanglandsTunnell_CubicInduction_integrable_apply_antidiagonal_mul_unipotentGL2_mul_addChar_of_mem_principalSeries2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_flatSection_jacquetIntegral_eq_finsum_cpow_of_embedding_principalSeries2
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction AutomorphicForm

open scoped NNReal

noncomputable section

namespace KcFlatFamily

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "ψ" => (NumberField.StandardAddChar.psiLocal ℚ p)

def qC : ℂ := (Ideal.absNorm p.asIdeal : ℂ)

theorem one_lt_q : (1 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p

theorem qC_ne_zero : qC p ≠ 0 := by
  rw [qC]
  have h := one_lt_q p
  exact_mod_cast (show (Ideal.absNorm p.asIdeal : ℝ) ≠ 0 by linarith)

theorem qC_eq_ofReal : qC p = ((Ideal.absNorm p.asIdeal : ℝ) : ℂ) := by
  rw [qC]; push_cast; rfl

def expChar (j : ℤ) : Multiplicative ℂ →* ℂ where
  toFun u := qC p ^ ((j : ℂ) * Multiplicative.toAdd u)
  map_one' := by simp
  map_mul' u v := by
    rw [toAdd_mul, mul_add, Complex.cpow_add _ _ (qC_ne_zero p)]

theorem expChar_apply (j : ℤ) (u : ℂ) : expChar p j (Multiplicative.ofAdd u) = qC p ^ ((j : ℂ) * u) := rfl

theorem expChar_injective : Function.Injective (expChar p) := by
  intro j j' h
  have h1 := congrArg (fun φ : Multiplicative ℂ →* ℂ => φ (Multiplicative.ofAdd 1)) h
  simp only [expChar_apply, mul_one] at h1
  rw [qC_eq_ofReal, Complex.cpow_intCast, Complex.cpow_intCast, ← Complex.ofReal_zpow, ← Complex.ofReal_zpow,
    Complex.ofReal_inj] at h1
  exact zpow_right_injective₀ (by linarith [one_lt_q p]) (one_lt_q p).ne' h1

theorem linearIndependent_expChar :
    LinearIndependent ℂ (M := Multiplicative ℂ → ℂ) (fun j : ℤ => (expChar p j : Multiplicative ℂ → ℂ)) :=
  (linearIndependent_monoidHom (Multiplicative ℂ) ℂ).comp (expChar p) (expChar_injective p)

theorem coeff_eq_of_forall_sum_eq {S : Finset ℤ} {c d : ℤ → ℂ}
    (h : ∀ u : ℂ, ∑ j ∈ S, c j * qC p ^ ((j : ℂ) * u) = ∑ j ∈ S, d j * qC p ^ ((j : ℂ) * u)) :
    ∀ j ∈ S, c j = d j := by
  intro j hj
  have hli := linearIndependent_expChar p
  have hsum : ∑ i ∈ S, (c i - d i) • (expChar p i : Multiplicative ℂ → ℂ) = 0 := by
    funext u
    have hu := h (Multiplicative.toAdd u)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have : ∀ i : ℤ, (expChar p i : Multiplicative ℂ → ℂ) u = qC p ^ ((i : ℂ) * Multiplicative.toAdd u) :=
      fun i => rfl
    simp only [this, sub_mul, Finset.sum_sub_distrib]
    rw [hu, sub_self]
  have := linearIndependent_iff'.mp hli S (fun i => c i - d i) hsum j hj
  exact sub_eq_zero.mp this

def extz (S : Finset ℤ) (c : ℤ → ℂ) : ℤ → ℂ := fun j => if j ∈ S then c j else 0

theorem sum_extz_eq (S T : Finset ℤ) (hST : S ⊆ T) (c : ℤ → ℂ) (φ : ℤ → ℂ) :
    ∑ j ∈ T, extz S c j * φ j = ∑ j ∈ S, c j * φ j := by
  classical
  rw [← Finset.sum_subset hST (f := fun j => extz S c j * φ j)]
  · refine Finset.sum_congr rfl fun j hj => ?_
    simp [extz, hj]
  · intro j _ hjS
    simp [extz, hjS]

theorem extz_eq_of_forall_sum_eq {S S' : Finset ℤ} {c c' : ℤ → ℂ}
    (h : ∀ u : ℂ, ∑ j ∈ S, c j * qC p ^ ((j : ℂ) * u) = ∑ j ∈ S', c' j * qC p ^ ((j : ℂ) * u)) :
    extz S c = extz S' c' := by
  classical
  funext j
  by_cases hj : j ∈ S ∪ S'
  · refine coeff_eq_of_forall_sum_eq p (S := S ∪ S') (fun u => ?_) j hj
    rw [sum_extz_eq S (S ∪ S') Finset.subset_union_left, sum_extz_eq S' (S ∪ S') Finset.subset_union_right]
    exact h u
  · rw [Finset.mem_union, not_or] at hj
    simp [extz, hj.1, hj.2]

theorem finsum_extz_eq_sum (S : Finset ℤ) (c : ℤ → ℂ) (φ : ℤ → ℂ) :
    ∑ᶠ j : ℤ, extz S c j * φ j = ∑ j ∈ S, c j * φ j := by
  classical
  rw [finsum_eq_sum_of_support_subset (s := S)]
  · exact Finset.sum_congr rfl fun j hj => by simp [extz, hj]
  · intro j hj
    rw [Function.mem_support] at hj
    rw [Finset.mem_coe]
    by_contra hjS
    exact hj (by simp [extz, hjS])

variable {p}

theorem modR_pos (a : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : 0 < ((modulus (a : F) : ℝ)) := by
  exact_mod_cast modulus_pos a.ne_zero

theorem modC_ne_zero (a : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) : (((modulus (a : F) : ℝ)) : ℂ) ≠ 0 := by
  exact_mod_cast (modR_pos a).ne'

variable (p) in

def twist (χ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ) (u : ℂ) :
    (HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ where
  toFun a := χ a * Units.mk0 ((((modulus (a : F) : ℝ)) : ℂ) ^ u) (by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl (modC_ne_zero a))
  map_one' := by
    ext
    simp
  map_mul' a b := by
    ext
    simp only [Units.val_mul, Units.val_mk0, map_mul, modulus_mul, NNReal.coe_mul, Complex.ofReal_mul]
    rw [Complex.mul_cpow_ofReal_nonneg (modR_pos a).le (modR_pos b).le]
    ring

theorem twist_apply (χ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ) (u : ℂ)
    (a : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) :
    ((twist p χ u a : ℂˣ) : ℂ) = ((χ a : ℂˣ) : ℂ) * ((((modulus (a : F) : ℝ)) : ℂ) ^ u) := rfl

theorem coe_modulus_eq_norm (x : F) : ((modulus x : ℝ≥0) : ℝ) = ‖x‖ := by
  rw [modulus_adicCompletion_eq_nnnorm ℚ p x, coe_nnnorm]

theorem norm_eq_one_iff (x : F) : ‖x‖ = 1 ↔ Valued.v x = 1 := by
  rw [NumberField.FinitePlace.norm_def, ← NNReal.coe_one, NNReal.coe_inj]
  exact WithZeroMulInt.toNNReal_eq_one_iff _ (NumberField.HeightOneSpectrum.absNorm_ne_zero p)
    (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p).ne'

theorem norm_lt_one_iff (x : F) : ‖x‖ < 1 ↔ Valued.v x < 1 := by
  rw [NumberField.FinitePlace.norm_def, ← NNReal.coe_one, NNReal.coe_lt_coe]
  exact WithZeroMulInt.toNNReal_lt_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p)

theorem modulus_eq_one_of_v_eq_one {a : (HeightOneSpectrum.adicCompletion ℚ p)ˣ} (ha : Valued.v (a : F) = 1) :
    ((modulus (a : F) : ℝ)) = 1 := by
  rw [coe_modulus_eq_norm, (norm_eq_one_iff _).mpr ha]

theorem twist_eq_of_v_eq_one (χ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ) (u : ℂ)
    {a : (HeightOneSpectrum.adicCompletion ℚ p)ˣ} (ha : Valued.v (a : F) = 1) : twist p χ u a = χ a := by
  refine Units.ext ?_
  rw [twist_apply, modulus_eq_one_of_v_eq_one ha, Complex.ofReal_one, Complex.one_cpow, mul_one]

theorem norm_twist (χ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ) (u : ℂ)
    (a : (HeightOneSpectrum.adicCompletion ℚ p)ˣ) :
    ‖((twist p χ u a : ℂˣ) : ℂ)‖ = ‖((χ a : ℂˣ) : ℂ)‖ * ((modulus (a : F) : ℝ)) ^ u.re := by
  rw [twist_apply, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (modR_pos a)]

def chiU (χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ)) (u : ℂ) :
    Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ) :=
  ![twist p (χ 0) u, twist p (χ 1) (-u)]

@[scoped simp] theorem chiU_zero (χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ)) (u : ℂ) :
    chiU χ u 0 = twist p (χ 0) u := rfl

@[scoped simp] theorem chiU_one (χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ)) (u : ℂ) :
    chiU χ u 1 = twist p (χ 1) (-u) := rfl

theorem chiU_higherUnits (χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ)) (cχ : Fin 2 → ℕ)
    (hcχ : ∀ i, ∀ a ∈ higherUnitsAt ℚ p (cχ i), χ i a = 1) (u : ℂ) :
    ∀ i, ∀ a ∈ higherUnitsAt ℚ p (cχ i), chiU χ u i a = 1 := by
  refine Fin.forall_fin_two.mpr ⟨fun a ha => ?_, fun a ha => ?_⟩
  · rw [chiU_zero, twist_eq_of_v_eq_one _ _ ((mem_higherUnitsAt_iff ℚ p).mp ha).1]; exact hcχ 0 a ha
  · rw [chiU_one, twist_eq_of_v_eq_one _ _ ((mem_higherUnitsAt_iff ℚ p).mp ha).1]; exact hcχ 1 a ha

theorem exists_uniformizer :
    ∃ ϖ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ, Valued.v (ϖ : F) = WithZero.exp (-1 : ℤ) :=
  ⟨NumberField.AdelicLevel.uniformizerUnit ℚ p, NumberField.AdelicLevel.valued_uniformizerUnit ℚ p⟩

theorem exists_forall_dominant (χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ))
    {ϖ : (HeightOneSpectrum.adicCompletion ℚ p)ˣ} (hϖ : Valued.v (ϖ : F) = WithZero.exp (-1 : ℤ)) :
    ∃ u₁ : ℝ, ∀ u : ℂ, u₁ < u.re →
      ‖((chiU χ u 0 ϖ : ℂˣ) : ℂ)‖ < ‖((chiU χ u 1 ϖ : ℂˣ) : ℂ)‖ := by
  set m : ℝ := ((modulus (ϖ : F) : ℝ)) with hm
  have hm0 : 0 < m := modR_pos ϖ
  have hm1 : m < 1 := by
    rw [hm, coe_modulus_eq_norm, norm_lt_one_iff, hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  set A : ℝ := ‖((χ 0 ϖ : ℂˣ) : ℂ)‖ with hA
  set B : ℝ := ‖((χ 1 ϖ : ℂˣ) : ℂ)‖ with hB
  have hA0 : 0 < A := norm_pos_iff.mpr (Units.ne_zero _)
  have hB0 : 0 < B := norm_pos_iff.mpr (Units.ne_zero _)

  set M : ℝ := m⁻¹ with hM
  have hM1 : 1 < M := by rw [hM]; exact one_lt_inv_iff₀.mpr ⟨hm0, hm1⟩
  have hM0 : 0 < M := by linarith
  refine ⟨Real.logb M (A / B) / 2, fun u hu => ?_⟩
  simp only [chiU_zero, chiU_one, norm_twist]
  rw [← hm, ← hA, ← hB, Complex.neg_re]
  have h2 : Real.logb M (A / B) < 2 * u.re := by linarith
  have h3 : A / B < M ^ (2 * u.re) := by
    have := Real.rpow_lt_rpow_of_exponent_lt hM1 h2
    rwa [Real.rpow_logb hM0 hM1.ne' (div_pos hA0 hB0)] at this
  have hmM : m = M⁻¹ := by rw [hM, inv_inv]
  rw [hmM, Real.inv_rpow hM0.le, Real.inv_rpow hM0.le, Real.rpow_neg hM0.le, inv_inv]

  have hMx : 0 < M ^ u.re := Real.rpow_pos_of_pos hM0 _
  rw [div_lt_iff₀ hB0] at h3
  have : M ^ (2 * u.re) = M ^ u.re * M ^ u.re := by
    rw [two_mul, Real.rpow_add hM0]
  rw [this] at h3
  calc A * (M ^ u.re)⁻¹ = A / M ^ u.re := by rw [div_eq_mul_inv]
    _ < B * M ^ u.re := by
        rw [div_lt_iff₀ hMx]
        calc A < M ^ u.re * M ^ u.re * B := h3
          _ = B * M ^ u.re * M ^ u.re := by ring

theorem unipotentGL2_eq (y : F) : (unipotentGL2 y : G) = upperUnipotent2 p y := by
  refine Units.ext ?_
  rw [unipotentGL2_coe, upperUnipotent2_coe]

theorem coe_rep (χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ)) (h : G)
    (f : ↥(principalSeries2 p χ)) :
    ((principalSeries2Rep χ h f : ↥(principalSeries2 p χ)) : G → ℂ) = fun g => (f : G → ℂ) (g * h) := rfl

section Identification

abbrev Vsp (w : G → ℂ) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h))

theorem self_mem_Vsp (w : G → ℂ) : w ∈ Vsp w := by
  refine Submodule.subset_span ⟨1, ?_⟩
  funext g; simp

theorem translate_mem_Vsp {w v : G → ℂ} (hv : v ∈ Vsp w) (h : G) : (fun g => v (g * h)) ∈ Vsp w := by
  refine Submodule.span_induction (p := fun v _ => (fun g => v (g * h)) ∈ Vsp w) ?_ ?_ ?_ ?_ hv
  · rintro x ⟨h', rfl⟩
    refine Submodule.subset_span ⟨h * h', ?_⟩
    funext g; simp [mul_assoc]
  · exact (Vsp w).zero_mem
  · intro x y _ _ hx hy
    exact (Vsp w).add_mem hx hy
  · intro a x _ hx
    exact (Vsp w).smul_mem a hx

theorem Vsp_law {w : G → ℂ} (hwlaw : ∀ (x : F) (g : G), w (unipotentGL2 x * g) = ψ x * w g)
    {v : G → ℂ} (hv : v ∈ Vsp w) (x : F) : ∀ g : G, v (unipotentGL2 x * g) = ψ x * v g := by
  refine Submodule.span_induction (p := fun v _ => ∀ g : G, v (unipotentGL2 x * g) = ψ x * v g) ?_ ?_ ?_ ?_ hv
  · rintro y ⟨h', rfl⟩ g
    simp only
    rw [mul_assoc, hwlaw]
  · intro g; simp
  · intro y z _ _ hy hz g
    simp only [Pi.add_apply]; rw [hy, hz]; ring
  · intro a y _ hy g
    simp only [Pi.smul_apply, smul_eq_mul]; rw [hy]; ring

theorem psi_neg_mul (x : F) : ψ (-x) * ψ x = 1 := by
  rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

theorem inv_psiInv_apply (x : F) : ((ψ⁻¹ : AddChar F ℂ) x)⁻¹ = ψ x := by
  rw [AddChar.inv_apply]
  exact inv_eq_of_mul_eq_one_right (psi_neg_mul x)

theorem exists_eq_lam (χ : Fin 2 → ((HeightOneSpectrum.adicCompletion ℚ p)ˣ →* ℂˣ)) {w : G → ℂ}
    (hwlaw : ∀ (x : F) (g : G), w (unipotentGL2 x * g) = ψ x * w g)
    (hPS : ∃ Φ : (G → ℂ) →ₗ[ℂ] (G → ℂ),
      (∀ v ∈ Vsp w, ∀ h : G, Φ (fun g => v (g * h)) = fun g => Φ v (g * h)) ∧
      (∀ v ∈ Vsp w, Φ v = 0 → v = 0) ∧
      (∀ v ∈ Vsp w, Φ v ∈ principalSeries2 p χ))
    (Λ : ↥(principalSeries2 p χ) →ₗ[ℂ] (G → ℂ))
    (hΛiii : ∀ (f : ↥(principalSeries2 p χ)) (x : F) (g : G),
      Λ f (unipotentGL2 x * g) = ((ψ⁻¹ : AddChar F ℂ) x)⁻¹ * Λ f g)
    (hΛiv : ∀ (f : ↥(principalSeries2 p χ)) (h g : G), Λ (principalSeries2Rep χ h f) g = Λ f (g * h))
    (hΛv : ∃ f : ↥(principalSeries2 p χ), Λ f 1 ≠ 0) :
    ∃ f : ↥(principalSeries2 p χ),
      (∀ k : G, (∀ g : G, w (g * k) = w g) → ∀ g : G, (f : G → ℂ) (g * k) = (f : G → ℂ) g) ∧
      ∀ g : G, w g = Λ f g := by
  classical
  obtain ⟨Φ, hΦeq, hΦinj, hΦPS⟩ := hPS
  have hψ1 : (ψ : AddChar F ℂ) ≠ 1 := psiLocal_ne_one ℚ p

  have hinj : ∀ v ∈ Vsp w, ∀ v' ∈ Vsp w, Φ v = Φ v' → v = v' := by
    intro v hv v' hv' h
    have h0 : Φ (v - v') = 0 := by rw [map_sub, h, sub_self]
    exact sub_eq_zero.mp (hΦinj _ ((Vsp w).sub_mem hv hv') h0)

  let Us : Submodule ℂ ↥(principalSeries2 p χ) :=
    { carrier := {f | ∃ v ∈ Vsp w, Φ v = (f : G → ℂ)}
      zero_mem' := ⟨0, (Vsp w).zero_mem, by simp⟩
      add_mem' := by
        rintro f₁ f₂ ⟨v₁, hv₁, h₁⟩ ⟨v₂, hv₂, h₂⟩
        exact ⟨v₁ + v₂, (Vsp w).add_mem hv₁ hv₂, by rw [map_add, h₁, h₂]; rfl⟩
      smul_mem' := by
        rintro a f ⟨v, hv, h⟩
        exact ⟨a • v, (Vsp w).smul_mem a hv, by rw [map_smul, h]; rfl⟩ }
  have hUs_mem : ∀ f : ↥(principalSeries2 p χ), f ∈ Us ↔ ∃ v ∈ Vsp w, Φ v = (f : G → ℂ) := fun f => Iff.rfl

  have hUN : ∀ (x : F), ∀ f ∈ Us, principalSeries2Rep χ (upperUnipotent2 p x) f ∈ Us := by
    intro x f hf
    obtain ⟨v, hv, hvf⟩ := (hUs_mem f).mp hf
    refine (hUs_mem _).mpr ⟨fun g => v (g * upperUnipotent2 p x), translate_mem_Vsp hv _, ?_⟩
    rw [hΦeq v hv, coe_rep, hvf]

  have hpre : ∀ f : ↥Us, ∃ v ∈ Vsp w, Φ v = ((f : ↥(principalSeries2 p χ)) : G → ℂ) := fun f => f.2
  choose pre hpreV hpreΦ using hpre
  have pre_eq : ∀ (f : ↥Us) (v : G → ℂ), v ∈ Vsp w → Φ v = ((f : ↥(principalSeries2 p χ)) : G → ℂ) →
      pre f = v := fun f v hv hΦv => hinj _ (hpreV f) _ hv ((hpreΦ f).trans hΦv.symm)
  let ℓ : ↥Us →ₗ[ℂ] ℂ :=
    { toFun := fun f => pre f 1
      map_add' := by
        intro f₁ f₂
        have h := pre_eq (f₁ + f₂) (pre f₁ + pre f₂) ((Vsp w).add_mem (hpreV f₁) (hpreV f₂))
          (by rw [map_add, hpreΦ, hpreΦ]; rfl)
        rw [h]; rfl
      map_smul' := by
        intro a f
        have h := pre_eq (a • f) (a • pre f) ((Vsp w).smul_mem a (hpreV f)) (by rw [map_smul, hpreΦ]; rfl)
        rw [h]; rfl }
  have hℓ_apply : ∀ f : ↥Us, ℓ f = pre f 1 := fun f => rfl
  have hℓ : ∀ (x : F) (f : ↥Us),
      ℓ ⟨principalSeries2Rep χ (upperUnipotent2 p x) f, hUN x f f.2⟩ = ψ x * ℓ f := by
    intro x f
    rw [hℓ_apply, hℓ_apply]
    have h := pre_eq ⟨principalSeries2Rep χ (upperUnipotent2 p x) f, hUN x f f.2⟩
      (fun g => pre f (g * upperUnipotent2 p x)) (translate_mem_Vsp (hpreV f) _)
      (by rw [hΦeq _ (hpreV f), hpreΦ]; rfl)
    rw [h]
    simp only
    rw [one_mul, ← mul_one (upperUnipotent2 p x), ← unipotentGL2_eq, Vsp_law hwlaw (hpreV f) x 1]

  obtain ⟨L, hL, hLext⟩ :=
    LanglandsTunnell.CubicInduction.exists_linearMap_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul_and_apply_eq_of_forall_mem
      p χ ψ Us hUN ℓ hℓ

  let ℓ₁ : ↥(principalSeries2 p χ) →ₗ[ℂ] ℂ := (LinearMap.proj (1 : G) : (G → ℂ) →ₗ[ℂ] ℂ).comp Λ
  have hℓ₁_apply : ∀ f, ℓ₁ f = Λ f 1 := fun f => rfl
  have hℓ₁ : ∀ (x : F) (f : ↥(principalSeries2 p χ)),
      ℓ₁ (principalSeries2Rep χ (upperUnipotent2 p x) f) = ψ x * ℓ₁ f := by
    intro x f
    rw [hℓ₁_apply, hℓ₁_apply, hΛiv, one_mul, ← mul_one (upperUnipotent2 p x), ← unipotentGL2_eq, hΛiii,
      inv_psiInv_apply]
  have hℓ₁ne : ℓ₁ ≠ 0 := by
    obtain ⟨f, hf⟩ := hΛv
    intro h0
    exact hf (by rw [← hℓ₁_apply, h0, LinearMap.zero_apply])
  obtain ⟨c, hc⟩ :=
    LanglandsTunnell.CubicInduction.exists_eq_smul_of_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul
      p χ ψ hψ1 ℓ₁ L hℓ₁ hL hℓ₁ne

  have hw : w ∈ Vsp w := self_mem_Vsp w
  set fw : ↥(principalSeries2 p χ) := ⟨Φ w, hΦPS w hw⟩ with hfw
  refine ⟨c • fw, fun k hk g => ?_, fun g => ?_⟩
  · have hwk : (fun g => w (g * k)) = w := funext hk
    have h1 := hΦeq w hw k
    rw [hwk] at h1
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hfw]
    rw [show Φ w (g * k) = (fun g => Φ w (g * k)) g from rfl, ← h1]
  ·
    have hvg : (fun g' => w (g' * g)) ∈ Vsp w := translate_mem_Vsp hw g
    let fg : ↥Us := ⟨⟨Φ (fun g' => w (g' * g)), hΦPS _ hvg⟩, _, hvg, rfl⟩
    have h1 : ℓ fg = w g := by
      rw [hℓ_apply, pre_eq fg _ hvg rfl]; simp
    have h2 : (fg : ↥(principalSeries2 p χ)) = principalSeries2Rep χ g fw := by
      refine Subtype.ext ?_
      rw [coe_rep]
      exact hΦeq w hw g
    rw [← h1, ← hLext fg, hc, LinearMap.smul_apply, h2, hℓ₁_apply, hΛiv, one_mul, smul_eq_mul,
      LinearMap.map_smul, Pi.smul_apply, smul_eq_mul]

end Identification

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem psiInv_level : ∃ k : ℤ, ∀ y : F, Valued.v y ≤ WithZero.exp k → (ψ⁻¹ : AddChar F ℂ) y = 1 := by
  refine ⟨0, fun y hy => ?_⟩
  rw [AddChar.inv_apply]
  refine psiLocal_eq_one_of_mem_integers ℚ p (-y) ?_
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_neg]
  simpa using hy

theorem psiInv_ne_one : (ψ⁻¹ : AddChar F ℂ) ≠ 1 := by
  intro h
  apply psiLocal_ne_one ℚ p
  have := congrArg Inv.inv h
  simpa using this

theorem continuous_psiInv : Continuous (ψ⁻¹ : AddChar F ℂ) := by
  have : ((ψ⁻¹ : AddChar F ℂ) : F → ℂ) = fun y => ψ (-y) := funext fun y => AddChar.inv_apply _ _
  rw [this]
  exact (NumberField.StandardAddChar.continuous_psiLocal ℚ p).comp continuous_neg

theorem extz_mul (S : Finset ℤ) (c : ℤ → ℂ) (φ : ℂ) (j : ℤ) :
    extz S (fun j => φ * c j) j = φ * extz S c j := by
  by_cases hj : j ∈ S <;> simp [extz, hj]

variable (p) in

theorem main
    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (cχ : Fin 2 → ℕ)
    (hcχ : ∀ i, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (cχ i), χ i u = 1)
    (U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)))
    (hU : IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))))
    (hUK : U ≤ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤)
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (unipotentGL2 x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g)
    (hwU : ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g)
    (hPS : ∃ Φ : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
      (∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)), ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
        Φ (fun g => v (g * h)) = fun g => Φ v (g * h)) ∧
      (∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)), Φ v = 0 → v = 0) ∧
      (∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)), Φ v ∈ principalSeries2 p χ))
    (w₀ : GL (Fin 2) (p.adicCompletion ℚ))
    (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0])
    (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure] :
      ∃ (fu : ℂ → GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (χu : ℂ → Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
        (E : ℤ → GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (u₁ : ℝ),
        (∀ (u : ℂ) (a : (p.adicCompletion ℚ)ˣ),
          ((χu u 0 a : ℂˣ) : ℂ) = ((χ 0 a : ℂˣ) : ℂ) * (((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ u)) ∧
        (∀ (u : ℂ) (a : (p.adicCompletion ℚ)ˣ),
          ((χu u 1 a : ℂˣ) : ℂ) = ((χ 1 a : ℂˣ) : ℂ) * (((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-u))) ∧
        (∀ u : ℂ, fu u ∈ principalSeries2 p (χu u)) ∧
        (∀ u : ℂ, ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), fu u (g * k) = fu u g) ∧
        (∀ i : ℤ, ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), E i (g * k) = E i g) ∧
        (∀ (i : ℤ) (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
          E i (unipotentGL2 x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * E i g) ∧
        (∀ C : Set (GL (Fin 2) (p.adicCompletion ℚ)), IsCompact C →
          {i : ℤ | ∃ g ∈ C, E i g ≠ 0}.Finite) ∧
        (∀ u : ℂ, u₁ < u.re → ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
          Integrable (fun y : p.adicCompletion ℚ =>
            fu u (w₀ * unipotentGL2 y * g) * (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ y) ν ∧
          ∫ y, fu u (w₀ * unipotentGL2 y * g) * (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ y ∂ν =
            ∑ᶠ i : ℤ, (Ideal.absNorm p.asIdeal : ℂ) ^ (-(i : ℂ) * u) * E i g) ∧
        (∀ g : GL (Fin 2) (p.adicCompletion ℚ), w g = ∑ᶠ i : ℤ, E i g) := by
  classical
  have hθk := psiInv_level (p := p)
  have hθ1 := psiInv_ne_one (p := p)
  have hθc := continuous_psiInv (p := p)

  obtain ⟨Λ₀, hΛi, -, hΛiii, hΛiv, hΛv⟩ :=
    LanglandsTunnell.CubicInduction.exists_linearMap_stabilised_jacquetIntegral_principalSeries2
      p χ cχ hcχ w₀ hw₀ ψ⁻¹ hθk hθ1 ν
  obtain ⟨f, hfU', hwf⟩ := exists_eq_lam χ hwlaw hPS Λ₀ hΛiii hΛiv hΛv
  have hf : (f : G → ℂ) ∈ principalSeries2 p χ := f.2
  have hfU : ∀ k ∈ U, ∀ g : G, (f : G → ℂ) (g * k) = (f : G → ℂ) g := fun k hk => hfU' k (hwU k hk)

  set H : G → ℝ := fun g =>
    ‖(g : Matrix (Fin 2) (Fin 2) F).det‖ /
      max ‖(g : Matrix (Fin 2) (Fin 2) F) 1 0‖ ‖(g : Matrix (Fin 2) (Fin 2) F) 1 1‖ ^ 2 with hH
  set fu : ℂ → G → ℂ := fun u g => (f : G → ℂ) g * ((H g : ℝ) : ℂ) ^ u with hfu
  have hR1a := fun u : ℂ =>
    LanglandsTunnell.CubicInduction.flatSection_mem_principalSeries2_and_iwasawaHeight_mul_eq p χ (chiU χ u) u
      (fun a => twist_apply (χ 0) u a) (fun a => twist_apply (χ 1) (-u) a) (f : G → ℂ) hf
  have hfuPS : ∀ u : ℂ, fu u ∈ principalSeries2 p (chiU χ u) := fun u => (hR1a u).1
  have hfuU : ∀ u : ℂ, ∀ k ∈ U, ∀ g : G, fu u (g * k) = fu u g := by
    intro u k hk g
    simp only [hfu, hH]
    rw [hfU k hk g, (hR1a u).2.2.2.1 g k (hUK hk)]

  have hR1b := fun g : G =>
    LanglandsTunnell.CubicInduction.exists_finset_forall_setIntegral_flatSection_antidiagonal_unipotentGL2_addChar_eq_sum_cpow
      p χ cχ hcχ (f : G → ℂ) hf w₀ hw₀ ψ⁻¹ hθk hθ1 g ν
  choose M₀ S c hSc using hR1b

  have hball : ∀ (g : G) (u : ℂ) (M : ℤ), M₀ g ≤ M →
      ∫ y in {y : F | Valued.v y ≤ WithZero.exp M}, fu u (w₀ * unipotentGL2 y * g) * (ψ⁻¹ : AddChar F ℂ) y ∂ν =
        ∑ j ∈ S g, c g j * qC p ^ ((j : ℂ) * u) := by
    intro g u M hM
    exact (hSc g u M hM).2
  set E : ℤ → G → ℂ := fun i g => extz (S g) (c g) (-i) with hE

  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer (p := p)
  obtain ⟨u₁, hu₁⟩ := exists_forall_dominant χ hϖ

  have hΛu : ∀ u : ℂ, ∃ Λ : ↥(principalSeries2 p (chiU χ u)) →ₗ[ℂ] (G → ℂ),
      (∀ (f' : ↥(principalSeries2 p (chiU χ u))) (g : G), ∃ M₁ : ℤ, ∀ M : ℤ, M₁ ≤ M →
          IntegrableOn (fun y : F => (f' : G → ℂ) (w₀ * unipotentGL2 y * g) * (ψ⁻¹ : AddChar F ℂ) y)
            {y : F | Valued.v y ≤ WithZero.exp M} ν ∧
          Λ f' g = ∫ y in {y : F | Valued.v y ≤ WithZero.exp M},
            (f' : G → ℂ) (w₀ * unipotentGL2 y * g) * (ψ⁻¹ : AddChar F ℂ) y ∂ν) ∧
      (∀ (f' : ↥(principalSeries2 p (chiU χ u))) (g : G),
          Integrable (fun y : F => (f' : G → ℂ) (w₀ * unipotentGL2 y * g) * (ψ⁻¹ : AddChar F ℂ) y) ν →
          Λ f' g = ∫ y, (f' : G → ℂ) (w₀ * unipotentGL2 y * g) * (ψ⁻¹ : AddChar F ℂ) y ∂ν) ∧
      (∀ (f' : ↥(principalSeries2 p (chiU χ u))) (x : F) (g : G),
          Λ f' (unipotentGL2 x * g) = ((ψ⁻¹ : AddChar F ℂ) x)⁻¹ * Λ f' g) := by
    intro u
    obtain ⟨Λ, h1, h2, h3, -, -⟩ :=
      LanglandsTunnell.CubicInduction.exists_linearMap_stabilised_jacquetIntegral_principalSeries2
        p (chiU χ u) cχ (chiU_higherUnits χ cχ hcχ u) w₀ hw₀ ψ⁻¹ hθk hθ1 ν
    exact ⟨Λ, h1, h2, h3⟩

  have key : ∀ (g g' : G) (φ : ℂ),
      (∀ u : ℂ, ∃ M : ℤ, M₀ g ≤ M ∧ M₀ g' ≤ M ∧
        ∫ y in {y : F | Valued.v y ≤ WithZero.exp M}, fu u (w₀ * unipotentGL2 y * g') * (ψ⁻¹ : AddChar F ℂ) y ∂ν =
          φ * ∫ y in {y : F | Valued.v y ≤ WithZero.exp M},
            fu u (w₀ * unipotentGL2 y * g) * (ψ⁻¹ : AddChar F ℂ) y ∂ν) →
      extz (S g') (c g') = fun j => φ * extz (S g) (c g) j := by
    intro g g' φ h
    have hext : extz (S g') (c g') = extz (S g) (fun j => φ * c g j) := by
      refine extz_eq_of_forall_sum_eq p fun u => ?_
      obtain ⟨M, hM, hM', hint⟩ := h u
      rw [← hball g' u M hM', hint, hball g u M hM, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hext]
    funext j
    exact extz_mul _ _ _ _

  have hEU : ∀ i : ℤ, ∀ k ∈ U, ∀ g : G, E i (g * k) = E i g := by
    intro i k hk g
    have h := key g (g * k) 1 fun u => ⟨max (M₀ g) (M₀ (g * k)), le_max_left _ _, le_max_right _ _, ?_⟩
    · simp only [hE]
      rw [h]; simp
    · rw [one_mul]
      congr 1
      funext y
      rw [← mul_assoc, hfuU u k hk]

  have hElaw : ∀ (i : ℤ) (x : F) (g : G), E i (unipotentGL2 x * g) = ψ x * E i g := by
    intro i x g
    have h := key g (unipotentGL2 x * g) (ψ x) fun u => ?_
    · simp only [hE]
      rw [h]
    · obtain ⟨Λ, hΛ1, -, hΛ3⟩ := hΛu u
      let f' : ↥(principalSeries2 p (chiU χ u)) := ⟨fu u, hfuPS u⟩
      obtain ⟨M₁, hM₁⟩ := hΛ1 f' g
      obtain ⟨M₂, hM₂⟩ := hΛ1 f' (unipotentGL2 x * g)
      set M : ℤ := max (max (M₀ g) (M₀ (unipotentGL2 x * g))) (max M₁ M₂) with hM
      refine ⟨M, (le_max_left _ _).trans (le_max_left _ _), (le_max_right _ _).trans (le_max_left _ _), ?_⟩
      have e1 := (hM₁ M ((le_max_left _ _).trans (le_max_right _ _))).2
      have e2 := (hM₂ M ((le_max_right _ _).trans (le_max_right _ _))).2
      change Λ f' g = ∫ y in _, fu u (w₀ * unipotentGL2 y * g) * (ψ⁻¹ : AddChar F ℂ) y ∂ν at e1
      change Λ f' (unipotentGL2 x * g) = ∫ y in _, fu u (w₀ * unipotentGL2 y * (unipotentGL2 x * g)) *
        (ψ⁻¹ : AddChar F ℂ) y ∂ν at e2
      rw [← e1, ← e2, hΛ3, inv_psiInv_apply]

  have hEfin : ∀ C : Set G, IsCompact C → {i : ℤ | ∃ g ∈ C, E i g ≠ 0}.Finite := by
    intro C hC
    obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun g : G => (fun k : G => g * k) '' (U : Set G))
      (fun g => isOpenMap_mul_left g _ hU) (fun g _ => Set.mem_iUnion.mpr ⟨g, 1, U.one_mem, mul_one g⟩)
    refine Set.Finite.subset (Set.Finite.biUnion t.finite_toSet fun g₀ _ =>
      ((S g₀).finite_toSet.image fun j : ℤ => -j)) ?_
    rintro i ⟨g, hg, hi⟩
    obtain ⟨g₀, hg₀, hgg₀⟩ : ∃ g₀ ∈ t, g ∈ (fun k : G => g₀ * k) '' (U : Set G) := by
      have := ht hg
      simpa only [Set.mem_iUnion, exists_prop] using this
    obtain ⟨k, hk, rfl⟩ := hgg₀
    rw [hEU i k hk g₀] at hi
    refine Set.mem_biUnion hg₀ ⟨-i, Finset.mem_coe.mpr ?_, neg_neg i⟩
    simp only [hE, extz] at hi
    by_contra hni
    exact hi (by rw [if_neg hni])

  have hfinsum : ∀ (g : G) (u : ℂ),
      ∑ᶠ i : ℤ, qC p ^ (-(i : ℂ) * u) * E i g = ∑ j ∈ S g, c g j * qC p ^ ((j : ℂ) * u) := by
    intro g u
    have h1 : ∀ i : ℤ, qC p ^ (-(i : ℂ) * u) * E i g =
        (fun j : ℤ => extz (S g) (c g) j * qC p ^ ((j : ℂ) * u)) (Equiv.neg ℤ i) := by
      intro i
      simp only [hE, Equiv.neg_apply, Int.cast_neg, neg_mul]
      ring
    rw [finsum_congr h1]
    exact (finsum_comp_equiv (Equiv.neg ℤ) (f := fun j : ℤ => extz (S g) (c g) j * qC p ^ ((j : ℂ) * u))).trans
      (finsum_extz_eq_sum _ _ _)
  refine ⟨fu, chiU χ, E, u₁, fun u a => twist_apply (χ 0) u a, fun u a => twist_apply (χ 1) (-u) a, hfuPS, hfuU,
    hEU, hElaw, hEfin, fun u hu g => ?_, fun g => ?_⟩
  ·
    have hint :=
      LanglandsTunnell.CubicInduction.integrable_apply_antidiagonal_mul_unipotentGL2_mul_addChar_of_mem_principalSeries2
        p (chiU χ u) cχ (chiU_higherUnits χ cχ hcχ u) ϖ hϖ (hu₁ u hu) (fu u) (hfuPS u) w₀ hw₀ ψ⁻¹ hθc g ν
    refine ⟨hint, ?_⟩
    obtain ⟨Λ, hΛ1, hΛ2, -⟩ := hΛu u
    let f' : ↥(principalSeries2 p (chiU χ u)) := ⟨fu u, hfuPS u⟩
    obtain ⟨M₁, hM₁⟩ := hΛ1 f' g
    have e0 := hΛ2 f' g hint
    have e1 := (hM₁ (max M₁ (M₀ g)) (le_max_left _ _)).2
    change Λ f' g = ∫ y, fu u (w₀ * unipotentGL2 y * g) * (ψ⁻¹ : AddChar F ℂ) y ∂ν at e0
    change Λ f' g = ∫ y in _, fu u (w₀ * unipotentGL2 y * g) * (ψ⁻¹ : AddChar F ℂ) y ∂ν at e1
    rw [← e0, e1, hball g u _ (le_max_right _ _), ← hfinsum g u]
    rfl
  ·
    obtain ⟨M₁, hM₁⟩ := hΛi f g
    have e1 := (hM₁ (max M₁ (M₀ g)) (le_max_left _ _)).2
    have e2 := hball g 0 (max M₁ (M₀ g)) (le_max_right _ _)
    have h0 : (fun y : F => fu 0 (w₀ * unipotentGL2 y * g) * (ψ⁻¹ : AddChar F ℂ) y) =
        fun y : F => (f : G → ℂ) (w₀ * unipotentGL2 y * g) * (ψ⁻¹ : AddChar F ℂ) y := by
      funext y
      simp only [hfu, Complex.cpow_zero, mul_one]
    rw [h0] at e2
    rw [hwf g, e1, e2]
    have h3 := hfinsum g 0
    simp only [mul_zero, Complex.cpow_zero, one_mul, mul_one] at h3
    simp only [mul_zero, Complex.cpow_zero, mul_one]
    exact h3.symm

end KcFlatFamily
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_flatSection_jacquetIntegral_eq_finsum_cpow_of_embedding_principalSeries2.KcFlatFamily"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_flatSection_jacquetIntegral_eq_finsum_cpow_of_embedding_principalSeries2.KcFlatFamily"

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction AutomorphicForm in

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (cχ : Fin 2 → ℕ)
    (hcχ : ∀ i, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p (cχ i), χ i u = 1)
    (U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)))
    (hU : IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))))
    (hUK : U ≤ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤)
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w (unipotentGL2 x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g)
    (hwU : ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g)
    (hPS : ∃ Φ : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
      (∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)), ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
        Φ (fun g => v (g * h)) = fun g => Φ v (g * h)) ∧
      (∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)), Φ v = 0 → v = 0) ∧
      (∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)), Φ v ∈ principalSeries2 p χ))
    (w₀ : GL (Fin 2) (p.adicCompletion ℚ))
    (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0]) :
    letI := localBorel ℚ p
    ∀ (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure],
      ∃ (fu : ℂ → GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (χu : ℂ → Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
        (E : ℤ → GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (u₁ : ℝ),

        (∀ (u : ℂ) (a : (p.adicCompletion ℚ)ˣ),
          ((χu u 0 a : ℂˣ) : ℂ) = ((χ 0 a : ℂˣ) : ℂ) * (((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ u)) ∧
        (∀ (u : ℂ) (a : (p.adicCompletion ℚ)ˣ),
          ((χu u 1 a : ℂˣ) : ℂ) = ((χ 1 a : ℂˣ) : ℂ) * (((modulus (a : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (-u))) ∧

        (∀ u : ℂ, fu u ∈ principalSeries2 p (χu u)) ∧
        (∀ u : ℂ, ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), fu u (g * k) = fu u g) ∧

        (∀ i : ℤ, ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), E i (g * k) = E i g) ∧
        (∀ (i : ℤ) (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
          E i (unipotentGL2 x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * E i g) ∧
        (∀ C : Set (GL (Fin 2) (p.adicCompletion ℚ)), IsCompact C →
          {i : ℤ | ∃ g ∈ C, E i g ≠ 0}.Finite) ∧

        (∀ u : ℂ, u₁ < u.re → ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
          Integrable (fun y : p.adicCompletion ℚ =>
            fu u (w₀ * unipotentGL2 y * g) * (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ y) ν ∧
          ∫ y, fu u (w₀ * unipotentGL2 y * g) * (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ y ∂ν =
            ∑ᶠ i : ℤ, (Ideal.absNorm p.asIdeal : ℂ) ^ (-(i : ℂ) * u) * E i g) ∧

        (∀ g : GL (Fin 2) (p.adicCompletion ℚ), w g = ∑ᶠ i : ℤ, E i g) := by
  intro ν _
  exact KcFlatFamily.main p χ cχ hcχ U hU hUK w hwlaw hwU hPS w₀ hw₀ ν

end S_LanglandsTunnell_CubicInduction_exists_flatSection_jacquetIntegral_eq_finsum_cpow_of_embedding_principalSeries2
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_flatSection_jacquetIntegral_eq_finsum_cpow_of_embedding_principalSeries2 (solution)
