-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.godementWhittaker2_symplecticFourier_swap_eq_godementWhittaker2_of_weight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/68b4b33f-7bff-553d-b647-952a39d0feba

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_HaarQuotient
import Theorems.Thm_LanglandsTunnell_TateLocal_integral_symplecticFourier_mul_psiLocal_eq_integral_swap_mul_psiLocal
import Theorems.Thm_LanglandsTunnell_TateLocal_symplecticFourier_comp_rowAction_eq_inv_modulus_det_mul_symplecticFourier
import Theorems.Thm_LanglandsTunnell_TateLocal_isHaarMeasure_comap_val_mulMeasure
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_godementWhittaker2_symplecticFourier_swap_eq_godementWhittaker2_of_weight
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction Filter Topology

open scoped NNReal ENNReal Pointwise

noncomputable section

namespace WG1D2R

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "ψ" => (NumberField.StandardAddChar.psiLocal ℚ p)
local notation "ν" => (selfDualHaarAt ℚ p)
local notation "τ" => (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) :
  Measure (HeightOneSpectrum.adicCompletion ℚ p)ˣ)

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
attribute [local instance] LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem isAddHaarMeasure_sd : (selfDualHaarAt ℚ p).IsAddHaarMeasure := by
  have : selfDualHaarAt ℚ p = Measure.addHaarMeasure (integersPositiveCompacts ℚ p) := by
    unfold selfDualHaarAt
    rw [LanglandsTunnell.TateLocal.addCharLevel_psiLocal_rat p]
    simp
  rw [this]; infer_instance

attribute [local instance] isAddHaarMeasure_sd

theorem borelSpace_units : BorelSpace (F)ˣ := by
  refine ⟨?_⟩
  show MeasurableSpace.comap Units.val (borel F) = borel (F)ˣ
  rw [← borel_comap]
  congr 1
  exact (Units.isEmbedding_val₀ (G₀ := F)).eq_induced.symm

theorem secondCountableTopology_units : SecondCountableTopology (F)ˣ :=
  (Units.isEmbedding_val₀ (G₀ := F)).isInducing.secondCountableTopology

theorem pseudoMetrizableSpace_units : TopologicalSpace.PseudoMetrizableSpace (F)ˣ :=
  (Units.isEmbedding_val₀ (G₀ := F)).isInducing.pseudoMetrizableSpace

theorem locallyCompactSpace_units : LocallyCompactSpace (F)ˣ := by
  refine (⟨Units.isEmbedding_val₀, ?_⟩ : Topology.IsOpenEmbedding (Units.val : (F)ˣ → F)).locallyCompactSpace
  have : Set.range (Units.val : (F)ˣ → F) = {x | x ≠ 0} := by
    ext x
    simp only [Set.mem_range, Set.mem_setOf_eq]
    exact ⟨by rintro ⟨u, rfl⟩; exact u.ne_zero, fun hx => ⟨Units.mk0 x hx, rfl⟩⟩
  rw [this]; exact isOpen_ne

attribute [local instance] borelSpace_units secondCountableTopology_units pseudoMetrizableSpace_units
  locallyCompactSpace_units

theorem isHaarMeasure_tau : (τ).IsHaarMeasure :=
  LanglandsTunnell.TateLocal.isHaarMeasure_comap_val_mulMeasure ℚ p (selfDualHaarAt ℚ p)

attribute [local instance] isHaarMeasure_tau

theorem integral_comp_inv_mul (d : (F)ˣ) (H : (F)ˣ → ℂ) :
    ∫ t : (F)ˣ, H ((d * t)⁻¹) ∂τ = ∫ t : (F)ˣ, H t ∂τ := by
  have h1 := integral_mul_left_eq_self (μ := τ) (fun t : (F)ˣ => H t⁻¹) d
  have h2 := integral_inv_eq_self (fun t : (F)ˣ => H t) τ
  rw [h1, h2]

theorem coe_modulus_eq_norm (x : F) : ((modulus x : ℝ≥0) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p x, coe_nnnorm]

theorem smul_set_eq_preimage {c : F} (hc : c ≠ 0) (T : Set F) :
    c • T = (fun y => c⁻¹ * y) ⁻¹' T := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [smul_eq_mul, inv_mul_cancel_left₀ hc] using hy
  · intro hx
    exact ⟨c⁻¹ * x, hx, by simp [smul_eq_mul, mul_inv_cancel_left₀ hc]⟩

theorem map_mul_left_eq_smul (u : (F)ˣ) :
    (ν).map (fun x : F => (u : F) * x) = ((modulus (u : F) : ℝ≥0∞))⁻¹ • ν := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply (measurable_const_mul _) hs, Measure.smul_apply, smul_eq_mul]
  have hpre : (fun x : F => (u : F) * x) ⁻¹' s = ((u⁻¹ : (F)ˣ) : F) • s := by
    rw [smul_set_eq_preimage p (u⁻¹).ne_zero, Units.val_inv_eq_inv_val, inv_inv]
  rw [hpre]
  have h := distribHaarChar_mul ν (u⁻¹) s
  rw [show ((u⁻¹ : (F)ˣ) • s : Set F) = ((u⁻¹ : (F)ˣ) : F) • s from rfl] at h
  rw [← h, map_inv, modulus_coe_units, ENNReal.coe_inv (distribHaarChar_pos).ne']

theorem integral_comp_units_mul (u : (F)ˣ) (g : F → ℂ) :
    ∫ x, g ((u : F) * x) ∂ν = ((‖(u : F)‖⁻¹ : ℝ) : ℂ) * ∫ x, g x ∂ν := by
  have h1 : ∫ x, g ((u : F) * x) ∂ν = ∫ y, g y ∂((ν).map fun x : F => (u : F) * x) :=
    (integral_map_equiv (Homeomorph.mulLeft₀ (u : F) u.ne_zero).toMeasurableEquiv g).symm
  rw [h1, map_mul_left_eq_smul p u, integral_smul_measure, ENNReal.toReal_inv, ENNReal.coe_toReal,
    coe_modulus_eq_norm, Complex.real_smul]

variable (g : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

def rho (Φ : (Fin 2 → F) → ℂ) : (Fin 2 → F) → ℂ :=
  fun u => Φ (fun j : Fin 2 => u 0 * (g : Matrix (Fin 2) (Fin 2) F) 0 j + u 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 j)

def sharp (Φ : (Fin 2 → F) → ℂ) : (Fin 2 → F) → ℂ :=
  fun v => ∫ u : Fin 2 → F, Φ u * ψ (u 1 * v 0 - u 0 * v 1) ∂(Measure.pi fun _ : Fin 2 => ν)

def inner (X : (Fin 2 → F) → ℂ) (s : F) : ℂ :=
  ∫ y : F, X (fun j : Fin 2 => s * (g : Matrix (Fin 2) (Fin 2) F) 0 j + y * (g : Matrix (Fin 2) (Fin 2) F) 1 j) *
    ψ (s⁻¹ * y) ∂ν

def rowHomeo : (Fin 2 → F) ≃ₜ (Fin 2 → F) where
  toFun u := Matrix.vecMul u (g : Matrix (Fin 2) (Fin 2) F)
  invFun w := Matrix.vecMul w ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
  left_inv u := by
    show Matrix.vecMul (Matrix.vecMul u (g : Matrix (Fin 2) (Fin 2) F)) ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = u
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  right_inv w := by
    show Matrix.vecMul (Matrix.vecMul w ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) (g : Matrix (Fin 2) (Fin 2) F) = w
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one]
  continuous_toFun := continuous_id.matrix_vecMul continuous_const
  continuous_invFun := continuous_id.matrix_vecMul continuous_const

theorem rho_eq_comp (Φ : (Fin 2 → F) → ℂ) : rho p g Φ = Φ ∘ (rowHomeo p g) := by
  funext u
  show Φ _ = Φ (Matrix.vecMul u (g : Matrix (Fin 2) (Fin 2) F))
  congr 1
  funext j
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem rho_lc_cs (Φ : (Fin 2 → F) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ) :
    IsLocallyConstant (rho p g Φ) ∧ HasCompactSupport (rho p g Φ) := by
  rw [rho_eq_comp]
  exact ⟨hΦ.1.comp_continuous (rowHomeo p g).continuous, hΦ.2.comp_homeomorph (rowHomeo p g)⟩

theorem inner_eq (Φ : (Fin 2 → F) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ) (t : (F)ˣ) :
    inner p g Φ (t : F) =
      inner p g (sharp p Φ) (((Matrix.GeneralLinearGroup.det g * t)⁻¹ : (F)ˣ) : F) := by
  set d : (F)ˣ := Matrix.GeneralLinearGroup.det g with hd
  have hd0 : (d : F) ≠ 0 := d.ne_zero
  have ht0 : (t : F) ≠ 0 := t.ne_zero
  have hmod : (((modulus (d : F) : ℝ) : ℂ))⁻¹ * ((‖(d : F)‖ : ℝ) : ℂ) = 1 := by
    rw [coe_modulus_eq_norm]
    exact inv_mul_cancel₀ (by exact_mod_cast norm_ne_zero_iff.mpr hd0)

  have ha : inner p g Φ (t : F) = ∫ y : F, rho p g Φ ![(t : F), y] * ψ ((t : F)⁻¹ * y) ∂ν := by
    simp only [inner, rho, Matrix.cons_val_zero, Matrix.cons_val_one]

  have hb := LanglandsTunnell.TateLocal.integral_symplecticFourier_mul_psiLocal_eq_integral_swap_mul_psiLocal p
    (rho p g Φ) (rho_lc_cs p g Φ hΦ) ((t : F)⁻¹) (t : F)
  rw [ha, ← hb]

  have hc : ∀ y : F,
      (fun v : Fin 2 → F => ∫ u : Fin 2 → F, rho p g Φ u * ψ (u 1 * v 0 - u 0 * v 1)
          ∂(Measure.pi fun _ : Fin 2 => ν)) ![(t : F)⁻¹, y] * ψ ((t : F) * y) =
        (((modulus (d : F) : ℝ) : ℂ))⁻¹ *
          (sharp p Φ (fun j : Fin 2 => ((d : F)⁻¹ * (t : F)⁻¹) * (g : Matrix (Fin 2) (Fin 2) F) 0 j + ((d : F)⁻¹ * y) * (g : Matrix (Fin 2) (Fin 2) F) 1 j) *
            ψ ((t : F) * y)) := by
    intro y
    have he := LanglandsTunnell.TateLocal.symplecticFourier_comp_rowAction_eq_inv_modulus_det_mul_symplecticFourier p
      Φ hΦ g ![(t : F)⁻¹, y]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at he
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, rho, sharp]
    rw [← hd] at he
    rw [he]
    have e0 : (d : F)⁻¹ * ((t : F)⁻¹ * (g : Matrix (Fin 2) (Fin 2) F) 0 0 + y * (g : Matrix (Fin 2) (Fin 2) F) 1 0) =
        ((d : F)⁻¹ * (t : F)⁻¹) * (g : Matrix (Fin 2) (Fin 2) F) 0 0 + ((d : F)⁻¹ * y) * (g : Matrix (Fin 2) (Fin 2) F) 1 0 := by ring
    have e1 : (d : F)⁻¹ * ((t : F)⁻¹ * (g : Matrix (Fin 2) (Fin 2) F) 0 1 + y * (g : Matrix (Fin 2) (Fin 2) F) 1 1) =
        ((d : F)⁻¹ * (t : F)⁻¹) * (g : Matrix (Fin 2) (Fin 2) F) 0 1 + ((d : F)⁻¹ * y) * (g : Matrix (Fin 2) (Fin 2) F) 1 1 := by ring
    rw [e0, e1]
    ring
  rw [integral_congr_ae (ae_of_all _ hc), integral_const_mul]

  have hdil := integral_comp_units_mul p d⁻¹
    (fun y : F => sharp p Φ (fun j : Fin 2 => ((d : F)⁻¹ * (t : F)⁻¹) * (g : Matrix (Fin 2) (Fin 2) F) 0 j + y * (g : Matrix (Fin 2) (Fin 2) F) 1 j) *
      ψ (((t : F) * (d : F)) * y))
  rw [Units.val_inv_eq_inv_val, norm_inv, inv_inv] at hdil
  have hfun : ∀ y : F,
      sharp p Φ (fun j : Fin 2 => ((d : F)⁻¹ * (t : F)⁻¹) * (g : Matrix (Fin 2) (Fin 2) F) 0 j + ((d : F)⁻¹ * y) * (g : Matrix (Fin 2) (Fin 2) F) 1 j) * ψ ((t : F) * y) =
        (fun y : F => sharp p Φ (fun j : Fin 2 => ((d : F)⁻¹ * (t : F)⁻¹) * (g : Matrix (Fin 2) (Fin 2) F) 0 j + y * (g : Matrix (Fin 2) (Fin 2) F) 1 j) *
          ψ (((t : F) * (d : F)) * y)) ((d : F)⁻¹ * y) := by
    intro y
    simp only
    rw [show (t : F) * (d : F) * ((d : F)⁻¹ * y) = (t : F) * y by
      rw [← mul_assoc, mul_assoc (t : F), mul_inv_cancel₀ hd0, mul_one]]
  rw [integral_congr_ae (ae_of_all _ hfun), hdil, ← mul_assoc, hmod, one_mul]

  have h1 : ((d : F) * (t : F))⁻¹ = (d : F)⁻¹ * (t : F)⁻¹ := by rw [mul_inv]
  have h2 : (((d : F) * (t : F))⁻¹)⁻¹ = (t : F) * (d : F) := by rw [inv_inv, mul_comm]
  simp only [inner, Units.val_inv_eq_inv_val, Units.val_mul]
  rw [h2, h1]

theorem main (χ : Fin 2 → ((F)ˣ →* ℂˣ)) (Φ : (Fin 2 → F) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (c : WithZero (Multiplicative ℤ) → ℂ) :
    ((χ 1 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
        ((modulus ((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
      ∫ t : (F)ˣ, c (Valued.v (t : F) * Valued.v ((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F)) *
          inner p g (sharp p Φ) (t : F) * ((χ 1 t : ℂˣ) : ℂ) * (((χ 0 t : ℂˣ) : ℂ))⁻¹ ∂τ =
    ((χ 0 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
        ((modulus ((Matrix.GeneralLinearGroup.det g : (F)ˣ) : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
      ∫ t : (F)ˣ, c (Valued.v (t : F))⁻¹ *
          inner p g Φ (t : F) * ((χ 0 t : ℂˣ) : ℂ) * (((χ 1 t : ℂˣ) : ℂ))⁻¹ ∂τ := by
  set d : (F)ˣ := Matrix.GeneralLinearGroup.det g with hd
  have hinv : ∀ t : (F)ˣ, (d * (d * t)⁻¹)⁻¹ = t := fun t => by
    rw [mul_inv_rev, inv_inv, mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]

  have hR : ∀ t : (F)ˣ, c (Valued.v (t : F))⁻¹ * inner p g Φ (t : F) * ((χ 0 t : ℂˣ) : ℂ) * (((χ 1 t : ℂˣ) : ℂ))⁻¹ =
      c (Valued.v (t : F))⁻¹ * inner p g (sharp p Φ) (((d * t)⁻¹ : (F)ˣ) : F) * ((χ 0 t : ℂˣ) : ℂ) *
        (((χ 1 t : ℂˣ) : ℂ))⁻¹ := by
    intro t; rw [inner_eq p g Φ hΦ t]
  rw [integral_congr_ae (ae_of_all _ hR)]

  have hsub := integral_comp_inv_mul p d (fun s : (F)ˣ =>
    c (Valued.v (((d * s)⁻¹ : (F)ˣ) : F))⁻¹ * inner p g (sharp p Φ) (s : F) *
      ((χ 0 ((d * s)⁻¹) : ℂˣ) : ℂ) * (((χ 1 ((d * s)⁻¹) : ℂˣ) : ℂ))⁻¹)
  simp only [hinv] at hsub
  rw [hsub, ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  dsimp only
  have hv : (Valued.v (((d * s)⁻¹ : (F)ˣ) : F))⁻¹ = Valued.v (s : F) * Valued.v (d : F) := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, inv_inv, Units.val_mul, map_mul, mul_comm]
  rw [hv, map_inv, map_mul, map_inv, map_mul]
  simp only [Units.val_inv_eq_inv_val, Units.val_mul, mul_inv, inv_inv]
  have h0 : ((χ 0 d : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have h0s : ((χ 0 s : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have h1s : ((χ 1 s : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp

end WG1D2R

end

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction in

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hχ : ∀ i, IsLocallyConstant (χ i))
    (Φ : (Fin 2 → p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (c : WithZero (Multiplicative ℤ) → ℂ)
    (g : GL (Fin 2) (p.adicCompletion ℚ)) :
    letI := localBorel ℚ p
    ((χ 1 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
          ∫ t : (p.adicCompletion ℚ)ˣ,
            c (Valued.v (t : p.adicCompletion ℚ) * Valued.v ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ)) *
              (∫ y : p.adicCompletion ℚ, (fun v : Fin 2 → p.adicCompletion ℚ =>
              ∫ u : Fin 2 → p.adicCompletion ℚ, Φ u * NumberField.StandardAddChar.psiLocal ℚ p (u 1 * v 0 - u 0 * v 1)
                ∂(Measure.pi fun _ : Fin 2 => selfDualHaarAt ℚ p)) (fun j : Fin 2 => (t : p.adicCompletion ℚ) * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 j + y * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j) *
                  NumberField.StandardAddChar.psiLocal ℚ p ((t : p.adicCompletion ℚ)⁻¹ * y) ∂(selfDualHaarAt ℚ p)) *
              ((χ 1 t : ℂˣ) : ℂ) * (((χ 0 t : ℂˣ) : ℂ))⁻¹ ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) =
      ((χ 0 (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
          ∫ t : (p.adicCompletion ℚ)ˣ,
            c (Valued.v (t : p.adicCompletion ℚ))⁻¹ *
              (∫ y : p.adicCompletion ℚ, Φ (fun j : Fin 2 => (t : p.adicCompletion ℚ) * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 j + y * (g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 j) *
                  NumberField.StandardAddChar.psiLocal ℚ p ((t : p.adicCompletion ℚ)⁻¹ * y) ∂(selfDualHaarAt ℚ p)) *
              ((χ 0 t : ℂˣ) : ℂ) * (((χ 1 t : ℂˣ) : ℂ))⁻¹ ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) := by
  letI := localBorel ℚ p
  exact WG1D2R.main p g χ Φ hΦ c

end S_LanglandsTunnell_CubicInduction_godementWhittaker2_symplecticFourier_swap_eq_godementWhittaker2_of_weight
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_godementWhittaker2_symplecticFourier_swap_eq_godementWhittaker2_of_weight (solution)
