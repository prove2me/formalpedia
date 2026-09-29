-- Prove2me | solution 1 for NumberField.AdelicFourier.tsum_apply_smul_vecMul_add_eq_ideleNorm_cpow_neg_two_mul_tsum_reflectPair_of_mem_schwartzBruhat2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/557b80cd-bdcf-5a96-b83d-63214cf5fbad

import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_NumberField_AdelicFourier_tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_of_mem_schwartzBruhat2
import Theorems.Thm_NumberField_AdelicFourier_addHaar_image_vecMul_eq_ideleNorm_det_mul_and_fourierTransform2_comp_vecMul
import Theorems.Thm_NumberField_AdelicFourier_continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_tsum_apply_smul_vecMul_add_eq_ideleNorm_cpow_neg_two_mul_tsum_reflectPair_of_mem_schwartzBruhat2
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply ContinuousAddEquiv.preimage_mulLeft_smul IsModuleTopology.continuousLinearEquiv_apply"
p2m_attr_erase "simp" "AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply"

set_option autoImplicit false

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_AdelicFourier_tsum_apply_smul_vecMul_add_eq_ideleNorm_cpow_neg_two_mul_tsum_reflectPair_of_mem_schwartzBruhat2.NumberField NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_tsum_apply_smul_vecMul_add_eq_ideleNorm_cpow_neg_two_mul_tsum_reflectPair_of_mem_schwartzBruhat2.NumberField.AdelicFourier NumberField.AdelicBox NumberField.TateGlobal AutomorphicForm IsDedekindDomain"

noncomputable section

namespace NumberField
p2m_export "NumberField" "AdeleRing AdelicFourier.tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_of_mem_schwartzBruhat2 AdelicFourier.addHaar_image_vecMul_eq_ideleNorm_det_mul_and_fourierTransform2_comp_vecMul AdelicFourier.continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2"
namespace AdelicFourier
p2m_export "NumberField.AdelicFourier" "schwartzBruhat2 fourierTransform2 reflectPair tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_of_mem_schwartzBruhat2 addHaar_image_vecMul_eq_ideleNorm_det_mul_and_fourierTransform2_comp_vecMul continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2"
namespace ThetaInvSol
p2m_open "NumberField.AdelicFourier NumberField"

variable {F : Type} [Field F] [NumberField F]

section LinAlg

variable {R : Type*} [CommRing R]

def wP : Matrix (Fin 2) (Fin 2) R := !![0, 1; -1, 0]

def wPinv : Matrix (Fin 2) (Fin 2) R := !![0, -1; 1, 0]

theorem vecMul_wPinv (x : Fin 2 → R) : Matrix.vecMul x wPinv = ![x 1, -x 0] := by
  funext i
  fin_cases i <;> simp [wPinv, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem vecMul_wP (x : Fin 2 → R) : Matrix.vecMul x wP = ![-x 1, x 0] := by
  funext i
  fin_cases i <;> simp [wP, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem mulVec_vecMul_wP_wPinv (M : Matrix (Fin 2) (Fin 2) R) (y : Fin 2 → R) :
    Matrix.mulVec M (Matrix.vecMul (Matrix.vecMul (Matrix.vecMul y wP) M) wPinv) = M.det • y := by
  rw [vecMul_wP, vecMul_wPinv, Matrix.det_fin_two]
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Matrix.vecMul, Fin.sum_univ_two] <;> ring

theorem scalar_mulVec (r : R) (v : Fin 2 → R) : Matrix.mulVec (Matrix.scalar (Fin 2) r) v = r • v := by
  funext i
  rw [Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]

theorem mulVec_inv_scalar_mul (t : Rˣ) (g : GL (Fin 2) R) (y : Fin 2 → R) :
    Matrix.mulVec (((Matrix.GeneralLinearGroup.scalar (Fin 2) t * g)⁻¹ : GL (Fin 2) R) :
        Matrix (Fin 2) (Fin 2) R) y
      = ((t⁻¹ * (Matrix.GeneralLinearGroup.det g)⁻¹ : Rˣ) : R) •
          Matrix.vecMul (Matrix.vecMul (Matrix.vecMul y wP) (g : Matrix (Fin 2) (Fin 2) R)) wPinv := by
  set u : GL (Fin 2) R := Matrix.GeneralLinearGroup.scalar (Fin 2) t * g with hu
  set c : Rˣ := t⁻¹ * (Matrix.GeneralLinearGroup.det g)⁻¹ with hc
  set v : Fin 2 → R :=
    Matrix.vecMul (Matrix.vecMul (Matrix.vecMul y wP) (g : Matrix (Fin 2) (Fin 2) R)) wPinv with hv

  have hcoe : ((Matrix.GeneralLinearGroup.scalar (Fin 2) t : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
      = Matrix.scalar (Fin 2) (t : R) := rfl
  have key : Matrix.mulVec (u : Matrix (Fin 2) (Fin 2) R) ((c : R) • v) = y := by
    rw [hu, Matrix.GeneralLinearGroup.coe_mul, hcoe, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec,
      hv, mulVec_vecMul_wP_wPinv, ← Matrix.GeneralLinearGroup.val_det_apply, Matrix.mulVec_smul,
      scalar_mulVec, smul_smul, smul_smul]
    have h1 : (c : R) * ((Matrix.GeneralLinearGroup.det g : Rˣ) : R) * (t : R) = 1 := by
      rw [← Units.val_mul, ← Units.val_mul, hc, inv_mul_cancel_right, inv_mul_cancel, Units.val_one]
    rw [h1, one_smul]
  calc Matrix.mulVec ((u⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) y
      = Matrix.mulVec ((u⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
          (Matrix.mulVec (u : Matrix (Fin 2) (Fin 2) R) ((c : R) • v)) := by rw [key]
    _ = Matrix.mulVec (((u⁻¹ * u : GL (Fin 2) R)) : Matrix (Fin 2) (Fin 2) R) ((c : R) • v) := by
        rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul]
    _ = (c : R) • v := by rw [inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem vecMul_scalar_mul (t : Rˣ) (g : GL (Fin 2) R) (x : Fin 2 → R) :
    Matrix.vecMul x ((Matrix.GeneralLinearGroup.scalar (Fin 2) t * g : GL (Fin 2) R) :
        Matrix (Fin 2) (Fin 2) R)
      = (t : R) • Matrix.vecMul x (g : Matrix (Fin 2) (Fin 2) R) := by
  have hcoe : ((Matrix.GeneralLinearGroup.scalar (Fin 2) t : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
      = Matrix.scalar (Fin 2) (t : R) := rfl
  rw [Matrix.GeneralLinearGroup.coe_mul, hcoe, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul,
    Matrix.vecMul_smul]

theorem det_scalar_mul (t : Rˣ) (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) t * g)
      = t * t * Matrix.GeneralLinearGroup.det g := by
  rw [map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, pow_two]

end LinAlg

def ι (ξ : Fin 2 → F) : Fin 2 → AdeleRing (𝓞 F) F := fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)

theorem ι_zero : ι (0 : Fin 2 → F) = 0 := by
  funext i; simp [ι]

def reindex : (Fin 2 → F) ≃ (Fin 2 → F) where
  toFun ξ := ![-ξ 1, ξ 0]
  invFun ξ := ![ξ 1, -ξ 0]
  left_inv ξ := by funext i; fin_cases i <;> simp
  right_inv ξ := by funext i; fin_cases i <;> simp

theorem vecMul_ι_wP (ξ : Fin 2 → F) : Matrix.vecMul (ι ξ) wP = ι (reindex ξ) := by
  rw [vecMul_wP]
  funext i
  fin_cases i <;> simp [ι, reindex, map_neg]

theorem reflectPair_eq [MeasurableSpace (AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (μ₁ : Measure (AdeleRing (𝓞 F) F)) (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ)
    (x : Fin 2 → AdeleRing (𝓞 F) F) :
    fourierTransform2 ψ μ₁ Φ (Matrix.vecMul x wPinv) = reflectPair ψ μ₁ Φ x := by
  rw [vecMul_wPinv]
  rfl

omit [NumberField F] in
theorem tsum_ne_zero_add {f : (Fin 2 → F) → ℂ} (hf : Summable f) :
    ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, f ξ.1 + f 0 = ∑' ξ, f ξ := by
  classical
  rw [hf.tsum_eq_add_tsum_ite 0, add_comm]
  congr 1
  rw [show (∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, f ξ.1) = ∑' ξ : ({ξ | ξ ≠ 0} : Set (Fin 2 → F)), f ξ
      from rfl, tsum_subtype]
  refine tsum_congr fun ξ => ?_
  by_cases h : ξ = 0
  · rw [if_pos h, Set.indicator_of_notMem (by simpa using h)]
  · rw [if_neg h, Set.indicator_of_mem (by simpa using h)]

end NumberField.AdelicFourier.ThetaInvSol

end

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_AdelicFourier_tsum_apply_smul_vecMul_add_eq_ideleNorm_cpow_neg_two_mul_tsum_reflectPair_of_mem_schwartzBruhat2.NumberField NumberField.AdelicFourier P2MW.S_NumberField_AdelicFourier_tsum_apply_smul_vecMul_add_eq_ideleNorm_cpow_neg_two_mul_tsum_reflectPair_of_mem_schwartzBruhat2.NumberField.AdelicFourier NumberField.AdelicBox NumberField.TateGlobal AutomorphicForm IsDedekindDomain"

open NumberField.AdelicFourier.ThetaInvSol in

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ₁ : Measure (AdeleRing (𝓞 F) F)) [μ₁.IsAddHaarMeasure] (hμ₁ : μ₁ (adelicBox F) = 1)
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F)
    (g : AdelicGL2 (𝓞 F) F) (t : (AdeleRing (𝓞 F) F)ˣ) :
    ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
        Φ ((t : AdeleRing (𝓞 F) F) •
          Matrix.vecMul (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 i))
            (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
      + Φ 0 =
    ((ideleNorm F t : ℝ) : ℂ) ^ (-(2 : ℂ)) *
      ((((ideleNorm F (Matrix.GeneralLinearGroup.det g))⁻¹ : ℝ) : ℂ) *
          ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
            reflectPair ψ μ₁ Φ (((t⁻¹ * (Matrix.GeneralLinearGroup.det g)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) :
                AdeleRing (𝓞 F) F) •
              Matrix.vecMul (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 i))
                (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
        + (((ideleNorm F (Matrix.GeneralLinearGroup.det g))⁻¹ : ℝ) : ℂ) * reflectPair ψ μ₁ Φ 0) := by

  set g' : AdelicGL2 (𝓞 F) F := Matrix.GeneralLinearGroup.scalar (Fin 2) t * g with hg'
  set D : (AdeleRing (𝓞 F) F)ˣ := Matrix.GeneralLinearGroup.det g with hD
  set c : (AdeleRing (𝓞 F) F)ˣ := t⁻¹ * D⁻¹ with hc
  set Ψ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ :=
    fun x => Φ (Matrix.vecMul x (g' : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) with hΨ
  have hΨmem : Ψ ∈ schwartzBruhat2 F :=
    (NumberField.AdelicFourier.continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
      F Φ hΦ).2.2.2.2.1 g'

  obtain ⟨hsΨ, hsΨhat, hpoisson⟩ :=
    NumberField.AdelicFourier.tsum_eq_inv_measure_sq_mul_tsum_fourierTransform2_of_mem_schwartzBruhat2
      F μ₁ hψ hΨmem
  have hbox : (((μ₁ (adelicBox F)).toReal : ℂ) ^ 2)⁻¹ = 1 := by
    rw [hμ₁, ENNReal.toReal_one, Complex.ofReal_one, one_pow, inv_one]
  rw [hbox, one_mul] at hpoisson

  set L : (Fin 2 → F) → ℂ := fun η =>
    reflectPair ψ μ₁ Φ ((c : AdeleRing (𝓞 F) F) •
      Matrix.vecMul (ι η) (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) with hL
  set K : ℂ := (((ideleNorm F (Matrix.GeneralLinearGroup.det g'))⁻¹ : ℝ) : ℂ) with hK
  have hhat : ∀ ξ : Fin 2 → F, fourierTransform2 ψ μ₁ Ψ (ι ξ) = K * L (reindex ξ) := by
    intro ξ
    have h4 := (NumberField.AdelicFourier.addHaar_image_vecMul_eq_ideleNorm_det_mul_and_fourierTransform2_comp_vecMul
      F g').2.2.2 μ₁ ψ Φ (ι ξ)
    rw [hΨ, h4, hK, hL, hg', mulVec_inv_scalar_mul, ← hD, ← hc, ← Matrix.smul_vecMul, reflectPair_eq,
      vecMul_ι_wP]

  have hKval : K = ((ideleNorm F t : ℝ) : ℂ) ^ (-(2 : ℂ)) * (((ideleNorm F D)⁻¹ : ℝ) : ℂ) := by
    rw [hK, hg', det_scalar_mul, ← hD, ideleNorm_mul, ideleNorm_mul,
      show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_neg, Complex.cpow_natCast]
    have ht : (ideleNorm F t : ℂ) ≠ 0 := by exact_mod_cast (ideleNorm_pos t).ne'
    have hd : (ideleNorm F D : ℂ) ≠ 0 := by exact_mod_cast (ideleNorm_pos D).ne'
    push_cast
    field_simp
  have hK0 : K ≠ 0 := by
    rw [hK]
    exact_mod_cast (inv_pos.2 (ideleNorm_pos _)).ne'

  have hsL : Summable L := by
    have h1 : Summable fun ξ : Fin 2 → F => K * L (reindex ξ) := by
      refine hsΨhat.congr fun ξ => ?_
      exact hhat ξ
    have h2 : Summable fun ξ : Fin 2 → F => L (reindex ξ) := (summable_mul_left_iff hK0).1 h1
    exact (Equiv.summable_iff reindex (f := L)).1 h2

  have hΨι : ∀ ξ : Fin 2 → F, Ψ (ι ξ) = Φ ((t : AdeleRing (𝓞 F) F) •
      Matrix.vecMul (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))
        (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) := by
    intro ξ
    rw [hΨ, hg']
    show Φ (Matrix.vecMul (ι ξ) _) = _
    rw [vecMul_scalar_mul]
    rfl
  have hΨ0 : Ψ (ι 0) = Φ 0 := by
    rw [hΨι, show (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((0 : Fin 2 → F) i)) = ι 0 from rfl, ι_zero,
      Matrix.zero_vecMul, smul_zero]
  have hL0 : L 0 = reflectPair ψ μ₁ Φ 0 := by
    rw [hL]
    show reflectPair ψ μ₁ Φ ((c : AdeleRing (𝓞 F) F) • Matrix.vecMul (ι 0) _) = _
    rw [ι_zero, Matrix.zero_vecMul, smul_zero]
  have lhs : ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
        Φ ((t : AdeleRing (𝓞 F) F) •
          Matrix.vecMul (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 i))
            (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
      + Φ 0 = ∑' ξ : Fin 2 → F, Ψ (ι ξ) := by
    rw [← hΨ0, ← tsum_ne_zero_add (f := fun ξ => Ψ (ι ξ)) hsΨ]
    congr 1
    exact tsum_congr fun ξ => (hΨι ξ.1).symm

  have rhs : ((ideleNorm F t : ℝ) : ℂ) ^ (-(2 : ℂ)) *
      ((((ideleNorm F D)⁻¹ : ℝ) : ℂ) *
          ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
            reflectPair ψ μ₁ Φ ((c : AdeleRing (𝓞 F) F) •
              Matrix.vecMul (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 i))
                (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
        + (((ideleNorm F D)⁻¹ : ℝ) : ℂ) * reflectPair ψ μ₁ Φ 0)
      = ∑' ξ : Fin 2 → F, fourierTransform2 ψ μ₁ Ψ (ι ξ) := by
    rw [← mul_add, ← mul_assoc, ← hKval, ← hL0,
      show (∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
            reflectPair ψ μ₁ Φ ((c : AdeleRing (𝓞 F) F) •
              Matrix.vecMul (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 i))
                (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))))
          = ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, L ξ.1 from rfl,
      tsum_ne_zero_add hsL, ← Equiv.tsum_eq reindex L, ← tsum_mul_left]
    exact tsum_congr fun ξ => (hhat ξ).symm
  rw [lhs, rhs]
  exact hpoisson

end S_NumberField_AdelicFourier_tsum_apply_smul_vecMul_add_eq_ideleNorm_cpow_neg_two_mul_tsum_reflectPair_of_mem_schwartzBruhat2
end P2MW
export P2MW.S_NumberField_AdelicFourier_tsum_apply_smul_vecMul_add_eq_ideleNorm_cpow_neg_two_mul_tsum_reflectPair_of_mem_schwartzBruhat2 (solution)
