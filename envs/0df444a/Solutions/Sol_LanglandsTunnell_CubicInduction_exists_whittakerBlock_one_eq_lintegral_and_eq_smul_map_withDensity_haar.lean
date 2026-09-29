-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_whittakerBlock_one_eq_lintegral_and_eq_smul_map_withDensity_haar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/112bdf61-57d1-5027-9a56-cfe26cc9f8f0

import Definitions.Def_LanglandsTunnell_CubicInduction_WhittakerBlock
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdelicFourier_isLocallyConstant_and_hasCompactSupport_prod_mul_ite_forall_mem_adicCompletionIntegers
import Theorems.Thm_WhittakerBlock_isHaarMeasure_unipotentHaar3
import Theorems.Thm_WhittakerBlock_isMulRightInvariant_unipotentHaar3
import Theorems.Thm_HaarQuotient_lintegral_density_mul_eq_one
import Theorems.Thm_LanglandsTunnell_CubicInduction_whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_whittakerBlock_one_eq_lintegral_and_eq_smul_map_withDensity_haar
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory LanglandsTunnell.CubicInduction.SlabL2
open scoped ENNReal InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel

open LanglandsTunnell.CubicInduction

noncomputable section

namespace Fibration

section Furniture

private def bottomRow (g : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ) : Fin 3 → AdeleRing (𝓞 ℚ) ℚ :=
  fun j => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j

private theorem bottomRow_mul (g h : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ) :
    bottomRow (g * h) = fun j => ∑ k, bottomRow g k * (h : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) k j := by
  funext j
  simp [bottomRow, Units.val_mul, Matrix.mul_apply]

private def e₃ : Fin 3 → AdeleRing (𝓞 ℚ) ℚ := fun j => if j = 2 then 1 else 0

private theorem bottomRow_one : bottomRow (1 : LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ) = e₃ := by
  funext j
  simp [bottomRow, e₃, Matrix.one_apply, eq_comm]

private def mirabolic : Subgroup (LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ) where
  carrier := {g | bottomRow g = e₃}
  one_mem' := bottomRow_one
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_setOf_eq] at hg hh ⊢
    rw [bottomRow_mul, hg]
    funext j
    have := congrFun hh j
    simp only [bottomRow] at this
    simp [e₃, this]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_setOf_eq] at hg ⊢
    have h1 : bottomRow (g * g⁻¹) = e₃ := by rw [mul_inv_cancel, bottomRow_one]
    rw [bottomRow_mul, hg] at h1
    funext j
    have := congrFun h1 j
    simpa [e₃, Fin.sum_univ_three, bottomRow] using this

private theorem continuous_bottomRow : Continuous bottomRow := by
  refine continuous_pi fun j => ?_
  exact (continuous_apply j).comp ((continuous_apply (2 : Fin 3)).comp
    (Units.continuous_val (M := Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))))

private theorem isClosed_mirabolic :
    IsClosed ((mirabolic : Subgroup (LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ)) :
      Set (LanglandsTunnell.CubicInduction.AdelicGL 3 (𝓞 ℚ) ℚ)) :=
  isClosed_singleton.preimage continuous_bottomRow

end Furniture

section RowSets

attribute [local instance] NumberField.AdelicHaar.adeleBorel

private abbrev evalHom (q : HeightOneSpectrum (𝓞 ℚ)) : AdeleRing (𝓞 ℚ) ℚ →+* q.adicCompletion ℚ :=
  (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ q).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)

private def PrimitiveAt (p : HeightOneSpectrum (𝓞 ℚ)) (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) : Prop :=
  (∀ j, evalHom p (x j) ∈ p.adicCompletionIntegers ℚ) ∧ ∃ j, Valued.v (evalHom p (x j)) = 1

private def NonzeroAt (p : HeightOneSpectrum (𝓞 ℚ)) (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) : Prop :=
  ∃ j, evalHom p (x j) ≠ 0

private def NonzeroArch (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) : Prop :=
  ∃ j, AdelicLevel.adeleArch (𝓞 ℚ) ℚ (x j) ≠ 0

private def explicitRows (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Set (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) :=
  {x | (∀ p, p ∉ S → PrimitiveAt p x) ∧ (∀ p ∈ S, NonzeroAt p x) ∧ NonzeroArch x}

private def rowDomain : Set (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) :=
  {x | (∀ p, NonzeroAt p x) ∧ NonzeroArch x ∧ ∀ᶠ p in Filter.cofinite, PrimitiveAt p x}

private abbrev rowHaar : Measure (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) :=
  Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ

end RowSets

section DeviceIdentities

section DeviceAlgebra

private theorem bottomRow_mul_eq_vecMul (g h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    bottomRow (g * h) = bottomRow g ᵥ* (h : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) := by
  rw [bottomRow_mul]
  funext j
  simp [Matrix.vecMul, dotProduct]

private theorem e₃_vecMul (h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    e₃ ᵥ* (h : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = bottomRow h := by
  funext j
  simp [e₃, Matrix.vecMul, dotProduct, bottomRow]

private theorem bottomRow_mul_of_mem {p : AdelicGL 3 (𝓞 ℚ) ℚ} (hp : p ∈ mirabolic)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) : bottomRow (p * g) = bottomRow g := by
  rw [bottomRow_mul_eq_vecMul, show bottomRow p = e₃ from hp, e₃_vecMul]

private theorem mul_inv_mem_mirabolic_iff (a b : AdelicGL 3 (𝓞 ℚ) ℚ) :
    a * b⁻¹ ∈ mirabolic ↔ bottomRow a = bottomRow b := by
  constructor
  · intro h
    have := bottomRow_mul_of_mem h b
    rwa [inv_mul_cancel_right] at this
  · intro h
    show bottomRow (a * b⁻¹) = e₃
    rw [bottomRow_mul_eq_vecMul, h, ← e₃_vecMul b, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.vecMul_one]

private def modulus (g : AdelicGL 3 (𝓞 ℚ) ℚ) : ℝ≥0∞ :=
  ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g))

private theorem modulus_pos (g : AdelicGL 3 (𝓞 ℚ) ℚ) : 0 < modulus g :=
  ENNReal.ofReal_pos.2 (NumberField.TateGlobal.ideleNorm_pos _)

private theorem modulus_ne_zero (g : AdelicGL 3 (𝓞 ℚ) ℚ) : modulus g ≠ 0 :=
  (modulus_pos g).ne'

private theorem modulus_ne_top (g : AdelicGL 3 (𝓞 ℚ) ℚ) : modulus g ≠ ⊤ :=
  ENNReal.ofReal_ne_top

private theorem modulus_mul (g h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    modulus (g * h) = modulus g * modulus h := by
  unfold modulus
  rw [map_mul, NumberField.TateGlobal.ideleNorm_mul,
    ENNReal.ofReal_mul (NumberField.TateGlobal.ideleNorm_pos _).le]

private theorem modulus_one : modulus (1 : AdelicGL 3 (𝓞 ℚ) ℚ) = 1 := by
  have h := modulus_mul (1 : AdelicGL 3 (𝓞 ℚ) ℚ) 1
  rw [one_mul] at h
  have h2 : modulus (1 : AdelicGL 3 (𝓞 ℚ) ℚ) * modulus 1 = modulus 1 * 1 := by
    rw [mul_one]
    exact h.symm
  exact (ENNReal.mul_right_inj (modulus_ne_zero 1) (modulus_ne_top 1)).1 h2

private theorem modulus_inv (g : AdelicGL 3 (𝓞 ℚ) ℚ) : modulus g⁻¹ = (modulus g)⁻¹ := by
  refine ENNReal.eq_inv_of_mul_eq_one_left ?_
  rw [← modulus_mul, inv_mul_cancel, modulus_one]

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel in
private theorem measurable_modulus : Measurable modulus :=
  ENNReal.measurable_ofReal.comp ((NumberField.TateGlobal.continuous_ideleNorm ℚ).comp
    Matrix.GeneralLinearGroup.continuous_det).measurable

end DeviceAlgebra

end DeviceIdentities

section JacobianAndModulus

section JacobianUnimodular

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

attribute [local instance] NumberField.AdeleRing.secondCountableTopology

open scoped NNReal Pointwise

open NumberField.AdelicHaar

section Generation

variable {R : Type*} [CommRing R] {M : Type*} [CommGroup M]

private def HasIdempotentPivots (R : Type*) [CommRing R] : Prop :=
  ∀ b c : Fin 3 → R, b ⬝ᵥ c = 1 → ∃ e : Fin 3 → R,
    (∀ i, e i * e i = e i) ∧ (∀ i j, i ≠ j → e i * e j = 0) ∧ e 0 + e 1 + e 2 = 1 ∧
      IsUnit (e 0 * c 0 + e 1 * c 1 + e 2 * c 2)

private def glOf (A B : Matrix (Fin 3) (Fin 3) R) (h : A * B = 1) : GL (Fin 3) R :=
  ⟨A, B, h, mul_eq_one_comm.mp h⟩

@[scoped simp] private theorem coe_glOf (A B : Matrix (Fin 3) (Fin 3) R) (h : A * B = 1) :
    ((glOf A B h : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = A := rfl

private def tGL (i j : Fin 3) (hij : i ≠ j) (c : R) : GL (Fin 3) R :=
  glOf (transvection i j c) (transvection i j (-c))
    (by rw [transvection_mul_transvection_same (h := hij), add_neg_cancel, transvection_zero])

@[scoped simp] private theorem coe_tGL (i j : Fin 3) (hij : i ≠ j) (c : R) :
    ((tGL i j hij c : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = transvection i j c := rfl

private def dGL (d : Fin 3 → Rˣ) : GL (Fin 3) R :=
  glOf (diagonal fun i => (d i : R)) (diagonal fun i => ((d i)⁻¹ : Rˣ))
    (by rw [diagonal_mul_diagonal]; simp)

@[scoped simp] private theorem coe_dGL (d : Fin 3 → Rˣ) :
    ((dGL d : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = diagonal fun i => (d i : R) := rfl

private theorem coe_dGL_inv (d : Fin 3 → Rˣ) :
    (((dGL d)⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = diagonal fun i => (((d i)⁻¹ : Rˣ) : R) := rfl

private theorem dGL_mul (d d' : Fin 3 → Rˣ) : dGL d * dGL d' = dGL (d * d') := by
  refine Units.ext ?_
  simp [diagonal_mul_diagonal]

private theorem apply_congr (ρ : GL (Fin 3) R →* M) {g h : GL (Fin 3) R}
    (hgh : (g : Matrix (Fin 3) (Fin 3) R) = h) : ρ g = ρ h := by
  rw [Units.ext hgh]

private theorem apply_tGL (h2 : IsUnit (2 : R)) (ρ : GL (Fin 3) R →* M) (i j : Fin 3) (hij : i ≠ j) (c : R) :
    ρ (tGL i j hij c) = 1 := by
  obtain ⟨w, hw⟩ := h2
  let d : Fin 3 → Rˣ := Function.update 1 i w
  have hdi : (d i : R) = 2 := by simp [d, hw]
  have hdj : ((d j)⁻¹ : Rˣ) = 1 := by simp [d, Function.update_of_ne (Ne.symm hij)]
  have hconj : ((dGL d * tGL i j hij c * (dGL d)⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
      (tGL i j hij c * tGL i j hij c : GL (Fin 3) R) := by
    have hinv : (((dGL d)⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = diagonal fun k => (((d k)⁻¹ : Rˣ) : R) :=
      rfl
    rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_dGL, coe_tGL, hinv,
      transvection_mul_transvection_same (h := hij)]
    ext a b
    rw [mul_diagonal, diagonal_mul]
    simp only [transvection, Matrix.add_apply, Matrix.single_apply]
    by_cases hab : a = b
    · subst hab
      have hne : ¬(i = a ∧ j = a) := fun h => hij (h.1.trans h.2.symm)
      simp [hne]
    · by_cases h' : i = a ∧ j = b
      · obtain ⟨rfl, rfl⟩ := h'
        simp [Matrix.one_apply_ne hab, hdi, hdj, two_mul]
      · simp [Matrix.one_apply_ne hab, h']
  have key := apply_congr ρ hconj
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm, map_mul] at key
  exact (mul_eq_left.mp key.symm)

private def swap01 : Matrix (Fin 3) (Fin 3) R := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

private def swap02 : Matrix (Fin 3) (Fin 3) R := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

private theorem swap01_mul_self : (swap01 : Matrix (Fin 3) (Fin 3) R) * swap01 = 1 := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [swap01, Matrix.mul_apply, Fin.sum_univ_three]

private theorem swap02_mul_self : (swap02 : Matrix (Fin 3) (Fin 3) R) * swap02 = 1 := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [swap02, Matrix.mul_apply, Fin.sum_univ_three]

private theorem swap01_conj (a : Rˣ) :
    (swap01 : Matrix (Fin 3) (Fin 3) R) * (diagonal fun k => ((Function.update (1 : Fin 3 → Rˣ) 0 a k : Rˣ) : R)) *
      swap01 = diagonal fun k => ((Function.update (1 : Fin 3 → Rˣ) 1 a k : Rˣ) : R) := by
  ext x y; fin_cases x <;> fin_cases y <;> simp only [Matrix.mul_apply, Fin.sum_univ_three] <;>
    simp [swap01, Function.update_apply]

private theorem swap02_conj (a : Rˣ) :
    (swap02 : Matrix (Fin 3) (Fin 3) R) * (diagonal fun k => ((Function.update (1 : Fin 3 → Rˣ) 0 a k : Rˣ) : R)) *
      swap02 = diagonal fun k => ((Function.update (1 : Fin 3 → Rˣ) 2 a k : Rˣ) : R) := by
  ext x y; fin_cases x <;> fin_cases y <;> simp only [Matrix.mul_apply, Fin.sum_univ_three] <;>
    simp [swap02, Function.update_apply]

private theorem apply_conj_invol (ρ : GL (Fin 3) R →* M) (P : Matrix (Fin 3) (Fin 3) R) (hP : P * P = 1)
    (g h : GL (Fin 3) R) (hc : P * (g : Matrix (Fin 3) (Fin 3) R) * P = h) : ρ g = ρ h := by
  have hmat : ((glOf P P hP * g * glOf P P hP : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = h := by
    rw [Units.val_mul, Units.val_mul, coe_glOf, hc]
  rw [← apply_congr ρ hmat, map_mul, map_mul, mul_right_comm, ← map_mul]
  have h1 : glOf P P hP * glOf P P hP = (1 : GL (Fin 3) R) := Units.ext (by rw [Units.val_mul, coe_glOf, hP]; rfl)
  rw [h1, map_one, one_mul]

private theorem apply_dGL (hM3 : ∀ x : M, x ^ 3 = 1 → x = 1) (ρ : GL (Fin 3) R →* M)
    (hscalar : ∀ a : Rˣ, ρ (dGL fun _ => a) = 1) (d : Fin 3 → Rˣ) : ρ (dGL d) = 1 := by
  have h1 : ∀ a : Rˣ, ρ (dGL (Function.update 1 1 a)) = ρ (dGL (Function.update 1 0 a)) := fun a =>
    (apply_conj_invol ρ swap01 swap01_mul_self (dGL (Function.update 1 0 a)) (dGL (Function.update 1 1 a))
      (swap01_conj a)).symm
  have h2 : ∀ a : Rˣ, ρ (dGL (Function.update 1 2 a)) = ρ (dGL (Function.update 1 0 a)) := fun a =>
    (apply_conj_invol ρ swap02 swap02_mul_self (dGL (Function.update 1 0 a)) (dGL (Function.update 1 2 a))
      (swap02_conj a)).symm
  have hsplit : ∀ d : Fin 3 → Rˣ,
      dGL d = dGL (Function.update 1 0 (d 0)) * dGL (Function.update 1 1 (d 1)) * dGL (Function.update 1 2 (d 2)) := by
    intro d
    rw [dGL_mul, dGL_mul]
    congr 1
    ext k
    fin_cases k <;> simp
  have hθ : ∀ a : Rˣ, ρ (dGL (Function.update 1 0 a)) = 1 := by
    intro a
    refine hM3 _ ?_
    have := hscalar a
    rw [hsplit (fun _ => a), map_mul, map_mul, h1, h2] at this
    simpa [pow_succ] using this
  rw [hsplit d, map_mul, map_mul, hθ, h1, hθ, h2, hθ, one_mul, one_mul]

private theorem apply_invol (hM2 : ∀ x : M, x ^ 2 = 1 → x = 1) (ρ : GL (Fin 3) R →* M)
    (W : Matrix (Fin 3) (Fin 3) R) (hW : W * W = 1) : ρ (glOf W W hW) = 1 := by
  refine hM2 _ ?_
  have h1 : glOf W W hW * glOf W W hW = (1 : GL (Fin 3) R) := Units.ext (by rw [Units.val_mul, coe_glOf, hW]; rfl)
  rw [sq, ← map_mul, h1, map_one]

private def pivot₁ (e : Fin 3 → R) : Matrix (Fin 3) (Fin 3) R :=
  !![e 0, e 1, e 2; e 1, e 0 + e 2, 0; e 2, 0, e 0 + e 1]

private def pivot₂ (f : Fin 3 → R) : Matrix (Fin 3) (Fin 3) R :=
  !![1, 0, 0; 0, f 0, f 1 + f 2; 0, f 1 + f 2, f 0]

section Pivots

variable {e : Fin 3 → R} (hii : ∀ i, e i * e i = e i) (hij : ∀ i j, i ≠ j → e i * e j = 0)
  (hsum : e 0 + e 1 + e 2 = 1)

include hii hij hsum

private theorem pivot₁_mul_self : pivot₁ e * pivot₁ e = 1 := by
  have h00 := hii 0; have h11 := hii 1; have h22 := hii 2
  have h01 := hij 0 1 (by decide); have h02 := hij 0 2 (by decide); have h12 := hij 1 2 (by decide)
  have h10 := hij 1 0 (by decide); have h20 := hij 2 0 (by decide); have h21 := hij 2 1 (by decide)
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [pivot₁, Matrix.mul_apply, Fin.sum_univ_three, mul_add, add_mul, h00, h11, h22, h01, h02, h12, h10, h20,
      h21] <;>
    linear_combination hsum

private theorem pivot₂_mul_self : pivot₂ e * pivot₂ e = 1 := by
  have h00 := hii 0; have h11 := hii 1; have h22 := hii 2
  have h01 := hij 0 1 (by decide); have h02 := hij 0 2 (by decide); have h12 := hij 1 2 (by decide)
  have h10 := hij 1 0 (by decide); have h20 := hij 2 0 (by decide); have h21 := hij 2 1 (by decide)
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [pivot₂, Matrix.mul_apply, Fin.sum_univ_three, mul_add, add_mul, h00, h11, h22, h01, h02, h12, h10, h20,
      h21] <;>
    linear_combination hsum

end Pivots

private theorem pivot₁_mul_apply (e : Fin 3 → R) (A : Matrix (Fin 3) (Fin 3) R) (b : Fin 3) :
    (pivot₁ e * A) 0 b = e 0 * A 0 b + e 1 * A 1 b + e 2 * A 2 b := by
  simp [pivot₁, Matrix.mul_apply, Fin.sum_univ_three]

private theorem pivot₂_mul_apply₀ (f : Fin 3 → R) (A : Matrix (Fin 3) (Fin 3) R) (b : Fin 3) :
    (pivot₂ f * A) 0 b = A 0 b := by
  simp [pivot₂, Matrix.mul_apply, Fin.sum_univ_three]

private theorem pivot₂_mul_apply₁ (f : Fin 3 → R) (A : Matrix (Fin 3) (Fin 3) R) (b : Fin 3) :
    (pivot₂ f * A) 1 b = f 0 * A 1 b + (f 1 + f 2) * A 2 b := by
  simp [pivot₂, Matrix.mul_apply, Fin.sum_univ_three]

private theorem pivot₂_mul_apply₂ (f : Fin 3 → R) (A : Matrix (Fin 3) (Fin 3) R) (b : Fin 3) :
    (pivot₂ f * A) 2 b = (f 1 + f 2) * A 1 b + f 0 * A 2 b := by
  simp [pivot₂, Matrix.mul_apply, Fin.sum_univ_three]

private theorem apply_of_offDiag_eq_zero (hM3 : ∀ x : M, x ^ 3 = 1 → x = 1) (ρ : GL (Fin 3) R →* M)
    (hscalar : ∀ a : Rˣ, ρ (dGL fun _ => a) = 1) (g : GL (Fin 3) R) (h01 : (g : Matrix (Fin 3) (Fin 3) R) 0 1 = 0)
    (h02 : (g : Matrix (Fin 3) (Fin 3) R) 0 2 = 0) (h10 : (g : Matrix (Fin 3) (Fin 3) R) 1 0 = 0)
    (h12 : (g : Matrix (Fin 3) (Fin 3) R) 1 2 = 0) (h20 : (g : Matrix (Fin 3) (Fin 3) R) 2 0 = 0)
    (h21 : (g : Matrix (Fin 3) (Fin 3) R) 2 1 = 0) : ρ g = 1 := by
  have hdiag : (g : Matrix (Fin 3) (Fin 3) R) = diagonal fun k => (g : Matrix (Fin 3) (Fin 3) R) k k := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h02, h10, h12, h20, h21]
  have hdet : IsUnit (∏ k, (g : Matrix (Fin 3) (Fin 3) R) k k) := by
    have := isUnits_det_units g
    rwa [hdiag, det_diagonal] at this
  rw [Fin.prod_univ_three, IsUnit.mul_iff, IsUnit.mul_iff] at hdet
  obtain ⟨⟨h0, h1⟩, h2⟩ := hdet
  let d : Fin 3 → Rˣ := ![h0.unit, h1.unit, h2.unit]
  have hd : (g : Matrix (Fin 3) (Fin 3) R) = (dGL d : GL (Fin 3) R) := by
    rw [hdiag, coe_dGL]
    congr 1
    ext k
    fin_cases k <;> simp [d]
  rw [apply_congr ρ hd]
  exact apply_dGL hM3 ρ hscalar d

private theorem eq_one_of_apply_scalar (hP : HasIdempotentPivots R) (h2 : IsUnit (2 : R))
    (hM2 : ∀ x : M, x ^ 2 = 1 → x = 1) (hM3 : ∀ x : M, x ^ 3 = 1 → x = 1) (ρ : GL (Fin 3) R →* M)
    (hscalar : ∀ a : Rˣ, ρ (dGL fun _ => a) = 1) (g : GL (Fin 3) R) : ρ g = 1 := by
  have hT : ∀ (i j : Fin 3) (hij : i ≠ j) (c : R), tGL i j hij c ∈ ρ.ker := fun i j hij c =>
    (MonoidHom.mem_ker).mpr (apply_tGL h2 ρ i j hij c)
  have hW : ∀ (W : Matrix (Fin 3) (Fin 3) R) (hW : W * W = 1), glOf W W hW ∈ ρ.ker := fun W hW =>
    (MonoidHom.mem_ker).mpr (apply_invol hM2 ρ W hW)
  rw [← MonoidHom.mem_ker]

  obtain ⟨e, hii, hij, hsum, hu⟩ := hP (fun j => ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) 0 j)
    (fun i => (g : Matrix (Fin 3) (Fin 3) R) i 0) (by
      have := congrFun (congrFun (g.inv_mul) 0) 0
      rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
      exact this)
  refine (Subgroup.mul_mem_cancel_left (h := hW (pivot₁ e) (pivot₁_mul_self hii hij hsum))).mp ?_
  set g₁ : GL (Fin 3) R := glOf (pivot₁ e) (pivot₁ e) (pivot₁_mul_self hii hij hsum) * g with hg₁
  have h00 : IsUnit ((g₁ : Matrix (Fin 3) (Fin 3) R) 0 0) := by
    rw [hg₁, Units.val_mul, coe_glOf, pivot₁_mul_apply]; exact hu
  clear_value g₁
  obtain ⟨u, hu⟩ := h00

  set t₁ : R := -((g₁ : Matrix (Fin 3) (Fin 3) R) 1 0 * ((u⁻¹ : Rˣ) : R)) with ht₁
  set t₂ : R := -((g₁ : Matrix (Fin 3) (Fin 3) R) 2 0 * ((u⁻¹ : Rˣ) : R)) with ht₂
  refine (Subgroup.mul_mem_cancel_left (h := hT 2 0 (by decide) t₂)).mp
    ((Subgroup.mul_mem_cancel_left (h := hT 1 0 (by decide) t₁)).mp ?_)
  set g₂ : GL (Fin 3) R := tGL 1 0 (by decide) t₁ * (tGL 2 0 (by decide) t₂ * g₁) with hg₂
  have h₂00 : (g₂ : Matrix (Fin 3) (Fin 3) R) 0 0 = u := by
    simp [hg₂, transvection_mul_apply_of_ne, hu]
  have h₂10 : (g₂ : Matrix (Fin 3) (Fin 3) R) 1 0 = 0 := by
    simp only [hg₂, Units.val_mul, coe_tGL, transvection_mul_apply_same, ne_eq, Fin.reduceEq, not_false_eq_true,
      transvection_mul_apply_of_ne, ht₁, ← hu]
    linear_combination (-(g₁ : Matrix (Fin 3) (Fin 3) R) 1 0) * u.inv_mul
  have h₂20 : (g₂ : Matrix (Fin 3) (Fin 3) R) 2 0 = 0 := by
    simp only [hg₂, Units.val_mul, coe_tGL, transvection_mul_apply_same, ne_eq, Fin.reduceEq, not_false_eq_true,
      transvection_mul_apply_of_ne, ht₂, ← hu]
    linear_combination (-(g₁ : Matrix (Fin 3) (Fin 3) R) 2 0) * u.inv_mul
  clear_value g₂
  set s₁ : R := -(((u⁻¹ : Rˣ) : R) * (g₂ : Matrix (Fin 3) (Fin 3) R) 0 1) with hs₁
  set s₂ : R := -(((u⁻¹ : Rˣ) : R) * (g₂ : Matrix (Fin 3) (Fin 3) R) 0 2) with hs₂
  refine (Subgroup.mul_mem_cancel_right (h := hT 0 1 (by decide) s₁)).mp
    ((Subgroup.mul_mem_cancel_right (h := hT 0 2 (by decide) s₂)).mp ?_)
  set g₃ : GL (Fin 3) R := g₂ * tGL 0 1 (by decide) s₁ * tGL 0 2 (by decide) s₂ with hg₃
  have h₃c0 : ∀ i, (g₃ : Matrix (Fin 3) (Fin 3) R) i 0 = (g₂ : Matrix (Fin 3) (Fin 3) R) i 0 := by
    intro i; simp [hg₃, mul_transvection_apply_of_ne]
  have h₃00 : (g₃ : Matrix (Fin 3) (Fin 3) R) 0 0 = u := by rw [h₃c0, h₂00]
  have h₃10 : (g₃ : Matrix (Fin 3) (Fin 3) R) 1 0 = 0 := by rw [h₃c0, h₂10]
  have h₃20 : (g₃ : Matrix (Fin 3) (Fin 3) R) 2 0 = 0 := by rw [h₃c0, h₂20]
  have h₃01 : (g₃ : Matrix (Fin 3) (Fin 3) R) 0 1 = 0 := by
    simp only [hg₃, Units.val_mul, coe_tGL, ne_eq, Fin.reduceEq, not_false_eq_true, mul_transvection_apply_of_ne,
      mul_transvection_apply_same, hs₁, h₂00]
    linear_combination (-(g₂ : Matrix (Fin 3) (Fin 3) R) 0 1) * u.inv_mul
  have h₃02 : (g₃ : Matrix (Fin 3) (Fin 3) R) 0 2 = 0 := by
    simp only [hg₃, Units.val_mul, coe_tGL, ne_eq, Fin.reduceEq, not_false_eq_true, mul_transvection_apply_of_ne,
      mul_transvection_apply_same, hs₂, h₂00]
    linear_combination (-(g₂ : Matrix (Fin 3) (Fin 3) R) 0 2) * u.inv_mul
  clear_value g₃

  obtain ⟨f, fii, fij, fsum, fu⟩ := hP ![((g₃⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) 1 1,
      ((g₃⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) 1 2, 0]
    ![(g₃ : Matrix (Fin 3) (Fin 3) R) 1 1, (g₃ : Matrix (Fin 3) (Fin 3) R) 2 1,
      (g₃ : Matrix (Fin 3) (Fin 3) R) 2 1] (by
      have := congrFun (congrFun (g₃.inv_mul) 1) 1
      rw [Matrix.mul_apply, Matrix.one_apply_eq, Fin.sum_univ_three, h₃01, mul_zero, zero_add] at this
      simpa [dotProduct, Fin.sum_univ_three] using this)
  refine (Subgroup.mul_mem_cancel_left (h := hW (pivot₂ f) (pivot₂_mul_self fii fij fsum))).mp ?_
  set g₄ : GL (Fin 3) R := glOf (pivot₂ f) (pivot₂ f) (pivot₂_mul_self fii fij fsum) * g₃ with hg₄
  have h₄11 : IsUnit ((g₄ : Matrix (Fin 3) (Fin 3) R) 1 1) := by
    rw [hg₄, Units.val_mul, coe_glOf, pivot₂_mul_apply₁]
    convert fu using 1
    simp; ring
  have h₄00 : (g₄ : Matrix (Fin 3) (Fin 3) R) 0 0 = u := by rw [hg₄, Units.val_mul, coe_glOf, pivot₂_mul_apply₀, h₃00]
  have h₄01 : (g₄ : Matrix (Fin 3) (Fin 3) R) 0 1 = 0 := by rw [hg₄, Units.val_mul, coe_glOf, pivot₂_mul_apply₀, h₃01]
  have h₄02 : (g₄ : Matrix (Fin 3) (Fin 3) R) 0 2 = 0 := by rw [hg₄, Units.val_mul, coe_glOf, pivot₂_mul_apply₀, h₃02]
  have h₄10 : (g₄ : Matrix (Fin 3) (Fin 3) R) 1 0 = 0 := by
    rw [hg₄, Units.val_mul, coe_glOf, pivot₂_mul_apply₁, h₃10, h₃20]; ring
  have h₄20 : (g₄ : Matrix (Fin 3) (Fin 3) R) 2 0 = 0 := by
    rw [hg₄, Units.val_mul, coe_glOf, pivot₂_mul_apply₂, h₃10, h₃20]; ring
  clear_value g₄
  obtain ⟨v, hv⟩ := h₄11

  set t₃ : R := -((g₄ : Matrix (Fin 3) (Fin 3) R) 2 1 * ((v⁻¹ : Rˣ) : R)) with ht₃
  refine (Subgroup.mul_mem_cancel_left (h := hT 2 1 (by decide) t₃)).mp ?_
  set g₅ : GL (Fin 3) R := tGL 2 1 (by decide) t₃ * g₄ with hg₅
  have h₅r0 : ∀ b, (g₅ : Matrix (Fin 3) (Fin 3) R) 0 b = (g₄ : Matrix (Fin 3) (Fin 3) R) 0 b := by
    intro b; simp [hg₅, transvection_mul_apply_of_ne]
  have h₅r1 : ∀ b, (g₅ : Matrix (Fin 3) (Fin 3) R) 1 b = (g₄ : Matrix (Fin 3) (Fin 3) R) 1 b := by
    intro b; simp [hg₅, transvection_mul_apply_of_ne]
  have h₅20 : (g₅ : Matrix (Fin 3) (Fin 3) R) 2 0 = 0 := by
    simp only [hg₅, Units.val_mul, coe_tGL, transvection_mul_apply_same, h₄20, h₄10, mul_zero, add_zero]
  have h₅21 : (g₅ : Matrix (Fin 3) (Fin 3) R) 2 1 = 0 := by
    simp only [hg₅, Units.val_mul, coe_tGL, transvection_mul_apply_same, ht₃, ← hv]
    linear_combination (-(g₄ : Matrix (Fin 3) (Fin 3) R) 2 1) * v.inv_mul
  clear_value g₅
  set s₃ : R := -(((v⁻¹ : Rˣ) : R) * (g₅ : Matrix (Fin 3) (Fin 3) R) 1 2) with hs₃
  refine (Subgroup.mul_mem_cancel_right (h := hT 1 2 (by decide) s₃)).mp ?_
  set g₆ : GL (Fin 3) R := g₅ * tGL 1 2 (by decide) s₃ with hg₆
  have h₆c0 : ∀ a, (g₆ : Matrix (Fin 3) (Fin 3) R) a 0 = (g₅ : Matrix (Fin 3) (Fin 3) R) a 0 := by
    intro a; simp [hg₆, mul_transvection_apply_of_ne]
  have h₆c1 : ∀ a, (g₆ : Matrix (Fin 3) (Fin 3) R) a 1 = (g₅ : Matrix (Fin 3) (Fin 3) R) a 1 := by
    intro a; simp [hg₆, mul_transvection_apply_of_ne]
  have h₆02 : (g₆ : Matrix (Fin 3) (Fin 3) R) 0 2 = 0 := by
    simp only [hg₆, Units.val_mul, coe_tGL, mul_transvection_apply_same, h₅r0, h₄02, h₄01, mul_zero, add_zero]
  have h₆12 : (g₆ : Matrix (Fin 3) (Fin 3) R) 1 2 = 0 := by
    simp only [hg₆, Units.val_mul, coe_tGL, mul_transvection_apply_same, hs₃, h₅r1, ← hv]
    linear_combination (-(g₄ : Matrix (Fin 3) (Fin 3) R) 1 2) * v.inv_mul

  exact (MonoidHom.mem_ker).mpr (apply_of_offDiag_eq_zero hM3 ρ hscalar g₆ (by rw [h₆c1, h₅r0, h₄01]) h₆02
    (by rw [h₆c0, h₅r1, h₄10]) h₆12 (by rw [h₆c0, h₅20]) (by rw [h₆c1, h₅21]))

end Generation

section Adele

variable (K : Type*) [Field K] [NumberField K]

local notation "𝔸" => AdeleRing (𝓞 K) K

private theorem snd_mul_apply (x y : 𝔸) (v : HeightOneSpectrum (𝓞 K)) : (x * y).2 v = x.2 v * y.2 v := rfl

private theorem snd_add_apply (x y : 𝔸) (v : HeightOneSpectrum (𝓞 K)) : (x + y).2 v = x.2 v + y.2 v := rfl

private theorem snd_one_apply (v : HeightOneSpectrum (𝓞 K)) : (1 : 𝔸).2 v = 1 := rfl

private theorem snd_zero_apply (v : HeightOneSpectrum (𝓞 K)) : (0 : 𝔸).2 v = 0 := rfl

private theorem tab_mul_self {A : Type*} [MulZeroOneClass A] (k i : Fin 3) :
    (if k = i then (1 : A) else 0) * (if k = i then 1 else 0) = if k = i then 1 else 0 := by
  split <;> simp

private theorem tab_mul_of_ne {A : Type*} [MulZeroOneClass A] (k i j : Fin 3) (hij : i ≠ j) :
    (if k = i then (1 : A) else 0) * (if k = j then 1 else 0) = 0 := by
  by_cases h : k = i
  · subst h; simp [hij]
  · simp [h]

private theorem tab_sum {A : Type*} [AddMonoidWithOne A] (k : Fin 3) :
    (if k = 0 then (1 : A) else 0) + (if k = 1 then 1 else 0) + (if k = 2 then 1 else 0) = 1 := by
  fin_cases k <;> simp

private theorem tab_select {A : Type*} [NonAssocSemiring A] (k : Fin 3) (x : Fin 3 → A) :
    (if k = 0 then (1 : A) else 0) * x 0 + (if k = 1 then 1 else 0) * x 1 + (if k = 2 then 1 else 0) * x 2 = x k := by
  fin_cases k <;> simp

private theorem tab_zero {A : Type*} [NonAssocSemiring A] (y x : Fin 3 → A) (h : ∀ j, x j = 0) :
    y 0 * x 0 + y 1 * x 1 + y 2 * x 2 = 0 := by
  simp [h]

private theorem adele_ext {x y : 𝔸} (h₁ : ∀ w, x.1 w = y.1 w) (h₂ : ∀ v, x.2 v = y.2 v) : x = y :=
  Prod.ext (funext h₁) (FiniteAdeleRing.ext K h₂)

private theorem hasIdempotentPivots_adeleRing : HasIdempotentPivots 𝔸 := by
  intro b c hbc

  have hmax₁ : ∀ w : InfinitePlace K, ∃ i : Fin 3, ∀ j, ‖(c j).1 w‖ ≤ ‖(c i).1 w‖ := fun w => by
    obtain ⟨i, -, hi⟩ :=
      Finset.exists_max_image Finset.univ (fun j : Fin 3 => ‖(c j).1 w‖) Finset.univ_nonempty
    exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩
  have hmax₂ : ∀ v : HeightOneSpectrum (𝓞 K), ∃ i : Fin 3, ∀ j, Valued.v ((c j).2 v) ≤ Valued.v ((c i).2 v) :=
    fun v => by
    obtain ⟨i, -, hi⟩ :=
      Finset.exists_max_image Finset.univ (fun j : Fin 3 => Valued.v ((c j).2 v)) Finset.univ_nonempty
    exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩
  choose ι₁ hι₁ using hmax₁
  choose ι₂ hι₂ using hmax₂
  let e : Fin 3 → 𝔸 := fun i =>
    (fun w => if ι₁ w = i then 1 else 0, ⟨fun v => if ι₂ v = i then 1 else 0, Filter.Eventually.of_forall fun v => by
      by_cases h : ι₂ v = i
      · simp only [h, if_true, SetLike.mem_coe]; exact one_mem _
      · simp only [h, if_false, SetLike.mem_coe]; exact zero_mem _⟩)
  have he₁ : ∀ i w, (e i).1 w = if ι₁ w = i then 1 else 0 := fun i w => rfl
  have he₂ : ∀ i v, (e i).2 v = if ι₂ v = i then 1 else 0 := fun i v => rfl

  have hbc' : b 0 * c 0 + b 1 * c 1 + b 2 * c 2 = 1 := by simpa [dotProduct, Fin.sum_univ_three] using hbc
  have hbc₁ : ∀ w, (b 0 * c 0 + b 1 * c 1 + b 2 * c 2).1 w = (1 : 𝔸).1 w := fun w => by rw [hbc']
  have hbc₂ : ∀ v, (b 0).2 v * (c 0).2 v + (b 1).2 v * (c 1).2 v + (b 2).2 v * (c 2).2 v = 1 := fun v => by
    have := congrArg (fun x : 𝔸 => x.2 v) hbc'
    simpa only [snd_add_apply, snd_mul_apply, snd_one_apply] using this
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · intro i
    exact adele_ext K (fun w => tab_mul_self (ι₁ w) i) (fun v => by rw [snd_mul_apply, he₂, tab_mul_self])
  · intro i j hij
    exact adele_ext K (fun w => tab_mul_of_ne (ι₁ w) i j hij)
      (fun v => by rw [snd_mul_apply, he₂, he₂, tab_mul_of_ne _ _ _ hij, snd_zero_apply])
  · exact adele_ext K (fun w => tab_sum (ι₁ w))
      (fun v => by rw [snd_add_apply, snd_add_apply, he₂, he₂, he₂, tab_sum, snd_one_apply])
  ·
    have hu₁ : ∀ w, (e 0 * c 0 + e 1 * c 1 + e 2 * c 2).1 w = (c (ι₁ w)).1 w := fun w =>
      tab_select (ι₁ w) fun j => (c j).1 w
    have hu₂ : ∀ v, (e 0 * c 0 + e 1 * c 1 + e 2 * c 2).2 v = (c (ι₂ v)).2 v := fun v => by
      rw [snd_add_apply, snd_add_apply, snd_mul_apply, snd_mul_apply, snd_mul_apply, he₂, he₂, he₂]
      exact tab_select (ι₂ v) fun j => (c j).2 v

    have hne₁ : ∀ w, (e 0 * c 0 + e 1 * c 1 + e 2 * c 2).1 w ≠ 0 := fun w h0 => by
      have hall : ∀ j, (c j).1 w = 0 := fun j => by
        have := hι₁ w j
        rw [← hu₁ w, h0, norm_zero] at this
        exact norm_le_zero_iff.mp this
      have hzero : (b 0 * c 0 + b 1 * c 1 + b 2 * c 2).1 w = 0 :=
        tab_zero (fun j => (b j).1 w) (fun j => (c j).1 w) hall
      exact (isUnit_one (M := w.Completion)).ne_zero ((hbc₁ w).symm.trans hzero)

    have hne₂ : ∀ v, (e 0 * c 0 + e 1 * c 1 + e 2 * c 2).2 v ≠ 0 := fun v h0 => by
      rw [hu₂] at h0
      have hall : ∀ j, (c j).2 v = 0 := fun j => by
        have := hι₂ v j
        rw [h0, Valuation.map_zero, le_zero_iff] at this
        exact (Valuation.zero_iff _).mp this
      have := hbc₂ v
      rw [hall 0, hall 1, hall 2, mul_zero, mul_zero, mul_zero, add_zero, add_zero] at this
      exact zero_ne_one this

    have hint : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        ∀ j, (b j).2 v ∈ v.adicCompletionIntegers K ∧ (c j).2 v ∈ v.adicCompletionIntegers K := by
      simp only [Filter.eventually_all, Filter.eventually_and]
      exact fun j => ⟨(b j).2.2, (c j).2.2⟩
    refine Prod.isUnit_iff.mpr ⟨Pi.isUnit_iff.mpr fun w => (hne₁ w).isUnit, ?_⟩
    refine RestrictedProduct.isUnit_of_eventually_isUnit (fun v => (hne₂ v).isUnit) ?_
    filter_upwards [hint] with v hv

    have hle : Valued.v ((e 0 * c 0 + e 1 * c 1 + e 2 * c 2).2 v) ≤ 1 := by
      rw [hu₂]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp (hv _).2
    have hbj : ∀ j, Valued.v ((b j).2 v * (c j).2 v) ≤ Valued.v ((c (ι₂ v)).2 v) := fun j => by
      rw [Valuation.map_mul]
      calc Valued.v ((b j).2 v) * Valued.v ((c j).2 v) ≤ 1 * Valued.v ((c (ι₂ v)).2 v) :=
            mul_le_mul' ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp (hv j).1) (hι₂ v j)
        _ = _ := one_mul _
    have hge : 1 ≤ Valued.v ((e 0 * c 0 + e 1 * c 1 + e 2 * c 2).2 v) := by
      rw [hu₂, ← (Valued.v : Valuation (v.adicCompletion K) _).map_one, ← hbc₂ v]
      exact Valuation.map_add_le _ (Valuation.map_add_le _ (hbj 0) (hbj 1)) (hbj 2)
    have hone : Valued.v ((e 0 * c 0 + e 1 * c 1 + e 2 * c 2).2 v) = 1 := le_antisymm hle hge
    refine ⟨(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mpr hle,
      isUnit_iff_exists_inv.mpr ⟨⟨((e 0 * c 0 + e 1 * c 1 + e 2 * c 2).2 v)⁻¹, ?_⟩, ?_⟩⟩
    · refine (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mpr ?_
      rw [map_inv₀, hone, inv_one]
    · exact Subtype.ext (mul_inv_cancel₀ (hne₂ v))

private theorem isUnit_two_adeleRing : IsUnit (2 : 𝔸) := by
  have h : IsUnit (2 : K) := isUnit_iff_ne_zero.mpr two_ne_zero
  have := h.map (algebraMap K 𝔸)
  rwa [map_ofNat] at this

end Adele

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

section Torsion

private theorem units_pow_eq_one {n : ℕ} (hn : n ≠ 0) (x : ℝ≥0ˣ) (hx : x ^ n = 1) : x = 1 := by
  have h1 : ((x : ℝ≥0) : ℝ) ^ n = 1 := by
    have := congrArg (fun u : ℝ≥0ˣ => ((u : ℝ≥0) : ℝ)) hx
    simpa using this
  have h2 : ((x : ℝ≥0) : ℝ) = 1 := by
    rcases (pow_eq_one_iff_of_ne_zero hn).mp h1 with h | ⟨h, -⟩
    · exact h
    · have : (0 : ℝ) ≤ ((x : ℝ≥0) : ℝ) := (x : ℝ≥0).coe_nonneg
      linarith
  exact Units.ext (NNReal.coe_injective (by simpa using h2))

end Torsion

section RowAction

private scoped instance : ContinuousConstSMul (Matrix (Fin 3) (Fin 3) 𝔸) (Fin 3 → 𝔸) :=
  ⟨fun A => continuous_pi fun i => by
    simp only [Matrix.smul_eq_mulVec, Matrix.mulVec, dotProduct]
    exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)⟩

private theorem secondCountableTopology_adelicGL3 : SecondCountableTopology (AdelicGL 3 (𝓞 ℚ) ℚ) := by
  haveI : SecondCountableTopology (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
    inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → AdeleRing (𝓞 ℚ) ℚ))
  haveI : SecondCountableTopology (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

private theorem domSMul_rowHaar (h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    DomMulAct.mk h • (rowHaar : Measure (Fin 3 → 𝔸)) = distribHaarChar (Fin 3 → 𝔸) h • rowHaar := by
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul (DomMulAct.mk h • (rowHaar : Measure (Fin 3 → 𝔸))) rowHaar]
  rw [addHaarScalarFactor_smul_eq_distribHaarChar]

private theorem domSMul_adelicAddHaar (a : 𝔸ˣ) :
    DomMulAct.mk a • (adelicAddHaar (𝓞 ℚ) ℚ : Measure 𝔸) = distribHaarChar 𝔸 a • adelicAddHaar (𝓞 ℚ) ℚ := by
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul (DomMulAct.mk a • (adelicAddHaar (𝓞 ℚ) ℚ : Measure 𝔸))
    (adelicAddHaar (𝓞 ℚ) ℚ)]
  rw [addHaarScalarFactor_smul_eq_distribHaarChar]

private theorem addHaarScalarFactor_congr {A : Type*} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [MeasurableSpace A] [BorelSpace A] {μ₁ μ₂ μ : Measure A} [μ.IsAddHaarMeasure] [IsFiniteMeasureOnCompacts μ₁]
    [μ₁.IsAddLeftInvariant] [IsFiniteMeasureOnCompacts μ₂] [μ₂.IsAddLeftInvariant] (h : μ₁ = μ₂) :
    μ₁.addHaarScalarFactor μ = μ₂.addHaarScalarFactor μ := by
  subst h
  rfl

private theorem haarScalarFactor_congr {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] {μ₁ μ₂ μ : Measure G} [μ.IsHaarMeasure] [IsFiniteMeasureOnCompacts μ₁]
    [μ₁.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ₂] [μ₂.IsMulLeftInvariant] (h : μ₁ = μ₂) :
    μ₁.haarScalarFactor μ = μ₂.haarScalarFactor μ := by
  subst h
  rfl

private theorem distribHaarChar_rows_scalar (a : 𝔸ˣ) :
    distribHaarChar (Fin 3 → 𝔸) (dGL fun _ : Fin 3 => a) = distribHaarChar 𝔸 a ^ 3 := by

  have hset : ∀ s : Fin 3 → Set 𝔸,
      ((dGL fun _ : Fin 3 => a) • Set.univ.pi s : Set (Fin 3 → 𝔸)) = Set.univ.pi fun i => a • s i := by
    intro s
    ext x
    simp only [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_univ_pi]
    refine forall_congr' fun i => ?_
    rw [Units.smul_def, coe_dGL_inv, Matrix.smul_eq_mulVec, Matrix.mulVec_diagonal, Units.smul_def, smul_eq_mul]

  have h1 : Measure.pi (fun _ : Fin 3 => distribHaarChar 𝔸 a • adelicAddHaar (𝓞 ℚ) ℚ) =
      DomMulAct.mk (dGL fun _ : Fin 3 => a) • (rowHaar : Measure (Fin 3 → 𝔸)) := by
    refine Measure.pi_eq fun s _ => ?_
    rw [Measure.domSMul_apply, Equiv.symm_apply_apply, hset,
      show (rowHaar : Measure (Fin 3 → 𝔸)) = Measure.pi fun _ : Fin 3 => adelicAddHaar (𝓞 ℚ) ℚ from rfl,
      Measure.pi_pi]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← domSMul_adelicAddHaar a, Measure.domSMul_apply, Equiv.symm_apply_apply]
  have h2 : Measure.pi (fun _ : Fin 3 => distribHaarChar 𝔸 a • adelicAddHaar (𝓞 ℚ) ℚ) =
      (distribHaarChar 𝔸 a ^ 3) • (rowHaar : Measure (Fin 3 → 𝔸)) := by
    refine Measure.pi_eq fun s _ => ?_
    rw [Measure.coe_nnreal_smul_apply,
      show (rowHaar : Measure (Fin 3 → 𝔸)) = Measure.pi fun _ : Fin 3 => adelicAddHaar (𝓞 ℚ) ℚ from rfl,
      Measure.pi_pi]
    simp only [Measure.coe_nnreal_smul_apply]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.coe_pow]
  rw [← addHaarScalarFactor_smul_eq_distribHaarChar rowHaar, addHaarScalarFactor_congr (h1.symm.trans h2),
    Measure.addHaarScalarFactor_smul, Measure.addHaarScalarFactor_self, smul_eq_mul, mul_one]

private def transposeGL (g : AdelicGL 3 (𝓞 ℚ) ℚ) : AdelicGL 3 (𝓞 ℚ) ℚ :=
  ⟨(g : Matrix (Fin 3) (Fin 3) 𝔸)ᵀ, ((g⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸)ᵀ,
    by rw [← Matrix.transpose_mul, g.inv_mul, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, g.mul_inv, Matrix.transpose_one]⟩

private theorem det_transposeGL (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Matrix.GeneralLinearGroup.det (transposeGL g) = Matrix.GeneralLinearGroup.det g :=
  Units.ext (Matrix.det_transpose _)

private theorem distribHaarChar_rows (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    distribHaarChar (Fin 3 → 𝔸) g = distribHaarChar 𝔸 (Matrix.GeneralLinearGroup.det g) := by
  let χ : AdelicGL 3 (𝓞 ℚ) ℚ →* ℝ≥0 := distribHaarChar (Fin 3 → 𝔸)
  let ψ : AdelicGL 3 (𝓞 ℚ) ℚ →* ℝ≥0 := (distribHaarChar 𝔸).comp Matrix.GeneralLinearGroup.det
  let ρ : AdelicGL 3 (𝓞 ℚ) ℚ →* ℝ≥0ˣ := χ.toHomUnits / ψ.toHomUnits
  have hρ : ∀ h, ρ h = 1 ↔ χ h = ψ h := fun h => by
    simp only [ρ, MonoidHom.div_apply, div_eq_one, Units.ext_iff, MonoidHom.coe_toHomUnits]
  suffices ρ g = 1 from (hρ g).mp this
  refine eq_one_of_apply_scalar (hasIdempotentPivots_adeleRing ℚ) (isUnit_two_adeleRing ℚ)
    (units_pow_eq_one two_ne_zero) (units_pow_eq_one three_ne_zero) ρ (fun a => (hρ _).mpr ?_) g
  have hdet : Matrix.GeneralLinearGroup.det (dGL fun _ : Fin 3 => a) = a ^ 3 := by
    refine Units.ext ?_
    simp [Matrix.GeneralLinearGroup.val_det_apply, det_diagonal, Finset.prod_const]
  simp only [χ, ψ, MonoidHom.comp_apply, hdet, map_pow]
  exact distribHaarChar_rows_scalar a

end RowAction

private theorem scalar_comm (a : 𝔸ˣ) (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    x * dGL (fun _ : Fin 3 => a) = dGL (fun _ : Fin 3 => a) * x := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_dGL, ← Matrix.scalar_apply]
  exact (Matrix.scalar_commute (a : 𝔸) (fun r' => Commute.all _ _) _).eq.symm

private theorem unipotentSubgroup3_le_mirabolic : WhittakerBlock.unipotentSubgroup3 ≤ mirabolic := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨t, rfl⟩
  show bottomRow _ = e₃
  funext j
  fin_cases j <;> simp [bottomRow, e₃, upperUnipotent3_coe]

private theorem dGL_mem_mirabolic (w₀ w₁ : 𝔸ˣ) : dGL ![w₀, w₁, 1] ∈ mirabolic := by
  show bottomRow _ = e₃
  funext j
  fin_cases j <;> simp [bottomRow, e₃, coe_dGL, diagonal]

private theorem upperUnipotent3_eq (x y z : 𝔸) :
    (upperUnipotent3 x y z : AdelicGL 3 (𝓞 ℚ) ℚ) =
      upperUnipotent3 0 0 z * upperUnipotent3 0 y 0 * upperUnipotent3 x 0 0 := by
  refine Units.ext ?_
  simp only [Units.val_mul, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem dGL_mul_upperUnipotent3 {w : 𝔸ˣ} (hw : (w : 𝔸) = 2) (x y z : 𝔸) :
    (dGL ![w, 1, 1] * upperUnipotent3 x 0 0 : AdelicGL 3 (𝓞 ℚ) ℚ) =
        upperUnipotent3 x 0 0 * upperUnipotent3 x 0 0 * dGL ![w, 1, 1] ∧
      (dGL ![w, w, 1] * upperUnipotent3 0 y 0 : AdelicGL 3 (𝓞 ℚ) ℚ) =
        upperUnipotent3 0 y 0 * upperUnipotent3 0 y 0 * dGL ![w, w, 1] ∧
      (dGL ![w, 1, 1] * upperUnipotent3 0 0 z : AdelicGL 3 (𝓞 ℚ) ℚ) =
        upperUnipotent3 0 0 z * upperUnipotent3 0 0 z * dGL ![w, 1, 1] := by
  refine ⟨Units.ext ?_, Units.ext ?_, Units.ext ?_⟩
  all_goals
    simp only [Units.val_mul, upperUnipotent3_coe, coe_dGL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, diagonal, hw]
  all_goals ring

private theorem map_vecMul_rowHaar (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Measure.map (fun x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ => x ᵥ* (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) rowHaar =
      (ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g)))⁻¹ • rowHaar := by
  have hfun : (fun x : Fin 3 → 𝔸 => x ᵥ* (g : Matrix (Fin 3) (Fin 3) 𝔸)) = fun x => transposeGL g • x := by
    funext x
    rw [Units.smul_def, Matrix.smul_eq_mulVec]
    exact (Matrix.mulVec_transpose _ _).symm
  have hmap : Measure.map (fun x : Fin 3 → 𝔸 => transposeGL g • x) rowHaar =
      DomMulAct.mk (transposeGL g)⁻¹ • (rowHaar : Measure (Fin 3 → 𝔸)) := by
    refine Measure.ext fun s hs => ?_
    rw [Measure.map_apply (measurable_const_smul _) hs, Set.preimage_smul, Measure.domSMul_apply,
      Equiv.symm_apply_apply]
  have hinv : distribHaarChar (Fin 3 → 𝔸) (transposeGL g)⁻¹ = (distribHaarChar (Fin 3 → 𝔸) (transposeGL g))⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel, map_one])
  have hne : distribHaarChar 𝔸 (Matrix.GeneralLinearGroup.det g) ≠ 0 := (distribHaarChar_pos).ne'
  rw [hfun, hmap, domSMul_rowHaar, hinv, distribHaarChar_rows, det_transposeGL, NumberField.TateGlobal.ideleNorm,
    ENNReal.ofReal_coe_nnreal]
  refine Measure.ext fun s _ => ?_
  rw [Measure.coe_nnreal_smul_apply, Measure.smul_apply, smul_eq_mul, ENNReal.coe_inv hne]

private theorem lintegral_vecMul_rowHaar (g : AdelicGL 3 (𝓞 ℚ) ℚ) (φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℝ≥0∞)
    (hφ : Measurable φ) :
    ∫⁻ x, φ (x ᵥ* (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) ∂rowHaar =
      (ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g)))⁻¹ *
        ∫⁻ x, φ x ∂rowHaar := by
  have hmeas : Measurable fun x : Fin 3 → 𝔸 => x ᵥ* (g : Matrix (Fin 3) (Fin 3) 𝔸) := by
    have : (fun x : Fin 3 → 𝔸 => x ᵥ* (g : Matrix (Fin 3) (Fin 3) 𝔸)) = fun x => transposeGL g • x := by
      funext x
      rw [Units.smul_def, Matrix.smul_eq_mulVec]
      exact (Matrix.mulVec_transpose _ _).symm
    rw [this]
    exact measurable_const_smul _
  rw [← lintegral_map hφ hmeas, map_vecMul_rowHaar, lintegral_smul_measure, smul_eq_mul]

private theorem isMulRightInvariant_adelicGLHaar :
    (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).IsMulRightInvariant := by
  haveI := secondCountableTopology_adelicGL3
  set μ : Measure (AdelicGL 3 (𝓞 ℚ) ℚ) := adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ with hμ

  have hΔ : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, Measure.modularCharacter g = 1 := by
    intro g
    let ρ : AdelicGL 3 (𝓞 ℚ) ℚ →* ℝ≥0ˣ := (Measure.modularCharacter).toHomUnits
    suffices ρ g = 1 by
      have := congrArg (fun u : ℝ≥0ˣ => (u : ℝ≥0)) this
      simpa [ρ, MonoidHom.coe_toHomUnits] using this
    refine eq_one_of_apply_scalar (hasIdempotentPivots_adeleRing ℚ) (isUnit_two_adeleRing ℚ)
      (units_pow_eq_one two_ne_zero) (units_pow_eq_one three_ne_zero) ρ (fun a => Units.ext ?_) g
    show Measure.modularCharacterFun (dGL fun _ : Fin 3 => a) = ((1 : ℝ≥0ˣ) : ℝ≥0)
    rw [Units.val_one, Measure.modularCharacterFun_eq_haarScalarFactor μ]
    have hz : Measure.map (fun x => x * dGL fun _ : Fin 3 => a) μ = μ := by
      rw [show (fun x => x * dGL fun _ : Fin 3 => a) = fun x => dGL (fun _ : Fin 3 => a) * x from
        funext (scalar_comm a)]
      exact map_mul_left_eq_self μ _
    rw [haarScalarFactor_congr hz, Measure.haarScalarFactor_self]
  refine ⟨fun g => ?_⟩
  rw [Measure.isMulLeftInvariant_eq_smul (Measure.map (· * g) μ) μ,
    ← Measure.modularCharacterFun_eq_haarScalarFactor μ g]
  change Measure.modularCharacter g • μ = μ
  rw [hΔ g]
  exact one_smul ℝ≥0 μ

private theorem map_mul_left_haar_inv_mirabolic [LocallyCompactSpace ↥mirabolic] (n : ↥mirabolic)
    (hn : (n : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ WhittakerBlock.unipotentSubgroup3) :
    Measure.map (fun p : ↥mirabolic => n * p) (Measure.haar : Measure ↥mirabolic).inv =
      (Measure.haar : Measure ↥mirabolic).inv := by
  haveI := secondCountableTopology_adelicGL3
  haveI : SecondCountableTopology ↥mirabolic := TopologicalSpace.Subtype.secondCountableTopology _
  let Δ : ↥mirabolic →* ℝ≥0 := Measure.modularCharacter
  have hΔne : ∀ p, Δ p ≠ 0 := fun p => ((Group.isUnit p).map Δ).ne_zero

  have hsq : ∀ d p : ↥mirabolic, d * p = p * p * d → Δ p = 1 := by
    intro d p h
    have h' := congrArg Δ h
    rw [map_mul, map_mul, map_mul, mul_comm (Δ d) (Δ p)] at h'
    exact (mul_eq_left₀ (hΔne p)).mp (mul_right_cancel₀ (hΔne d) h').symm
  obtain ⟨w, hw⟩ := isUnit_two_adeleRing ℚ
  have hNP := unipotentSubgroup3_le_mirabolic
  have hmem : ∀ x y z : 𝔸, (upperUnipotent3 x y z : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ mirabolic := fun x y z =>
    hNP (Subgroup.subset_closure ⟨(x, y, z), rfl⟩)

  have hgen : ∀ x y z : 𝔸, Δ ⟨upperUnipotent3 x y z, hmem x y z⟩ = 1 := by
    intro x y z
    obtain ⟨c1, c2, c3⟩ := dGL_mul_upperUnipotent3 hw x y z
    have hsplit : (⟨upperUnipotent3 x y z, hmem x y z⟩ : ↥mirabolic) =
        ⟨_, hmem 0 0 z⟩ * ⟨_, hmem 0 y 0⟩ * ⟨_, hmem x 0 0⟩ := Subtype.ext (upperUnipotent3_eq x y z)
    rw [hsplit, map_mul, map_mul, hsq ⟨_, dGL_mem_mirabolic w 1⟩ ⟨_, hmem 0 0 z⟩ (Subtype.ext c3),
      hsq ⟨_, dGL_mem_mirabolic w w⟩ ⟨_, hmem 0 y 0⟩ (Subtype.ext c2),
      hsq ⟨_, dGL_mem_mirabolic w 1⟩ ⟨_, hmem x 0 0⟩ (Subtype.ext c1), one_mul, one_mul]

  have hall : ∀ m (hm : m ∈ WhittakerBlock.unipotentSubgroup3), Δ ⟨m, hNP hm⟩ = 1 := by
    intro m hm
    induction hm using Subgroup.closure_induction with
    | mem m hm' =>
      obtain ⟨t, rfl⟩ := hm'
      exact hgen _ _ _
    | one => exact map_one Δ
    | mul m m' hm hm' ih ih' =>
      have : (⟨m * m', hNP (mul_mem hm hm')⟩ : ↥mirabolic) = ⟨m, hNP hm⟩ * ⟨m', hNP hm'⟩ := rfl
      rw [this, map_mul, ih, ih', one_mul]
    | inv m hm ih =>
      have hprod := map_mul Δ ⟨m⁻¹, hNP (inv_mem hm)⟩ ⟨m, hNP hm⟩
      have : (⟨m⁻¹, hNP (inv_mem hm)⟩ : ↥mirabolic) * ⟨m, hNP hm⟩ = 1 := Subtype.ext (inv_mul_cancel m)
      rw [this, map_one, ih, mul_one] at hprod
      exact hprod.symm

  have hright : ∀ m : ↥mirabolic, Δ m = 1 →
      Measure.map (fun p : ↥mirabolic => p * m) (Measure.haar : Measure ↥mirabolic) = Measure.haar := by
    intro m hm
    rw [Measure.isMulLeftInvariant_eq_smul (Measure.map (fun p : ↥mirabolic => p * m) Measure.haar) Measure.haar,
      ← Measure.modularCharacterFun_eq_haarScalarFactor]
    change Δ m • (Measure.haar : Measure ↥mirabolic) = Measure.haar
    rw [hm]
    exact one_smul ℝ≥0 _
  have hn' : Δ n⁻¹ = 1 := hall _ (inv_mem hn)
  rw [Measure.inv_def, Measure.map_map (measurable_const_mul n) measurable_inv]
  have hcomp : ((fun p : ↥mirabolic => n * p) ∘ Inv.inv) = Inv.inv ∘ fun p : ↥mirabolic => p * n⁻¹ := by
    funext p
    simp [_root_.mul_inv_rev]
  rw [hcomp, ← Measure.map_map measurable_inv (measurable_mul_const n⁻¹), hright n⁻¹ hn']

end JacobianUnimodular

end JacobianAndModulus

section CosetDensity

section Cosets

variable {G : Type} [Group G] (H : Subgroup G)

private theorem exists_mem_mul_eq_out (g : G) :
    ∃ n ∈ H, n * g = (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out := by
  have h : (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out ∈ MulAction.orbit H g := by
    rw [← MulAction.orbitRel.Quotient.orbit_mk]
    exact MulAction.orbitRel.Quotient.mem_orbit.2 (Quotient.out_eq' _)
  obtain ⟨n, hn⟩ := MulAction.mem_orbit_iff.1 h
  exact ⟨n, n.2, hn⟩

variable {H}

private theorem apply_out_mk {α : Type} {h : G → α} (hinv : ∀ n ∈ H, ∀ g, h (n * g) = h g) (g : G) :
    h (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out = h g := by
  obtain ⟨n, hn, e⟩ := exists_mem_mul_eq_out H g
  rw [← e, hinv n hn]

private theorem prop_out_mk_iff {P : G → Prop} (hinv : ∀ n ∈ H, ∀ g, P (n * g) ↔ P g) (g : G) :
    P (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out ↔ P g := by
  obtain ⟨n, hn, e⟩ := exists_mem_mul_eq_out H g
  rw [← e, hinv n hn]

private theorem measurableSet_setOf_out [MeasurableSpace G] {P : G → Prop} (hP : MeasurableSet {g | P g})
    (hinv : ∀ n ∈ H, ∀ g, P (n * g) ↔ P g) : MeasurableSet {q : MulAction.orbitRel.Quotient H G | P q.out} := by
  rw [measurableSet_quotient]
  convert hP using 1
  ext g
  exact prop_out_mk_iff hinv g

end Cosets

section QuotientDensity

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] in
private theorem measurable_weight (H : Subgroup G) (μH : Measure H) : Measurable (HaarQuotient.weight H μH) := by
  unfold HaarQuotient.weight
  split_ifs with h
  · haveI := h.1
    haveI := h.2
    exact Measurable.tsum fun n =>
      measurable_const.mul (measurable_const.indicator isOpen_interior.measurableSet)
  · exact measurable_const

private theorem measurable_density (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H)
    [μH.IsHaarMeasure] : Measurable (HaarQuotient.density H μH) := by
  haveI : SigmaCompactSpace H := hH.sigmaCompactSpace
  unfold HaarQuotient.density
  refine (measurable_weight H μH).div ?_
  refine Measurable.lintegral_prod_right (f := fun g (x : H) => HaarQuotient.weight H μH ((x : G) * g)) ?_
  exact (measurable_weight H μH).comp
    ((continuous_subtype_val.comp continuous_snd).mul continuous_fst).measurable

private theorem lintegral_out_eq_lintegral_density_mul (μ : Measure G) (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] (h : G → ℝ≥0∞) (hh : Measurable h)
    (hinv : ∀ n ∈ H, ∀ g, h (n * g) = h g) :
    ∫⁻ q, h q.out ∂(HaarQuotient.measure μ H μH) = ∫⁻ g, HaarQuotient.density H μH g * h g ∂μ := by
  have hout : (fun g : G => h (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out) = h := by
    funext g
    exact apply_out_mk hinv g
  have hq : Measurable fun q : MulAction.orbitRel.Quotient H G => h q.out := by
    rw [measurable_from_quotient]
    have hcomp : ((fun q : MulAction.orbitRel.Quotient H G => h q.out) ∘
        (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G)) = h := hout
    rw [hcomp]
    exact hh
  unfold HaarQuotient.measure
  rw [lintegral_map hq measurable_quotient_mk'', hout,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_density H hH μH) hh]
  rfl

end QuotientDensity

section Block

attribute [local instance] secondCountableTopology_adelicGL3 NumberField.AdelicHaar.borelSpace_glBorel

private def integrand (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (σ : ℝ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) : ℝ≥0∞ :=
  (‖W g‖₊ : ℝ≥0∞) ^ 2 * (‖Φ fun j : Fin 3 => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖₊ : ℝ≥0∞) *
    ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ)

private theorem block_eq_setLIntegral (pins : AutomorphicForm.CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (σ : ℝ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    WhittakerBlock.block pins ψ f Φ σ S =
      ∫⁻ q in WhittakerBlock.zerothShell S, integrand (whittaker3 pins ψ f) Φ σ q.out
        ∂WhittakerBlock.quotientMeasure :=
  rfl

private theorem block_eq_lintegral_density_mul (pins : AutomorphicForm.CarrierPins ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (σ : ℝ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) [WhittakerBlock.unipotentHaar3.IsHaarMeasure]
    (C : AdelicGL 3 (𝓞 ℚ) ℚ → Prop) (hC : WhittakerBlock.zerothShell S = {q | C q.out})
    (hCmeas : MeasurableSet {g | C g})
    (hCinv : ∀ n ∈ WhittakerBlock.unipotentSubgroup3, ∀ g, C (n * g) ↔ C g)
    (hI : Measurable (integrand (whittaker3 pins ψ f) Φ σ))
    (hIinv : ∀ n ∈ WhittakerBlock.unipotentSubgroup3, ∀ g,
      integrand (whittaker3 pins ψ f) Φ σ (n * g) = integrand (whittaker3 pins ψ f) Φ σ g) :
    WhittakerBlock.block pins ψ f Φ σ S =
      ∫⁻ g, HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3 g *
        {g | C g}.indicator (integrand (whittaker3 pins ψ f) Φ σ) g
        ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
  classical
  rw [block_eq_setLIntegral, hC, ← lintegral_indicator (measurableSet_setOf_out hCmeas hCinv)]
  have hrepr : ∀ q : MulAction.orbitRel.Quotient WhittakerBlock.unipotentSubgroup3 (AdelicGL 3 (𝓞 ℚ) ℚ),
      {q | C q.out}.indicator (fun q => integrand (whittaker3 pins ψ f) Φ σ q.out) q =
        {g | C g}.indicator (integrand (whittaker3 pins ψ f) Φ σ) q.out := by
    intro q
    by_cases hq : C q.out
    · rw [Set.indicator_of_mem (show q ∈ {q | C q.out} from hq),
        Set.indicator_of_mem (show q.out ∈ {g | C g} from hq)]
    · rw [Set.indicator_of_notMem (show q ∉ {q | C q.out} from hq),
        Set.indicator_of_notMem (show q.out ∉ {g | C g} from hq)]
  simp only [hrepr]
  have hmain := lintegral_out_eq_lintegral_density_mul (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)
    WhittakerBlock.unipotentSubgroup3 WhittakerBlock.isClosed_unipotentSubgroup3 WhittakerBlock.unipotentHaar3
    ({g | C g}.indicator (integrand (whittaker3 pins ψ f) Φ σ)) (hI.indicator hCmeas) ?_
  · exact hmain
  · intro n hn g
    by_cases hg : C g
    · rw [Set.indicator_of_mem (show n * g ∈ {g | C g} from (hCinv n hn g).2 hg),
        Set.indicator_of_mem (show g ∈ {g | C g} from hg), hIinv n hn g]
    · rw [Set.indicator_of_notMem (show n * g ∉ {g | C g} from fun h => hg ((hCinv n hn g).1 h)),
        Set.indicator_of_notMem (show g ∉ {g | C g} from hg)]

end Block

section Translate

private theorem whittaker3_translateRight (pins : AutomorphicForm.CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (h : AdelicGL 3 (𝓞 ℚ) ℚ) (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 pins ψ (SlabL2.translateRight h F) g = whittaker3 pins ψ F (g * h) := by
  simp only [whittaker3, SlabL2.translateRight_apply, mul_assoc]

end Translate

end CosetDensity

section ShellCondition

section Shell

private def ShellCond (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (g : AdelicGL 3 (𝓞 ℚ) ℚ) : Prop :=
  ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S →
    ∃ (x y z : p.adicCompletion ℚ) (k : GL (Fin 3) (p.adicCompletion ℚ)),
      k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p ∧ componentAt3 (𝓞 ℚ) ℚ p g = upperUnipotent3 x y z * k

section Local

variable (p : HeightOneSpectrum (𝓞 ℚ))

private def LocUnip (n : LocalGL3 p) : Prop :=
  ∃ x y z : p.adicCompletion ℚ, n = upperUnipotent3 x y z

private theorem locUnip_mul {n n' : LocalGL3 p} (hn : LocUnip p n) (hn' : LocUnip p n') : LocUnip p (n * n') := by
  obtain ⟨x, y, z, rfl⟩ := hn
  obtain ⟨x', y', z', rfl⟩ := hn'
  refine ⟨x' + x, y' + y, z' + x * y' + z, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem locUnip_inv {n : LocalGL3 p} (hn : LocUnip p n) : LocUnip p n⁻¹ := by
  obtain ⟨x, y, z, rfl⟩ := hn
  exact ⟨-x, -y, x * y - z, Units.ext rfl⟩

private def ZeroShellAt (x : LocalGL3 p) : Prop :=
  ∃ (a b c : p.adicCompletion ℚ) (k : GL (Fin 3) (p.adicCompletion ℚ)),
    k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p ∧ x = upperUnipotent3 a b c * k

private theorem zeroShellAt_unip_mul_iff {n : LocalGL3 p} (hn : LocUnip p n) (x : LocalGL3 p) :
    ZeroShellAt p (n * x) ↔ ZeroShellAt p x := by
  constructor
  · rintro ⟨a, b, c, k, hk, h⟩
    obtain ⟨a', b', c', hm⟩ := locUnip_mul p (locUnip_inv p hn) ⟨a, b, c, rfl⟩
    exact ⟨a', b', c', k, hk, by rw [← hm, mul_assoc, ← h, inv_mul_cancel_left]⟩
  · rintro ⟨a, b, c, k, hk, rfl⟩
    obtain ⟨a', b', c', hm⟩ := locUnip_mul p hn ⟨a, b, c, rfl⟩
    exact ⟨a', b', c', k, hk, by rw [← mul_assoc, hm]⟩

private theorem zeroShellAt_mul_right_iff {k₀ : LocalGL3 p} (hk₀ : k₀ ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    (x : LocalGL3 p) : ZeroShellAt p (x * k₀) ↔ ZeroShellAt p x := by
  constructor
  · rintro ⟨a, b, c, k, hk, h⟩
    exact ⟨a, b, c, k * k₀⁻¹, mul_mem hk (inv_mem hk₀), by rw [← mul_assoc, ← h, mul_inv_cancel_right]⟩
  · rintro ⟨a, b, c, k, hk, rfl⟩
    exact ⟨a, b, c, k * k₀, mul_mem hk hk₀, by rw [mul_assoc]⟩

private theorem isOpen_localMaximalCompact3 : IsOpen ((localMaximalCompact3 (𝓞 ℚ) ℚ p : Set (LocalGL3 p))) := by
  have hpre : ∀ f : LocalGL3 p → p.adicCompletion ℚ, Continuous f → IsOpen {k : LocalGL3 p | Valued.v (f k) ≤ 1} :=
    fun f hf => by
      simpa [Set.preimage, Valuation.mem_integer_iff] using (Valued.isOpen_integer (p.adicCompletion ℚ)).preimage hf
  have hK : (localMaximalCompact3 (𝓞 ℚ) ℚ p : Set (LocalGL3 p)) =
      (⋂ i, ⋂ j, {k : LocalGL3 p | Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ 1}) ∩
        ⋂ i, ⋂ j, {k : LocalGL3 p |
          Valued.v (((k⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ 1} := by
    ext k
    simp only [SetLike.mem_coe, mem_localMaximalCompact3_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [hK]
  exact (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hpre _ (Units.continuous_val.matrix_elem i j)).inter
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hpre _ (Units.continuous_coe_inv.matrix_elem i j))

private theorem isOpen_setOf_zeroShellAt : IsOpen {x : LocalGL3 p | ZeroShellAt p x} := by
  have h : {x : LocalGL3 p | ZeroShellAt p x} =
      ⋃ t : p.adicCompletion ℚ × p.adicCompletion ℚ × p.adicCompletion ℚ,
        (fun k : LocalGL3 p => upperUnipotent3 t.1 t.2.1 t.2.2 * k) ''
          (localMaximalCompact3 (𝓞 ℚ) ℚ p : Set (LocalGL3 p)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, SetLike.mem_coe]
    constructor
    · rintro ⟨a, b, c, k, hk, rfl⟩
      exact ⟨(a, b, c), k, hk, rfl⟩
    · rintro ⟨t, k, hk, rfl⟩
      exact ⟨t.1, t.2.1, t.2.2, k, hk, rfl⟩
  rw [h]
  exact isOpen_iUnion fun t => (isOpenMap_mul_left _) _ (isOpen_localMaximalCompact3 p)

end Local

private theorem map_upperUnipotent3 {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x y z : A) :
    Matrix.GeneralLinearGroup.map f (upperUnipotent3 x y z) = upperUnipotent3 (f x) (f y) (f z) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.map, RingHom.mapMatrix_apply, Matrix.map_apply, upperUnipotent3_coe]

private theorem locUnip_componentAt3 {n : AdelicGL 3 (𝓞 ℚ) ℚ} (hn : n ∈ WhittakerBlock.unipotentSubgroup3)
    (p : HeightOneSpectrum (𝓞 ℚ)) : LocUnip p (componentAt3 (𝓞 ℚ) ℚ p n) := by
  obtain ⟨x, y, z, rfl⟩ := (WhittakerBlock.mem_unipotentSubgroup3_iff n).1 hn
  exact ⟨_, _, _, map_upperUnipotent3 (evalHom p) x y z⟩

private theorem continuous_evalHom (q : HeightOneSpectrum (𝓞 ℚ)) : Continuous (evalHom q) :=
  (AdelicLevel.continuous_finAdeleEval (𝓞 ℚ) ℚ q).comp continuous_snd

private theorem continuous_componentAt3 (q : HeightOneSpectrum (𝓞 ℚ)) : Continuous (componentAt3 (𝓞 ℚ) ℚ q) :=
  Continuous.units_map _ ((continuous_id.matrix_map (continuous_evalHom q)) :
    Continuous fun m : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ) => m.map (evalHom q))

private theorem countable_heightOneSpectrum : Countable (HeightOneSpectrum (𝓞 ℚ)) :=
  Countable.of_equiv _ (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm

private theorem zerothShell_eq_setOf_shellCond (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    WhittakerBlock.zerothShell S = {q | ShellCond S q.out} := by
  ext q
  rfl

private theorem measurableSet_shellCond (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    MeasurableSet {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} := by
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := countable_heightOneSpectrum
  have h : {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} =
      ⋂ p, ⋂ (_ : p ∉ S), {g : AdelicGL 3 (𝓞 ℚ) ℚ | ZeroShellAt p (componentAt3 (𝓞 ℚ) ℚ p g)} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rfl
  rw [h]
  exact MeasurableSet.iInter fun p => MeasurableSet.iInter fun _ =>
    ((isOpen_setOf_zeroShellAt p).preimage (continuous_componentAt3 p)).measurableSet

private theorem shellCond_mul_left_iff (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    ∀ n ∈ WhittakerBlock.unipotentSubgroup3, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ShellCond S (n * g) ↔ ShellCond S g := by
  intro n hn g
  show (∀ p, p ∉ S → ZeroShellAt p (componentAt3 (𝓞 ℚ) ℚ p (n * g))) ↔
    ∀ p, p ∉ S → ZeroShellAt p (componentAt3 (𝓞 ℚ) ℚ p g)
  exact forall_congr' fun p => imp_congr_right fun _ => by
    rw [map_mul]
    exact zeroShellAt_unip_mul_iff p (locUnip_componentAt3 hn p) _

private theorem shellCond_mul_right_iff (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (g h : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hh : ∀ p, p ∉ S → componentAt3 (𝓞 ℚ) ℚ p h ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    ShellCond S (g * h) ↔ ShellCond S g := by
  show (∀ p, p ∉ S → ZeroShellAt p (componentAt3 (𝓞 ℚ) ℚ p (g * h))) ↔
    ∀ p, p ∉ S → ZeroShellAt p (componentAt3 (𝓞 ℚ) ℚ p g)
  exact forall_congr' fun p => imp_congr_right fun hp => by
    rw [map_mul]
    exact zeroShellAt_mul_right_iff p (hh p hp) _

end Shell

end ShellCondition

section RowsOfTheShell

section ShellRows

private theorem primitiveAt_bottomRow_of_shellCond (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {g : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hg : ShellCond S g) (p : HeightOneSpectrum (𝓞 ℚ)) (hp : p ∉ S) : PrimitiveAt p (bottomRow g) := by
  obtain ⟨x, y, z, k, hk, hgk⟩ := hg p hp
  rw [mem_localMaximalCompact3_iff] at hk

  have hrow : ∀ j : Fin 3, evalHom p (bottomRow g j) = (k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 j := by
    intro j
    have h1 : evalHom p (bottomRow g j) =
        ((componentAt3 (𝓞 ℚ) ℚ p g : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))
          2 j := rfl
    rw [h1, hgk, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, upperUnipotent3_coe]
    simp
  refine ⟨fun j => ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hrow]
    exact hk.1 2 j
  ·
    by_contra hne
    have hlt : ∀ j : Fin 3, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 j) < 1 := fun j =>
      lt_of_le_of_ne (hk.1 2 j) fun h => hne ⟨j, by rw [hrow]; exact h⟩
    have hkk : ∑ j : Fin 3, (k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 j *
        ((k⁻¹ : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) j 2 = 1 := by
      have h := congrFun (congrFun k.mul_inv 2) 2
      rwa [Matrix.mul_apply, Matrix.one_apply_eq] at h
    have hone : Valued.v (∑ j : Fin 3, (k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 j *
        ((k⁻¹ : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) j 2) < 1 := by
      refine Valuation.map_sum_lt Valued.v one_ne_zero fun j _ => ?_
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (hk.2 j 2)) (hlt j)
    rw [hkk, map_one] at hone
    exact lt_irrefl _ hone

private theorem nonzeroAt_bottomRow (g : AdelicGL 3 (𝓞 ℚ) ℚ) (p : HeightOneSpectrum (𝓞 ℚ)) :
    NonzeroAt p (bottomRow g) := by
  by_contra hne
  have h0 : ∀ j : Fin 3,
      ((componentAt3 (𝓞 ℚ) ℚ p g : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) 2 j
        = 0 := fun j => by
    by_contra h
    exact hne ⟨j, h⟩
  have hdet := Matrix.det_eq_zero_of_row_eq_zero 2 h0
  rw [← Matrix.GeneralLinearGroup.val_det_apply] at hdet
  exact (Matrix.GeneralLinearGroup.det (componentAt3 (𝓞 ℚ) ℚ p g)).ne_zero hdet

private theorem nonzeroArch_bottomRow (g : AdelicGL 3 (𝓞 ℚ) ℚ) : NonzeroArch (bottomRow g) := by
  by_contra hne
  have h0 : ∀ j : Fin 3,
      ((archComponent3 (𝓞 ℚ) ℚ g : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))
        2 j = 0 := fun j => by
    by_contra h
    exact hne ⟨j, h⟩
  have hdet := Matrix.det_eq_zero_of_row_eq_zero 2 h0
  rw [← Matrix.GeneralLinearGroup.val_det_apply] at hdet
  exact (Matrix.GeneralLinearGroup.det (archComponent3 (𝓞 ℚ) ℚ g)).ne_zero hdet

private theorem bottomRow_mem_explicitRows_of_shellCond (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {g : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hg : ShellCond S g) : bottomRow g ∈ explicitRows S := by
  exact ⟨fun p hp => primitiveAt_bottomRow_of_shellCond S hg p hp, fun p _ => nonzeroAt_bottomRow g p,
    nonzeroArch_bottomRow g⟩

end ShellRows

end RowsOfTheShell

section SectionAndRowSets

section SectionHeads

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

attribute [local instance] NumberField.AdeleRing.secondCountableTopology

open scoped RestrictedProduct

open Topology

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

private theorem arch_mul_apply (a b : 𝔸) (w : InfinitePlace ℚ) : (a * b).1 w = a.1 w * b.1 w := rfl

private theorem arch_add_apply (a b : 𝔸) (w : InfinitePlace ℚ) : (a + b).1 w = a.1 w + b.1 w := rfl

private theorem arch_one_apply (w : InfinitePlace ℚ) : (1 : 𝔸).1 w = 1 := rfl

private theorem arch_zero_apply (w : InfinitePlace ℚ) : (0 : 𝔸).1 w = 0 := rfl

private theorem fin_mul_apply (a b : 𝔸) (p : HeightOneSpectrum (𝓞 ℚ)) : (a * b).2 p = a.2 p * b.2 p := rfl

private theorem fin_add_apply (a b : 𝔸) (p : HeightOneSpectrum (𝓞 ℚ)) : (a + b).2 p = a.2 p + b.2 p := rfl

private theorem fin_one_apply (p : HeightOneSpectrum (𝓞 ℚ)) : (1 : 𝔸).2 p = 1 := rfl

private theorem fin_zero_apply (p : HeightOneSpectrum (𝓞 ℚ)) : (0 : 𝔸).2 p = 0 := rfl

private theorem ext_of_places {a b : 𝔸} (h₁ : ∀ w, a.1 w = b.1 w) (h₂ : ∀ p, a.2 p = b.2 p) : a = b :=
  Prod.ext (funext h₁) (FiniteAdeleRing.ext ℚ h₂)

private theorem evalHom_eq (p : HeightOneSpectrum (𝓞 ℚ)) (a : 𝔸) : evalHom p a = a.2 p := rfl

private theorem adeleArch_eq (a : 𝔸) : AdelicLevel.adeleArch (𝓞 ℚ) ℚ a = a.1 := rfl

private def rowAt (p : HeightOneSpectrum (𝓞 ℚ)) (x : Fin 3 → 𝔸) : Fin 3 → p.adicCompletion ℚ := fun j => (x j).2 p

private def rowArch (w : InfinitePlace ℚ) (x : Fin 3 → 𝔸) : Fin 3 → w.Completion := fun j => (x j).1 w

private theorem rowAt_apply (p : HeightOneSpectrum (𝓞 ℚ)) (x : Fin 3 → 𝔸) (j : Fin 3) : rowAt p x j = (x j).2 p := rfl

private theorem rowArch_apply (w : InfinitePlace ℚ) (x : Fin 3 → 𝔸) (j : Fin 3) : rowArch w x j = (x j).1 w := rfl

private theorem mem_explicitRows {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {x : Fin 3 → 𝔸} :
    x ∈ explicitRows S ↔ (∀ p, p ∉ S → PrimitiveAt p x) ∧ (∀ p ∈ S, NonzeroAt p x) ∧ NonzeroArch x :=
  Iff.rfl

private theorem mem_rowDomain {x : Fin 3 → 𝔸} :
    x ∈ rowDomain ↔ (∀ p, NonzeroAt p x) ∧ NonzeroArch x ∧ ∀ᶠ p in Filter.cofinite, PrimitiveAt p x :=
  Iff.rfl

private theorem primitiveAt_iff (p : HeightOneSpectrum (𝓞 ℚ)) (x : Fin 3 → 𝔸) :
    PrimitiveAt p x ↔ (∀ j, Valued.v (rowAt p x j) ≤ 1) ∧ ∃ j, Valued.v (rowAt p x j) = 1 :=
  Iff.rfl

private theorem nonzeroAt_iff (p : HeightOneSpectrum (𝓞 ℚ)) (x : Fin 3 → 𝔸) : NonzeroAt p x ↔ ∃ j, rowAt p x j ≠ 0 :=
  Iff.rfl

private theorem mem_rowDomain_of_mem_explicitRows {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {x : Fin 3 → 𝔸}
    (hx : x ∈ explicitRows S) : x ∈ rowDomain := by
  obtain ⟨hprim, hS, harch⟩ := mem_explicitRows.mp hx
  refine mem_rowDomain.mpr ⟨fun p => ?_, harch, ?_⟩
  · by_cases hp : p ∈ S
    · exact hS p hp
    · obtain ⟨j, hj⟩ := (hprim p hp).2
      exact ⟨j, fun h0 => by rw [h0, map_zero] at hj; exact zero_ne_one hj⟩
  · refine Filter.eventually_cofinite.mpr (S.finite_toSet.subset fun p hp => ?_)
    by_contra hpS
    exact hp (hprim p fun h => hpS (Finset.mem_coe.mpr h))

private theorem exists_rowArch_ne_zero {x : Fin 3 → 𝔸} (hx : NonzeroArch x) (w : InfinitePlace ℚ) :
    ∃ j, rowArch w x j ≠ 0 := by
  obtain ⟨j, hj⟩ := hx
  refine ⟨j, fun h0 => hj ?_⟩
  rw [adeleArch_eq]
  funext w'
  rw [Subsingleton.elim w' w]
  exact h0

private theorem nonzeroArch_of_rowArch {x : Fin 3 → 𝔸} {w : InfinitePlace ℚ} (h : ∃ j, rowArch w x j ≠ 0) :
    NonzeroArch x := by
  obtain ⟨j, hj⟩ := h
  exact ⟨j, fun h0 => hj (by rw [rowArch_apply, ← adeleArch_eq, h0]; rfl)⟩

private def preferredIndex (P : Fin 3 → Prop) [DecidablePred P] : Fin 3 :=
  if P 2 then 2 else if P 1 then 1 else 0

private theorem preferredIndex_spec {P : Fin 3 → Prop} [DecidablePred P] (h : ∃ j, P j) : P (preferredIndex P) := by
  unfold preferredIndex
  split_ifs with h2 h1
  · exact h2
  · exact h1
  · obtain ⟨j, hj⟩ := h
    fin_cases j
    · exact hj
    · exact absurd hj h1
    · exact absurd hj h2

private theorem preferredIndex_eq_two {P : Fin 3 → Prop} [DecidablePred P] (h : P 2) : preferredIndex P = 2 := by
  simp [preferredIndex, h]

private def unitPattern (p : HeightOneSpectrum (𝓞 ℚ)) (y : Fin 3 → p.adicCompletion ℚ) : Fin 3 :=
  preferredIndex fun j => Valued.v (y j) = 1

private theorem valued_unitPattern (p : HeightOneSpectrum (𝓞 ℚ)) {y : Fin 3 → p.adicCompletion ℚ}
    (h : ∃ j, Valued.v (y j) = 1) : Valued.v (y (unitPattern p y)) = 1 :=
  preferredIndex_spec h

open scoped Classical in

private def finitePivot (p : HeightOneSpectrum (𝓞 ℚ)) (y : Fin 3 → p.adicCompletion ℚ) : Fin 3 :=
  if ∃ j, Valued.v (y j) = 1 then unitPattern p y else preferredIndex fun j => y j ≠ 0

private theorem finitePivot_of_exists_unit (p : HeightOneSpectrum (𝓞 ℚ)) {y : Fin 3 → p.adicCompletion ℚ}
    (h : ∃ j, Valued.v (y j) = 1) : finitePivot p y = unitPattern p y := by
  unfold finitePivot
  rw [if_pos h]

private theorem valued_finitePivot (p : HeightOneSpectrum (𝓞 ℚ)) {y : Fin 3 → p.adicCompletion ℚ}
    (h : ∃ j, Valued.v (y j) = 1) : Valued.v (y (finitePivot p y)) = 1 := by
  rw [finitePivot_of_exists_unit p h]
  exact valued_unitPattern p h

open scoped Classical in
private theorem finitePivot_ne_zero (p : HeightOneSpectrum (𝓞 ℚ)) {y : Fin 3 → p.adicCompletion ℚ} (h : ∃ j, y j ≠ 0) :
    y (finitePivot p y) ≠ 0 := by
  unfold finitePivot
  split_ifs with hu
  · intro h0
    have h1 := valued_unitPattern p hu
    rw [h0, map_zero] at h1
    exact zero_ne_one h1
  · exact preferredIndex_spec h

private theorem finitePivot_eq_two (p : HeightOneSpectrum (𝓞 ℚ)) {y : Fin 3 → p.adicCompletion ℚ}
    (h : Valued.v (y 2) = 1) : finitePivot p y = 2 := by
  rw [finitePivot_of_exists_unit p ⟨2, h⟩]
  exact preferredIndex_eq_two h

open scoped Classical in

private def archPivot (w : InfinitePlace ℚ) (y : Fin 3 → w.Completion) : Fin 3 :=
  preferredIndex fun j => y j ≠ 0

open scoped Classical in
private theorem archPivot_ne_zero (w : InfinitePlace ℚ) {y : Fin 3 → w.Completion} (h : ∃ j, y j ≠ 0) :
    y (archPivot w y) ≠ 0 :=
  preferredIndex_spec h

open scoped Classical in
private theorem archPivot_eq_two (w : InfinitePlace ℚ) {y : Fin 3 → w.Completion} (h : y 2 ≠ 0) : archPivot w y = 2 :=
  preferredIndex_eq_two h

private def pivotIdempotent (x : Fin 3 → 𝔸) (j : Fin 3) : 𝔸 :=
  (fun w => if archPivot w (rowArch w x) = j then 1 else 0,
    ⟨fun p => if finitePivot p (rowAt p x) = j then 1 else 0, Filter.Eventually.of_forall fun p => by
      by_cases h : finitePivot p (rowAt p x) = j
      · simp only [h, if_true, SetLike.mem_coe]
        exact one_mem _
      · simp only [h, if_false, SetLike.mem_coe]
        exact zero_mem _⟩)

private theorem pivotIdempotent_arch (x : Fin 3 → 𝔸) (j : Fin 3) (w : InfinitePlace ℚ) :
    (pivotIdempotent x j).1 w = if archPivot w (rowArch w x) = j then 1 else 0 := rfl

private theorem pivotIdempotent_fin (x : Fin 3 → 𝔸) (j : Fin 3) (p : HeightOneSpectrum (𝓞 ℚ)) :
    (pivotIdempotent x j).2 p = if finitePivot p (rowAt p x) = j then 1 else 0 := rfl

open scoped Classical in

private def pivotInverse (x : Fin 3 → 𝔸) : 𝔸 :=
  if hx : x ∈ rowDomain then
    (fun w => (rowArch w x (archPivot w (rowArch w x)))⁻¹,
      ⟨fun p => (rowAt p x (finitePivot p (rowAt p x)))⁻¹, by
        filter_upwards [hx.2.2] with p hp
        simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀,
          valued_finitePivot p ((primitiveAt_iff p x).mp hp).2, inv_one, le_refl]⟩)
  else 0

private theorem pivotInverse_arch {x : Fin 3 → 𝔸} (hx : x ∈ rowDomain) (w : InfinitePlace ℚ) :
    (pivotInverse x).1 w = (rowArch w x (archPivot w (rowArch w x)))⁻¹ := by
  unfold pivotInverse
  rw [dif_pos hx]

private theorem pivotInverse_fin {x : Fin 3 → 𝔸} (hx : x ∈ rowDomain) (p : HeightOneSpectrum (𝓞 ℚ)) :
    (pivotInverse x).2 p = (rowAt p x (finitePivot p (rowAt p x)))⁻¹ := by
  unfold pivotInverse
  rw [dif_pos hx]
  rfl

private theorem pivotIdempotent_mul_self (x : Fin 3 → 𝔸) (j : Fin 3) :
    pivotIdempotent x j * pivotIdempotent x j = pivotIdempotent x j :=
  ext_of_places
    (fun w => by
      rw [arch_mul_apply, pivotIdempotent_arch]
      split_ifs <;> simp)
    (fun p => by
      rw [fin_mul_apply, pivotIdempotent_fin]
      split_ifs <;> simp)

private theorem pivotIdempotent_mul_of_ne (x : Fin 3 → 𝔸) {i j : Fin 3} (hij : i ≠ j) :
    pivotIdempotent x i * pivotIdempotent x j = 0 :=
  ext_of_places
    (fun w => by
      rw [arch_mul_apply, arch_zero_apply, pivotIdempotent_arch, pivotIdempotent_arch]
      split_ifs with hi hj
      · exact absurd (hi.symm.trans hj) hij
      all_goals simp)
    (fun p => by
      rw [fin_mul_apply, fin_zero_apply, pivotIdempotent_fin, pivotIdempotent_fin]
      split_ifs with hi hj
      · exact absurd (hi.symm.trans hj) hij
      all_goals simp)

private theorem pivotIdempotent_sum (x : Fin 3 → 𝔸) :
    pivotIdempotent x 0 + pivotIdempotent x 1 + pivotIdempotent x 2 = 1 :=
  ext_of_places
    (fun w => by
      rw [arch_add_apply, arch_add_apply, arch_one_apply, pivotIdempotent_arch, pivotIdempotent_arch,
        pivotIdempotent_arch]
      generalize archPivot w (rowArch w x) = k
      fin_cases k <;> simp)
    (fun p => by
      rw [fin_add_apply, fin_add_apply, fin_one_apply, pivotIdempotent_fin, pivotIdempotent_fin, pivotIdempotent_fin]
      generalize finitePivot p (rowAt p x) = k
      fin_cases k <;> simp)

private theorem pivotIdempotent_mul_pivotInverse {x : Fin 3 → 𝔸} (hx : x ∈ rowDomain) (j : Fin 3) :
    pivotIdempotent x j * (x j * pivotInverse x) = pivotIdempotent x j :=
  ext_of_places
    (fun w => by
      rw [arch_mul_apply, arch_mul_apply, pivotIdempotent_arch, pivotInverse_arch hx]
      split_ifs with h
      · have hne := archPivot_ne_zero w (exists_rowArch_ne_zero hx.2.1 w)
        rw [h] at hne ⊢
        rw [one_mul]
        exact mul_inv_cancel₀ hne
      · exact zero_mul _)
    (fun p => by
      rw [fin_mul_apply, fin_mul_apply, pivotIdempotent_fin, pivotInverse_fin hx]
      split_ifs with h
      · have hne := finitePivot_ne_zero p ((nonzeroAt_iff p x).mp (hx.1 p))
        rw [h] at hne ⊢
        rw [one_mul]
        exact mul_inv_cancel₀ hne
      · exact zero_mul _)

section Chart

variable {A : Type*} [CommRing A]

private def chartMatrix (e y : Fin 3 → A) : Matrix (Fin 3) (Fin 3) A :=
  !![e 2 + e 1, e 0, 0; 0, e 2, e 1 + e 0; y 0, y 1, y 2]

private def chartInverse (e y : Fin 3 → A) (d : A) : Matrix (Fin 3) (Fin 3) A :=
  !![e 2 + e 1 - e 0 * (y 1 * d), -(e 0 * (y 2 * d)), e 0 * d;
    e 0 - e 1 * (y 0 * d), e 2 - e 1 * (y 2 * d), e 1 * d;
    -(e 2 * (y 0 * d)), e 1 + e 0 - e 2 * (y 1 * d), e 2 * d]

private theorem chartMatrix_mul_chartInverse (e y : Fin 3 → A) (d : A) (h00 : e 0 * e 0 = e 0)
    (h11 : e 1 * e 1 = e 1) (h22 : e 2 * e 2 = e 2) (h01 : e 0 * e 1 = 0) (h02 : e 0 * e 2 = 0) (h12 : e 1 * e 2 = 0)
    (hsum : e 0 + e 1 + e 2 = 1) (hp0 : e 0 * (y 0 * d) = e 0) (hp1 : e 1 * (y 1 * d) = e 1)
    (hp2 : e 2 * (y 2 * d) = e 2) : chartMatrix e y * chartInverse e y d = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chartMatrix, chartInverse, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first
    | linear_combination h22 + h11 + h00 + 2 * h12 - (y 1 * d) * h02 - (y 1 * d) * h01 - (y 0 * d) * h01 + hsum
    | linear_combination (1 - y 2 * d) * h02 - 2 * (y 2 * d) * h01
    | linear_combination d * h02 + 2 * d * h01
    | linear_combination (1 - y 0 * d) * h02 - 2 * (y 0 * d) * h12
    | linear_combination h22 + h11 + h00 + 2 * h01 - (y 2 * d) * h12 - (y 1 * d) * h12 - (y 1 * d) * h02 + hsum
    | linear_combination 2 * d * h12 + d * h02
    | linear_combination (-(y 1)) * hp0 - y 0 * hp1 - y 0 * hp2
    | linear_combination (-(y 2)) * hp0 - y 2 * hp1 - y 1 * hp2
    | linear_combination hp0 + hp1 + hp2 + hsum

private theorem chartMatrix_map {B : Type*} [CommRing B] (f : A →+* B) (e y : Fin 3 → A) :
    (chartMatrix e y).map f = chartMatrix (f ∘ e) (f ∘ y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chartMatrix]

private theorem chartInverse_map {B : Type*} [CommRing B] (f : A →+* B) (e y : Fin 3 → A) (d : A) :
    (chartInverse e y d).map f = chartInverse (f ∘ e) (f ∘ y) (f d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chartInverse]

private theorem chartMatrix_apply_mem {S : Type*} [SetLike S A] [SubringClass S A] (O : S) {e y : Fin 3 → A}
    (he : ∀ j, e j ∈ O) (hy : ∀ j, y j ∈ O) (i j : Fin 3) : chartMatrix e y i j ∈ O := by
  fin_cases i <;> fin_cases j <;> simp [chartMatrix] <;>
    first
    | exact add_mem (he _) (he _)
    | exact he _
    | exact hy _

private theorem chartInverse_apply_mem {S : Type*} [SetLike S A] [SubringClass S A] (O : S) {e y : Fin 3 → A} {d : A}
    (he : ∀ j, e j ∈ O) (hy : ∀ j, y j ∈ O) (hd : d ∈ O) (i j : Fin 3) : chartInverse e y d i j ∈ O := by
  fin_cases i <;> fin_cases j <;> simp [chartInverse] <;>
    first
    | exact sub_mem (add_mem (he _) (he _)) (mul_mem (he _) (mul_mem (hy _) hd))
    | exact mul_mem (he _) (mul_mem (hy _) hd)
    | exact neg_mem (mul_mem (he _) (mul_mem (hy _) hd))
    | exact mul_mem (he _) hd
    | exact sub_mem (he _) (mul_mem (he _) (mul_mem (hy _) hd))

end Chart

private theorem chartMatrix_mul_chartInverse_pivot {x : Fin 3 → 𝔸} (hx : x ∈ rowDomain) :
    chartMatrix (pivotIdempotent x) x * chartInverse (pivotIdempotent x) x (pivotInverse x) = 1 :=
  chartMatrix_mul_chartInverse _ _ _ (pivotIdempotent_mul_self x 0) (pivotIdempotent_mul_self x 1)
    (pivotIdempotent_mul_self x 2) (pivotIdempotent_mul_of_ne x (by decide)) (pivotIdempotent_mul_of_ne x (by decide))
    (pivotIdempotent_mul_of_ne x (by decide)) (pivotIdempotent_sum x) (pivotIdempotent_mul_pivotInverse hx 0)
    (pivotIdempotent_mul_pivotInverse hx 1) (pivotIdempotent_mul_pivotInverse hx 2)

open scoped Classical in

private def sectionUnit (x : Fin 3 → 𝔸) : AdelicGL 3 (𝓞 ℚ) ℚ :=
  if hx : x ∈ rowDomain then
    ⟨chartMatrix (pivotIdempotent x) x, chartInverse (pivotIdempotent x) x (pivotInverse x),
      chartMatrix_mul_chartInverse_pivot hx, _root_.mul_eq_one_comm.mp (chartMatrix_mul_chartInverse_pivot hx)⟩
  else 1

private theorem val_componentAt3 (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (componentAt3 (𝓞 ℚ) ℚ p g : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) =
      (g : Matrix (Fin 3) (Fin 3) 𝔸).map (evalHom p) := rfl

private theorem val_componentAt3_inv (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (((componentAt3 (𝓞 ℚ) ℚ p g)⁻¹ : Matrix.GeneralLinearGroup (Fin 3) (p.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) =
      ((g⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸).map (evalHom p) := rfl

private theorem val_archComponent3 (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (archComponent3 (𝓞 ℚ) ℚ g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) =
      (g : Matrix (Fin 3) (Fin 3) 𝔸).map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) := rfl

private theorem mem_localMaximalCompact3_of_forall {p : HeightOneSpectrum (𝓞 ℚ)}
    {k : Matrix.GeneralLinearGroup (Fin 3) (p.adicCompletion ℚ)}
    (h₁ : ∀ i j, (k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j ∈ p.adicCompletionIntegers ℚ)
    (h₂ : ∀ i j, ((k⁻¹ : Matrix.GeneralLinearGroup (Fin 3) (p.adicCompletion ℚ)) :
      Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j ∈ p.adicCompletionIntegers ℚ) :
    k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p :=
  (mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ p).mpr
    ⟨fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).mp (h₁ i j),
      fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ p).mp (h₂ i j)⟩

private theorem eventually_componentAt3_mem (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∀ᶠ p in Filter.cofinite, componentAt3 (𝓞 ℚ) ℚ p g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p := by
  have hmat : ∀ M : Matrix (Fin 3) (Fin 3) 𝔸,
      ∀ᶠ p in Filter.cofinite, ∀ i j, evalHom p (M i j) ∈ p.adicCompletionIntegers ℚ := fun M => by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    filter_upwards [RestrictedProduct.eventually _ _ (M i j).2] with p hp
    exact hp
  filter_upwards [hmat (g : Matrix (Fin 3) (Fin 3) 𝔸), hmat ((g⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸)]
    with p h₁ h₂
  refine mem_localMaximalCompact3_of_forall (fun i j => ?_) (fun i j => ?_)
  · rw [val_componentAt3, Matrix.map_apply]
    exact h₁ i j
  · rw [val_componentAt3_inv, Matrix.map_apply]
    exact h₂ i j

private theorem rowAt_vecMul (p : HeightOneSpectrum (𝓞 ℚ)) (x : Fin 3 → 𝔸) (M : Matrix (Fin 3) (Fin 3) 𝔸) :
    rowAt p (x ᵥ* M) = rowAt p x ᵥ* M.map (evalHom p) := by
  funext j
  simp only [rowAt_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, fin_add_apply, fin_mul_apply,
    Matrix.map_apply, evalHom_eq]

private theorem exists_vecMul_ne_zero {A : Type*} [CommRing A] (u : (Matrix (Fin 3) (Fin 3) A)ˣ) {y : Fin 3 → A}
    (hy : ∃ j, y j ≠ 0) : ∃ j, (y ᵥ* (u : Matrix (Fin 3) (Fin 3) A)) j ≠ 0 := by
  by_contra hall
  have h0 : y ᵥ* (u : Matrix (Fin 3) (Fin 3) A) = 0 := funext fun j => not_not.mp fun h => hall ⟨j, h⟩
  have h1 : y = y ᵥ* ((u : Matrix (Fin 3) (Fin 3) A) *
      ((u⁻¹ : (Matrix (Fin 3) (Fin 3) A)ˣ) : Matrix (Fin 3) (Fin 3) A)) := by
    rw [Units.mul_inv, Matrix.vecMul_one]
  have hy0 : y = 0 := by
    rw [h1, ← Matrix.vecMul_vecMul, h0, Matrix.zero_vecMul]
  obtain ⟨j, hj⟩ := hy
  exact hj (congrFun hy0 j)

private theorem valued_vecMul_le {p : HeightOneSpectrum (𝓞 ℚ)} {C : WithZero (Multiplicative ℤ)}
    {y : Fin 3 → p.adicCompletion ℚ} {k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)} (hy : ∀ i, Valued.v (y i) ≤ C)
    (hk : ∀ i j, Valued.v (k i j) ≤ 1) (j : Fin 3) : Valued.v ((y ᵥ* k) j) ≤ C := by
  have hterm : ∀ i, Valued.v (y i * k i j) ≤ C := fun i => by
    rw [map_mul]
    exact (mul_le_mul' (hy i) (hk i j)).trans_eq (mul_one C)
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_three]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (hterm 2))
  exact le_trans (Valuation.map_add _ _ _) (max_le (hterm 0) (hterm 1))

private theorem primitiveAt_vecMul {p : HeightOneSpectrum (𝓞 ℚ)} {x : Fin 3 → 𝔸} (hx : PrimitiveAt p x)
    {g : AdelicGL 3 (𝓞 ℚ) ℚ} (hg : componentAt3 (𝓞 ℚ) ℚ p g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    PrimitiveAt p (x ᵥ* (g : Matrix (Fin 3) (Fin 3) 𝔸)) := by
  obtain ⟨hk, hk'⟩ := (mem_localMaximalCompact3_iff (𝓞 ℚ) ℚ p).mp hg
  rw [val_componentAt3] at hk
  rw [val_componentAt3_inv] at hk'
  rw [primitiveAt_iff] at hx ⊢
  rw [rowAt_vecMul]
  refine ⟨fun j => valued_vecMul_le hx.1 hk j, ?_⟩
  by_contra hall

  set z := rowAt p x ᵥ* (g : Matrix (Fin 3) (Fin 3) 𝔸).map (evalHom p) with hz
  have hzlt : ∀ j, Valued.v (z j) < 1 := fun j => lt_of_le_of_ne (valued_vecMul_le hx.1 hk j) fun h => hall ⟨j, h⟩
  set C := max (max (Valued.v (z 0)) (Valued.v (z 1))) (Valued.v (z 2)) with hC
  have hCle : ∀ j, Valued.v (z j) ≤ C := by
    intro j
    rw [hC]
    fin_cases j <;> simp
  have hClt : C < 1 := max_lt (max_lt (hzlt 0) (hzlt 1)) (hzlt 2)
  have hback : rowAt p x = z ᵥ* ((g⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸).map (evalHom p) := by
    rw [hz, Matrix.vecMul_vecMul, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one (evalHom p) (map_zero _) (map_one _),
      Matrix.vecMul_one]
  obtain ⟨i, hi⟩ := hx.2
  have : Valued.v (rowAt p x i) ≤ C := by
    rw [hback]
    exact valued_vecMul_le hCle hk' i
  rw [hi] at this
  exact absurd (lt_of_le_of_lt this hClt) (lt_irrefl _)

private theorem eq_one_of_le_one_of_not_le {γ : WithZero (Multiplicative ℤ)} (h1 : γ ≤ 1)
    (h2 : ¬ γ ≤ WithZero.exp (-1 : ℤ)) : γ = 1 := by
  have hne : γ ≠ 0 := fun h0 => h2 (by rw [h0]; exact zero_le')
  have hl1 : WithZero.log γ ≤ 0 := (WithZero.log_le_iff_le_exp hne).mpr (by rwa [WithZero.exp_zero])
  have hl2 : ¬ WithZero.log γ ≤ -1 := fun h => h2 ((WithZero.log_le_iff_le_exp hne).mp h)
  have hl : WithZero.log γ = 0 := by omega
  rw [← WithZero.exp_log hne, hl, WithZero.exp_zero]

private theorem isClopen_setOf_valued_eq_one (p : HeightOneSpectrum (𝓞 ℚ)) :
    IsClopen {y : p.adicCompletion ℚ | Valued.v y = 1} := by
  obtain ⟨t, ht0, ht⟩ := AdelicLevel.exists_valued_eq_exp_neg (K := ℚ) p 1
  simp only [Nat.cast_one] at ht
  have hset : {y : p.adicCompletion ℚ | Valued.v y = 1} =
      {y : p.adicCompletion ℚ | Valued.v y ≤ Valued.v (1 : p.adicCompletion ℚ)} \
        {y : p.adicCompletion ℚ | Valued.v y ≤ Valued.v t} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_diff, map_one, ht]
    constructor
    · intro h
      rw [h]
      refine ⟨le_rfl, fun h' => ?_⟩
      rw [← WithZero.exp_zero, WithZero.exp_le_exp] at h'
      omega
    · rintro ⟨h1, h2⟩
      exact eq_one_of_le_one_of_not_le h1 h2
  rw [hset]
  exact IsClopen.diff
    ⟨AdelicLevel.isClosed_setOf_valued_le p (1 : p.adicCompletion ℚ) one_ne_zero,
      AdelicLevel.isOpen_setOf_valued_le p (1 : p.adicCompletion ℚ) one_ne_zero⟩
    ⟨AdelicLevel.isClosed_setOf_valued_le p t ht0, AdelicLevel.isOpen_setOf_valued_le p t ht0⟩

private scoped instance : Countable (HeightOneSpectrum (𝓞 ℚ)) :=
  Countable.of_equiv _ Rat.HeightOneSpectrum.primesEquiv.symm

private theorem continuous_rowAt (p : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 3) :
    Continuous fun x : Fin 3 → 𝔸 => rowAt p x j :=
  ((AdelicLevel.continuous_finAdeleEval (R := 𝓞 ℚ) (K := ℚ) p).comp
    (AdelicLevel.continuous_adeleFin (R := 𝓞 ℚ) (K := ℚ))).comp (continuous_apply j)

private theorem continuous_rowArch (w : InfinitePlace ℚ) (j : Fin 3) : Continuous fun x : Fin 3 → 𝔸 => rowArch w x j :=
  ((AdelicLevel.continuous_archEval (K := ℚ) w).comp (AdelicLevel.continuous_adeleArch (R := 𝓞 ℚ) (K := ℚ))).comp
    (continuous_apply j)

private theorem isClopen_valued_rowAt_eq_one (p : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 3) :
    IsClopen {x : Fin 3 → 𝔸 | Valued.v (rowAt p x j) = 1} :=
  (isClopen_setOf_valued_eq_one p).preimage (continuous_rowAt p j)

private theorem measurableSet_valued_rowAt_eq_one (p : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 3) :
    MeasurableSet {x : Fin 3 → 𝔸 | Valued.v (rowAt p x j) = 1} :=
  (isClopen_valued_rowAt_eq_one p j).isClosed.measurableSet

private theorem measurableSet_valued_rowAt_le_one (p : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 3) :
    MeasurableSet {x : Fin 3 → 𝔸 | Valued.v (rowAt p x j) ≤ 1} := by
  have h : IsClosed {y : p.adicCompletion ℚ | Valued.v y ≤ 1} := by
    simpa using AdelicLevel.isClosed_setOf_valued_le p (1 : p.adicCompletion ℚ) one_ne_zero
  exact (h.preimage (continuous_rowAt p j)).measurableSet

private theorem measurableSet_rowAt_ne_zero (p : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 3) :
    MeasurableSet {x : Fin 3 → 𝔸 | rowAt p x j ≠ 0} := by
  have h : IsOpen {y : p.adicCompletion ℚ | y ≠ 0} := isOpen_ne
  exact (h.preimage (continuous_rowAt p j)).measurableSet

private theorem measurableSet_rowArch_ne_zero (w : InfinitePlace ℚ) (j : Fin 3) :
    MeasurableSet {x : Fin 3 → 𝔸 | rowArch w x j ≠ 0} := by
  have h : IsOpen {y : w.Completion | y ≠ 0} := isOpen_ne
  exact (h.preimage (continuous_rowArch w j)).measurableSet

private theorem measurableSet_primitiveAt (p : HeightOneSpectrum (𝓞 ℚ)) :
    MeasurableSet {x : Fin 3 → 𝔸 | PrimitiveAt p x} := by
  have h : {x : Fin 3 → 𝔸 | PrimitiveAt p x} =
      (⋂ j, {x : Fin 3 → 𝔸 | Valued.v (rowAt p x j) ≤ 1}) ∩ ⋃ j, {x : Fin 3 → 𝔸 | Valued.v (rowAt p x j) = 1} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_iUnion, primitiveAt_iff]
  rw [h]
  exact (MeasurableSet.iInter fun j => measurableSet_valued_rowAt_le_one p j).inter
    (MeasurableSet.iUnion fun j => measurableSet_valued_rowAt_eq_one p j)

private theorem measurableSet_nonzeroAt (p : HeightOneSpectrum (𝓞 ℚ)) :
    MeasurableSet {x : Fin 3 → 𝔸 | NonzeroAt p x} := by
  have h : {x : Fin 3 → 𝔸 | NonzeroAt p x} = ⋃ j, {x : Fin 3 → 𝔸 | rowAt p x j ≠ 0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, nonzeroAt_iff]
  rw [h]
  exact MeasurableSet.iUnion fun j => measurableSet_rowAt_ne_zero p j

private theorem measurableSet_nonzeroArch : MeasurableSet {x : Fin 3 → 𝔸 | NonzeroArch x} := by
  have h : {x : Fin 3 → 𝔸 | NonzeroArch x} = ⋃ j, {x : Fin 3 → 𝔸 | rowArch default x j ≠ 0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    exact ⟨fun hx => exists_rowArch_ne_zero hx default, fun hx => nonzeroArch_of_rowArch hx⟩
  rw [h]
  exact MeasurableSet.iUnion fun j => measurableSet_rowArch_ne_zero default j

private theorem setOf_eventually_cofinite_eq {P : HeightOneSpectrum (𝓞 ℚ) → (Fin 3 → 𝔸) → Prop} :
    {x | ∀ᶠ p in Filter.cofinite, P p x} =
      ⋃ T : Finset (HeightOneSpectrum (𝓞 ℚ)), ⋂ p, ⋂ (_ : p ∉ T), {x | P p x} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter]
  constructor
  · intro h
    have hfin := Filter.eventually_cofinite.mp h
    refine ⟨hfin.toFinset, fun p hp => ?_⟩
    by_contra hnp
    exact hp (hfin.mem_toFinset.mpr hnp)
  · rintro ⟨T, hT⟩
    refine Filter.eventually_cofinite.mpr (T.finite_toSet.subset fun p hp => ?_)
    by_contra hpT
    exact hp (hT p fun h => hpT (Finset.mem_coe.mpr h))

private theorem rowDomain_measurableSet : MeasurableSet rowDomain := by
  have h : rowDomain = (⋂ p, {x : Fin 3 → 𝔸 | NonzeroAt p x}) ∩
      ({x : Fin 3 → 𝔸 | NonzeroArch x} ∩ {x : Fin 3 → 𝔸 | ∀ᶠ p in Filter.cofinite, PrimitiveAt p x}) := by
    ext x
    simp only [mem_rowDomain, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [h, setOf_eventually_cofinite_eq]
  refine (MeasurableSet.iInter fun p => measurableSet_nonzeroAt p).inter (measurableSet_nonzeroArch.inter ?_)
  exact MeasurableSet.iUnion fun T =>
    MeasurableSet.iInter fun p => MeasurableSet.iInter fun _ => measurableSet_primitiveAt p

private theorem measurable_finitePivot (p : HeightOneSpectrum (𝓞 ℚ)) :
    Measurable fun x : Fin 3 → 𝔸 => finitePivot p (rowAt p x) := by
  have hunit : ∀ j, MeasurableSet {x : Fin 3 → 𝔸 | Valued.v (rowAt p x j) = 1} := measurableSet_valued_rowAt_eq_one p
  have hne : ∀ j, MeasurableSet {x : Fin 3 → 𝔸 | rowAt p x j ≠ 0} := measurableSet_rowAt_ne_zero p
  simp only [finitePivot, unitPattern, preferredIndex]
  refine Measurable.ite ?_ ?_ ?_
  · rw [Set.setOf_exists]
    exact MeasurableSet.iUnion hunit
  · exact Measurable.ite (hunit 2) measurable_const (Measurable.ite (hunit 1) measurable_const measurable_const)
  · exact Measurable.ite (hne 2) measurable_const (Measurable.ite (hne 1) measurable_const measurable_const)

private theorem measurable_archPivot (w : InfinitePlace ℚ) :
    Measurable fun x : Fin 3 → 𝔸 => archPivot w (rowArch w x) := by
  have hne : ∀ j, MeasurableSet {x : Fin 3 → 𝔸 | rowArch w x j ≠ 0} := measurableSet_rowArch_ne_zero w
  simp only [archPivot, preferredIndex]
  exact Measurable.ite (hne 2) measurable_const (Measurable.ite (hne 1) measurable_const measurable_const)

private def piece (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (π : T → Fin 3) (a : Fin 3) : Set (Fin 3 → 𝔸) :=
  {x | x ∈ rowDomain ∧ (∀ p, p ∉ T → PrimitiveAt p x) ∧ (∀ p (hp : p ∈ T), finitePivot p (rowAt p x) = π ⟨p, hp⟩) ∧
    ∀ w, archPivot w (rowArch w x) = a}

private theorem mem_piece {T : Finset (HeightOneSpectrum (𝓞 ℚ))} {π : T → Fin 3} {a : Fin 3} {x : Fin 3 → 𝔸} :
    x ∈ piece T π a ↔ x ∈ rowDomain ∧ (∀ p, p ∉ T → PrimitiveAt p x) ∧
      (∀ p (hp : p ∈ T), finitePivot p (rowAt p x) = π ⟨p, hp⟩) ∧ ∀ w, archPivot w (rowArch w x) = a :=
  Iff.rfl

private theorem piece_subset_rowDomain (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (π : T → Fin 3) (a : Fin 3) :
    piece T π a ⊆ rowDomain :=
  fun _ hx => hx.1

private theorem measurableSet_piece (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (π : T → Fin 3) (a : Fin 3) :
    MeasurableSet (piece T π a) := by
  have h : piece T π a = rowDomain ∩ ((⋂ p, ⋂ (_ : p ∉ T), {x : Fin 3 → 𝔸 | PrimitiveAt p x}) ∩
      ((⋂ p, ⋂ (hp : p ∈ T), {x : Fin 3 → 𝔸 | finitePivot p (rowAt p x) = π ⟨p, hp⟩}) ∩
        ⋂ w, {x : Fin 3 → 𝔸 | archPivot w (rowArch w x) = a})) := by
    ext x
    simp only [mem_piece, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [h]
  refine rowDomain_measurableSet.inter
    ((MeasurableSet.iInter fun p => MeasurableSet.iInter fun _ => measurableSet_primitiveAt p).inter
      ((MeasurableSet.iInter fun p => MeasurableSet.iInter fun hp => ?_).inter (MeasurableSet.iInter fun w => ?_)))
  · exact measurable_finitePivot p (measurableSet_singleton (π ⟨p, hp⟩))
  · exact measurable_archPivot w (measurableSet_singleton a)

private theorem exists_mem_piece {x : Fin 3 → 𝔸} (hx : x ∈ rowDomain) :
    ∃ i : (Σ T : Finset (HeightOneSpectrum (𝓞 ℚ)), (T → Fin 3)) × Fin 3, x ∈ piece i.1.1 i.1.2 i.2 := by
  have hfin : {p | ¬ PrimitiveAt p x}.Finite := Filter.eventually_cofinite.mp hx.2.2
  refine ⟨⟨⟨hfin.toFinset, fun p => finitePivot p.1 (rowAt p.1 x)⟩, archPivot default (rowArch default x)⟩,
    mem_piece.mpr ⟨hx, fun p hp => ?_, fun p hp => rfl, fun w => ?_⟩⟩
  · by_contra h
    exact hp (hfin.mem_toFinset.mpr h)
  · rw [Subsingleton.elim w default]

private theorem continuous_ite_of_isClopen {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {P : X → Prop}
    [DecidablePred P] (hP : IsClopen {x | P x}) {f g : X → Y} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => if P x then f x else g x := by
  rw [continuous_def]
  intro u hu
  have h : (fun x => if P x then f x else g x) ⁻¹' u = ({x | P x} ∩ f ⁻¹' u) ∪ ({x | P x}ᶜ ∩ g ⁻¹' u) := by
    ext x
    by_cases hx : P x <;> simp [hx]
  rw [h]
  exact (hP.isOpen.inter (hu.preimage hf)).union (hP.compl.isOpen.inter (hu.preimage hg))

private theorem continuous_unitPattern (p : HeightOneSpectrum (𝓞 ℚ)) :
    Continuous fun x : Fin 3 → 𝔸 => unitPattern p (rowAt p x) := by
  have hc : ∀ j, IsClopen {x : Fin 3 → 𝔸 | Valued.v (rowAt p x j) = 1} := isClopen_valued_rowAt_eq_one p
  simp only [unitPattern, preferredIndex]
  exact continuous_ite_of_isClopen (hc 2) continuous_const
    (continuous_ite_of_isClopen (hc 1) continuous_const continuous_const)

private theorem continuousOn_inv_unitPattern (p : HeightOneSpectrum (𝓞 ℚ)) :
    ContinuousOn (fun x : Fin 3 → 𝔸 => (rowAt p x (unitPattern p (rowAt p x)))⁻¹)
      {x : Fin 3 → 𝔸 | ∃ j, Valued.v (rowAt p x j) = 1} := by
  intro x₀ hx₀
  have hU : {x : Fin 3 → 𝔸 | unitPattern p (rowAt p x) = unitPattern p (rowAt p x₀)} ∈ 𝓝 x₀ :=
    ((isOpen_discrete {unitPattern p (rowAt p x₀)}).preimage (continuous_unitPattern p)).mem_nhds rfl
  have hne : rowAt p x₀ (unitPattern p (rowAt p x₀)) ≠ 0 := fun h0 => by
    have h1 := valued_unitPattern p hx₀
    rw [h0, map_zero] at h1
    exact zero_ne_one h1
  have hG : ContinuousAt (fun x : Fin 3 → 𝔸 => (rowAt p x (unitPattern p (rowAt p x₀)))⁻¹) x₀ :=
    (continuous_rowAt p _).continuousAt.inv₀ hne
  refine (hG.congr ?_).continuousWithinAt
  filter_upwards [hU] with x hx
  show (rowAt p x (unitPattern p (rowAt p x₀)))⁻¹ = (rowAt p x (unitPattern p (rowAt p x)))⁻¹
  rw [hx]

private theorem continuousOn_finiteAdele {X : Type*} [TopologicalSpace X] {s : Set X}
    {T : Set (HeightOneSpectrum (𝓞 ℚ))} (hT : T.Finite) (f : X → FiniteAdeleRing (𝓞 ℚ) ℚ)
    (hint : ∀ x ∈ s, ∀ p, p ∉ T → f x p ∈ p.adicCompletionIntegers ℚ)
    (hcont : ∀ p, ContinuousOn (fun x => f x p) s) : ContinuousOn f s := by
  have hle : Filter.cofinite ≤ Filter.principal Tᶜ := Filter.le_principal_iff.mpr hT.compl_mem_cofinite
  let g : s → Πʳ p : HeightOneSpectrum (𝓞 ℚ), [p.adicCompletion ℚ, p.adicCompletionIntegers ℚ]_[Filter.principal Tᶜ] :=
    fun z => ⟨fun p => f z.1 p, Filter.eventually_principal.mpr fun p hp => hint z.1 z.2 p hp⟩
  have hg : Continuous g := by
    rw [RestrictedProduct.continuous_rng_of_principal]
    exact continuous_pi fun p => continuousOn_iff_continuous_restrict.mp (hcont p)
  have hfg : s.domRestrict f = RestrictedProduct.inclusion _ _ hle ∘ g :=
    funext fun z => FiniteAdeleRing.ext ℚ fun p => rfl
  rw [continuousOn_iff_continuous_restrict, hfg]
  exact (RestrictedProduct.continuous_inclusion hle).comp hg

private theorem continuousOn_adele {X : Type*} [TopologicalSpace X] {F : X → 𝔸} {s : Set X}
    (h₁ : ∀ w, ContinuousOn (fun x => (F x).1 w) s) (h₂ : ContinuousOn (fun x => (F x).2) s) : ContinuousOn F s :=
  ContinuousOn.prodMk (continuousOn_pi.mpr h₁) h₂

section ChartContinuity

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] {X : Type*} [TopologicalSpace X]

private theorem continuous_chartMatrix {e y : X → Fin 3 → A} (he : ∀ j, Continuous fun x => e x j)
    (hy : ∀ j, Continuous fun x => y x j) : Continuous fun x => chartMatrix (e x) (y x) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [chartMatrix] <;>
    first
    | exact continuous_const
    | exact (he _).add (he _)
    | exact he _
    | exact hy _

private theorem continuous_chartInverse {e y : X → Fin 3 → A} {d : X → A} (he : ∀ j, Continuous fun x => e x j)
    (hy : ∀ j, Continuous fun x => y x j) (hd : Continuous d) :
    Continuous fun x => chartInverse (e x) (y x) (d x) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [chartInverse] <;>
    first
    | exact continuous_const
    | exact ((he _).add (he _)).sub ((he _).mul ((hy _).mul hd))
    | exact ((he _).mul ((hy _).mul hd)).neg
    | exact (he _).mul ((hy _).mul hd)
    | exact (he _).mul hd
    | exact (he _).sub ((he _).mul ((hy _).mul hd))

end ChartContinuity

private theorem pivotIdempotent_fin_mem (x : Fin 3 → 𝔸) (j : Fin 3) (p : HeightOneSpectrum (𝓞 ℚ)) :
    (pivotIdempotent x j).2 p ∈ p.adicCompletionIntegers ℚ := by
  rw [pivotIdempotent_fin]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

private theorem pivotInverse_fin_mem {x : Fin 3 → 𝔸} (hx : x ∈ rowDomain) {p : HeightOneSpectrum (𝓞 ℚ)}
    (hp : PrimitiveAt p x) : (pivotInverse x).2 p ∈ p.adicCompletionIntegers ℚ := by
  simp only [pivotInverse_fin hx, HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀,
    valued_finitePivot p ((primitiveAt_iff p x).mp hp).2, inv_one, le_refl]

private theorem continuousOn_pivotIdempotent (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (π : T → Fin 3) (a : Fin 3)
    (j : Fin 3) : ContinuousOn (fun x => pivotIdempotent x j) (piece T π a) := by
  refine continuousOn_adele (fun w => ?_) ?_
  · refine ContinuousOn.congr (continuousOn_const : ContinuousOn (fun _ => if a = j then (1 : w.Completion) else 0) _)
      fun x hx => ?_
    show (pivotIdempotent x j).1 w = if a = j then 1 else 0
    rw [pivotIdempotent_arch, hx.2.2.2 w]
  · refine continuousOn_finiteAdele T.finite_toSet _ (fun x _ p _ => pivotIdempotent_fin_mem x j p) fun p => ?_
    by_cases hp : p ∈ T
    · refine ContinuousOn.congr
        (continuousOn_const : ContinuousOn (fun _ => if π ⟨p, hp⟩ = j then (1 : p.adicCompletion ℚ) else 0) _)
        fun x hx => ?_
      show (pivotIdempotent x j).2 p = if π ⟨p, hp⟩ = j then 1 else 0
      rw [pivotIdempotent_fin, hx.2.2.1 p hp]
    · have hcont : Continuous fun x : Fin 3 → 𝔸 =>
          if unitPattern p (rowAt p x) = j then (1 : p.adicCompletion ℚ) else 0 :=
        (continuous_of_discreteTopology (f := fun k : Fin 3 => if k = j then (1 : p.adicCompletion ℚ) else 0)).comp
          (continuous_unitPattern p)
      refine hcont.continuousOn.congr fun x hx => ?_
      show (pivotIdempotent x j).2 p = if unitPattern p (rowAt p x) = j then 1 else 0
      rw [pivotIdempotent_fin, finitePivot_of_exists_unit p ((primitiveAt_iff p x).mp (hx.2.1 p hp)).2]

private theorem continuousOn_pivotInverse (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (π : T → Fin 3) (a : Fin 3) :
    ContinuousOn pivotInverse (piece T π a) := by
  refine continuousOn_adele (fun w => ?_) ?_
  · have hc : ContinuousOn (fun x : Fin 3 → 𝔸 => (rowArch w x a)⁻¹) (piece T π a) :=
      (continuous_rowArch w a).continuousOn.inv₀ fun x hx => by
        have h := archPivot_ne_zero w (exists_rowArch_ne_zero hx.1.2.1 w)
        rwa [hx.2.2.2 w] at h
    refine hc.congr fun x hx => ?_
    show (pivotInverse x).1 w = (rowArch w x a)⁻¹
    rw [pivotInverse_arch hx.1, hx.2.2.2 w]
  · refine continuousOn_finiteAdele T.finite_toSet _ (fun x hx p hp => pivotInverse_fin_mem hx.1 (hx.2.1 p hp))
      fun p => ?_
    by_cases hp : p ∈ T
    · have hc : ContinuousOn (fun x : Fin 3 → 𝔸 => (rowAt p x (π ⟨p, hp⟩))⁻¹) (piece T π a) :=
        (continuous_rowAt p _).continuousOn.inv₀ fun x hx => by
          have h := finitePivot_ne_zero p ((nonzeroAt_iff p x).mp (hx.1.1 p))
          rwa [hx.2.2.1 p hp] at h
      refine hc.congr fun x hx => ?_
      show (pivotInverse x).2 p = (rowAt p x (π ⟨p, hp⟩))⁻¹
      rw [pivotInverse_fin hx.1, hx.2.2.1 p hp]
    · have hsub : piece T π a ⊆ {x : Fin 3 → 𝔸 | ∃ j, Valued.v (rowAt p x j) = 1} :=
        fun x hx => ((primitiveAt_iff p x).mp (hx.2.1 p hp)).2
      refine ((continuousOn_inv_unitPattern p).mono hsub).congr fun x hx => ?_
      show (pivotInverse x).2 p = (rowAt p x (unitPattern p (rowAt p x)))⁻¹
      rw [pivotInverse_fin hx.1, finitePivot_of_exists_unit p ((primitiveAt_iff p x).mp (hx.2.1 p hp)).2]

private theorem rowAt_e₃ (p : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 3) : rowAt p e₃ j = if j = 2 then 1 else 0 := by
  fin_cases j <;> rfl

private theorem rowArch_e₃ (w : InfinitePlace ℚ) (j : Fin 3) : rowArch w e₃ j = if j = 2 then 1 else 0 := by
  fin_cases j <;> rfl

private theorem valued_rowAt_e₃_two (p : HeightOneSpectrum (𝓞 ℚ)) : Valued.v (rowAt p e₃ 2) = 1 := by
  rw [rowAt_e₃, if_pos rfl]
  exact map_one _

private theorem rowArch_e₃_two_ne_zero (w : InfinitePlace ℚ) : rowArch w e₃ 2 ≠ 0 := by
  rw [rowArch_e₃, if_pos rfl]
  exact one_ne_zero

private theorem primitiveAt_e₃ (p : HeightOneSpectrum (𝓞 ℚ)) : PrimitiveAt p e₃ := by
  refine (primitiveAt_iff p e₃).mpr ⟨fun j => ?_, 2, valued_rowAt_e₃_two p⟩
  rw [rowAt_e₃]
  split_ifs <;> simp

private theorem nonzeroAt_e₃ (p : HeightOneSpectrum (𝓞 ℚ)) : NonzeroAt p e₃ :=
  (nonzeroAt_iff p e₃).mpr ⟨2, fun h => one_ne_zero ((valued_rowAt_e₃_two p).symm.trans (by rw [h, map_zero]))⟩

private theorem nonzeroArch_e₃ : NonzeroArch e₃ :=
  nonzeroArch_of_rowArch (w := default) ⟨2, rowArch_e₃_two_ne_zero default⟩

private theorem e₃_mem_rowDomain : e₃ ∈ rowDomain :=
  mem_rowDomain.mpr ⟨nonzeroAt_e₃, nonzeroArch_e₃, Filter.Eventually.of_forall primitiveAt_e₃⟩

private theorem finitePivot_e₃ (p : HeightOneSpectrum (𝓞 ℚ)) : finitePivot p (rowAt p e₃) = 2 :=
  finitePivot_eq_two p (valued_rowAt_e₃_two p)

private theorem archPivot_e₃ (w : InfinitePlace ℚ) : archPivot w (rowArch w e₃) = 2 :=
  archPivot_eq_two w (rowArch_e₃_two_ne_zero w)

private theorem pivotIdempotent_e₃ (j : Fin 3) : pivotIdempotent e₃ j = e₃ j := by
  refine ext_of_places (fun w => ?_) fun p => ?_
  · rw [pivotIdempotent_arch, archPivot_e₃]
    fin_cases j <;> rfl
  · rw [pivotIdempotent_fin, finitePivot_e₃]
    fin_cases j <;> rfl

private theorem e₃_mem_piece (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : e₃ ∈ piece S (fun _ => 2) 2 :=
  mem_piece.mpr ⟨e₃_mem_rowDomain, fun p _ => primitiveAt_e₃ p, fun p _ => finitePivot_e₃ p, archPivot_e₃⟩

private theorem piece_mem_nhdsWithin_e₃ (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    piece S (fun _ => 2) 2 ∈ nhdsWithin e₃ (explicitRows S) := by
  have hS : ∀ᶠ x : Fin 3 → 𝔸 in nhds e₃, ∀ p ∈ S, Valued.v (rowAt p x 2) = 1 :=
    (Filter.eventually_all_finset S).mpr fun p _ =>
      (isClopen_valued_rowAt_eq_one p 2).isOpen.mem_nhds (valued_rowAt_e₃_two p)
  have hA : ∀ᶠ x : Fin 3 → 𝔸 in nhds e₃, rowArch default x 2 ≠ 0 :=
    (continuous_rowArch default 2).continuousAt.eventually_ne (rowArch_e₃_two_ne_zero default)
  filter_upwards [mem_nhdsWithin_of_mem_nhds hS, mem_nhdsWithin_of_mem_nhds hA, self_mem_nhdsWithin] with x hxS hxA hx
  obtain ⟨hprim, -, -⟩ := mem_explicitRows.mp hx
  refine mem_piece.mpr
    ⟨mem_rowDomain_of_mem_explicitRows hx, hprim, fun p hp => finitePivot_eq_two p (hxS p hp), fun w => ?_⟩
  rw [Subsingleton.elim w default]
  exact archPivot_eq_two default hxA

attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

private abbrev residueChar (v : HeightOneSpectrum (𝓞 ℚ)) : ℕ := Rat.HeightOneSpectrum.natGenerator v

private theorem residueChar_prime (v : HeightOneSpectrum (𝓞 ℚ)) : (residueChar v).Prime :=
  Rat.HeightOneSpectrum.prime_natGenerator v

private theorem residueChar_injective : Function.Injective residueChar := fun _ _ h =>
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective (Subtype.ext h)

private theorem natCast_mem_asIdeal_of_dvd {v : HeightOneSpectrum (𝓞 ℚ)} {n : ℕ} (h : residueChar v ∣ n) :
    (n : 𝓞 ℚ) ∈ v.asIdeal := by
  obtain ⟨x, hx, hxn⟩ := (Ideal.mem_map_iff_of_surjective
    (hf := (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).surjective)).mp ((Rat.HeightOneSpectrum.natGenerator_dvd_iff v).mp h)
  have hxn' : x = (n : 𝓞 ℚ) := (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).injective (by rw [hxn, map_natCast])
  exact hxn' ▸ hx

private theorem natCast_notMem_asIdeal_of_not_dvd {v : HeightOneSpectrum (𝓞 ℚ)} {n : ℕ} (h : ¬ residueChar v ∣ n) :
    (n : 𝓞 ℚ) ∉ v.asIdeal := fun hmem =>
  h ((Rat.HeightOneSpectrum.natGenerator_dvd_iff v).mpr
    (by simpa using Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hmem))

private abbrev levelRadius (N : ℕ) (v : HeightOneSpectrum (𝓞 ℚ)) : WithZero (Multiplicative ℤ) :=
  Valued.v (algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) (N : 𝓞 ℚ))

private theorem levelRadius_le_one (N : ℕ) (v : HeightOneSpectrum (𝓞 ℚ)) : levelRadius N v ≤ 1 := by
  simp only [levelRadius]
  rw [AdelicTrace.valued_algebraMap]
  exact v.intValuation_le_one _

private theorem levelRadius_eq_one {N : ℕ} {v : HeightOneSpectrum (𝓞 ℚ)} (h : ¬ residueChar v ∣ N) :
    levelRadius N v = 1 := by
  simp only [levelRadius]
  rw [AdelicTrace.valued_algebraMap]
  exact HeightOneSpectrum.intValuation_eq_one_iff.mpr (natCast_notMem_asIdeal_of_not_dvd h)

private theorem levelRadius_lt_one {N : ℕ} {v : HeightOneSpectrum (𝓞 ℚ)} (h : residueChar v ∣ N) :
    levelRadius N v < 1 := by
  simp only [levelRadius]
  rw [AdelicTrace.valued_algebraMap]
  exact (v.intValuation_lt_one_iff_mem _).mpr (natCast_mem_asIdeal_of_dvd h)

private theorem levelRadius_le_of_dvd {M N : ℕ} (h : M ∣ N) (v : HeightOneSpectrum (𝓞 ℚ)) :
    levelRadius N v ≤ levelRadius M v := by
  obtain ⟨k, rfl⟩ := h
  simp only [levelRadius]
  rw [Nat.cast_mul, map_mul, map_mul]
  exact mul_le_of_le_one_right' (levelRadius_le_one k v)

private theorem valued_natCast_eq_one {v : HeightOneSpectrum (𝓞 ℚ)} {n : ℕ} (h : ¬ residueChar v ∣ n) :
    Valued.v (n : v.adicCompletion ℚ) = 1 := by
  rw [← map_natCast (algebraMap (𝓞 ℚ) (v.adicCompletion ℚ)) n]
  exact levelRadius_eq_one h

private theorem valued_natCast_le_one (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    Valued.v (n : v.adicCompletion ℚ) ≤ 1 := by
  rw [← map_natCast (algebraMap (𝓞 ℚ) (v.adicCompletion ℚ)) n]
  exact levelRadius_le_one n v

private theorem valued_add_le_one_iff {v : HeightOneSpectrum (𝓞 ℚ)} {r : v.adicCompletion ℚ} (hr : Valued.v r ≤ 1)
    (y : v.adicCompletion ℚ) : Valued.v (y + r) ≤ 1 ↔ Valued.v y ≤ 1 :=
  ⟨fun h => by
    have h' : Valued.v (y + r - r) ≤ 1 := Valuation.map_sub_le _ h hr
    rwa [add_sub_cancel_right] at h', fun h => Valuation.map_add_le _ h hr⟩

private theorem forall_place_iff {P : HeightOneSpectrum (𝓞 ℚ) → Prop} (v : HeightOneSpectrum (𝓞 ℚ)) :
    (∀ w, P w) ↔ P v ∧ ∀ w, w ≠ v → P w :=
  ⟨fun h => ⟨h v, fun w _ => h w⟩, fun h w => by
    by_cases hw : w = v
    · exact hw ▸ h.1
    · exact h.2 w hw⟩

private theorem continuous_finPart_apply (v : HeightOneSpectrum (𝓞 ℚ)) : Continuous fun a : 𝔸 => a.2 v :=
  (AdelicLevel.continuous_finAdeleEval (R := 𝓞 ℚ) (K := ℚ) v).comp
    (AdelicLevel.continuous_adeleFin (R := 𝓞 ℚ) (K := ℚ))

private def finBox (N : ℕ) (a : 𝔸) : Set 𝔸 :=
  {b | ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((b - a).2 v) ≤ levelRadius N v}

private theorem mem_finBox {N : ℕ} {a b : 𝔸} :
    b ∈ finBox N a ↔ ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((b - a).2 v) ≤ levelRadius N v :=
  Iff.rfl

private theorem finBox_antitone {M N : ℕ} (h : M ∣ N) (a : 𝔸) : finBox N a ⊆ finBox M a := fun _ hb v =>
  (hb v).trans (levelRadius_le_of_dvd h v)

private theorem measurableSet_finBox (N : ℕ) (a : 𝔸) : MeasurableSet (finBox N a) := by
  have : finBox N a = ⋂ v : HeightOneSpectrum (𝓞 ℚ),
      (fun b : 𝔸 => (b - a).2 v) ⁻¹' {y | Valued.v y ≤ levelRadius N v} := by
    ext b
    simp only [finBox, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [this]
  refine MeasurableSet.iInter fun v => ?_
  exact ((AdelicTrace.isClosed_setOf_valued_le v _).preimage
    ((continuous_finPart_apply v).comp (continuous_id.sub continuous_const))).measurableSet

private def intMap (z : Π v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ) : FiniteAdeleRing (𝓞 ℚ) ℚ :=
  RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 ℚ) => v.adicCompletion ℚ)
    (fun v => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) Filter.cofinite z

private theorem intMap_apply (z : Π v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ)
    (v : HeightOneSpectrum (𝓞 ℚ)) : intMap z v = (z v : v.adicCompletion ℚ) := rfl

private theorem nhds_zero_eq_map_intMap : nhds (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) = Filter.map intMap (nhds 0) := by
  have h0 : intMap 0 = 0 := FiniteAdeleRing.ext ℚ fun _ => rfl
  rw [← h0]
  exact RestrictedProduct.nhds_zero_eq_map_structureMap (fun v : HeightOneSpectrum (𝓞 ℚ) => v.adicCompletion ℚ)
    (B := fun v => v.adicCompletionIntegers ℚ) fun _ => Valued.isOpen_valuationSubring _

private theorem finBox_mem_nhds {N : ℕ} (hN : N ≠ 0) (a : 𝔸) : finBox N a ∈ nhds a := by
  have himg : intMap '' AdelicTrace.valBox ℚ N ∈ nhds (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) := by
    rw [nhds_zero_eq_map_intMap]
    exact Filter.image_mem_map (AdelicTrace.valBox_mem_nhds_zero (F := ℚ) hN)
  have hpre : (fun b : 𝔸 => b.2 - a.2) ⁻¹' (intMap '' AdelicTrace.valBox ℚ N) ∈ nhds a :=
    (continuous_snd.sub continuous_const).continuousAt.preimage_mem_nhds (by simpa using himg)
  refine Filter.mem_of_superset hpre fun b hb => mem_finBox.mpr fun v => ?_
  obtain ⟨z, hz, hzb⟩ := hb
  have h : (b - a).2 v = (z v : v.adicCompletion ℚ) := by
    rw [← intMap_apply, hzb]
    rfl
  rw [h]
  exact hz v

private theorem exists_finBox_subset {a : 𝔸} {U : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hU : U ∈ nhds a.2) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ b : 𝔸, b ∈ finBox N a → b.2 ∈ U := by
  have hU0 : (fun y : FiniteAdeleRing (𝓞 ℚ) ℚ => a.2 + y) ⁻¹' U ∈ nhds (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hU)
  rw [nhds_zero_eq_map_intMap, Filter.mem_map] at hU0
  obtain ⟨N, hN, hbox⟩ := AdelicTrace.exists_valBox_subset hU0
  refine ⟨N, hN, fun b hb => ?_⟩
  have hint : ∀ v : HeightOneSpectrum (𝓞 ℚ), (b - a).2 v ∈ v.adicCompletionIntegers ℚ := fun v =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr ((hb v).trans (levelRadius_le_one N v))
  let z : Π v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ := fun v => ⟨(b - a).2 v, hint v⟩
  have hz : z ∈ AdelicTrace.valBox ℚ N := AdelicTrace.mem_valBox.mpr fun v => hb v
  have hmem := hbox hz
  have heq : intMap z = b.2 - a.2 := FiniteAdeleRing.ext ℚ fun _ => rfl
  rw [Set.mem_preimage, Set.mem_preimage, heq, add_sub_cancel] at hmem
  exact hmem

private theorem exists_open_finBox_subset {a : 𝔸} {V : Set 𝔸} (hV : V ∈ nhds a) :
    ∃ (W : Set (InfiniteAdeleRing ℚ)) (K : Set (InfiniteAdeleRing ℚ)) (N : ℕ), IsOpen W ∧ a.1 ∈ W ∧ IsCompact K ∧
      W ⊆ K ∧ N ≠ 0 ∧ ∀ b : 𝔸, b.1 ∈ W → b ∈ finBox N a → b ∈ V := by
  obtain ⟨a₁, a₂⟩ := a
  obtain ⟨u, hu, s, hs, hus⟩ := mem_nhds_prod_iff.mp hV
  obtain ⟨K, hKa, -, hK⟩ := LocallyCompactSpace.local_compact_nhds a₁ Set.univ Filter.univ_mem
  obtain ⟨W, hWuK, hWo, haW⟩ := mem_nhds_iff.mp (Filter.inter_mem hu hKa)
  obtain ⟨N, hN, hbox⟩ := exists_finBox_subset (a := (a₁, a₂)) hs
  exact ⟨W, K, N, hWo, haW, hK, fun y hy => (hWuK hy).2, hN, fun b hb1 hb2 =>
    hus (Set.mem_prod.mpr ⟨(hWuK hb1).1, hbox b hb2⟩)⟩

private theorem e₃_two_fin (v : HeightOneSpectrum (𝓞 ℚ)) : (e₃ 2).2 v = 1 := rfl

private theorem valued_e₃_fin_le_one (j : Fin 3) (v : HeightOneSpectrum (𝓞 ℚ)) : Valued.v ((e₃ j).2 v) ≤ 1 :=
  ((primitiveAt_iff v e₃).mp (primitiveAt_e₃ v)).1 j

private def goodRows (W : Fin 3 → Set (InfiniteAdeleRing ℚ)) (N : ℕ) : Set (Fin 3 → 𝔸) :=
  {x | (∀ j, (x j).1 ∈ W j ∧ x j ∈ finBox N (e₃ j)) ∧ rowArch default x 2 ≠ 0}

private theorem mem_goodRows {W : Fin 3 → Set (InfiniteAdeleRing ℚ)} {N : ℕ} {x : Fin 3 → 𝔸} :
    x ∈ goodRows W N ↔ (∀ j, (x j).1 ∈ W j ∧ x j ∈ finBox N (e₃ j)) ∧ rowArch default x 2 ≠ 0 :=
  Iff.rfl

private theorem measurableSet_goodRows {W : Fin 3 → Set (InfiniteAdeleRing ℚ)} (hW : ∀ j, IsOpen (W j)) (N : ℕ) :
    MeasurableSet (goodRows W N) := by
  have : goodRows W N = (⋂ j, (fun x : Fin 3 → 𝔸 => x j) ⁻¹' ((fun b : 𝔸 => b.1) ⁻¹' W j ∩ finBox N (e₃ j))) ∩
      {x | rowArch default x 2 ≠ 0} := by
    ext x
    simp only [goodRows, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
  rw [this]
  refine (MeasurableSet.iInter fun j => measurable_pi_apply j ?_).inter (measurableSet_rowArch_ne_zero default 2)
  have hWj : IsOpen ((fun b : 𝔸 => b.1) ⁻¹' W j) := (hW j).preimage continuous_fst
  exact hWj.measurableSet.inter (measurableSet_finBox N (e₃ j))

private theorem goodRows_mem_nhds {W : Fin 3 → Set (InfiniteAdeleRing ℚ)} (hW : ∀ j, IsOpen (W j))
    (hW₃ : ∀ j, (e₃ j).1 ∈ W j) {N : ℕ} (hN : N ≠ 0) : goodRows W N ∈ nhds e₃ := by
  have hj : ∀ j : Fin 3, (fun x : Fin 3 → 𝔸 => x j) ⁻¹' (Prod.fst ⁻¹' W j ∩ finBox N (e₃ j)) ∈ nhds e₃ := fun j =>
    (continuous_apply j).continuousAt.preimage_mem_nhds
      (Filter.inter_mem (continuous_fst.continuousAt.preimage_mem_nhds ((hW j).mem_nhds (hW₃ j)))
        (finBox_mem_nhds hN (e₃ j)))
  have harch : {x : Fin 3 → 𝔸 | rowArch default x 2 ≠ 0} ∈ nhds e₃ :=
    (continuous_rowArch default 2).continuousAt.eventually_ne (rowArch_e₃_two_ne_zero default)
  filter_upwards [Filter.iInter_mem.mpr hj, harch] with x hx hx'
  exact mem_goodRows.mpr ⟨fun j => Set.mem_iInter.mp hx j, hx'⟩

private theorem goodRows_subset_pi {W K : Fin 3 → Set (InfiniteAdeleRing ℚ)} (hWK : ∀ j, W j ⊆ K j) (N : ℕ) :
    goodRows W N ⊆ Set.univ.pi fun j => K j ×ˢ AdelicLevel.integralFiniteAdeles (𝓞 ℚ) ℚ := by
  intro x hx j _
  obtain ⟨hx, -⟩ := mem_goodRows.mp hx
  refine Set.mem_prod.mpr ⟨hWK j (hx j).1, fun v => ?_⟩
  have h : (x j).2 v = (x j - e₃ j).2 v + (e₃ j).2 v := by rw [← fin_add_apply, sub_add_cancel]
  rw [h]
  refine add_mem ?_ ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (valued_e₃_fin_le_one j v))
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (((hx j).2 v).trans (levelRadius_le_one N v))

private theorem measure_goodRows_ne_top {W K : Fin 3 → Set (InfiniteAdeleRing ℚ)} (hK : ∀ j, IsCompact (K j))
    (hWK : ∀ j, W j ⊆ K j) (N : ℕ) : rowHaar (goodRows W N) ≠ ⊤ :=
  ((measure_mono (goodRows_subset_pi hWK N)).trans_lt (IsFiniteMeasureOnCompacts.lt_top_of_isCompact
    (isCompact_univ_pi fun j => (hK j).prod (AdelicLevel.isCompact_integralFiniteAdeles (𝓞 ℚ) ℚ)))).ne

private theorem valued_rowAt_le_one_of_mem_goodRows {W : Fin 3 → Set (InfiniteAdeleRing ℚ)} {N : ℕ} {x : Fin 3 → 𝔸}
    (hx : x ∈ goodRows W N) (v : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 3) : Valued.v (rowAt v x j) ≤ 1 := by
  have h : rowAt v x j = (x j - e₃ j).2 v + (e₃ j).2 v := by rw [rowAt_apply, ← fin_add_apply, sub_add_cancel]
  rw [h]
  exact Valuation.map_add_le _ (((mem_goodRows.mp hx).1 j).2 v |>.trans (levelRadius_le_one N v))
    (valued_e₃_fin_le_one j v)

private theorem valued_rowAt_two_of_mem_goodRows {W : Fin 3 → Set (InfiniteAdeleRing ℚ)} {N : ℕ} {x : Fin 3 → 𝔸}
    (hx : x ∈ goodRows W N) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : residueChar v ∣ N) : Valued.v (rowAt v x 2) = 1 := by
  have h : rowAt v x 2 = 1 + (x 2 - e₃ 2).2 v := by
    rw [rowAt_apply, add_comm, ← e₃_two_fin v, ← fin_add_apply, sub_add_cancel]
  rw [h]
  exact Valuation.map_one_add_of_lt _ (((mem_goodRows.mp hx).1 2).2 v |>.trans_lt (levelRadius_lt_one hv))

private theorem primitiveAt_of_mem_goodRows {W : Fin 3 → Set (InfiniteAdeleRing ℚ)} {N : ℕ} {x : Fin 3 → 𝔸}
    (hx : x ∈ goodRows W N) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : residueChar v ∣ N) : PrimitiveAt v x :=
  (primitiveAt_iff v x).mpr ⟨valued_rowAt_le_one_of_mem_goodRows hx v, 2, valued_rowAt_two_of_mem_goodRows hx hv⟩

private theorem nonzeroAt_of_mem_goodRows {W : Fin 3 → Set (InfiniteAdeleRing ℚ)} {N : ℕ} {x : Fin 3 → 𝔸}
    (hx : x ∈ goodRows W N) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : residueChar v ∣ N) : NonzeroAt v x :=
  (nonzeroAt_iff v x).mpr ⟨2, fun h => by
    have h1 := valued_rowAt_two_of_mem_goodRows hx hv
    rw [h, map_zero] at h1
    exact zero_ne_one h1⟩

private abbrev singleAt (v : HeightOneSpectrum (𝓞 ℚ)) (r : v.adicCompletion ℚ) : 𝔸 :=
  StandardAddChar.adeleSingleAt ℚ v r

private theorem singleAt_arch (v : HeightOneSpectrum (𝓞 ℚ)) (r : v.adicCompletion ℚ) (w : InfinitePlace ℚ) :
    (singleAt v r).1 w = 0 := rfl

private theorem singleAt_fin_self (v : HeightOneSpectrum (𝓞 ℚ)) (r : v.adicCompletion ℚ) : (singleAt v r).2 v = r :=
  StandardAddChar.finAdeleSingleAt_apply_self ℚ v r

private theorem singleAt_fin_of_ne (v : HeightOneSpectrum (𝓞 ℚ)) (r : v.adicCompletion ℚ) {w : HeightOneSpectrum (𝓞 ℚ)}
    (h : w ≠ v) : (singleAt v r).2 w = 0 :=
  StandardAddChar.finAdeleSingleAt_apply_of_ne ℚ v r h

private theorem fst_add_singleAt (v : HeightOneSpectrum (𝓞 ℚ)) (r : v.adicCompletion ℚ) (b : 𝔸) :
    (b + singleAt v r).1 = b.1 := by
  funext w
  rw [arch_add_apply, singleAt_arch, add_zero]

private theorem add_singleAt_mem_finBox_iff {N : ℕ} {v : HeightOneSpectrum (𝓞 ℚ)} (hv : levelRadius N v = 1)
    {r : v.adicCompletion ℚ} (hr : Valued.v r ≤ 1) (a b : 𝔸) : b + singleAt v r ∈ finBox N a ↔ b ∈ finBox N a := by
  have hcomp : ∀ w : HeightOneSpectrum (𝓞 ℚ), (b + singleAt v r - a).2 w = (b - a).2 w + (singleAt v r).2 w :=
    fun w => by rw [add_sub_right_comm, fin_add_apply]
  simp only [mem_finBox, hcomp]
  refine (forall_place_iff v).trans (Iff.trans ?_ (forall_place_iff v).symm)
  rw [singleAt_fin_self, hv]
  refine and_congr (valued_add_le_one_iff hr _) (forall_congr' fun w => forall_congr' fun hw => ?_)
  rw [singleAt_fin_of_ne v r hw, add_zero]

private abbrev shiftRow (v : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 3) (r : v.adicCompletion ℚ) : Fin 3 → 𝔸 :=
  Pi.single j (singleAt v r)

private theorem shiftRow_apply_fst (v : HeightOneSpectrum (𝓞 ℚ)) (j i : Fin 3) (r : v.adicCompletion ℚ)
    (w : InfinitePlace ℚ) : (shiftRow v j r i).1 w = 0 := by
  by_cases h : i = j
  · rw [h]
    simp only [shiftRow, Pi.single_eq_same, singleAt_arch]
  · simp only [shiftRow, Pi.single_eq_of_ne h, arch_zero_apply]

private theorem rowArch_add_shiftRow (v : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 3) (r : v.adicCompletion ℚ)
    (x : Fin 3 → 𝔸) (w : InfinitePlace ℚ) (i : Fin 3) : rowArch w (x + shiftRow v j r) i = rowArch w x i := by
  rw [rowArch_apply, rowArch_apply, Pi.add_apply, arch_add_apply, shiftRow_apply_fst, add_zero]

private theorem rowAt_add_shiftRow_of_ne (v : HeightOneSpectrum (𝓞 ℚ)) (j i : Fin 3) (h : i ≠ j)
    (r : v.adicCompletion ℚ) (x : Fin 3 → 𝔸) : rowAt v (x + shiftRow v j r) i = rowAt v x i := by
  simp only [rowAt_apply, Pi.add_apply, shiftRow, Pi.single_eq_of_ne h, add_zero]

private theorem rowAt_shiftRow_add (v : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 3) (r : v.adicCompletion ℚ) (x : Fin 3 → 𝔸) :
    rowAt v (shiftRow v j r + x) j = r + rowAt v x j := by
  simp only [rowAt_apply, Pi.add_apply, shiftRow, Pi.single_eq_same, fin_add_apply, singleAt_fin_self]

private theorem add_shiftRow_mem_goodRows_iff {W : Fin 3 → Set (InfiniteAdeleRing ℚ)} {N : ℕ}
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : levelRadius N v = 1) (j : Fin 3) {r : v.adicCompletion ℚ} (hr : Valued.v r ≤ 1)
    (x : Fin 3 → 𝔸) : x + shiftRow v j r ∈ goodRows W N ↔ x ∈ goodRows W N := by
  simp only [mem_goodRows, rowArch_add_shiftRow]
  refine and_congr (forall_congr' fun i => ?_) Iff.rfl
  by_cases h : i = j
  · rw [h]
    simp only [Pi.add_apply, shiftRow, Pi.single_eq_same]
    rw [fst_add_singleAt, add_singleAt_mem_finBox_iff hv hr]
  · simp only [Pi.add_apply, shiftRow, Pi.single_eq_of_ne h, add_zero]

private theorem measurableSet_valued_rowAt_lt_one (v : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 3) :
    MeasurableSet {x : Fin 3 → 𝔸 | Valued.v (rowAt v x j) < 1} := by
  have : {x : Fin 3 → 𝔸 | Valued.v (rowAt v x j) < 1} =
      {x | Valued.v (rowAt v x j) ≤ 1} \ {x | Valued.v (rowAt v x j) = 1} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_diff, lt_iff_le_and_ne]
  rw [this]
  exact (measurableSet_valued_rowAt_le_one v j).diff (measurableSet_valued_rowAt_eq_one v j)

private theorem residueChar_mul_measure_le {Q : Set (Fin 3 → 𝔸)} (hQ : MeasurableSet Q) (v : HeightOneSpectrum (𝓞 ℚ))
    (j : Fin 3) (hstab : ∀ r : v.adicCompletion ℚ, Valued.v r ≤ 1 → ∀ x, x + shiftRow v j r ∈ Q ↔ x ∈ Q) :
    (residueChar v : ℝ≥0∞) * rowHaar (Q ∩ {x | Valued.v (rowAt v x j) < 1}) ≤ rowHaar Q := by
  have hDm : MeasurableSet (Q ∩ {x | Valued.v (rowAt v x j) < 1}) := hQ.inter (measurableSet_valued_rowAt_lt_one v j)
  let T : ℕ → Set (Fin 3 → 𝔸) := fun k =>
    (fun x => shiftRow v j (k : v.adicCompletion ℚ) + x) ⁻¹' (Q ∩ {x | Valued.v (rowAt v x j) < 1})
  have hTm : ∀ k, MeasurableSet (T k) := fun k => measurable_const_add _ hDm
  have hTμ : ∀ k, rowHaar (T k) = rowHaar (Q ∩ {x | Valued.v (rowAt v x j) < 1}) := fun k => measure_preimage_add _ _ _
  have hTQ : ∀ k, T k ⊆ Q := fun k x hx => by
    have hx' : shiftRow v j (k : v.adicCompletion ℚ) + x ∈ Q := hx.1
    rw [add_comm] at hx'
    exact (hstab _ (valued_natCast_le_one v k) x).mp hx'
  have hdisj : ∀ k l : ℕ, k < l → l < residueChar v → Disjoint (T k) (T l) := fun k l hkl hl => by
    refine Set.disjoint_left.mpr fun x hk hl' => ?_
    have h1 : Valued.v ((k : v.adicCompletion ℚ) + rowAt v x j) < 1 := by
      have h := hk.2
      rwa [Set.mem_setOf_eq, rowAt_shiftRow_add] at h
    have h2 : Valued.v ((l : v.adicCompletion ℚ) + rowAt v x j) < 1 := by
      have h := hl'.2
      rwa [Set.mem_setOf_eq, rowAt_shiftRow_add] at h
    have h3 : Valued.v ((l - k : ℕ) : v.adicCompletion ℚ) = 1 :=
      valued_natCast_eq_one (Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hkl) (by omega))
    have h4 : ((l - k : ℕ) : v.adicCompletion ℚ) =
        ((l : v.adicCompletion ℚ) + rowAt v x j) - ((k : v.adicCompletion ℚ) + rowAt v x j) := by
      rw [Nat.cast_sub hkl.le]
      ring
    rw [h4] at h3
    have h5 := Valuation.map_sub_lt _ h2 h1
    rw [h3] at h5
    exact lt_irrefl _ h5
  have hunion : rowHaar (⋃ k ∈ Finset.range (residueChar v), T k) =
      (residueChar v : ℝ≥0∞) * rowHaar (Q ∩ {x | Valued.v (rowAt v x j) < 1}) := by
    rw [measure_biUnion_finset ?_ fun k _ => hTm k]
    · simp only [hTμ, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    · intro k hk l hl hkl
      rcases hkl.lt_or_gt with h | h
      · exact hdisj k l h (Finset.mem_range.mp hl)
      · exact (hdisj l k h (Finset.mem_range.mp hk)).symm
  rw [← hunion]
  exact measure_mono (Set.iUnion₂_subset fun k _ => hTQ k)

private def tailTerm (i : ℕ) : ℝ≥0∞ := if 3 ≤ i then ((i : ℝ≥0∞) ^ 2)⁻¹ else 0

private theorem sum_range_tailTerm_le (n : ℕ) : ∑ i ∈ Finset.range n, tailTerm i ≤ ENNReal.ofReal (2 / 3) := by
  calc ∑ i ∈ Finset.range n, tailTerm i = ∑ i ∈ Finset.Ioo 2 n, ((i : ℝ≥0∞) ^ 2)⁻¹ := by
        simp only [tailTerm]
        rw [← Finset.sum_filter]
        congr 1
        ext i
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioo]
        constructor <;> intro h <;> omega
    _ = ∑ i ∈ Finset.Ioo 2 n, ENNReal.ofReal (((i : ℝ) ^ 2)⁻¹) := Finset.sum_congr rfl fun i hi => by
        have hi0 : (0 : ℝ) < i := Nat.cast_pos.mpr (by have := (Finset.mem_Ioo.mp hi).1; omega)
        rw [ENNReal.ofReal_inv_of_pos (pow_pos hi0 2), ENNReal.ofReal_pow hi0.le, ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal (∑ i ∈ Finset.Ioo 2 n, ((i : ℝ) ^ 2)⁻¹) :=
        (ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity).symm
    _ ≤ ENNReal.ofReal (2 / 3) :=
        ENNReal.ofReal_le_ofReal ((sum_Ioo_inv_sq_le (α := ℝ) 2 n).trans (by norm_num))

private theorem tsum_tailTerm_le : ∑' i, tailTerm i ≤ ENNReal.ofReal (2 / 3) :=
  ENNReal.tsum_le_of_sum_range_le sum_range_tailTerm_le

private theorem tailTerm_residueChar {v : HeightOneSpectrum (𝓞 ℚ)} {N : ℕ} (h2 : 2 ∣ N) (hv : ¬ residueChar v ∣ N) :
    tailTerm (residueChar v) = ((residueChar v : ℝ≥0∞) * residueChar v)⁻¹ := by
  have hne : residueChar v ≠ 2 := fun h => hv (h ▸ h2)
  have h3 : 3 ≤ residueChar v := by
    have := (residueChar_prime v).two_le
    omega
  rw [tailTerm, if_pos h3, pow_two]

private theorem measure_badRows_le {W : Fin 3 → Set (InfiniteAdeleRing ℚ)} (hW : ∀ j, IsOpen (W j)) {N : ℕ}
    (h2 : 2 ∣ N) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : ¬ residueChar v ∣ N) :
    rowHaar ((goodRows W N ∩ {x | Valued.v (rowAt v x 1) < 1}) ∩ {x | Valued.v (rowAt v x 0) < 1}) ≤
      rowHaar (goodRows W N) * tailTerm (residueChar v) := by
  have hrad : levelRadius N v = 1 := levelRadius_eq_one hv
  have hq0 : (residueChar v : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (residueChar_prime v).ne_zero
  have hqq0 : (residueChar v : ℝ≥0∞) * residueChar v ≠ 0 := mul_ne_zero hq0 hq0
  have hqqt : (residueChar v : ℝ≥0∞) * residueChar v ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _)
  have hstep1 := residueChar_mul_measure_le (measurableSet_goodRows hW N) v 1 fun r hr x =>
    add_shiftRow_mem_goodRows_iff hrad 1 hr x
  have hstep0 := residueChar_mul_measure_le
    ((measurableSet_goodRows hW N).inter (measurableSet_valued_rowAt_lt_one v 1)) v 0 fun r hr x => by
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, add_shiftRow_mem_goodRows_iff hrad 0 hr x,
        rowAt_add_shiftRow_of_ne v 0 1 (by decide) r x]
  have hboth : (residueChar v : ℝ≥0∞) * residueChar v *
      rowHaar ((goodRows W N ∩ {x | Valued.v (rowAt v x 1) < 1}) ∩ {x | Valued.v (rowAt v x 0) < 1}) ≤
        rowHaar (goodRows W N) := by
    rw [mul_assoc]
    exact (mul_le_mul' le_rfl hstep0).trans hstep1
  rw [tailTerm_residueChar h2 hv, ← div_eq_mul_inv]
  rw [mul_comm] at hboth
  exact (ENNReal.le_div_iff_mul_le (Or.inl hqq0) (Or.inl hqqt)).mpr hboth

private def sec0 (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) : AdelicGL 3 (𝓞 ℚ) ℚ :=
  sectionUnit x

private theorem coe_sec0 {x : Fin 3 → 𝔸} (hx : x ∈ rowDomain) :
    (sec0 x : Matrix (Fin 3) (Fin 3) 𝔸) = chartMatrix (pivotIdempotent x) x := by
  unfold sec0 sectionUnit
  rw [dif_pos hx]

private theorem coe_sec0_inv {x : Fin 3 → 𝔸} (hx : x ∈ rowDomain) :
    (((sec0 x)⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) =
      chartInverse (pivotIdempotent x) x (pivotInverse x) := by
  unfold sec0 sectionUnit
  rw [dif_pos hx]
  rfl

private theorem sec0_of_notMem {x : Fin 3 → 𝔸} (hx : x ∉ rowDomain) : sec0 x = 1 := by
  unfold sec0 sectionUnit
  rw [dif_neg hx]

private theorem measurable_of_pieces {X Y ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [Countable ι] {f : X → Y} {s : Set X}
    (hs : MeasurableSet s) (t : ι → Set X) (ht : ∀ i, MeasurableSet (t i)) (hts : ∀ i, t i ⊆ s)
    (hcov : ∀ x ∈ s, ∃ i, x ∈ t i) (hf : ∀ i, ContinuousOn f (t i)) {c : Y} (hc : ∀ x, x ∉ s → f x = c) :
    Measurable f := by
  refine measurable_of_isOpen fun u hu => ?_
  have h1 : f ⁻¹' u ∩ s = ⋃ i, f ⁻¹' u ∩ t i := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨hxu, hxs⟩
      obtain ⟨i, hi⟩ := hcov x hxs
      exact ⟨i, hxu, hi⟩
    · rintro ⟨i, hxu, hi⟩
      exact ⟨hxu, hts i hi⟩
  have h1m : MeasurableSet (f ⁻¹' u ∩ s) := by
    rw [h1]
    refine MeasurableSet.iUnion fun i => ?_
    obtain ⟨v, hv, hvu⟩ := continuousOn_iff'.mp (hf i) u hu
    rw [hvu]
    exact hv.measurableSet.inter (ht i)
  have h2m : MeasurableSet (f ⁻¹' u ∩ sᶜ) := by
    by_cases hcu : c ∈ u
    · have h : f ⁻¹' u ∩ sᶜ = sᶜ := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, and_iff_right_iff_imp]
        intro hxs
        rw [hc x hxs]
        exact hcu
      rw [h]
      exact hs.compl
    · have h : f ⁻¹' u ∩ sᶜ = ∅ := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_and]
        intro hxu hxs
        rw [hc x hxs] at hxu
        exact hcu hxu
      rw [h]
      exact MeasurableSet.empty
  have h : f ⁻¹' u = (f ⁻¹' u ∩ s) ∪ (f ⁻¹' u ∩ sᶜ) := (Set.inter_union_compl _ _).symm
  rw [h]
  exact h1m.union h2m

private theorem continuousOn_sec0_piece (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (π : T → Fin 3) (a : Fin 3) :
    ContinuousOn sec0 (piece T π a) := by
  rw [continuousOn_iff_continuous_restrict]
  have hε : ∀ j, Continuous fun z : piece T π a => pivotIdempotent z.1 j := fun j =>
    continuousOn_iff_continuous_restrict.mp (continuousOn_pivotIdempotent T π a j)
  have hd : Continuous fun z : piece T π a => pivotInverse z.1 :=
    continuousOn_iff_continuous_restrict.mp (continuousOn_pivotInverse T π a)
  have hx : ∀ j, Continuous fun z : piece T π a => z.1 j := fun j => (continuous_apply j).comp continuous_subtype_val
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_chartMatrix (fun j => hε j) hx).congr fun z => (coe_sec0 z.2.1).symm
  · exact (continuous_chartInverse (fun j => hε j) hx hd).congr fun z => (coe_sec0_inv z.2.1).symm

private theorem sec0_e₃ : sec0 e₃ = 1 := by
  have he : pivotIdempotent e₃ = e₃ := funext pivotIdempotent_e₃
  apply Units.ext
  rw [coe_sec0 e₃_mem_rowDomain, he, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chartMatrix, e₃]

private theorem bottomRow_sec0 {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ} (hx : x ∈ rowDomain) : bottomRow (sec0 x) = x := by
  funext j
  simp only [bottomRow, coe_sec0 hx]
  fin_cases j <;> simp [chartMatrix]

private theorem componentAt3_sec0_mem {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ} (hx : x ∈ rowDomain)
    {p : HeightOneSpectrum (𝓞 ℚ)} (hp : PrimitiveAt p x) :
    componentAt3 (𝓞 ℚ) ℚ p (sec0 x) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p := by
  have hunit : ∃ j, Valued.v (rowAt p x j) = 1 := hp.2
  have he : ∀ j, evalHom p (pivotIdempotent x j) ∈ p.adicCompletionIntegers ℚ := fun j => by
    rw [evalHom_eq, pivotIdempotent_fin]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hd : evalHom p (pivotInverse x) ∈ p.adicCompletionIntegers ℚ := by
    simp only [evalHom_eq, pivotInverse_fin hx, HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀,
      valued_finitePivot p hunit, inv_one, le_refl]
  refine mem_localMaximalCompact3_of_forall (fun i j => ?_) (fun i j => ?_)
  · rw [val_componentAt3, coe_sec0 hx, chartMatrix_map]
    exact chartMatrix_apply_mem _ he hp.1 i j
  · rw [val_componentAt3_inv, coe_sec0_inv hx, chartInverse_map]
    exact chartInverse_apply_mem _ he hp.1 hd i j

private theorem componentAt3_sec0_congr {x y : Fin 3 → AdeleRing (𝓞 ℚ) ℚ} (hx : x ∈ rowDomain) (hy : y ∈ rowDomain)
    (p : HeightOneSpectrum (𝓞 ℚ)) (h : ∀ j, evalHom p (x j) = evalHom p (y j)) :
    componentAt3 (𝓞 ℚ) ℚ p (sec0 x) = componentAt3 (𝓞 ℚ) ℚ p (sec0 y) := by
  have hrow : rowAt p x = rowAt p y := funext fun j => h j
  have he : evalHom p ∘ pivotIdempotent x = evalHom p ∘ pivotIdempotent y := funext fun j => by
    simp only [Function.comp_apply, evalHom_eq, pivotIdempotent_fin, hrow]
  have hxy : evalHom p ∘ x = evalHom p ∘ y := funext h
  apply Units.ext
  rw [val_componentAt3, val_componentAt3, coe_sec0 hx, coe_sec0 hy, chartMatrix_map, chartMatrix_map, he, hxy]

private theorem archComponent3_sec0_congr {x y : Fin 3 → AdeleRing (𝓞 ℚ) ℚ} (hx : x ∈ rowDomain) (hy : y ∈ rowDomain)
    (h : ∀ j, AdelicLevel.adeleArch (𝓞 ℚ) ℚ (x j) = AdelicLevel.adeleArch (𝓞 ℚ) ℚ (y j)) :
    archComponent3 (𝓞 ℚ) ℚ (sec0 x) = archComponent3 (𝓞 ℚ) ℚ (sec0 y) := by
  have hrow : ∀ w, rowArch w x = rowArch w y := fun w => funext fun j => by
    rw [rowArch_apply, rowArch_apply, ← adeleArch_eq, ← adeleArch_eq, h j]
  apply Units.ext
  rw [val_archComponent3, val_archComponent3, coe_sec0 hx, coe_sec0 hy, chartMatrix_map, chartMatrix_map]
  congr 1
  · funext j
    show (pivotIdempotent x j).1 = (pivotIdempotent y j).1
    funext w
    rw [pivotIdempotent_arch, pivotIdempotent_arch, hrow w]
  · funext j
    exact h j

private theorem measurable_sec0 : Measurable sec0 := by
  exact measurable_of_pieces rowDomain_measurableSet
    (fun i : (Σ T : Finset (HeightOneSpectrum (𝓞 ℚ)), (T → Fin 3)) × Fin 3 => piece i.1.1 i.1.2 i.2)
    (fun i => measurableSet_piece _ _ _) (fun i => piece_subset_rowDomain _ _ _) (fun _ hx => exists_mem_piece hx)
    (fun i => continuousOn_sec0_piece _ _ _) fun _ hx => sec0_of_notMem hx

private theorem tendsto_sec0 (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    Filter.Tendsto sec0 (nhdsWithin e₃ (explicitRows S)) (nhds 1) := by
  have h : ContinuousWithinAt sec0 (explicitRows S) e₃ :=
    (continuousOn_sec0_piece S (fun _ => 2) 2 e₃ (e₃_mem_piece S)).mono_of_mem_nhdsWithin (piece_mem_nhdsWithin_e₃ S)
  rwa [ContinuousWithinAt, sec0_e₃] at h

private theorem measurableSet_explicitRows (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    MeasurableSet (explicitRows S) := by
  have h : explicitRows S = (⋂ p, ⋂ (_ : p ∉ S), {x : Fin 3 → 𝔸 | PrimitiveAt p x}) ∩
      ((⋂ p, ⋂ (_ : p ∈ S), {x : Fin 3 → 𝔸 | NonzeroAt p x}) ∩ {x : Fin 3 → 𝔸 | NonzeroArch x}) := by
    ext x
    simp only [mem_explicitRows, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [h]
  exact (MeasurableSet.iInter fun p => MeasurableSet.iInter fun _ => measurableSet_primitiveAt p).inter
    ((MeasurableSet.iInter fun p => MeasurableSet.iInter fun _ => measurableSet_nonzeroAt p).inter
      measurableSet_nonzeroArch)

private theorem measurableSet_rowDomain : MeasurableSet rowDomain := by
  exact rowDomain_measurableSet

private theorem explicitRows_subset_rowDomain (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : explicitRows S ⊆ rowDomain := by
  exact fun _ hx => mem_rowDomain_of_mem_explicitRows hx

private theorem vecMul_mem_rowDomain {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ} (hx : x ∈ rowDomain) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    x ᵥ* (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) ∈ rowDomain := by
  obtain ⟨hnz, harch, hprim⟩ := mem_rowDomain.mp hx
  refine mem_rowDomain.mpr ⟨fun p => ?_, ?_, ?_⟩
  · rw [nonzeroAt_iff, rowAt_vecMul, ← val_componentAt3]
    exact exists_vecMul_ne_zero _ ((nonzeroAt_iff p x).mp (hnz p))
  · obtain ⟨j, hj⟩ := exists_vecMul_ne_zero (archComponent3 (𝓞 ℚ) ℚ g)
      (y := fun j => AdelicLevel.adeleArch (𝓞 ℚ) ℚ (x j)) (by simpa [NonzeroArch] using harch)
    refine ⟨j, fun h0 => hj ?_⟩
    rw [val_archComponent3, ← h0]
    simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_three, Matrix.map_apply, map_add, map_mul]
  · filter_upwards [hprim, eventually_componentAt3_mem g] with p hp hg
    exact primitiveAt_vecMul hp hg

private theorem pos_rowHaar_inter_explicitRows (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {O : Set (Fin 3 → AdeleRing (𝓞 ℚ) ℚ)} (hO : O ∈ nhds e₃) : 0 < rowHaar (O ∩ explicitRows S) := by
  rw [nhds_pi, Filter.mem_pi] at hO
  obtain ⟨I, -, t, ht, hIt⟩ := hO
  choose W K N hWo hW₃ hK hWK hN hsub using fun j => exists_open_finBox_subset (ht j)
  obtain ⟨M, hM0, hNM, h2M, hSM⟩ : ∃ M : ℕ, M ≠ 0 ∧ (∀ j, N j ∣ M) ∧ 2 ∣ M ∧ ∀ v ∈ S, residueChar v ∣ M :=
    ⟨(∏ j, N j) * 2 * ∏ v ∈ S, residueChar v,
      mul_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ => hN j) two_ne_zero)
        (Finset.prod_ne_zero_iff.mpr fun v _ => (residueChar_prime v).ne_zero),
      fun j => ((Finset.dvd_prod_of_mem N (Finset.mem_univ j)).mul_right _).mul_right _,
      (dvd_mul_left 2 _).mul_right _,
      fun v hv => dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hv) _⟩
  have hQO : goodRows W M ⊆ O := fun x hx => hIt fun j _ =>
    hsub j (x j) ((mem_goodRows.mp hx).1 j).1 (finBox_antitone (hNM j) _ ((mem_goodRows.mp hx).1 j).2)
  refine lt_of_lt_of_le ?_ (measure_mono (Set.inter_subset_inter_left _ hQO))
  have hQpos : 0 < rowHaar (goodRows W M) := Measure.measure_pos_of_nonempty_interior (μ := rowHaar)
    ⟨e₃, mem_interior_iff_mem_nhds.mpr (goodRows_mem_nhds hWo hW₃ hM0)⟩
  have hQtop : rowHaar (goodRows W M) ≠ ⊤ := measure_goodRows_ne_top hK hWK M
  refine pos_iff_ne_zero.mpr fun h0 => ?_
  let E : {v : HeightOneSpectrum (𝓞 ℚ) // ¬ residueChar v ∣ M} → Set (Fin 3 → 𝔸) := fun v =>
    (goodRows W M ∩ {x | Valued.v (rowAt v.1 x 1) < 1}) ∩ {x | Valued.v (rowAt v.1 x 0) < 1}
  have hcover : goodRows W M ⊆ (goodRows W M ∩ explicitRows S) ∪ ⋃ v, E v := by
    intro x hx
    by_cases hxS : x ∈ explicitRows S
    · exact Or.inl ⟨hx, hxS⟩
    · have hprim : ¬ ∀ v, v ∉ S → PrimitiveAt v x := fun h =>
        hxS (mem_explicitRows.mpr ⟨h, fun v hv => nonzeroAt_of_mem_goodRows hx (hSM v hv),
          nonzeroArch_of_rowArch ⟨2, (mem_goodRows.mp hx).2⟩⟩)
      simp only [not_forall] at hprim
      obtain ⟨v, -, hvbad⟩ := hprim
      have hvM : ¬ residueChar v ∣ M := fun hdvd => hvbad (primitiveAt_of_mem_goodRows hx hdvd)
      have hle := valued_rowAt_le_one_of_mem_goodRows hx v
      refine Or.inr (Set.mem_iUnion.mpr ⟨⟨v, hvM⟩, ⟨hx, ?_⟩, ?_⟩)
      · exact lt_of_le_of_ne (hle 1) fun h1 => hvbad ((primitiveAt_iff v x).mpr ⟨hle, 1, h1⟩)
      · exact lt_of_le_of_ne (hle 0) fun h1 => hvbad ((primitiveAt_iff v x).mpr ⟨hle, 0, h1⟩)
  have hE : ∀ v, rowHaar (E v) ≤ rowHaar (goodRows W M) * tailTerm (residueChar v.1) := fun v =>
    measure_badRows_le hWo h2M v.2
  have hinj : Function.Injective fun v : {v : HeightOneSpectrum (𝓞 ℚ) // ¬ residueChar v ∣ M} => residueChar v.1 :=
    residueChar_injective.comp Subtype.val_injective
  have hsum : ∑' v, rowHaar (E v) ≤ rowHaar (goodRows W M) * ENNReal.ofReal (2 / 3) :=
    calc ∑' v, rowHaar (E v)
      _ ≤ ∑' v : {v : HeightOneSpectrum (𝓞 ℚ) // ¬ residueChar v ∣ M},
            rowHaar (goodRows W M) * tailTerm (residueChar v.1) :=
          ENNReal.tsum_le_tsum hE
      _ = rowHaar (goodRows W M) *
            ∑' v : {v : HeightOneSpectrum (𝓞 ℚ) // ¬ residueChar v ∣ M}, tailTerm (residueChar v.1) :=
          ENNReal.tsum_mul_left
      _ ≤ rowHaar (goodRows W M) * ∑' i, tailTerm i :=
          mul_le_mul' le_rfl (ENNReal.tsum_comp_le_tsum_of_injective hinj tailTerm)
      _ ≤ rowHaar (goodRows W M) * ENNReal.ofReal (2 / 3) := mul_le_mul' le_rfl tsum_tailTerm_le
  have hlt : rowHaar (goodRows W M) * ENNReal.ofReal (2 / 3) < rowHaar (goodRows W M) := by
    calc rowHaar (goodRows W M) * ENNReal.ofReal (2 / 3)
      _ = ENNReal.ofReal (2 / 3) * rowHaar (goodRows W M) := mul_comm _ _
      _ < 1 * rowHaar (goodRows W M) :=
          ENNReal.mul_lt_mul_left hQpos.ne' hQtop (ENNReal.ofReal_lt_one.mpr (by norm_num))
      _ = rowHaar (goodRows W M) := one_mul _
  refine lt_irrefl _ (hlt.trans_le ?_)
  calc rowHaar (goodRows W M) ≤ rowHaar ((goodRows W M ∩ explicitRows S) ∪ ⋃ v, E v) := measure_mono hcover
    _ ≤ rowHaar (goodRows W M ∩ explicitRows S) + rowHaar (⋃ v, E v) := measure_union_le _ _
    _ = rowHaar (⋃ v, E v) := by rw [h0, zero_add]
    _ ≤ ∑' v, rowHaar (E v) := measure_iUnion_le _
    _ ≤ rowHaar (goodRows W M) * ENNReal.ofReal (2 / 3) := hsum

end SectionHeads

end SectionAndRowSets

section WeightedFibreMeasure

section FibreLaw

variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H]

private def weightedMeasure (ρ : Measure H) (δ : H → ℝ≥0∞) : Measure H :=
  ρ.withDensity fun p => (δ p)⁻¹

omit [MeasurableSpace H] [MeasurableMul H] in

private theorem inv_modulus_eq (δ : H → ℝ≥0∞) (hδmul : ∀ p q : H, δ (p * q) = δ p * δ q) (hδ0 : ∀ p : H, δ p ≠ 0)
    (hδtop : ∀ p : H, δ p ≠ ⊤) (p q : H) : (δ p)⁻¹ = δ q * (δ (p * q))⁻¹ := by
  rw [hδmul, ENNReal.mul_inv (Or.inl (hδ0 p)) (Or.inl (hδtop p)), mul_left_comm,
    ENNReal.mul_inv_cancel (hδ0 q) (hδtop q), mul_one]

private theorem lintegral_mul_right_weightedMeasure (ρ : Measure H) [ρ.IsMulRightInvariant] {δ : H → ℝ≥0∞}
    (hδ : Measurable δ) (hδmul : ∀ p q : H, δ (p * q) = δ p * δ q) (hδ0 : ∀ p : H, δ p ≠ 0)
    (hδtop : ∀ p : H, δ p ≠ ⊤) (q : H) {F : H → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F (p * q) ∂weightedMeasure ρ δ = δ q * ∫⁻ p, F p ∂weightedMeasure ρ δ := by
  have hFq : Measurable fun p => F (p * q) := hF.comp (measurable_mul_const q)
  rw [weightedMeasure, lintegral_withDensity_eq_lintegral_mul _ (show Measurable fun p => (δ p)⁻¹ from hδ.inv) hFq,
    lintegral_withDensity_eq_lintegral_mul _ (show Measurable fun p => (δ p)⁻¹ from hδ.inv) hF]
  have hpt : ∀ p : H, ((fun p => (δ p)⁻¹) * fun p => F (p * q)) p =
      δ q * ((fun p => (δ p)⁻¹) * F) (p * q) := by
    intro p
    simp only [Pi.mul_apply]
    rw [inv_modulus_eq δ hδmul hδ0 hδtop p q, mul_assoc]
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ (hδtop q), lintegral_mul_right_eq_self ((fun p => (δ p)⁻¹) * F) q]

private scoped instance sFinite_weightedMeasure (ρ : Measure H) [SFinite ρ] (δ : H → ℝ≥0∞) :
    SFinite (weightedMeasure ρ δ) := by
  unfold weightedMeasure
  infer_instance

end FibreLaw

end WeightedFibreMeasure

section DeviceFiniteness

section GenericDevice

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] {Y : Type} [MeasurableSpace Y]

private def fibMeasure (P : Subgroup G) (sec : Y → G) (δ : G → ℝ≥0∞) (μP : Measure ↥P) (lam : Measure Y)
    (R : Set Y) : Measure G :=
  Measure.map (fun z : Y × ↥P => (z.2 : G) * sec z.1)
    (((lam.restrict R).withDensity fun x => (δ (sec x))⁻¹).prod μP)

private theorem measurable_fibMap (P : Subgroup G) {sec : Y → G} (hsec : Measurable sec) :
    Measurable fun z : Y × ↥P => (z.2 : G) * sec z.1 :=
  (measurable_subtype_coe.comp measurable_snd).mul (hsec.comp measurable_fst)

private theorem measurable_fibreIntegral (P : Subgroup G) {sec : Y → G} (hsec : Measurable sec) (μP : Measure ↥P)
    [SFinite μP] {f : G → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun x : Y => ∫⁻ p : ↥P, f ((p : G) * sec x) ∂μP := by
  have hfφ : Measurable fun z : Y × ↥P => f ((z.2 : G) * sec z.1) := hf.comp (measurable_fibMap P hsec)
  exact hfφ.lintegral_prod_right'

private theorem lintegral_fibMeasure (P : Subgroup G) {sec : Y → G} (hsec : Measurable sec) {δ : G → ℝ≥0∞}
    (hδ : Measurable δ) (μP : Measure ↥P) [SFinite μP] (lam : Measure Y) (R : Set Y) {f : G → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ g, f g ∂fibMeasure P sec δ μP lam R =
      ∫⁻ x in R, (δ (sec x))⁻¹ * ∫⁻ p : ↥P, f ((p : G) * sec x) ∂μP ∂lam := by
  have hfφ : Measurable fun z : Y × ↥P => f ((z.2 : G) * sec z.1) := hf.comp (measurable_fibMap P hsec)
  have hw : Measurable fun x : Y => (δ (sec x))⁻¹ := (hδ.comp hsec).inv
  rw [fibMeasure, lintegral_map hf (measurable_fibMap P hsec), lintegral_prod _ hfφ.aemeasurable]
  dsimp only
  rw [lintegral_withDensity_eq_lintegral_mul _ hw (measurable_fibreIntegral P hsec μP hf)]
  simp only [Pi.mul_apply]

private theorem lintegral_mul_right_fibMeasure (P : Subgroup G) (π : G → Y) (act : Y → G → Y) {sec : Y → G}
    (hsec : Measurable sec) {δ : G → ℝ≥0∞} (hδ : Measurable δ) (μP : Measure ↥P) [SFinite μP] (lam : Measure Y)
    {R : Set Y} (hR : MeasurableSet R)
    (hπmul : ∀ g h : G, π (g * h) = act (π g) h)
    (hπP : ∀ a b : G, π a = π b → a * b⁻¹ ∈ P)
    (hπsec : ∀ x ∈ R, π (sec x) = x)
    (hRact : ∀ (x : Y) (h : G), act x h ∈ R ↔ x ∈ R)
    (hδmul : ∀ g h : G, δ (g * h) = δ g * δ h) (hδinv : ∀ g : G, δ g⁻¹ = (δ g)⁻¹)
    (hδ0 : ∀ g : G, δ g ≠ 0) (hδtop : ∀ g : G, δ g ≠ ⊤)
    (hμP : ∀ (p₁ : ↥P) (F : ↥P → ℝ≥0∞), Measurable F →
      ∫⁻ p, F (p * p₁) ∂μP = δ (p₁ : G) * ∫⁻ p, F p ∂μP)
    (hlam : ∀ (h : G) (Ψ : Y → ℝ≥0∞), Measurable Ψ → ∫⁻ x, Ψ (act x h) ∂lam = (δ h)⁻¹ * ∫⁻ x, Ψ x ∂lam)
    (h : G) {f : G → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ g, f (g * h) ∂fibMeasure P sec δ μP lam R = ∫⁻ g, f g ∂fibMeasure P sec δ μP lam R := by
  have hfh : Measurable fun g => f (g * h) := hf.comp (measurable_mul_const h)
  rw [lintegral_fibMeasure P hsec hδ μP lam R hfh, lintegral_fibMeasure P hsec hδ μP lam R hf]

  set Ψ : Y → ℝ≥0∞ := fun x => (δ (sec x))⁻¹ * ∫⁻ p : ↥P, f ((p : G) * sec x) ∂μP with hΨ
  have hΨm : Measurable Ψ := (hδ.comp hsec).inv.mul (measurable_fibreIntegral P hsec μP hf)

  have hpt : ∀ x ∈ R, (δ (sec x))⁻¹ * ∫⁻ p : ↥P, f ((p : G) * sec x * h) ∂μP = δ h * Ψ (act x h) := by
    intro x hx
    have hx' : act x h ∈ R := (hRact x h).2 hx
    have hmem : sec x * h * (sec (act x h))⁻¹ ∈ P := by
      refine hπP _ _ ?_
      rw [hπmul, hπsec x hx, hπsec _ hx']
    set p₁ : ↥P := ⟨sec x * h * (sec (act x h))⁻¹, hmem⟩ with hp₁
    have hfactor : ∀ p : ↥P, (p : G) * sec x * h = ((p * p₁ : ↥P) : G) * sec (act x h) := by
      intro p
      simp only [hp₁, Subgroup.coe_mul, mul_assoc, inv_mul_cancel, mul_one]
    have hδp₁ : δ (p₁ : G) = δ (sec x) * δ h * (δ (sec (act x h)))⁻¹ := by
      simp only [hp₁, hδmul, hδinv]
    simp_rw [hfactor]
    rw [hμP p₁ (fun p => f ((p : G) * sec (act x h))) (hf.comp (measurable_subtype_coe.mul_const _)), hδp₁]
    simp only [hΨ]

    set I : ℝ≥0∞ := ∫⁻ p : ↥P, f ((p : G) * sec (act x h)) ∂μP
    calc (δ (sec x))⁻¹ * (δ (sec x) * δ h * (δ (sec (act x h)))⁻¹ * I)
        = ((δ (sec x))⁻¹ * δ (sec x)) * (δ h * ((δ (sec (act x h)))⁻¹ * I)) := by simp only [mul_assoc]
      _ = δ h * ((δ (sec (act x h)))⁻¹ * I) := by rw [ENNReal.inv_mul_cancel (hδ0 _) (hδtop _), one_mul]

  have hind : ∀ x : Y, R.indicator (fun x => Ψ (act x h)) x = R.indicator Ψ (act x h) := by
    intro x
    by_cases hx : x ∈ R
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hRact x h).2 hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx ((hRact x h).1 h'))]
  calc ∫⁻ x in R, (δ (sec x))⁻¹ * ∫⁻ p : ↥P, f ((p : G) * sec x * h) ∂μP ∂lam
      = ∫⁻ x in R, δ h * Ψ (act x h) ∂lam := setLIntegral_congr_fun hR hpt
    _ = δ h * ∫⁻ x in R, Ψ (act x h) ∂lam := lintegral_const_mul' _ _ (hδtop h)
    _ = δ h * ∫⁻ x, R.indicator Ψ (act x h) ∂lam := by
        rw [← lintegral_indicator hR]
        simp_rw [hind]
    _ = δ h * ((δ h)⁻¹ * ∫⁻ x, R.indicator Ψ x ∂lam) := by rw [hlam h _ (hΨm.indicator hR)]
    _ = ∫⁻ x, R.indicator Ψ x ∂lam := by rw [← mul_assoc, ENNReal.mul_inv_cancel (hδ0 h) (hδtop h), one_mul]
    _ = ∫⁻ x in R, Ψ x ∂lam := lintegral_indicator hR _

private theorem isMulRightInvariant_fibMeasure (P : Subgroup G) (π : G → Y) (act : Y → G → Y) {sec : Y → G}
    (hsec : Measurable sec) {δ : G → ℝ≥0∞} (hδ : Measurable δ) (μP : Measure ↥P) [SFinite μP] (lam : Measure Y)
    {R : Set Y} (hR : MeasurableSet R)
    (hπmul : ∀ g h : G, π (g * h) = act (π g) h)
    (hπP : ∀ a b : G, π a = π b → a * b⁻¹ ∈ P)
    (hπsec : ∀ x ∈ R, π (sec x) = x)
    (hRact : ∀ (x : Y) (h : G), act x h ∈ R ↔ x ∈ R)
    (hδmul : ∀ g h : G, δ (g * h) = δ g * δ h) (hδinv : ∀ g : G, δ g⁻¹ = (δ g)⁻¹)
    (hδ0 : ∀ g : G, δ g ≠ 0) (hδtop : ∀ g : G, δ g ≠ ⊤)
    (hμP : ∀ (p₁ : ↥P) (F : ↥P → ℝ≥0∞), Measurable F →
      ∫⁻ p, F (p * p₁) ∂μP = δ (p₁ : G) * ∫⁻ p, F p ∂μP)
    (hlam : ∀ (h : G) (Ψ : Y → ℝ≥0∞), Measurable Ψ → ∫⁻ x, Ψ (act x h) ∂lam = (δ h)⁻¹ * ∫⁻ x, Ψ x ∂lam) :
    (fibMeasure P sec δ μP lam R).IsMulRightInvariant := by
  refine (forall_measure_preimage_mul_right_iff _).1 fun h A hA => ?_
  have key := lintegral_mul_right_fibMeasure P π act hsec hδ μP lam hR hπmul hπP hπsec hRact hδmul hδinv hδ0 hδtop
    hμP hlam h (f := A.indicator fun _ => (1 : ℝ≥0∞)) (measurable_const.indicator hA)
  have hpre : (fun g => A.indicator (fun _ => (1 : ℝ≥0∞)) (g * h)) =
      ((fun g => g * h) ⁻¹' A).indicator fun _ => (1 : ℝ≥0∞) := by
    funext g
    by_cases hg : g * h ∈ A
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (show g ∈ (fun g => g * h) ⁻¹' A from hg)]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (show g ∉ (fun g => g * h) ⁻¹' A from hg)]
  rw [hpre, lintegral_indicator_const (hA.preimage (measurable_mul_const h)), lintegral_indicator_const hA, one_mul,
    one_mul] at key
  exact key

end GenericDevice

section Finiteness

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] {Y : Type} [MeasurableSpace Y]

private theorem fibMeasure_apply (P : Subgroup G) {sec : Y → G} (hsec : Measurable sec) {δ : G → ℝ≥0∞}
    (hδ : Measurable δ) (μP : Measure ↥P) [SFinite μP] (lam : Measure Y) (R : Set Y) {K : Set G}
    (hK : MeasurableSet K) :
    fibMeasure P sec δ μP lam R K =
      ∫⁻ x in R, (δ (sec x))⁻¹ * ∫⁻ p : ↥P, K.indicator (fun _ => (1 : ℝ≥0∞)) ((p : G) * sec x) ∂μP ∂lam := by
  rw [← one_mul (fibMeasure P sec δ μP lam R K), ← lintegral_indicator_const hK,
    lintegral_fibMeasure P hsec hδ μP lam R (measurable_const.indicator hK)]

private theorem fibMeasure_ne_top (P : Subgroup G) (π : G → Y) {sec : Y → G} (hsec : Measurable sec)
    {δ : G → ℝ≥0∞} (hδ : Measurable δ) (μP : Measure ↥P) [SFinite μP] (lam : Measure Y) {R : Set Y}
    (hR : MeasurableSet R)
    (hπleft : ∀ (p : ↥P) (g : G), π ((p : G) * g) = π g)
    (hπP : ∀ a b : G, π a = π b → a * b⁻¹ ∈ P)
    (hπsec : ∀ x ∈ R, π (sec x) = x)
    (hδmul : ∀ g h : G, δ (g * h) = δ g * δ h) (hδinv : ∀ g : G, δ g⁻¹ = (δ g)⁻¹)
    (hδ0 : ∀ g : G, δ g ≠ 0) (hδtop : ∀ g : G, δ g ≠ ⊤)
    (hμP : ∀ (p₁ : ↥P) (F : ↥P → ℝ≥0∞), Measurable F →
      ∫⁻ p, F (p * p₁) ∂μP = δ (p₁ : G) * ∫⁻ p, F p ∂μP)
    {K : Set G} (hK : MeasurableSet K)
    {T : Set Y} (hTmeas : MeasurableSet T) (hTtop : lam T ≠ ⊤) (hKT : ∀ k ∈ K, π k ∈ T)
    {C : Set ↥P} (hCmeas : MeasurableSet C) (hCtop : μP C ≠ ⊤)
    (hKC : ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ q : ↥P, (q : G) = k₁ * k₂⁻¹ → q ∈ C)
    {m : ℝ≥0∞} (hm0 : m ≠ 0) (hmK : ∀ k ∈ K, m ≤ δ k) :
    fibMeasure P sec δ μP lam R K ≠ ⊤ := by
  rw [fibMeasure_apply P hsec hδ μP lam R hK]

  have hrow : ∀ x ∈ R, (δ (sec x))⁻¹ * ∫⁻ p : ↥P, K.indicator (fun _ => (1 : ℝ≥0∞)) ((p : G) * sec x) ∂μP ≤
      T.indicator (fun _ => m⁻¹ * μP C) x := by
    intro x hx
    by_cases hxK : ∃ k ∈ K, π k = x
    · obtain ⟨k₀, hk₀, hπk₀⟩ := hxK
      have hxT : x ∈ T := hπk₀ ▸ hKT k₀ hk₀
      have hmem : sec x * k₀⁻¹ ∈ P := hπP _ _ (by rw [hπsec x hx, hπk₀])
      set p₀ : ↥P := ⟨sec x * k₀⁻¹, hmem⟩ with hp₀

      have hfib : ∀ p : ↥P, K.indicator (fun _ => (1 : ℝ≥0∞)) ((p : G) * sec x) ≤
          C.indicator (fun _ => (1 : ℝ≥0∞)) (p * p₀) := by
        intro p
        by_cases hpK : (p : G) * sec x ∈ K
        · have hpC : p * p₀ ∈ C := by
            refine hKC _ hpK k₀ hk₀ (p * p₀) ?_
            simp only [hp₀, Subgroup.coe_mul, mul_assoc]
          rw [Set.indicator_of_mem hpK, Set.indicator_of_mem hpC]
        · rw [Set.indicator_of_notMem hpK]
          exact zero_le
      have hδp₀ : δ (p₀ : G) = δ (sec x) * (δ k₀)⁻¹ := by
        simp only [hp₀, hδmul, hδinv]
      calc (δ (sec x))⁻¹ * ∫⁻ p : ↥P, K.indicator (fun _ => (1 : ℝ≥0∞)) ((p : G) * sec x) ∂μP
          ≤ (δ (sec x))⁻¹ * ∫⁻ p : ↥P, C.indicator (fun _ => (1 : ℝ≥0∞)) (p * p₀) ∂μP :=
            mul_le_mul' le_rfl (lintegral_mono fun p => hfib p)
        _ = (δ (sec x))⁻¹ * (δ (sec x) * (δ k₀)⁻¹ * μP C) := by
            rw [hμP p₀ _ (measurable_const.indicator hCmeas), lintegral_indicator_const hCmeas, one_mul, hδp₀]
        _ = (δ k₀)⁻¹ * μP C := by
            rw [← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel (hδ0 _) (hδtop _), one_mul]
        _ ≤ m⁻¹ * μP C := mul_le_mul' (ENNReal.inv_le_inv' (hmK k₀ hk₀)) le_rfl
        _ = T.indicator (fun _ => m⁻¹ * μP C) x := by rw [Set.indicator_of_mem hxT]
    ·
      have hzero : ∀ p : ↥P, K.indicator (fun _ => (1 : ℝ≥0∞)) ((p : G) * sec x) = 0 := by
        intro p
        refine Set.indicator_of_notMem (fun hpK => hxK ⟨_, hpK, ?_⟩) _
        rw [hπleft, hπsec x hx]
      simp only [hzero, lintegral_zero, mul_zero]
      exact zero_le
  refine ne_top_of_le_ne_top ?_ ((setLIntegral_mono' hR hrow).trans (setLIntegral_le_lintegral _ _))
  rw [lintegral_indicator_const hTmeas]
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hm0) hCtop) hTtop

end Finiteness

end DeviceFiniteness

section CompactSupports

section CompactInputs

open scoped Pointwise

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

attribute [local instance] NumberField.AdeleRing.secondCountableTopology

private theorem exists_ne_zero_le_on_of_isCompact {X : Type} [TopologicalSpace X] {f : X → ℝ≥0∞} (hf : Continuous f)
    (hf0 : ∀ x, f x ≠ 0) {K : Set X} (hK : IsCompact K) : ∃ m : ℝ≥0∞, m ≠ 0 ∧ ∀ k ∈ K, m ≤ f k := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨1, one_ne_zero, by simp [hKe]⟩
  · obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hKne hf.continuousOn
    exact ⟨f x₀, hf0 x₀, fun k hk => hmin hk⟩

private theorem continuous_ofReal_ideleNorm_det :
    Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ =>
      ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g)) :=
  ENNReal.continuous_ofReal.comp
    ((NumberField.TateGlobal.continuous_ideleNorm ℚ).comp Matrix.GeneralLinearGroup.continuous_det)

private theorem isFiniteMeasureOnCompacts_rowHaar :
    IsFiniteMeasureOnCompacts (rowHaar : Measure (Fin 3 → AdeleRing (𝓞 ℚ) ℚ)) :=
  inferInstance

private theorem isCompact_image_bottomRow {K : Set (AdelicGL 3 (𝓞 ℚ) ℚ)} (hK : IsCompact K) :
    IsCompact (bottomRow '' K) :=
  hK.image continuous_bottomRow

private theorem isCompact_mul_inv {K : Set (AdelicGL 3 (𝓞 ℚ) ℚ)} (hK : IsCompact K) : IsCompact (K * K⁻¹) :=
  hK.mul hK.inv

private theorem isCompact_preimage_mirabolic {L : Set (AdelicGL 3 (𝓞 ℚ) ℚ)} (hL : IsCompact L) :
    IsCompact ((fun q : ↥mirabolic => (q : AdelicGL 3 (𝓞 ℚ) ℚ)) ⁻¹' L) :=
  isClosed_mirabolic.isClosedEmbedding_subtypeVal.isCompact_preimage hL

private theorem mem_preimage_mul_inv_of_mem {K : Set (AdelicGL 3 (𝓞 ℚ) ℚ)} {k₁ : AdelicGL 3 (𝓞 ℚ) ℚ} (hk₁ : k₁ ∈ K)
    {k₂ : AdelicGL 3 (𝓞 ℚ) ℚ} (hk₂ : k₂ ∈ K) (q : ↥mirabolic) (hq : (q : AdelicGL 3 (𝓞 ℚ) ℚ) = k₁ * k₂⁻¹) :
    q ∈ (fun q : ↥mirabolic => (q : AdelicGL 3 (𝓞 ℚ) ℚ)) ⁻¹' (K * K⁻¹) := by
  show (q : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ K * K⁻¹
  rw [hq]
  exact Set.mul_mem_mul hk₁ (Set.inv_mem_inv.2 hk₂)

end CompactInputs

end CompactSupports

section OrbitSpaceMeasure

section OrbitSpace

variable {K : Type} [Group K] [MeasurableSpace K] (H : Subgroup K)

private theorem measurable_orbit_mk :
    Measurable (Quotient.mk'' : K → MulAction.orbitRel.Quotient H K) :=
  measurable_quotient_mk''

omit [MeasurableSpace K] in

private theorem invariant_apply_out (h : K → ℝ≥0∞) (hinv : ∀ (n : ↥H) (k : K), h ((n : K) * k) = h k) (k : K) :
    h (Quotient.out (Quotient.mk'' k : MulAction.orbitRel.Quotient H K)) = h k := by
  have hrel := Quotient.mk_out' (s₁ := MulAction.orbitRel H K) k
  obtain ⟨n, hn⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hrel)
  rw [← hn]
  exact hinv n k

private theorem measurable_invariant_out {h : K → ℝ≥0∞} (hmeas : Measurable h)
    (hinv : ∀ (n : ↥H) (k : K), h ((n : K) * k) = h k) :
    Measurable fun q : MulAction.orbitRel.Quotient H K => h (Quotient.out q) := by
  refine measurable_from_quotient.2 ?_
  have hfun : ((fun q : MulAction.orbitRel.Quotient H K => h (Quotient.out q)) ∘ Quotient.mk'') = h := by
    funext k
    exact invariant_apply_out H h hinv k
  rw [hfun]
  exact hmeas

private theorem lintegral_out_map_mk (μ : Measure K) {h : K → ℝ≥0∞} (hmeas : Measurable h)
    (hinv : ∀ (n : ↥H) (k : K), h ((n : K) * k) = h k) :
    ∫⁻ q, h (Quotient.out q) ∂(Measure.map (Quotient.mk'' : K → MulAction.orbitRel.Quotient H K) μ) =
      ∫⁻ k, h k ∂μ := by
  rw [lintegral_map (measurable_invariant_out H hmeas hinv) (measurable_orbit_mk H)]
  congr 1
  funext k
  exact invariant_apply_out H h hinv k

end OrbitSpace

end OrbitSpaceMeasure

section OrbitDensityTrade

section DensityIndependence

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {N P : Subgroup G} (μN : Measure N) [SFinite μN] (μP : Measure P) [SFinite μP]

private theorem lintegral_mul_density_eq (hNP : N ≤ P) (hPinv : ∀ n : P, (n : G) ∈ N → ∀ F : P → ℝ≥0∞, Measurable F →
      ∫⁻ p, F (n * p) ∂μP = ∫⁻ p, F p ∂μP)
    (hμN : ∀ f : N → ℝ≥0∞, ∫⁻ x, f x⁻¹ ∂μN = ∫⁻ x, f x ∂μN)
    {δ₁ δ₂ : G → ℝ≥0∞} (hδ₁m : Measurable δ₁) (hδ₂m : Measurable δ₂)
    (hδ₁ : ∀ g : G, ∫⁻ x : N, δ₁ ((x : G) * g) ∂μN = 1) (hδ₂ : ∀ g : G, ∫⁻ x : N, δ₂ ((x : G) * g) ∂μN = 1)
    {φ : P → ℝ≥0∞} (hφm : Measurable φ) (hφ : ∀ n : P, (n : G) ∈ N → ∀ p, φ (n * p) = φ p) :
    ∫⁻ p : P, φ p * δ₁ (p : G) ∂μP = ∫⁻ p : P, φ p * δ₂ (p : G) ∂μP := by
  have hjoint : Measurable fun q : P × N => φ q.1 * δ₁ (q.1 : G) * δ₂ ((q.2 : G) * (q.1 : G)) :=
    ((hφm.comp measurable_fst).mul (hδ₁m.comp (measurable_subtype_coe.comp measurable_fst))).mul
      (hδ₂m.comp ((measurable_subtype_coe.comp measurable_snd).mul (measurable_subtype_coe.comp measurable_fst)))
  have hjoint' : Measurable fun q : P × N => φ q.1 * δ₂ (q.1 : G) * δ₁ (((q.2⁻¹ : N) : G) * (q.1 : G)) :=
    ((hφm.comp measurable_fst).mul (hδ₂m.comp (measurable_subtype_coe.comp measurable_fst))).mul
      (hδ₁m.comp ((measurable_subtype_coe.comp measurable_snd.inv).mul (measurable_subtype_coe.comp measurable_fst)))
  calc ∫⁻ p : P, φ p * δ₁ (p : G) ∂μP
      = ∫⁻ p : P, φ p * δ₁ (p : G) * ∫⁻ x : N, δ₂ ((x : G) * (p : G)) ∂μN ∂μP := by
        simp only [hδ₂, mul_one]
    _ = ∫⁻ p : P, ∫⁻ x : N, φ p * δ₁ (p : G) * δ₂ ((x : G) * (p : G)) ∂μN ∂μP := by
        congr 1
        funext p
        exact (lintegral_const_mul _ (hδ₂m.comp (measurable_subtype_coe.mul measurable_const))).symm
    _ = ∫⁻ x : N, ∫⁻ p : P, φ p * δ₁ (p : G) * δ₂ ((x : G) * (p : G)) ∂μP ∂μN :=
        lintegral_lintegral_swap hjoint.aemeasurable
    _ = ∫⁻ x : N, ∫⁻ p : P, φ p * δ₂ (p : G) * δ₁ (((x⁻¹ : N) : G) * (p : G)) ∂μP ∂μN := by
        congr 1
        funext x
        have hx : ((⟨(x : G), hNP x.2⟩ : P) : G) ∈ N := x.2
        have h := hPinv ⟨(x : G), hNP x.2⟩ hx (fun p : P => φ p * δ₂ (p : G) * δ₁ (((x⁻¹ : N) : G) * (p : G)))
          (hjoint'.comp (measurable_id.prodMk measurable_const))
        refine Eq.trans ?_ h
        congr 1
        funext p
        beta_reduce
        rw [hφ _ hx]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_left]
        ring
    _ = ∫⁻ p : P, ∫⁻ x : N, φ p * δ₂ (p : G) * δ₁ (((x⁻¹ : N) : G) * (p : G)) ∂μN ∂μP :=
        (lintegral_lintegral_swap hjoint'.aemeasurable).symm
    _ = ∫⁻ p : P, φ p * δ₂ (p : G) * ∫⁻ x : N, δ₁ (((x⁻¹ : N) : G) * (p : G)) ∂μN ∂μP := by
        congr 1
        funext p
        exact lintegral_const_mul _ (hδ₁m.comp ((measurable_subtype_coe.comp measurable_inv).mul measurable_const))
    _ = ∫⁻ p : P, φ p * δ₂ (p : G) ∂μP := by
        congr 1
        funext p
        have h1 : ∫⁻ x : N, δ₁ (((x⁻¹ : N) : G) * (p : G)) ∂μN = 1 :=
          (hμN fun x : N => δ₁ ((x : G) * (p : G))).trans (hδ₁ (p : G))
        rw [h1, mul_one]

end DensityIndependence

end OrbitDensityTrade

section HaarUniqueness

section RightInvariantUniqueness

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

private theorem exists_eq_smul_of_isMulRightInvariant (m μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts m] [m.IsMulRightInvariant] :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ m = c • μ := by
  haveI : Measure.IsHaarMeasure μ.inv :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsMulLeftInvariant := inferInstance
      toIsOpenPosMeasure := inferInstance }
  obtain ⟨c, hc⟩ : ∃ c : NNReal, m.inv = c • μ.inv := ⟨_, Measure.isMulLeftInvariant_eq_smul m.inv μ.inv⟩
  refine ⟨c, ENNReal.coe_ne_top, ?_⟩
  ext s hs
  calc m s = m.inv.inv s := by rw [Measure.inv_inv]
    _ = m.inv s⁻¹ := Measure.inv_apply _ _
    _ = (c • μ.inv) s⁻¹ := by rw [hc]
    _ = c * μ.inv s⁻¹ := Measure.coe_nnreal_smul_apply _ _ _
    _ = c * μ s := by rw [Measure.inv_apply, inv_inv]
    _ = ((c : ℝ≥0∞) • μ) s := by rw [Measure.smul_apply, smul_eq_mul]

private theorem exists_ne_zero_and_eq_smul_of_isMulRightInvariant (m μ : Measure G) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts m] [m.IsMulRightInvariant] (hm : m ≠ 0) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ m = c • μ := by
  obtain ⟨c, hc, h⟩ := exists_eq_smul_of_isMulRightInvariant m μ
  refine ⟨c, ?_, hc, h⟩
  rintro rfl
  exact hm (by rw [h, zero_smul])

end RightInvariantUniqueness

end HaarUniqueness

section BlockIntegrand

private theorem continuous_coe_matrix :
    Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  Units.continuous_val

private theorem continuous_bottomRow_fun :
    Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => fun j : Fin 3 => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j :=
  continuous_pi fun j =>
    show Continuous ((fun r : Fin 3 → AdeleRing (𝓞 ℚ) ℚ => r j) ∘
        ((fun m : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ) => m 2) ∘
          fun g : AdelicGL 3 (𝓞 ℚ) ℚ => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)))) from
      (continuous_apply j).comp ((continuous_apply (2 : Fin 3)).comp continuous_coe_matrix)

attribute [local instance] NumberField.AdelicHaar.glBorel in
private theorem measurable_integrand {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hW : Continuous W)
    {Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ} (hΦ : Continuous Φ) (σ : ℝ) : Measurable (integrand W Φ σ) := by
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  have h1 : Measurable fun g : AdelicGL 3 (𝓞 ℚ) ℚ => (‖W g‖₊ : ℝ≥0∞) :=
    ENNReal.continuous_coe.measurable.comp hW.nnnorm.measurable
  have h1sq : Measurable fun g : AdelicGL 3 (𝓞 ℚ) ℚ => (‖W g‖₊ : ℝ≥0∞) ^ 2 := by
    simpa only [sq] using h1.fun_mul h1
  have h2 : Measurable fun g : AdelicGL 3 (𝓞 ℚ) ℚ =>
      (‖Φ fun j : Fin 3 => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖₊ : ℝ≥0∞) :=
    ENNReal.continuous_coe.measurable.comp (hΦ.comp continuous_bottomRow_fun).nnnorm.measurable
  have h3 : Measurable fun g : AdelicGL 3 (𝓞 ℚ) ℚ =>
      ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ) := by
    refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
    refine Continuous.rpow_const ((NumberField.TateGlobal.continuous_ideleNorm ℚ).comp
      Matrix.GeneralLinearGroup.continuous_det) fun g => Or.inl ?_
    exact (NumberField.TateGlobal.ideleNorm_pos _).ne'
  exact (h1sq.mul h2).mul h3

open scoped Classical in

private theorem continuous_of_mem_pureTensorSet {φ : AdeleRing (𝓞 ℚ) ℚ → ℂ} (hφ : φ ∈ AdelicFourier.pureTensorSet ℚ) :
    Continuous φ := by
  obtain ⟨g, h, hh, -, rfl⟩ := hφ
  exact (g.continuous.comp ((AdelicBox.continuous_ringEquiv_mixedSpace (K := ℚ)).comp continuous_fst)).mul
    (hh.continuous.comp continuous_snd)

private theorem continuous_prod_of_pureTensors {Φc : Fin 3 → AdeleRing (𝓞 ℚ) ℚ → ℂ}
    (hΦc : ∀ i, Φc i ∈ AdelicFourier.pureTensorSet ℚ) :
    Continuous fun x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ => ∏ i, Φc i (x i) :=
  continuous_finsetProd _ fun i _ => (continuous_of_mem_pureTensorSet (hΦc i)).comp (continuous_apply i)

private theorem upperUnipotent3_mul_apply_two {A : Type} [CommRing A] (x y z : A) (N : Matrix (Fin 3) (Fin 3) A)
    (j : Fin 3) : ((upperUnipotent3 x y z : GL (Fin 3) A) * N : Matrix (Fin 3) (Fin 3) A) 2 j = N 2 j := by
  simp [upperUnipotent3_coe, Matrix.mul_apply, Fin.sum_univ_three]

private theorem det_upperUnipotent3 {A : Type} [CommRing A] (x y z : A) :
    Matrix.GeneralLinearGroup.det (upperUnipotent3 x y z : GL (Fin 3) A) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, upperUnipotent3_coe, Units.val_one]
  simp [Matrix.det_fin_three]

private theorem integrand_mul_left {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hW : ∀ n ∈ WhittakerBlock.unipotentSubgroup3, ∀ g, ‖W (n * g)‖ = ‖W g‖) (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ)
    (σ : ℝ) (n : AdelicGL 3 (𝓞 ℚ) ℚ) (hn : n ∈ WhittakerBlock.unipotentSubgroup3) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    integrand W Φ σ (n * g) = integrand W Φ σ g := by
  obtain ⟨x, y, z, rfl⟩ := (WhittakerBlock.mem_unipotentSubgroup3_iff n).1 hn
  have h₁ : ‖W (upperUnipotent3 x y z * g)‖₊ = ‖W g‖₊ := NNReal.coe_injective (hW _ hn g)
  have h₂ : (fun j : Fin 3 => ((upperUnipotent3 x y z * g : AdelicGL 3 (𝓞 ℚ) ℚ) :
      Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j) =
      fun j => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j := by
    funext j
    rw [Units.val_mul]
    exact upperUnipotent3_mul_apply_two x y z _ j
  simp only [integrand, h₁, h₂, map_mul, det_upperUnipotent3, one_mul]

end BlockIntegrand

section WhittakerContinuity

private theorem continuous_integral_of_isCompact_carrier {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace Y] (hY : OpensMeasurableSpace Y) (ν : MeasureTheory.Measure Y)
    (hν : MeasureTheory.IsFiniteMeasure ν) {C : Set Y} (hC : IsCompact C) (hνC : ∀ᵐ y ∂ν, y ∈ C) (F : X → Y → ℂ)
    (hF : Continuous fun p : X × Y => F p.1 p.2) : Continuous fun x => ∫ y, F x y ∂ν := by
  haveI := hY
  haveI := hν
  have hslice : ∀ x, Continuous (F x) := fun x =>
    hF.comp (continuous_const.prodMk continuous_id : Continuous fun y : Y => (x, y))
  have hint : ∀ x, MeasureTheory.Integrable (F x) ν := by
    intro x
    obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn (hslice x).continuousOn
    exact MeasureTheory.Integrable.of_bound (hslice x).aestronglyMeasurable M (hνC.mono fun y hy => hM y hy)
  have hcurry : Continuous (ContinuousMap.curry (⟨fun p : X × Y => F p.1 p.2, hF⟩ : ContinuousMap (X × Y) ℂ)) :=
    (ContinuousMap.curry _).continuous
  rw [continuous_iff_continuousAt]
  intro x₀
  have hunif : TendstoUniformlyOn (fun x y => F x y) (F x₀) (nhds x₀) C :=
    (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1 (hcurry.tendsto x₀)) C hC
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hmpos : (0 : ℝ) < ν.real Set.univ + 1 := add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg one_pos
  have hδ : (0 : ℝ) < ε / (ν.real Set.univ + 1) := div_pos hε hmpos
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hunif _ hδ] with x hx
  show dist (∫ y, F x y ∂ν) (∫ y, F x₀ y ∂ν) < ε
  rw [dist_eq_norm, ← MeasureTheory.integral_sub (hint x) (hint x₀)]
  calc ‖∫ y, (F x y - F x₀ y) ∂ν‖ ≤ ε / (ν.real Set.univ + 1) * ν.real Set.univ :=
        MeasureTheory.norm_integral_le_of_norm_le_const (hνC.mono fun y hy => by
          rw [← dist_eq_norm, dist_comm]; exact (hx y hy).le)
    _ < ε / (ν.real Set.univ + 1) * (ν.real Set.univ + 1) := mul_lt_mul_of_pos_left (lt_add_one _) hδ
    _ = ε := div_mul_cancel₀ ε hmpos.ne'

private theorem continuous_upperUnipotent3_triple {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous fun p : A × A × A => LanglandsTunnell.CubicInduction.upperUnipotent3 p.1 p.2.1 p.2.2 := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [LanglandsTunnell.CubicInduction.upperUnipotent3] <;> fun_prop

private theorem exists_isCompact_ae_mem_productionPins_measure :
    ∃ C : Set (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ), IsCompact C ∧
      (∀ᵐ y ∂(AutomorphicForm.productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (NumberField.AdelicBox.adelicBox ℚ)).ν,
        y ∈ C) := by
  obtain ⟨C, hC, hsub⟩ := NumberField.AdelicBox.exists_isCompact_adelicBox_subset ℚ
  refine ⟨C, hC, ?_⟩
  have h : ∀ᵐ y ∂(AutomorphicForm.productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1)
      (NumberField.AdelicBox.adelicBox ℚ)).ν, y ∈ NumberField.AdelicBox.adelicBox ℚ :=
    MeasureTheory.Measure.ae_smul_measure
      (MeasureTheory.ae_restrict_mem (NumberField.AdelicBox.measurableSet_adelicBox ℚ)) _
  exact h.mono fun y hy => hsub hy

private theorem continuous_whittaker3_productionPins
    (ψ : AddChar (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ℂ) (hψ : Continuous ψ)
    (f : LanglandsTunnell.CubicInduction.AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hf : Continuous f) :
    Continuous (LanglandsTunnell.CubicInduction.whittaker3
      (AutomorphicForm.productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (NumberField.AdelicBox.adelicBox ℚ)) ψ f) := by
  letI : MeasurableSpace (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) :=
    NumberField.AdelicHaar.adeleBorel (NumberField.RingOfIntegers ℚ) ℚ
  have hY : OpensMeasurableSpace (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) :=
    (NumberField.AdelicHaar.borelSpace_adeleBorel (NumberField.RingOfIntegers ℚ) ℚ).opensMeasurable
  set ν : @MeasureTheory.Measure (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)
      (NumberField.AdelicHaar.adeleBorel (NumberField.RingOfIntegers ℚ) ℚ) :=
    (AutomorphicForm.productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (NumberField.AdelicBox.adelicBox ℚ)).ν
  haveI : MeasureTheory.IsProbabilityMeasure ν := NumberField.AdelicBox.isProbabilityMeasure_cond_adelicBox ℚ
  have hν : MeasureTheory.IsFiniteMeasure ν := inferInstance
  obtain ⟨C, hC, hνC⟩ := exists_isCompact_ae_mem_productionPins_measure
  have hn := continuous_upperUnipotent3_triple (A := NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)

  have hF₃ : Continuous fun p : (LanglandsTunnell.CubicInduction.AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ ×
      NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ×
      NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ =>
      ∫ z, f (LanglandsTunnell.CubicInduction.upperUnipotent3 p.1.2 p.2 z * p.1.1) * ψ (-(p.1.2 + p.2)) ∂ν := by
    refine continuous_integral_of_isCompact_carrier hY ν hν hC hνC _ ?_

    have hq : Continuous fun pz : ((LanglandsTunnell.CubicInduction.AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ => (pz.1.1.2, pz.1.2, pz.2) :=
      (continuous_snd.comp (continuous_fst.comp continuous_fst)).prodMk
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
    have hU : Continuous fun pz : ((LanglandsTunnell.CubicInduction.AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ =>
        LanglandsTunnell.CubicInduction.upperUnipotent3 pz.1.1.2 pz.1.2 pz.2 := hn.comp hq
    have hg : Continuous fun pz : ((LanglandsTunnell.CubicInduction.AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ => pz.1.1.1 :=
      continuous_fst.comp (continuous_fst.comp continuous_fst)
    have hs : Continuous fun pz : ((LanglandsTunnell.CubicInduction.AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ×
        NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ => -(pz.1.1.2 + pz.1.2) :=
      ((continuous_snd.comp (continuous_fst.comp continuous_fst)).add (continuous_snd.comp continuous_fst)).neg
    exact (hf.comp (hU.mul hg)).mul (hψ.comp hs)

  have hF₂ : Continuous fun gx : LanglandsTunnell.CubicInduction.AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ ×
      NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ =>
      ∫ y, ∫ z, f (LanglandsTunnell.CubicInduction.upperUnipotent3 gx.2 y z * gx.1) * ψ (-(gx.2 + y)) ∂ν ∂ν := by
    refine continuous_integral_of_isCompact_carrier hY ν hν hC hνC _ ?_
    exact hF₃

  have h1 : Continuous fun g : LanglandsTunnell.CubicInduction.AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ =>
      ∫ x, ∫ y, ∫ z, f (LanglandsTunnell.CubicInduction.upperUnipotent3 x y z * g) * ψ (-(x + y)) ∂ν ∂ν ∂ν := by
    refine continuous_integral_of_isCompact_carrier hY ν hν hC hνC _ ?_
    exact hF₂
  exact h1

end WhittakerContinuity

section UniquenessPrinciple

section UniquenessHead

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open Filter Topology Set

open scoped NNReal Classical

private theorem exists_smooth_approx {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U) :
    ∃ g : ℕ → E → ℝ, (∀ n, ContDiff ℝ (⊤ : ℕ∞) (g n)) ∧ (∀ n, HasCompactSupport (g n)) ∧
      (∀ n t, 0 ≤ g n t) ∧ (∀ n t, g n t ≤ 1) ∧ (∀ n t, t ∉ U → g n t = 0) ∧
      ∀ t, Tendsto (fun n => g n t) atTop (𝓝 (U.indicator (fun _ => (1 : ℝ)) t)) := by
  obtain ⟨f, hf_supp, hf_smooth, hf_range⟩ := hU.exists_contDiff_support_eq (n := ⊤)
  have hK : IsCompact (closure U) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hUb.closure
  have hf_zero : ∀ t, t ∉ U → f t = 0 := by
    intro t ht
    by_contra h
    have hmem : t ∈ Function.support f := Function.mem_support.mpr h
    rw [hf_supp] at hmem
    exact ht hmem
  have hf_nonneg : ∀ t, 0 ≤ f t := fun t => (hf_range ⟨t, rfl⟩).1
  refine ⟨fun n t => Real.smoothTransition ((n : ℝ) * f t), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact Real.smoothTransition.contDiff.comp (contDiff_const.mul hf_smooth)
  · intro n
    refine HasCompactSupport.intro hK fun t ht => ?_
    have ht' : t ∉ U := fun h => ht (subset_closure h)
    simp only [hf_zero t ht', mul_zero, Real.smoothTransition.zero]
  · intro n t
    exact Real.smoothTransition.nonneg _
  · intro n t
    exact Real.smoothTransition.le_one _
  · intro n t ht
    simp only [hf_zero t ht, mul_zero, Real.smoothTransition.zero]
  · intro t
    by_cases ht : t ∈ U
    · have hmem : t ∈ Function.support f := by
        rw [hf_supp]
        exact ht
      have hpos : 0 < f t := lt_of_le_of_ne (hf_nonneg t) (Function.mem_support.mp hmem).symm
      rw [indicator_of_mem ht]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈(f t)⁻¹⌉₊] with n hn
      refine (Real.smoothTransition.one_of_one_le ?_).symm
      have h1 : (f t)⁻¹ ≤ (n : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr hn)
      calc (1 : ℝ) = (f t)⁻¹ * f t := (inv_mul_cancel₀ hpos.ne').symm
        _ ≤ (n : ℝ) * f t := mul_le_mul_of_nonneg_right h1 hpos.le
    · rw [indicator_of_notMem ht]
      simp only [hf_zero t ht, mul_zero, Real.smoothTransition.zero]
      exact tendsto_const_nhds

private theorem exists_smooth_dominant {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {U : Set E} (hUb : Bornology.IsBounded U) :
    ∃ G : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) G ∧ HasCompactSupport G ∧ (∀ t, 0 ≤ G t) ∧ (∀ t, G t ≤ 1) ∧
      ∀ t ∈ U, G t = 1 := by
  obtain ⟨r, hr⟩ := hUb.subset_closedBall (0 : E)
  let b : ContDiffBump (0 : E) :=
    { rIn := max r 1
      rOut := max r 1 + 1
      rIn_pos := lt_of_lt_of_le one_pos (le_max_right r 1)
      rIn_lt_rOut := lt_add_one _ }
  refine ⟨b, b.contDiff, b.hasCompactSupport, fun t => b.nonneg, fun t => b.le_one, fun t ht => ?_⟩
  exact b.one_of_mem_closedBall (Metric.closedBall_subset_closedBall (le_max_left r 1) (hr ht))

private def smoothFamily {A E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (r : A → E) :
    Set (A → ℝ≥0) :=
  {φ | ∃ g : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧ (∀ t, 0 ≤ g t) ∧ (∀ t, g t ≤ 1) ∧
    φ = fun a => Real.toNNReal (g (r a))}

private theorem smoothFamily_approx {A E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (r : A → E) {c : Set A}
    (hc : c ∈ Set.preimage r '' {U : Set E | IsOpen U ∧ Bornology.IsBounded U}) :
    ∃ Φ ∈ smoothFamily r, ∃ φ : ℕ → A → ℝ≥0, (∀ n, φ n ∈ smoothFamily r) ∧
      (∀ n a, φ n a ≤ Φ a) ∧
      ∀ a, Tendsto (fun n => φ n a) atTop (𝓝 (c.indicator (fun _ => (1 : ℝ≥0)) a)) := by
  obtain ⟨U, ⟨hU, hUb⟩, rfl⟩ := hc
  obtain ⟨G, hG_smooth, hG_supp, hG_nonneg, hG_le, hG_one⟩ := exists_smooth_dominant hUb
  obtain ⟨g, hg_smooth, hg_supp, hg_nonneg, hg_le, hg_zero, hg_lim⟩ := exists_smooth_approx hU hUb
  refine ⟨fun a => Real.toNNReal (G (r a)), ⟨G, hG_smooth, hG_supp, hG_nonneg, hG_le, rfl⟩,
    fun n a => Real.toNNReal (g n (r a)),
    fun n => ⟨g n, hg_smooth n, hg_supp n, hg_nonneg n, hg_le n, rfl⟩, ?_, ?_⟩
  · intro n a
    apply Real.toNNReal_le_toNNReal
    by_cases ha : r a ∈ U
    · rw [hG_one _ ha]
      exact hg_le n _
    · rw [hg_zero n _ ha]
      exact hG_nonneg _
  · intro a
    have h := (continuous_real_toNNReal.tendsto _).comp (hg_lim (r a))
    have heq : Real.toNNReal (U.indicator (fun _ => (1 : ℝ)) (r a)) =
        (r ⁻¹' U).indicator (fun _ => (1 : ℝ≥0)) a := by
      by_cases ha : r a ∈ U
      · have ha' : a ∈ r ⁻¹' U := ha
        simp only [indicator_of_mem ha, indicator_of_mem ha', Real.toNNReal_one]
      · have ha' : a ∉ r ⁻¹' U := ha
        simp only [indicator_of_notMem ha, indicator_of_notMem ha', Real.toNNReal_zero]
    rw [← heq]
    exact h

private theorem isTopologicalBasis_compactOpen {X : Type} [TopologicalSpace X]
    (hnhds : ∀ x : X, ∀ U ∈ 𝓝 x, ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ U)
    (hcpt : ∀ x : X, ∃ W : Set X, IsCompact W ∧ IsOpen W ∧ x ∈ W) :
    TopologicalSpace.IsTopologicalBasis {V : Set X | IsCompact V ∧ IsOpen V} := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds (fun V hV => hV.2) ?_
  intro x U hxU hU
  obtain ⟨W, hWc, hWo, hxW⟩ := hcpt x
  obtain ⟨V, hV, hxV, hVU⟩ := hnhds x (U ∩ W) ((hU.inter hWo).mem_nhds ⟨hxU, hxW⟩)
  refine ⟨V, ⟨?_, hV.isOpen⟩, hxV, fun y hy => (hVU hy).1⟩
  exact hWc.of_isClosed_subset hV.isClosed fun y hy => (hVU hy).2

private theorem exists_compactOpen_exhaustion {X : Type} [TopologicalSpace X]
    [SigmaCompactSpace X] (hcpt : ∀ x : X, ∃ W : Set X, IsCompact W ∧ IsOpen W ∧ x ∈ W) :
    ∃ V : ℕ → Set X, (∀ n, IsCompact (V n) ∧ IsOpen (V n)) ∧ Monotone V ∧ ⋃ n, V n = univ := by
  have key : ∀ K : Set X, IsCompact K → ∃ W : Set X, IsCompact W ∧ IsOpen W ∧ K ⊆ W := by
    intro K hK
    choose W hWc hWo hxW using hcpt
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover W hWo fun x _ => mem_iUnion.2 ⟨x, hxW x⟩
    exact ⟨⋃ x ∈ t, W x, t.isCompact_biUnion fun x _ => hWc x,
      isOpen_iUnion fun x => isOpen_iUnion fun _ => hWo x, ht⟩
  choose W hW using fun n => key (compactCovering X n) (isCompact_compactCovering X n)
  refine ⟨fun n => ⋃ m ∈ Finset.range (n + 1), W m, fun n => ⟨?_, ?_⟩, ?_, ?_⟩
  · exact (Finset.range (n + 1)).isCompact_biUnion fun m _ => (hW m).1
  · exact isOpen_iUnion fun m => isOpen_iUnion fun _ => (hW m).2.1
  · intro a b hab x hx
    simp only [mem_iUnion, Finset.mem_range] at hx ⊢
    obtain ⟨m, hm, hxm⟩ := hx
    exact ⟨m, by omega, hxm⟩
  · refine eq_univ_of_forall fun x => ?_
    have hx : x ∈ ⋃ n, compactCovering X n := by
      rw [iUnion_compactCovering]
      exact mem_univ x
    obtain ⟨n, hn⟩ := mem_iUnion.1 hx
    simp only [mem_iUnion, Finset.mem_range]
    exact ⟨n, n, Nat.lt_succ_self n, (hW n).2.2 hn⟩

private theorem exists_compactOpen_mem {X : Type} [TopologicalSpace X] [AddGroup X]
    [IsTopologicalAddGroup X] {O : Set X} (hOc : IsCompact O) (hOo : IsOpen O)
    (h0 : (0 : X) ∈ O) (x : X) : ∃ W : Set X, IsCompact W ∧ IsOpen W ∧ x ∈ W := by
  refine ⟨(Homeomorph.subRight x) ⁻¹' O, (Homeomorph.subRight x).isCompact_preimage.2 hOc,
    hOo.preimage (Homeomorph.subRight x).continuous, ?_⟩
  show x - x ∈ O
  rwa [sub_self]

private theorem valued_exists_clopen {K Γ₀ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] (x : K) (U : Set K) (hU : U ∈ 𝓝 x) :
    ∃ V : Set K, IsClopen V ∧ x ∈ V ∧ V ⊆ U := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 hU
  refine ⟨_, ?_, ?_, hγ⟩
  · exact (Valued.isClopen_ball K γ.1).preimage (continuous_sub_right x)
  · simp

private theorem borel_eq_generateFrom_preimage {A E : Type} [TopologicalSpace A] [PolishSpace A]
    [mA : MeasurableSpace A] [BorelSpace A] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [mE : MeasurableSpace E] [BorelSpace E] {r : A → E}
    (hr : Continuous r) (hinj : Function.Injective r) :
    mA = MeasurableSpace.generateFrom
      (Set.preimage r '' {U : Set E | IsOpen U ∧ Bornology.IsBounded U}) := by
  have hemb : MeasurableEmbedding r := hr.measurableEmbedding hinj
  have hE : mE = MeasurableSpace.generateFrom {U : Set E | IsOpen U ∧ Bornology.IsBounded U} := by
    apply le_antisymm
    · rw [BorelSpace.measurable_eq (α := E)]
      show MeasurableSpace.generateFrom {U : Set E | IsOpen U} ≤ _
      refine MeasurableSpace.generateFrom_le fun U hU => ?_
      have hdecomp : U = ⋃ n : ℕ, U ∩ Metric.ball (0 : E) n := by
        rw [← inter_iUnion, Metric.iUnion_ball_nat, inter_univ]
      rw [hdecomp]
      refine MeasurableSet.iUnion fun n => MeasurableSpace.measurableSet_generateFrom ?_
      exact ⟨hU.inter Metric.isOpen_ball, Metric.isBounded_ball.subset inter_subset_right⟩
    · exact MeasurableSpace.generateFrom_le fun U hU => hU.1.measurableSet
  rw [← hemb.comap_eq, hE, MeasurableSpace.comap_generateFrom]

private theorem isLocallyConstant_indicator {X : Type} [TopologicalSpace X] {W : Set X} (hW : IsClopen W)
    (c : ℂ) : IsLocallyConstant (W.indicator fun _ => c) := by
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  by_cases hx : x ∈ W
  · exact ⟨W, hW.isOpen, hx, fun x' hx' => by rw [indicator_of_mem hx', indicator_of_mem hx]⟩
  · exact ⟨Wᶜ, hW.isClosed.isOpen_compl, hx,
      fun x' hx' => by rw [indicator_of_notMem hx', indicator_of_notMem hx]⟩

private theorem hasCompactSupport_indicator {X : Type} [TopologicalSpace X] [T2Space X] {W : Set X} (hW : IsCompact W)
    (c : ℂ) : HasCompactSupport (W.indicator fun _ => c) :=
  HasCompactSupport.intro hW fun _ hx => indicator_of_notMem hx _

section Determination

variable {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] {A : Type} [mA : MeasurableSpace A]
  {Q : ι₂ → Type} [mQ : ∀ k, MeasurableSpace (Q k)]

private def boxTest (φ : ι₁ → A → ℝ≥0) (V : ∀ k, Set (Q k)) (y : (ι₁ → A) × ∀ k, Q k) :
    ℝ≥0∞ :=
  (((∏ i, φ i (y.1 i)) * ∏ k, (V k).indicator (fun _ => (1 : ℝ≥0)) (y.2 k) : ℝ≥0) : ℝ≥0∞)

omit mA mQ in
private theorem boxTest_mono {φ ψ : ι₁ → A → ℝ≥0} (h : ∀ i a, φ i a ≤ ψ i a)
    (V : ∀ k, Set (Q k)) (y : (ι₁ → A) × ∀ k, Q k) : boxTest φ V y ≤ boxTest ψ V y := by
  unfold boxTest
  exact ENNReal.coe_le_coe.2 (mul_le_mul_left (Finset.prod_le_prod' fun i _ => h i _) _)

private theorem boxTest_measurable {φ : ι₁ → A → ℝ≥0} (hφ : ∀ i, Measurable (φ i))
    {V : ∀ k, Set (Q k)} (hV : ∀ k, MeasurableSet (V k)) : Measurable (boxTest φ V) := by
  unfold boxTest
  refine ENNReal.continuous_coe.measurable.comp (Measurable.mul ?_ ?_)
  · exact Finset.measurable_prod _ fun i _ =>
      (hφ i).comp ((measurable_pi_apply i).comp measurable_fst)
  · exact Finset.measurable_prod _ fun k _ =>
      (measurable_const.indicator (hV k)).comp ((measurable_pi_apply k).comp measurable_snd)

omit mA mQ in
private theorem boxTest_le_indicator {φ : ι₁ → A → ℝ≥0} {K : ι₁ → Set A} (hφ₁ : ∀ i a, φ i a ≤ 1)
    (hφK : ∀ i a, a ∉ K i → φ i a = 0) (V : ∀ k, Set (Q k)) (y : (ι₁ → A) × ∀ k, Q k) :
    boxTest φ V y ≤ ((univ.pi K) ×ˢ (univ.pi V)).indicator (fun _ => (1 : ℝ≥0∞)) y := by
  by_cases hy : y ∈ (univ.pi K) ×ˢ (univ.pi V)
  · rw [indicator_of_mem hy]
    unfold boxTest
    refine ENNReal.coe_le_one_iff.2 (mul_le_one' (Finset.prod_le_one' fun i _ => hφ₁ i _)
      (Finset.prod_le_one' fun k _ => ?_))
    by_cases hk : y.2 k ∈ V k <;> simp [hk]
  · rw [indicator_of_notMem hy]
    unfold boxTest
    rcases not_and_or.1 (mem_prod.not.1 hy) with hy1 | hy2
    · obtain ⟨i, hi⟩ := not_forall.1 (mem_univ_pi.not.1 hy1)
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (hφK i _ hi), zero_mul, ENNReal.coe_zero]
    · obtain ⟨k, hk⟩ := not_forall.1 (mem_univ_pi.not.1 hy2)
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (indicator_of_notMem hk _), mul_zero, ENNReal.coe_zero]

private theorem lintegral_boxTest_le (μ : Measure ((ι₁ → A) × ∀ k, Q k)) {φ : ι₁ → A → ℝ≥0}
    {K : ι₁ → Set A} (hφ₁ : ∀ i a, φ i a ≤ 1) (hφK : ∀ i a, a ∉ K i → φ i a = 0)
    (hK : ∀ i, MeasurableSet (K i)) {V : ∀ k, Set (Q k)} (hV : ∀ k, MeasurableSet (V k)) :
    ∫⁻ y, boxTest φ V y ∂μ ≤ μ ((univ.pi K) ×ˢ (univ.pi V)) := by
  calc ∫⁻ y, boxTest φ V y ∂μ
      ≤ ∫⁻ y, ((univ.pi K) ×ˢ (univ.pi V)).indicator (fun _ => (1 : ℝ≥0∞)) y ∂μ :=
        lintegral_mono fun y => boxTest_le_indicator hφ₁ hφK V y
    _ = μ ((univ.pi K) ×ˢ (univ.pi V)) := by
        rw [lintegral_indicator_const ((MeasurableSet.univ_pi hK).prod (MeasurableSet.univ_pi hV)) 1, one_mul]

omit mA mQ in

private theorem indicator_box_eq (c : ι₁ → Set A) (V : ∀ k, Set (Q k))
    (y : (ι₁ → A) × ∀ k, Q k) :
    ((univ.pi c) ×ˢ (univ.pi V)).indicator (fun _ => (1 : ℝ≥0∞)) y =
      boxTest (fun i => (c i).indicator fun _ => (1 : ℝ≥0)) V y := by
  unfold boxTest
  by_cases hy : y ∈ (univ.pi c) ×ˢ (univ.pi V)
  · rw [indicator_of_mem hy]
    obtain ⟨hy1, hy2⟩ := hy
    rw [Finset.prod_eq_one fun i _ => indicator_of_mem (hy1 i (mem_univ i)) _,
      Finset.prod_eq_one fun k _ => indicator_of_mem (hy2 k (mem_univ k)) _, one_mul,
      ENNReal.coe_one]
  · rw [indicator_of_notMem hy]
    rw [mem_prod, mem_univ_pi, mem_univ_pi] at hy
    push Not at hy
    by_cases hy1 : ∀ i, y.1 i ∈ c i
    · obtain ⟨k, hk⟩ := hy hy1
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (indicator_of_notMem hk _), mul_zero,
        ENNReal.coe_zero]
    · push Not at hy1
      obtain ⟨i, hi⟩ := hy1
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _), zero_mul,
        ENNReal.coe_zero]

private theorem indicator_eq_indicator_one_mul {Y : Type} (s : Set Y) (u : Y → ℝ≥0∞) (y : Y) :
    s.indicator u y = s.indicator (fun _ => (1 : ℝ≥0∞)) y * u y := by
  by_cases hy : y ∈ s
  · rw [indicator_of_mem hy, indicator_of_mem hy, one_mul]
  · rw [indicator_of_notMem hy, indicator_of_notMem hy, zero_mul]

private theorem tendsto_lintegral_boxTest (μ : Measure ((ι₁ → A) × ∀ k, Q k)) {v : _ → ℝ≥0∞}
    (hv : Measurable v) {c : ι₁ → Set A} {Φ : ι₁ → A → ℝ≥0} {φ : ι₁ → ℕ → A → ℝ≥0}
    (hΦ : ∀ i, Measurable (Φ i)) (hφ : ∀ i n, Measurable (φ i n))
    (hle : ∀ i n a, φ i n a ≤ Φ i a)
    (hlim : ∀ i a, Tendsto (fun n => φ i n a) atTop (𝓝 ((c i).indicator (fun _ => (1 : ℝ≥0)) a)))
    {V : ∀ k, Set (Q k)} (hV : ∀ k, MeasurableSet (V k))
    (hfin : ∫⁻ y, boxTest Φ V y * v y ∂μ ≠ ∞) :
    Tendsto (fun n => ∫⁻ y, boxTest (fun i => φ i n) V y * v y ∂μ) atTop
      (𝓝 (∫⁻ y, boxTest (fun i => (c i).indicator fun _ => (1 : ℝ≥0)) V y * v y ∂μ)) := by
  have hind_le : ∀ i a, (c i).indicator (fun _ => (1 : ℝ≥0)) a ≤ Φ i a := fun i a =>
    le_of_tendsto' (hlim i a) fun n => hle i n a
  refine tendsto_lintegral_of_dominated_convergence (fun y => boxTest Φ V y * v y)
    (fun n => (boxTest_measurable (fun i => hφ i n) hV).mul hv) ?_ hfin ?_
  · intro n
    exact Eventually.of_forall fun y =>
      mul_le_mul_left (boxTest_mono (fun i a => hle i n a) V y) _
  · filter_upwards [ae_lt_top ((boxTest_measurable hΦ hV).mul hv) hfin] with y hy
    by_cases hΦy : boxTest Φ V y = 0
    · have hzero : ∀ n, boxTest (fun i => φ i n) V y = 0 := fun n =>
        le_antisymm ((boxTest_mono (fun i a => hle i n a) V y).trans hΦy.le) zero_le
      have hzero' : boxTest (fun i => (c i).indicator fun _ => (1 : ℝ≥0)) V y = 0 :=
        le_antisymm ((boxTest_mono hind_le V y).trans hΦy.le) zero_le
      simp only [hzero, hzero', zero_mul]
      exact tendsto_const_nhds
    · have hvy : v y ≠ ∞ := (ENNReal.lt_top_of_mul_ne_top_right hy.ne hΦy).ne
      refine ENNReal.Tendsto.mul_const ?_ (Or.inr hvy)
      unfold boxTest
      refine (ENNReal.continuous_coe.tendsto _).comp ?_
      exact (tendsto_finsetProd _ fun i _ => hlim i (y.1 i)).mul tendsto_const_nhds

private theorem ae_eq_of_boxTests (μ : Measure ((ι₁ → A) × ∀ k, Q k)) [SigmaFinite μ]
    {u w : _ → ℝ≥0∞} (hu : Measurable u) (hw : Measurable w)
    (CA : Set (Set A)) (hCA : MeasurableSpace.generateFrom CA = mA) (hCAπ : IsPiSystem CA)
    (sA : ℕ → Set A) (hsA : ∀ n, sA n ∈ CA) (hsA_mono : Monotone sA) (hsA_univ : ⋃ n, sA n = univ)
    (CQ : ∀ k, Set (Set (Q k))) (hCQ : ∀ k, MeasurableSpace.generateFrom (CQ k) = mQ k)
    (hCQπ : ∀ k, IsPiSystem (CQ k)) (sQ : ∀ k, ℕ → Set (Q k)) (hsQ : ∀ k n, sQ k n ∈ CQ k)
    (hsQ_mono : ∀ k, Monotone (sQ k)) (hsQ_univ : ∀ k, ⋃ n, sQ k n = univ)
    (𝒜 : Set (A → ℝ≥0)) (h𝒜m : ∀ φ ∈ 𝒜, Measurable φ)
    (h𝒜 : ∀ c ∈ CA, ∃ Φ ∈ 𝒜, ∃ φ : ℕ → A → ℝ≥0, (∀ n, φ n ∈ 𝒜) ∧ (∀ n a, φ n a ≤ Φ a) ∧
      ∀ a, Tendsto (fun n => φ n a) atTop (𝓝 (c.indicator (fun _ => (1 : ℝ≥0)) a)))
    (hid : ∀ (φ : ι₁ → A → ℝ≥0) (V : ∀ k, Set (Q k)), (∀ i, φ i ∈ 𝒜) → (∀ k, V k ∈ CQ k) →
      ∫⁻ y, boxTest φ V y * u y ∂μ = ∫⁻ y, boxTest φ V y * w y ∂μ)
    (hfin : ∀ (φ : ι₁ → A → ℝ≥0) (V : ∀ k, Set (Q k)), (∀ i, φ i ∈ 𝒜) → (∀ k, V k ∈ CQ k) →
      ∫⁻ y, boxTest φ V y * w y ∂μ ≠ ∞) :
    u =ᵐ[μ] w := by
  have hCA_meas : ∀ c ∈ CA, MeasurableSet c := fun c hc =>
    hCA ▸ MeasurableSpace.measurableSet_generateFrom hc
  have hCQ_meas : ∀ k, ∀ V ∈ CQ k, MeasurableSet V := fun k V hV =>
    hCQ k ▸ MeasurableSpace.measurableSet_generateFrom hV
  have hCA_span : IsCountablySpanning CA := ⟨sA, hsA, hsA_univ⟩
  have hCQ_span : ∀ k, IsCountablySpanning (CQ k) := fun k => ⟨sQ k, hsQ k, hsQ_univ k⟩

  have hgen : (by infer_instance : MeasurableSpace ((ι₁ → A) × ∀ k, Q k)) =
      MeasurableSpace.generateFrom
        (image2 (· ×ˢ ·) (univ.pi '' univ.pi fun _ : ι₁ => CA) (univ.pi '' univ.pi CQ)) :=
    (generateFrom_eq_prod
      (generateFrom_eq_pi (fun _ => hCA) fun _ => hCA_span)
      (generateFrom_eq_pi hCQ hCQ_span)
      (IsCountablySpanning.pi fun _ => hCA_span) (IsCountablySpanning.pi hCQ_span)).symm
  have hπ : IsPiSystem
      (image2 (· ×ˢ ·) (univ.pi '' univ.pi fun _ : ι₁ => CA) (univ.pi '' univ.pi CQ)) :=
    (IsPiSystem.pi fun _ => hCAπ).prod (IsPiSystem.pi hCQπ)
  have hbox_mem : ∀ (c : ι₁ → Set A) (V : ∀ k, Set (Q k)), (∀ i, c i ∈ CA) →
      (∀ k, V k ∈ CQ k) → (univ.pi c) ×ˢ (univ.pi V) ∈
        image2 (· ×ˢ ·) (univ.pi '' univ.pi fun _ : ι₁ => CA) (univ.pi '' univ.pi CQ) :=
    fun c V hc hV => mem_image2_of_mem ⟨c, fun i _ => hc i, rfl⟩ ⟨V, fun k _ => hV k, rfl⟩
  have hbox_meas : ∀ (c : ι₁ → Set A) (V : ∀ k, Set (Q k)), (∀ i, c i ∈ CA) →
      (∀ k, V k ∈ CQ k) → MeasurableSet ((univ.pi c) ×ˢ (univ.pi V)) := fun c V hc hV =>
    (MeasurableSet.univ_pi fun i => hCA_meas _ (hc i)).prod
      (MeasurableSet.univ_pi fun k => hCQ_meas k _ (hV k))

  have hwith : ∀ (v : _ → ℝ≥0∞) (c : ι₁ → Set A) (V : ∀ k, Set (Q k)), (∀ i, c i ∈ CA) →
      (∀ k, V k ∈ CQ k) → μ.withDensity v ((univ.pi c) ×ˢ (univ.pi V)) =
        ∫⁻ y, boxTest (fun i => (c i).indicator fun _ => (1 : ℝ≥0)) V y * v y ∂μ := by
    intro v c V hc hV
    rw [withDensity_apply _ (hbox_meas c V hc hV), ← lintegral_indicator (hbox_meas c V hc hV)]
    refine lintegral_congr fun y => ?_
    rw [indicator_eq_indicator_one_mul, indicator_box_eq]

  have hagree : ∀ (c : ι₁ → Set A) (V : ∀ k, Set (Q k)), (∀ i, c i ∈ CA) → (∀ k, V k ∈ CQ k) →
      μ.withDensity u ((univ.pi c) ×ˢ (univ.pi V)) =
        μ.withDensity w ((univ.pi c) ×ˢ (univ.pi V)) := by
    intro c V hc hV
    choose Φ hΦ φ hφ hle hlim using fun i => h𝒜 (c i) (hc i)
    rw [hwith u c V hc hV, hwith w c V hc hV]
    have hΦm : ∀ i, Measurable (Φ i) := fun i => h𝒜m _ (hΦ i)
    have hφm : ∀ i n, Measurable (φ i n) := fun i n => h𝒜m _ (hφ i n)
    have hVm : ∀ k, MeasurableSet (V k) := fun k => hCQ_meas k _ (hV k)
    have hfinw : ∫⁻ y, boxTest Φ V y * w y ∂μ ≠ ∞ := hfin Φ V hΦ hV
    have hfinu : ∫⁻ y, boxTest Φ V y * u y ∂μ ≠ ∞ := by
      rw [hid Φ V hΦ hV]
      exact hfinw
    have h1 := (tendsto_lintegral_boxTest μ hu hΦm hφm hle hlim hVm hfinu).congr
      fun n => hid _ V (fun i => hφ i n) hV
    have h2 := tendsto_lintegral_boxTest μ hw hΦm hφm hle hlim hVm hfinw
    exact tendsto_nhds_unique h1 h2

  have hfin_box : ∀ n,
      μ.withDensity u ((univ.pi fun _ : ι₁ => sA n) ×ˢ (univ.pi fun k => sQ k n)) ≠ ∞ := by
    intro n
    rw [hagree _ _ (fun _ => hsA n) (fun k => hsQ k n),
      hwith w _ _ (fun _ => hsA n) (fun k => hsQ k n)]
    obtain ⟨Φ, hΦ, φ, -, hle, hlim⟩ := h𝒜 (sA n) (hsA n)
    have hind_le : ∀ a, (sA n).indicator (fun _ => (1 : ℝ≥0)) a ≤ Φ a := fun a =>
      le_of_tendsto' (hlim a) fun m => hle m a
    refine ne_top_of_le_ne_top
      (hfin (fun _ => Φ) (fun k => sQ k n) (fun _ => hΦ) fun k => hsQ k n) ?_
    exact lintegral_mono fun y => mul_le_mul_left (boxTest_mono (fun _ a => hind_le a) _ y) _

  have hcover : ⋃ n, (univ.pi fun _ : ι₁ => sA n) ×ˢ (univ.pi fun k => sQ k n) = univ := by
    refine eq_univ_of_forall fun y => ?_
    have h1 : ∀ i, ∀ᶠ n in atTop, y.1 i ∈ sA n := by
      intro i
      have hmem : y.1 i ∈ ⋃ n, sA n := by
        rw [hsA_univ]
        exact mem_univ _
      obtain ⟨n, hn⟩ := mem_iUnion.1 hmem
      exact eventually_atTop.2 ⟨n, fun m hm => hsA_mono hm hn⟩
    have h2 : ∀ k, ∀ᶠ n in atTop, y.2 k ∈ sQ k n := by
      intro k
      have hmem : y.2 k ∈ ⋃ n, sQ k n := by
        rw [hsQ_univ k]
        exact mem_univ _
      obtain ⟨n, hn⟩ := mem_iUnion.1 hmem
      exact eventually_atTop.2 ⟨n, fun m hm => hsQ_mono k hm hn⟩
    obtain ⟨n, hn1, hn2⟩ := ((eventually_all.2 h1).and (eventually_all.2 h2)).exists
    exact mem_iUnion.2 ⟨n, fun i _ => hn1 i, fun k _ => hn2 k⟩

  have hmeas_eq : μ.withDensity u = μ.withDensity w := by
    refine Measure.ext_of_generateFrom_of_iUnion _
      (fun n => (univ.pi fun _ : ι₁ => sA n) ×ˢ (univ.pi fun k => sQ k n)) hgen hπ hcover
      (fun n => hbox_mem _ _ (fun _ => hsA n) fun k => hsQ k n) hfin_box ?_
    rintro _ ⟨_, ⟨c, hc, rfl⟩, _, ⟨V, hV, rfl⟩, rfl⟩
    exact hagree c V (fun i => hc i (mem_univ i)) fun k => hV k (mem_univ k)
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite hu hw fun s hs _ => ?_
  rw [← withDensity_apply _ hs, ← withDensity_apply _ hs, hmeas_eq]

end Determination

private def archCoord : InfiniteAdeleRing ℚ → mixedEmbedding.mixedSpace ℚ :=
  InfiniteAdeleRing.ringEquiv_mixedSpace ℚ

private theorem archCoord_injective : Function.Injective archCoord :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).injective

private abbrev archBorel : MeasurableSpace (InfiniteAdeleRing ℚ) := borel _

attribute [local instance] archBorel

private theorem archBorelSpace : BorelSpace (InfiniteAdeleRing ℚ) := ⟨rfl⟩

attribute [local instance] archBorelSpace

private theorem archSecondCountable [∀ w : InfinitePlace ℚ, ProperSpace w.Completion] :
    SecondCountableTopology (InfiniteAdeleRing ℚ) :=
  inferInstanceAs (SecondCountableTopology ((w : InfinitePlace ℚ) → w.Completion))

private theorem archPolish [∀ w : InfinitePlace ℚ, ProperSpace w.Completion] :
    PolishSpace (InfiniteAdeleRing ℚ) :=
  inferInstanceAs (PolishSpace ((w : InfinitePlace ℚ) → w.Completion))

private theorem isCompact_preimage_archCoord [∀ w : InfinitePlace ℚ, ProperSpace w.Completion]
    (hcont : Continuous archCoord) {C : Set (mixedEmbedding.mixedSpace ℚ)} (hC : IsCompact C) :
    IsCompact (archCoord ⁻¹' C) := by
  obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall (0 : mixedEmbedding.mixedSpace ℚ)
  have hsub : archCoord ⁻¹' C ⊆
      (univ.pi fun w : InfinitePlace ℚ => Metric.closedBall (0 : w.Completion) R : Set (InfiniteAdeleRing ℚ)) := by
    intro x hx
    have hxR : ‖archCoord x‖ ≤ R := mem_closedBall_zero_iff.1 (hR hx)
    refine mem_univ_pi.2 fun w => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    rcases w.isReal_or_isComplex with hw | hw
    · have h1 : ‖(archCoord x).1 ⟨w, hw⟩‖ ≤ ‖(archCoord x).1‖ := norm_le_pi_norm _ _
      have h2 : ‖(archCoord x).1‖ ≤ ‖archCoord x‖ := norm_fst_le _
      have h3 : ‖(archCoord x).1 ⟨w, hw⟩‖ = ‖x w‖ := by
        have h := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).dist_eq (x w) 0
        rw [map_zero, dist_zero_right, dist_zero_right] at h
        exact h
      rw [← h3]
      exact h1.trans (h2.trans hxR)
    · have h1 : ‖(archCoord x).2 ⟨w, hw⟩‖ ≤ ‖(archCoord x).2‖ := norm_le_pi_norm _ _
      have h2 : ‖(archCoord x).2‖ ≤ ‖archCoord x‖ := norm_snd_le _
      have h3 : ‖(archCoord x).2 ⟨w, hw⟩‖ = ‖x w‖ := by
        have h := (InfinitePlace.Completion.isometry_extensionEmbedding w).dist_eq (x w) 0
        rw [map_zero, dist_zero_right, dist_zero_right] at h
        exact h
      rw [← h3]
      exact h1.trans (h2.trans hxR)
  have hcpt : IsCompact
      (univ.pi fun w : InfinitePlace ℚ => Metric.closedBall (0 : w.Completion) R : Set (InfiniteAdeleRing ℚ)) :=
    isCompact_univ_pi fun w => isCompact_closedBall (0 : w.Completion) R
  exact hcpt.of_isClosed_subset (hC.isClosed.preimage hcont) hsub

private def archGenerators : Set (Set (InfiniteAdeleRing ℚ)) :=
  Set.preimage archCoord '' {U : Set (mixedEmbedding.mixedSpace ℚ) | IsOpen U ∧ Bornology.IsBounded U}

private theorem archGenerate [∀ w : InfinitePlace ℚ, ProperSpace w.Completion] (hcont : Continuous archCoord) :
    MeasurableSpace.generateFrom archGenerators = archBorel := by
  haveI := archPolish
  exact (borel_eq_generateFrom_preimage hcont archCoord_injective).symm

private theorem archGenerators_piSystem : IsPiSystem archGenerators := by
  rintro _ ⟨U, ⟨hU, hUb⟩, rfl⟩ _ ⟨U', ⟨hU', -⟩, rfl⟩ -
  exact ⟨U ∩ U', ⟨hU.inter hU', hUb.subset inter_subset_left⟩, preimage_inter⟩

private def archBalls (n : ℕ) : Set (InfiniteAdeleRing ℚ) :=
  archCoord ⁻¹' Metric.ball (0 : mixedEmbedding.mixedSpace ℚ) n

private theorem archBalls_mem (n : ℕ) : archBalls n ∈ archGenerators :=
  ⟨Metric.ball 0 n, ⟨Metric.isOpen_ball, Metric.isBounded_ball⟩, rfl⟩

private theorem archBalls_mono : Monotone archBalls := fun _ _ hab =>
  preimage_mono (Metric.ball_subset_ball (Nat.cast_le.2 hab))

private theorem archBalls_iUnion : ⋃ n, archBalls n = univ := by
  unfold archBalls
  rw [← preimage_iUnion, Metric.iUnion_ball_nat, preimage_univ]

private theorem smoothFamily_archCoord_measurable (hcont : Continuous archCoord)
    {φ : InfiniteAdeleRing ℚ → ℝ≥0} (hφ : φ ∈ smoothFamily archCoord) : Measurable φ := by
  obtain ⟨g, hg, -, -, -, rfl⟩ := hφ
  exact (continuous_real_toNNReal.comp (hg.continuous.comp hcont)).measurable

private abbrev localBorel (p : HeightOneSpectrum (𝓞 ℚ)) : MeasurableSpace (p.adicCompletion ℚ) := borel _

attribute [local instance] localBorel

private theorem localBorelSpace (p : HeightOneSpectrum (𝓞 ℚ)) : BorelSpace (p.adicCompletion ℚ) := ⟨rfl⟩

attribute [local instance] localBorelSpace

private def localCompactOpens (p : HeightOneSpectrum (𝓞 ℚ)) : Set (Set (p.adicCompletion ℚ)) :=
  {V | IsCompact V ∧ IsOpen V}

private theorem localCompactOpens_piSystem (p : HeightOneSpectrum (𝓞 ℚ)) : IsPiSystem (localCompactOpens p) :=
  fun _ hV _ hW _ => ⟨hV.1.inter_right hW.1.isClosed, hV.2.inter hW.2⟩

private theorem isCompact_localIntegers (p : HeightOneSpectrum (𝓞 ℚ))
    [CompactSpace (p.adicCompletionIntegers ℚ)] :
    IsCompact (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ)) := by
  haveI : CompactSpace ((p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ))) :=
    inferInstanceAs (CompactSpace (p.adicCompletionIntegers ℚ))
  exact isCompact_iff_compactSpace.2 this

private theorem exists_localCompactOpen_mem (p : HeightOneSpectrum (𝓞 ℚ))
    [CompactSpace (p.adicCompletionIntegers ℚ)] (x : p.adicCompletion ℚ) :
    ∃ W : Set (p.adicCompletion ℚ), IsCompact W ∧ IsOpen W ∧ x ∈ W :=
  exists_compactOpen_mem (isCompact_localIntegers p) (Valued.isOpen_valuationSubring _)
    (SetLike.mem_coe.2 (zero_mem _)) x

private theorem localGenerate (p : HeightOneSpectrum (𝓞 ℚ)) [ProperSpace (p.adicCompletion ℚ)]
    [CompactSpace (p.adicCompletionIntegers ℚ)] :
    MeasurableSpace.generateFrom (localCompactOpens p) = localBorel p :=
  (isTopologicalBasis_compactOpen (fun x _ hU => valued_exists_clopen x _ hU)
    (exists_localCompactOpen_mem p)).borel_eq_generateFrom.symm

private theorem exists_localExhaustion (p : HeightOneSpectrum (𝓞 ℚ)) [ProperSpace (p.adicCompletion ℚ)]
    [CompactSpace (p.adicCompletionIntegers ℚ)] :
    ∃ V : ℕ → Set (p.adicCompletion ℚ), (∀ n, V n ∈ localCompactOpens p) ∧ Monotone V ∧ ⋃ n, V n = univ := by
  obtain ⟨V, hV, hmono, huniv⟩ := exists_compactOpen_exhaustion (exists_localCompactOpen_mem p)
  exact ⟨V, fun n => hV n, hmono, huniv⟩

private theorem coe_localToAdelic3 (p : HeightOneSpectrum (𝓞 ℚ)) (x : LocalGL3 p) :
    ((localToAdelic3 p x : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      finMatN (Fin 3) (𝓞 ℚ) ℚ (localMatN (Fin 3) (𝓞 ℚ) ℚ p (x : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))) :=
  rfl

private theorem coe_componentAt3 (q : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ((componentAt3 (𝓞 ℚ) ℚ q g : GL (Fin 3) (q.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (q.adicCompletion ℚ)) =
      (evalHom q).mapMatrix (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  rfl

private theorem coe_archComponent3 (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ((archComponent3 (𝓞 ℚ) ℚ g : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) =
      (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  rfl

private theorem componentAt3_localToAdelic3 (p : HeightOneSpectrum (𝓞 ℚ)) (x : LocalGL3 p) :
    componentAt3 (𝓞 ℚ) ℚ p (localToAdelic3 p x) = x := by
  apply Units.ext
  rw [coe_componentAt3, coe_localToAdelic3]
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, finMatN, AdelicLevel.adeleFin_apply, AdelicLevel.finAdeleEval_apply,
    localMatN_apply_self]

private theorem componentAt3_localToAdelic3_of_ne {p q : HeightOneSpectrum (𝓞 ℚ)} (hq : q ≠ p) (x : LocalGL3 p) :
    componentAt3 (𝓞 ℚ) ℚ q (localToAdelic3 p x) = 1 := by
  apply Units.ext
  rw [coe_componentAt3, coe_localToAdelic3, Units.val_one]
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, finMatN, AdelicLevel.adeleFin_apply, AdelicLevel.finAdeleEval_apply,
    localMatN_apply_of_ne (Fin 3) (𝓞 ℚ) ℚ p _ i j hq]

private theorem archComponent3_localToAdelic3 (p : HeightOneSpectrum (𝓞 ℚ)) (x : LocalGL3 p) :
    archComponent3 (𝓞 ℚ) ℚ (localToAdelic3 p x) = 1 := by
  apply Units.ext
  rw [coe_archComponent3, coe_localToAdelic3, mapMatrix_arch_finMatN, Units.val_one]

private theorem ext_of_components {g h : AdelicGL 3 (𝓞 ℚ) ℚ}
    (harch : archComponent3 (𝓞 ℚ) ℚ g = archComponent3 (𝓞 ℚ) ℚ h)
    (hfin : ∀ q : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ q g = componentAt3 (𝓞 ℚ) ℚ q h) : g = h := by
  apply Units.ext
  refine matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ ?_ ?_
  · have h₁ := congrArg Units.val harch
    rwa [coe_archComponent3, coe_archComponent3] at h₁
  · refine matrixFin_ext (Fin 3) (𝓞 ℚ) ℚ fun w => ?_
    have h₂ := congrArg Units.val (hfin w)
    rw [coe_componentAt3, coe_componentAt3] at h₂
    ext i j
    simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using congrFun (congrFun h₂ i) j

private theorem commute_localToAdelic3 {p : HeightOneSpectrum (𝓞 ℚ)} {g : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hg : componentAt3 (𝓞 ℚ) ℚ p g = 1) (x : LocalGL3 p) :
    g * localToAdelic3 p x = localToAdelic3 p x * g := by
  refine ext_of_components ?_ fun q => ?_
  · rw [map_mul, map_mul, archComponent3_localToAdelic3, mul_one, one_mul]
  · by_cases hq : q = p
    · subst hq
      rw [map_mul, map_mul, hg, one_mul, mul_one]
    · rw [map_mul, map_mul, componentAt3_localToAdelic3_of_ne hq, mul_one, one_mul]

private theorem componentAt3_apply (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3) :
    ((componentAt3 (𝓞 ℚ) ℚ p g : GL (Fin 3) (p.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j =
      evalHom p ((g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j) := by
  rw [coe_componentAt3]
  rfl

private def structureFin :
    (∀ q : HeightOneSpectrum (𝓞 ℚ), (q.adicCompletionIntegers ℚ : Set (q.adicCompletion ℚ))) →
      FiniteAdeleRing (𝓞 ℚ) ℚ :=
  RestrictedProduct.structureMap _ _ _

private theorem continuous_structureFin : Continuous structureFin :=
  (RestrictedProduct.isEmbedding_structureMap (𝓕 := Filter.cofinite)).continuous

private theorem tendsto_finAdele_of_components {ι : Type} {l : Filter ι} (a : ι → FiniteAdeleRing (𝓞 ℚ) ℚ)
    (a₀ : FiniteAdeleRing (𝓞 ℚ) ℚ) (ha : ∀ i q, a i q ∈ q.adicCompletionIntegers ℚ)
    (ha₀ : ∀ q, a₀ q ∈ q.adicCompletionIntegers ℚ) (hlim : ∀ q, ∀ᶠ i in l, a i q = a₀ q) :
    Tendsto a l (𝓝 a₀) := by
  let fam : ι → ∀ q : HeightOneSpectrum (𝓞 ℚ), (q.adicCompletionIntegers ℚ : Set (q.adicCompletion ℚ)) :=
    fun i q => ⟨a i q, ha i q⟩
  let fam₀ : ∀ q : HeightOneSpectrum (𝓞 ℚ), (q.adicCompletionIntegers ℚ : Set (q.adicCompletion ℚ)) :=
    fun q => ⟨a₀ q, ha₀ q⟩
  have hfam : ∀ i, structureFin (fam i) = a i := fun i => by
    apply RestrictedProduct.ext
    intro q
    rfl
  have hfam₀ : structureFin fam₀ = a₀ := by
    apply RestrictedProduct.ext
    intro q
    rfl
  have hpi : Tendsto fam l (𝓝 fam₀) := by
    refine tendsto_pi_nhds.2 fun q => tendsto_const_nhds.congr' ?_
    filter_upwards [hlim q] with i hi
    exact Subtype.ext hi.symm
  have h := (continuous_structureFin.tendsto fam₀).comp hpi
  rw [hfam₀] at h
  exact h.congr hfam

private theorem tendsto_adele_of_components {ι : Type} {l : Filter ι} (a : ι → AdeleRing (𝓞 ℚ) ℚ)
    (a₀ : AdeleRing (𝓞 ℚ) ℚ) (harch : ∀ i, AdelicLevel.adeleArch (𝓞 ℚ) ℚ (a i) = AdelicLevel.adeleArch (𝓞 ℚ) ℚ a₀)
    (ha : ∀ i q, evalHom q (a i) ∈ q.adicCompletionIntegers ℚ) (ha₀ : ∀ q, evalHom q a₀ ∈ q.adicCompletionIntegers ℚ)
    (hlim : ∀ q, ∀ᶠ i in l, evalHom q (a i) = evalHom q a₀) : Tendsto a l (𝓝 a₀) := by
  have h1 : Tendsto (fun i => (a i).1) l (𝓝 a₀.1) := tendsto_const_nhds.congr fun i => (harch i).symm
  have h2 : Tendsto (fun i => (a i).2) l (𝓝 a₀.2) := tendsto_finAdele_of_components (fun i => (a i).2) a₀.2 ha ha₀ hlim
  exact (Prod.tendsto_iff a a₀).2 ⟨h1, h2⟩

private theorem tendsto_val_of_components {ι : Type} {l : Filter ι} (g : ι → AdelicGL 3 (𝓞 ℚ) ℚ)
    (g₀ : AdelicGL 3 (𝓞 ℚ) ℚ) (harch : ∀ i, archComponent3 (𝓞 ℚ) ℚ (g i) = archComponent3 (𝓞 ℚ) ℚ g₀)
    (hK : ∀ i q, componentAt3 (𝓞 ℚ) ℚ q (g i) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q)
    (hK₀ : ∀ q, componentAt3 (𝓞 ℚ) ℚ q g₀ ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q)
    (hlim : ∀ q, ∀ᶠ i in l, componentAt3 (𝓞 ℚ) ℚ q (g i) = componentAt3 (𝓞 ℚ) ℚ q g₀) :
    Tendsto (fun i => ((g i : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) l
      (𝓝 ((g₀ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) := by
  refine tendsto_pi_nhds.2 fun r => tendsto_pi_nhds.2 fun c => ?_
  refine tendsto_adele_of_components
    (fun i => ((g i : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) r c) _ ?_ ?_ ?_ ?_
  · intro i
    have h := congrArg (fun u : GL (Fin 3) (InfiniteAdeleRing ℚ) =>
      (u : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) r c) (harch i)
    simpa only [coe_archComponent3, RingHom.mapMatrix_apply, Matrix.map_apply] using h
  · intro i q
    have h := (hK i q).1 r c
    rw [componentAt3_apply] at h
    exact (HeightOneSpectrum.mem_adicCompletionIntegers ..).2 h
  · intro q
    have h := (hK₀ q).1 r c
    rw [componentAt3_apply] at h
    exact (HeightOneSpectrum.mem_adicCompletionIntegers ..).2 h
  · intro q
    filter_upwards [hlim q] with i hi
    have h := congrArg (fun u : GL (Fin 3) (q.adicCompletion ℚ) =>
      (u : Matrix (Fin 3) (Fin 3) (q.adicCompletion ℚ)) r c) hi
    simpa only [componentAt3_apply] using h

private theorem tendsto_of_components {ι : Type} {l : Filter ι} (g : ι → AdelicGL 3 (𝓞 ℚ) ℚ)
    (g₀ : AdelicGL 3 (𝓞 ℚ) ℚ) (harch : ∀ i, archComponent3 (𝓞 ℚ) ℚ (g i) = archComponent3 (𝓞 ℚ) ℚ g₀)
    (hK : ∀ i q, componentAt3 (𝓞 ℚ) ℚ q (g i) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q)
    (hK₀ : ∀ q, componentAt3 (𝓞 ℚ) ℚ q g₀ ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q)
    (hlim : ∀ q, ∀ᶠ i in l, componentAt3 (𝓞 ℚ) ℚ q (g i) = componentAt3 (𝓞 ℚ) ℚ q g₀) :
    Tendsto g l (𝓝 g₀) := by
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  simp only [Function.comp_def, Units.embedProduct_apply]
  refine (Prod.tendsto_iff _ _).2 ⟨tendsto_val_of_components g g₀ harch hK hK₀ hlim, ?_⟩
  refine (MulOpposite.continuous_op.tendsto _).comp ?_
  refine tendsto_val_of_components (fun i => (g i)⁻¹) g₀⁻¹ (fun i => ?_) (fun i q => ?_) (fun q => ?_) fun q => ?_
  · simp only [map_inv, harch i]
  · simp only [map_inv]
    exact inv_mem (hK i q)
  · simp only [map_inv]
    exact inv_mem (hK₀ q)
  · filter_upwards [hlim q] with i hi
    simp only [map_inv, hi]

private def keptAt (g : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))) : AdelicGL 3 (𝓞 ℚ) ℚ :=
  T.noncommProd (fun q => localToAdelic3 q (componentAt3 (𝓞 ℚ) ℚ q g)) fun _ _ _ _ hab =>
    (commute_localToAdelic3 (componentAt3_localToAdelic3_of_ne hab _) _).symm

private theorem keptAt_insert (g : AdelicGL 3 (𝓞 ℚ) ℚ) {T : Finset (HeightOneSpectrum (𝓞 ℚ))}
    {a : HeightOneSpectrum (𝓞 ℚ)} (ha : a ∉ T) :
    keptAt g (insert a T) = localToAdelic3 a (componentAt3 (𝓞 ℚ) ℚ a g) * keptAt g T := by
  unfold keptAt
  rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha]

private theorem archComponent3_keptAt (g : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    archComponent3 (𝓞 ℚ) ℚ (keptAt g T) = 1 := by
  refine Finset.induction_on T ?_ ?_
  · simp [keptAt]
  · intro a T ha ih
    rw [keptAt_insert g ha, map_mul, archComponent3_localToAdelic3, one_mul, ih]

private theorem componentAt3_keptAt (g : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (q : HeightOneSpectrum (𝓞 ℚ)) :
    componentAt3 (𝓞 ℚ) ℚ q (keptAt g T) = if q ∈ T then componentAt3 (𝓞 ℚ) ℚ q g else 1 := by
  refine Finset.induction_on T ?_ ?_
  · simp [keptAt]
  · intro a T ha ih
    rw [keptAt_insert g ha, map_mul, ih]
    by_cases hqa : q = a
    · subst hqa
      simp [componentAt3_localToAdelic3, ha]
    · simp [componentAt3_localToAdelic3_of_ne hqa, hqa]

private theorem translate_keptAt_eq (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hinv : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) F)
    {k : AdelicGL 3 (𝓞 ℚ) ℚ} (hkS : ∀ p ∈ S, componentAt3 (𝓞 ℚ) ℚ p k = 1)
    (hkK : ∀ p, p ∉ S → componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    (T : Finset (HeightOneSpectrum (𝓞 ℚ))) : ∀ h : AdelicGL 3 (𝓞 ℚ) ℚ, F (h * keptAt k T) = F h := by
  refine Finset.induction_on T ?_ ?_
  · intro h
    simp [keptAt]
  · intro a T ha ih h
    rw [keptAt_insert k ha, ← mul_assoc, ih]
    by_cases haS : a ∈ S
    · rw [hkS a haS, map_one, mul_one]
    · exact hinv a haS h _ (Subgroup.mem_map.2 ⟨_, hkK a haS, rfl⟩)

private theorem translate_eq_of_components (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hF : Continuous F)
    (hinv : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) F)
    {k : AdelicGL 3 (𝓞 ℚ) ℚ} (hkArch : archComponent3 (𝓞 ℚ) ℚ k = 1) (hkS : ∀ p ∈ S, componentAt3 (𝓞 ℚ) ℚ p k = 1)
    (hkK : ∀ p, p ∉ S → componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) (h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    F (h * k) = F h := by
  have hkK' : ∀ q, componentAt3 (𝓞 ℚ) ℚ q k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ q := fun q => by
    by_cases hq : q ∈ S
    · rw [hkS q hq]
      exact one_mem _
    · exact hkK q hq
  have hlim : Tendsto (fun T => keptAt k T) atTop (𝓝 k) := by
    refine tendsto_of_components _ k (fun T => ?_) (fun T q => ?_) hkK' fun q => ?_
    · rw [archComponent3_keptAt, hkArch]
    · rw [componentAt3_keptAt]
      split_ifs
      · exact hkK' q
      · exact one_mem _
    · filter_upwards [eventually_ge_atTop ({q} : Finset (HeightOneSpectrum (𝓞 ℚ)))] with T hT
      rw [componentAt3_keptAt, if_pos (Finset.singleton_subset_iff.1 hT)]
  have h1 : Tendsto (fun T => F (h * keptAt k T)) atTop (𝓝 (F (h * k))) :=
    (hF.tendsto _).comp (tendsto_const_nhds.mul hlim)
  have h2 : (fun T => F (h * keptAt k T)) = fun _ => F h := funext fun T => translate_keptAt_eq S hinv hkS hkK T h
  rw [h2] at h1
  exact tendsto_nhds_unique h1 tendsto_const_nhds

private abbrev Coords (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Type :=
  (Fin 3 → InfiniteAdeleRing ℚ) × ∀ k : Fin 3 × {p // p ∈ S}, k.2.1.adicCompletion ℚ

private def coordsOf (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) : Coords S :=
  (fun j => AdelicLevel.adeleArch (𝓞 ℚ) ℚ (x j), fun k => evalHom k.2.1 (x k.1))

private theorem continuous_coordsOf (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Continuous (coordsOf S) := by
  refine Continuous.prodMk (continuous_pi fun j => ?_) (continuous_pi fun k => ?_)
  · exact (AdelicLevel.continuous_adeleArch (𝓞 ℚ) ℚ).comp (continuous_apply j)
  · exact (continuous_evalHom k.2.1).comp (continuous_apply k.1)

private def rowOf (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (y : Coords S) : Fin 3 → AdeleRing (𝓞 ℚ) ℚ :=
  fun j => (y.1 j, ∑ p ∈ S.attach, StandardAddChar.finAdeleSingleAt ℚ p.1 (y.2 (j, p)))

private theorem adeleArch_rowOf (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (y : Coords S) (j : Fin 3) :
    AdelicLevel.adeleArch (𝓞 ℚ) ℚ (rowOf S y j) = y.1 j :=
  rfl

private theorem evalHom_rowOf_of_mem (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (y : Coords S) (j : Fin 3)
    {p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ∈ S) : evalHom p (rowOf S y j) = y.2 (j, ⟨p, hp⟩) := by
  show AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p (∑ q ∈ S.attach, StandardAddChar.finAdeleSingleAt ℚ q.1 (y.2 (j, q))) = _
  rw [map_sum]
  simp only [AdelicLevel.finAdeleEval_apply]
  rw [Finset.sum_eq_single (⟨p, hp⟩ : {p // p ∈ S})]
  · exact StandardAddChar.finAdeleSingleAt_apply_self ℚ p _
  · intro q _ hq
    exact StandardAddChar.finAdeleSingleAt_apply_of_ne ℚ q.1 _ fun h => hq (Subtype.ext h.symm)
  · intro h
    exact absurd (Finset.mem_attach _ _) h

private theorem evalHom_rowOf_of_notMem (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (y : Coords S) (j : Fin 3)
    {p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ∉ S) : evalHom p (rowOf S y j) = 0 := by
  show AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p (∑ q ∈ S.attach, StandardAddChar.finAdeleSingleAt ℚ q.1 (y.2 (j, q))) = 0
  rw [map_sum]
  simp only [AdelicLevel.finAdeleEval_apply]
  exact Finset.sum_eq_zero fun q _ =>
    StandardAddChar.finAdeleSingleAt_apply_of_ne ℚ q.1 _ fun h => hp (by rw [h]; exact q.2)

private theorem continuous_rowOf (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Continuous (rowOf S) := by
  refine continuous_pi fun j => Continuous.prodMk ((continuous_apply j).comp continuous_fst) ?_
  exact continuous_finsetSum _ fun p _ =>
    (StandardAddChar.continuous_finAdeleSingleAt ℚ p.1).comp ((continuous_apply (j, p)).comp continuous_snd)

private theorem coordsOf_add_rowOf (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ)
    (t : Coords S) : coordsOf S (x + rowOf S t) = coordsOf S x + t := by
  refine Prod.ext (funext fun j => ?_) (funext fun k => ?_)
  · show AdelicLevel.adeleArch (𝓞 ℚ) ℚ (x j + rowOf S t j) = AdelicLevel.adeleArch (𝓞 ℚ) ℚ (x j) + t.1 j
    rw [map_add, adeleArch_rowOf]
  · show evalHom k.2.1 (x k.1 + rowOf S t k.1) = evalHom k.2.1 (x k.1) + t.2 k
    rw [map_add, evalHom_rowOf_of_mem S t k.1 k.2.2]

private theorem evalHom_add_rowOf (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ)
    (t : Coords S) {p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ∉ S) (j : Fin 3) :
    evalHom p ((x + rowOf S t) j) = evalHom p (x j) := by
  show evalHom p (x j + rowOf S t j) = evalHom p (x j)
  rw [map_add, evalHom_rowOf_of_notMem S t j hp, add_zero]

private def tailAdele (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : AdeleRing (𝓞 ℚ) ℚ :=
  ((0 : InfiniteAdeleRing ℚ), 1 - ∑ p ∈ S.attach, StandardAddChar.finAdeleSingleAt ℚ p.1 1)

private theorem evalHom_tailAdele (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (p : HeightOneSpectrum (𝓞 ℚ)) :
    evalHom p (tailAdele S) = if p ∈ S then 0 else 1 := by
  show AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p (1 - ∑ q ∈ S.attach, StandardAddChar.finAdeleSingleAt ℚ q.1 1) = _
  rw [map_sub, map_one, map_sum]
  simp only [AdelicLevel.finAdeleEval_apply]
  split_ifs with hp
  · rw [Finset.sum_eq_single (⟨p, hp⟩ : {p // p ∈ S})]
    · exact sub_eq_zero.2 (StandardAddChar.finAdeleSingleAt_apply_self ℚ p 1).symm
    · intro q _ hq
      exact StandardAddChar.finAdeleSingleAt_apply_of_ne ℚ q.1 _ fun h => hq (Subtype.ext h.symm)
    · intro h
      exact absurd (Finset.mem_attach _ _) h
  · rw [Finset.sum_eq_zero fun q _ =>
      StandardAddChar.finAdeleSingleAt_apply_of_ne ℚ q.1 _ fun h => hp (by rw [h]; exact q.2), sub_zero]

private def tailRow (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Fin 3 → AdeleRing (𝓞 ℚ) ℚ :=
  fun j => if j = 2 then tailAdele S else 0

private theorem coordsOf_tailRow (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : coordsOf S (tailRow S) = 0 := by
  refine Prod.ext (funext fun j => ?_) (funext fun k => ?_)
  · show AdelicLevel.adeleArch (𝓞 ℚ) ℚ (tailRow S j) = 0
    simp only [tailRow]
    split_ifs
    · rfl
    · exact map_zero _
  · show evalHom k.2.1 (tailRow S k.1) = 0
    simp only [tailRow]
    split_ifs
    · rw [evalHom_tailAdele, if_pos k.2.2]
    · exact map_zero _

private theorem evalHom_tailRow_of_notMem (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {p : HeightOneSpectrum (𝓞 ℚ)}
    (hp : p ∉ S) (j : Fin 3) : evalHom p (tailRow S j) = if j = 2 then 1 else 0 := by
  simp only [tailRow]
  split_ifs
  · rw [evalHom_tailAdele, if_neg hp]
  · exact map_zero _

private def rowRep (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (y : Coords S) : Fin 3 → AdeleRing (𝓞 ℚ) ℚ :=
  tailRow S + rowOf S y

private theorem continuous_rowRep (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Continuous (rowRep S) :=
  continuous_const.add (continuous_rowOf S)

private theorem coordsOf_rowRep (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (y : Coords S) :
    coordsOf S (rowRep S y) = y := by
  unfold rowRep
  rw [coordsOf_add_rowOf, coordsOf_tailRow, zero_add]

private theorem evalHom_rowRep_of_notMem (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (y : Coords S)
    {p : HeightOneSpectrum (𝓞 ℚ)} (hp : p ∉ S) (j : Fin 3) : evalHom p (rowRep S y j) = if j = 2 then 1 else 0 := by
  rw [rowRep, evalHom_add_rowOf S (tailRow S) y hp j, evalHom_tailRow_of_notMem S hp j]

private def primOff (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Set (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) :=
  {x | ∀ p, p ∉ S → PrimitiveAt p x}

private def intOff (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Set (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) :=
  {x | ∀ p, p ∉ S → ∀ j, evalHom p (x j) ∈ p.adicCompletionIntegers ℚ}

private def nonzeroCoords (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Set (Coords S) :=
  {y | (∀ v : {p // p ∈ S}, ∃ j, y.2 (j, v) ≠ 0) ∧ ∃ j, y.1 j ≠ 0}

private theorem primOff_subset_intOff (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : primOff S ⊆ intOff S :=
  fun _ hx p hp => (hx p hp).1

private theorem explicitRows_eq (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    explicitRows S = primOff S ∩ coordsOf S ⁻¹' nonzeroCoords S :=
  Set.ext fun _ => ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, fun v => h₂ v.1 v.2, h₃⟩,
    fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, fun p hp => h₂ ⟨p, hp⟩, h₃⟩⟩

private theorem mem_explicitRows_iff' (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ} :
    x ∈ explicitRows S ↔ x ∈ primOff S ∧ coordsOf S x ∈ nonzeroCoords S := by
  rw [explicitRows_eq]
  exact Iff.rfl

private theorem primitiveAt_congr (p : HeightOneSpectrum (𝓞 ℚ)) {x y : Fin 3 → AdeleRing (𝓞 ℚ) ℚ}
    (h : ∀ j, evalHom p (x j) = evalHom p (y j)) : PrimitiveAt p x ↔ PrimitiveAt p y := by
  unfold PrimitiveAt
  simp only [h]

private theorem add_rowOf_mem_primOff_iff (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ)
    (t : Coords S) : x + rowOf S t ∈ primOff S ↔ x ∈ primOff S :=
  forall₂_congr fun p hp => primitiveAt_congr p (evalHom_add_rowOf S x t hp)

private theorem add_rowOf_mem_intOff_iff (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ)
    (t : Coords S) : x + rowOf S t ∈ intOff S ↔ x ∈ intOff S :=
  forall₂_congr fun p hp => forall_congr' fun j => by rw [evalHom_add_rowOf S x t hp j]

private theorem rowRep_mem_primOff (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (y : Coords S) : rowRep S y ∈ primOff S := by
  intro p hp
  refine ⟨fun j => ?_, ⟨2, ?_⟩⟩
  · rw [evalHom_rowRep_of_notMem S y hp j]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · rw [evalHom_rowRep_of_notMem S y hp 2, if_pos rfl, map_one]

private theorem rowRep_mem_explicitRows (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {y : Coords S}
    (hy : y ∈ nonzeroCoords S) : rowRep S y ∈ explicitRows S := by
  rw [explicitRows_eq]
  refine ⟨rowRep_mem_primOff S y, ?_⟩
  show coordsOf S (rowRep S y) ∈ nonzeroCoords S
  rw [coordsOf_rowRep]
  exact hy

private def fibInt
    (ν : Measure (MulAction.orbitRel.Quotient (WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic) ↥mirabolic))
    (s : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → AdelicGL 3 (𝓞 ℚ) ℚ) (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) : ℝ≥0∞ :=
  ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
    NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) ∂ν

private theorem fibInt_eq_of_coordsOf_eq (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ν : Measure (MulAction.orbitRel.Quotient (WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic) ↥mirabolic))
    (s : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → AdelicGL 3 (𝓞 ℚ) ℚ)
    (hsK : ∀ x ∈ explicitRows S, ∀ p, p ∉ S → componentAt3 (𝓞 ℚ) ℚ p (s x) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    (hsS : ∀ x ∈ explicitRows S, ∀ y ∈ explicitRows S, ∀ p ∈ S, (∀ j, evalHom p (x j) = evalHom p (y j)) →
      componentAt3 (𝓞 ℚ) ℚ p (s x) = componentAt3 (𝓞 ℚ) ℚ p (s y))
    (hsArch : ∀ x ∈ explicitRows S, ∀ y ∈ explicitRows S,
      (∀ j, AdelicLevel.adeleArch (𝓞 ℚ) ℚ (x j) = AdelicLevel.adeleArch (𝓞 ℚ) ℚ (y j)) →
      archComponent3 (𝓞 ℚ) ℚ (s x) = archComponent3 (𝓞 ℚ) ℚ (s y))
    {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : Continuous F)
    (hinv : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) F)
    {x y : Fin 3 → AdeleRing (𝓞 ℚ) ℚ} (hx : x ∈ explicitRows S) (hy : y ∈ explicitRows S)
    (hxy : coordsOf S x = coordsOf S y) : fibInt ν s F x = fibInt ν s F y := by
  have harch : ∀ j, AdelicLevel.adeleArch (𝓞 ℚ) ℚ (x j) = AdelicLevel.adeleArch (𝓞 ℚ) ℚ (y j) := fun j =>
    congrFun (congrArg Prod.fst hxy) j
  have hfin : ∀ p, ∀ hp : p ∈ S, ∀ j, evalHom p (x j) = evalHom p (y j) := fun p hp j =>
    congrFun (congrArg Prod.snd hxy) (j, ⟨p, hp⟩)
  set k : AdelicGL 3 (𝓞 ℚ) ℚ := (s x)⁻¹ * s y with hk
  have hsy : s y = s x * k := by
    rw [hk, mul_inv_cancel_left]
  have hkArch : archComponent3 (𝓞 ℚ) ℚ k = 1 := by
    rw [hk, map_mul, map_inv, hsArch x hx y hy harch, inv_mul_cancel]
  have hkS : ∀ p ∈ S, componentAt3 (𝓞 ℚ) ℚ p k = 1 := fun p hp => by
    rw [hk, map_mul, map_inv, hsS x hx y hy p hp (hfin p hp), inv_mul_cancel]
  have hkK : ∀ p, p ∉ S → componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p := fun p hp => by
    rw [hk, map_mul, map_inv]
    exact mul_mem (inv_mem (hsK x hx p hp)) (hsK y hy p hp)
  have htr : translateRight (s y) F = translateRight (s x) F := by
    funext g
    show F (g * s y) = F (g * s x)
    rw [hsy, ← mul_assoc]
    exact translate_eq_of_components S hF hinv hkArch hkS hkK (g * s x)
  unfold fibInt
  rw [htr]

private theorem countable_primes : Countable (HeightOneSpectrum (𝓞 ℚ)) :=
  Countable.of_equiv _ Rat.HeightOneSpectrum.primesEquiv.symm

attribute [local instance] countable_primes

private theorem properCompletion (w : InfinitePlace ℚ) : ProperSpace w.Completion :=
  AdelicBox.properSpace_completion (K := ℚ) w

attribute [local instance] properCompletion archSecondCountable

private theorem secondCountableAdeles : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ) :=
  NumberField.AdeleRing.secondCountableTopology ℚ

attribute [local instance] secondCountableAdeles NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

private theorem borelRows : BorelSpace (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) := inferInstance

attribute [local instance] borelRows

private theorem haarRows : rowHaar.IsAddHaarMeasure := inferInstance

attribute [local instance] haarRows

private theorem localSecondCountable (p : HeightOneSpectrum (𝓞 ℚ)) : SecondCountableTopology (p.adicCompletion ℚ) :=
  secondCountable_of_proper

attribute [local instance] localSecondCountable

private theorem archRowsSecondCountable : SecondCountableTopology (Fin 3 → InfiniteAdeleRing ℚ) :=
  inferInstance

private theorem localRowsSecondCountable (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    SecondCountableTopology (∀ k : Fin 3 × {p // p ∈ S}, k.2.1.adicCompletion ℚ) :=
  inferInstance

attribute [local instance] archRowsSecondCountable localRowsSecondCountable

private theorem secondCountableCoords (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : SecondCountableTopology (Coords S) :=
  inferInstance

attribute [local instance] secondCountableCoords

private theorem archRowsBorel : BorelSpace (Fin 3 → InfiniteAdeleRing ℚ) := Pi.borelSpace

private theorem localRowsBorel (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    BorelSpace (∀ k : Fin 3 × {p // p ∈ S}, k.2.1.adicCompletion ℚ) :=
  Pi.borelSpace

attribute [local instance] archRowsBorel localRowsBorel

private theorem borelCoords (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : BorelSpace (Coords S) := Prod.borelSpace

attribute [local instance] borelCoords

private theorem locallyCompactCoords (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : LocallyCompactSpace (Coords S) :=
  inferInstance

attribute [local instance] locallyCompactCoords

private theorem sigmaCompactCoords (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : SigmaCompactSpace (Coords S) :=
  sigmaCompactSpace_of_locallyCompact_secondCountable

attribute [local instance] sigmaCompactCoords

private theorem measurable_coordsOf (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Measurable (coordsOf S) :=
  (continuous_coordsOf S).measurable

private theorem measurable_rowRep (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Measurable (rowRep S) :=
  (continuous_rowRep S).measurable

private theorem continuous_rowEval (p : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 3) :
    Continuous fun x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ => evalHom p (x j) :=
  (continuous_evalHom p).comp (continuous_apply j)

private theorem eq_one_of_le_one_of_not_le_exp {γ : WithZero (Multiplicative ℤ)} (h1 : γ ≤ 1)
    (h2 : ¬ γ ≤ WithZero.exp (-1 : ℤ)) : γ = 1 := by
  have hne : γ ≠ 0 := fun h0 => h2 (by rw [h0]; exact zero_le')
  have hl1 : WithZero.log γ ≤ 0 := (WithZero.log_le_iff_le_exp hne).mpr (by rwa [WithZero.exp_zero])
  have hl2 : ¬ WithZero.log γ ≤ -1 := fun h => h2 ((WithZero.log_le_iff_le_exp hne).mp h)
  have hl : WithZero.log γ = 0 := by omega
  rw [← WithZero.exp_log hne, hl, WithZero.exp_zero]

private theorem isClopen_unitSphere (p : HeightOneSpectrum (𝓞 ℚ)) :
    IsClopen {y : p.adicCompletion ℚ | Valued.v y = 1} := by
  obtain ⟨t, ht0, ht⟩ := AdelicLevel.exists_valued_eq_exp_neg (K := ℚ) p 1
  simp only [Nat.cast_one] at ht
  have hset : {y : p.adicCompletion ℚ | Valued.v y = 1} =
      {y : p.adicCompletion ℚ | Valued.v y ≤ Valued.v (1 : p.adicCompletion ℚ)} \
        {y : p.adicCompletion ℚ | Valued.v y ≤ Valued.v t} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_diff, map_one, ht]
    constructor
    · intro h
      rw [h]
      refine ⟨le_rfl, fun h' => ?_⟩
      rw [← WithZero.exp_zero, WithZero.exp_le_exp] at h'
      omega
    · rintro ⟨h1, h2⟩
      exact eq_one_of_le_one_of_not_le_exp h1 h2
  rw [hset]
  exact IsClopen.diff
    ⟨AdelicLevel.isClosed_setOf_valued_le p (1 : p.adicCompletion ℚ) one_ne_zero,
      AdelicLevel.isOpen_setOf_valued_le p (1 : p.adicCompletion ℚ) one_ne_zero⟩
    ⟨AdelicLevel.isClosed_setOf_valued_le p t ht0, AdelicLevel.isOpen_setOf_valued_le p t ht0⟩

private theorem measurableSet_rowEval_integral (p : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 3) :
    MeasurableSet {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | evalHom p (x j) ∈ p.adicCompletionIntegers ℚ} := by
  have h : IsClosed {y : p.adicCompletion ℚ | Valued.v y ≤ 1} := by
    simpa using AdelicLevel.isClosed_setOf_valued_le p (1 : p.adicCompletion ℚ) one_ne_zero
  exact (h.preimage (continuous_rowEval p j)).measurableSet

private theorem measurableSet_rowEval_unit (p : HeightOneSpectrum (𝓞 ℚ)) (j : Fin 3) :
    MeasurableSet {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | Valued.v (evalHom p (x j)) = 1} :=
  ((isClopen_unitSphere p).preimage (continuous_rowEval p j)).isClosed.measurableSet

private theorem measurableSet_setOf_primitiveAt (p : HeightOneSpectrum (𝓞 ℚ)) :
    MeasurableSet {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | PrimitiveAt p x} := by
  have h : {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | PrimitiveAt p x} =
      (⋂ j, {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | evalHom p (x j) ∈ p.adicCompletionIntegers ℚ}) ∩
        ⋃ j, {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | Valued.v (evalHom p (x j)) = 1} := by
    ext x
    simp only [PrimitiveAt, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_iUnion]
  rw [h]
  exact (MeasurableSet.iInter fun j => measurableSet_rowEval_integral p j).inter
    (MeasurableSet.iUnion fun j => measurableSet_rowEval_unit p j)

private theorem measurableSet_primOff (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : MeasurableSet (primOff S) := by
  have h : primOff S = ⋂ p, ⋂ (_ : p ∉ S), {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | PrimitiveAt p x} := by
    ext x
    simp only [primOff, Set.mem_setOf_eq, Set.mem_iInter]
  rw [h]
  exact MeasurableSet.iInter fun p => MeasurableSet.iInter fun _ => measurableSet_setOf_primitiveAt p

private theorem measurableSet_intOff (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : MeasurableSet (intOff S) := by
  have h : intOff S = ⋂ p, ⋂ (_ : p ∉ S), ⋂ j,
      {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | evalHom p (x j) ∈ p.adicCompletionIntegers ℚ} := by
    ext x
    simp only [intOff, Set.mem_setOf_eq, Set.mem_iInter]
  rw [h]
  exact MeasurableSet.iInter fun p => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun j =>
    measurableSet_rowEval_integral p j

private theorem measurableSet_nonzeroCoords (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    MeasurableSet (nonzeroCoords S) := by
  have h : nonzeroCoords S = (⋂ v : {p // p ∈ S}, ⋃ j, {y : Coords S | y.2 (j, v) ≠ 0}) ∩
      ⋃ j, {y : Coords S | y.1 j ≠ 0} := by
    ext y
    simp only [nonzeroCoords, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_iUnion]
  rw [h]
  refine (MeasurableSet.iInter fun v => MeasurableSet.iUnion fun j => ?_).inter
    (MeasurableSet.iUnion fun j => ?_)
  · exact (isOpen_ne.preimage ((continuous_apply (j, v)).comp continuous_snd)).measurableSet
  · exact (isOpen_ne.preimage ((continuous_apply j).comp continuous_fst)).measurableSet

private theorem explicitRows_measurableSet (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    MeasurableSet (explicitRows S) := by
  rw [explicitRows_eq]
  exact (measurableSet_primOff S).inter (measurable_coordsOf S (measurableSet_nonzeroCoords S))

private theorem rowOf_add (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (a b : Coords S) :
    rowOf S (a + b) = rowOf S a + rowOf S b := by
  funext j
  refine Prod.ext rfl ?_
  show (∑ p ∈ S.attach, StandardAddChar.finAdeleSingleAt ℚ p.1 (a.2 (j, p) + b.2 (j, p))) =
    (∑ p ∈ S.attach, StandardAddChar.finAdeleSingleAt ℚ p.1 (a.2 (j, p))) +
      ∑ p ∈ S.attach, StandardAddChar.finAdeleSingleAt ℚ p.1 (b.2 (j, p))
  simp only [map_add, Finset.sum_add_distrib]

private theorem rowOf_zero (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : rowOf S 0 = 0 := by
  funext j
  refine Prod.ext rfl ?_
  show (∑ p ∈ S.attach, StandardAddChar.finAdeleSingleAt ℚ p.1 ((0 : Coords S).2 (j, p))) = 0
  simp only [Prod.snd_zero, Pi.zero_apply, map_zero, Finset.sum_const_zero]

private theorem rowOf_neg_add (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (a : Coords S) :
    rowOf S (-a) + rowOf S a = 0 := by
  rw [← rowOf_add, neg_add_cancel, rowOf_zero]

private def integralPillar : Set (AdeleRing (𝓞 ℚ) ℚ) :=
  ({0} : Set (InfiniteAdeleRing ℚ)) ×ˢ AdelicBox.integralFiniteAdeles (𝓞 ℚ) ℚ

private theorem isCompact_integralPillar : IsCompact integralPillar :=
  isCompact_singleton.prod (AdelicBox.isCompact_integralFiniteAdeles (K := ℚ))

open scoped Pointwise in

private theorem exists_isCompact_superset (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {K : Set (Coords S)}
    (hK : IsCompact K) :
    ∃ L : Set (Fin 3 → AdeleRing (𝓞 ℚ) ℚ), IsCompact L ∧ coordsOf S ⁻¹' K ∩ intOff S ⊆ L := by
  refine ⟨(univ.pi fun _ : Fin 3 => integralPillar) + rowOf S '' K,
    (isCompact_univ_pi fun _ => isCompact_integralPillar).add (hK.image (continuous_rowOf S)), ?_⟩
  rintro x ⟨hxK, hxZ⟩
  have hw : x + rowOf S (-(coordsOf S x)) ∈ intOff S := (add_rowOf_mem_intOff_iff S x _).2 hxZ
  have hc : coordsOf S (x + rowOf S (-(coordsOf S x))) = 0 := by
    rw [coordsOf_add_rowOf, add_neg_cancel]
  refine Set.mem_add.2 ⟨x + rowOf S (-(coordsOf S x)), ?_, rowOf S (coordsOf S x), ⟨coordsOf S x, hxK, rfl⟩, ?_⟩
  · refine mem_univ_pi.2 fun j => ⟨?_, fun p => ?_⟩
    · exact congrFun (congrArg Prod.fst hc) j
    · by_cases hp : p ∈ S
      · have h0 : evalHom p ((x + rowOf S (-(coordsOf S x))) j) = 0 :=
          congrFun (congrArg Prod.snd hc) (j, ⟨p, hp⟩)
        show evalHom p ((x + rowOf S (-(coordsOf S x))) j) ∈ p.adicCompletionIntegers ℚ
        rw [h0]
        exact zero_mem _
      · exact hw p hp j
  · show x + rowOf S (-(coordsOf S x)) + rowOf S (coordsOf S x) = x
    rw [add_assoc, rowOf_neg_add, add_zero]

private def pushed (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (B : Set (Fin 3 → AdeleRing (𝓞 ℚ) ℚ)) :
    Measure (Coords S) :=
  Measure.map (coordsOf S) (rowHaar.restrict B)

private theorem pushed_isAddLeftInvariant (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {B : Set (Fin 3 → AdeleRing (𝓞 ℚ) ℚ)} (hB : ∀ x t, x + rowOf S t ∈ B ↔ x ∈ B) :
    (pushed S B).IsAddLeftInvariant := by
  refine ⟨fun t => ?_⟩
  have hcomp : (fun y : Coords S => t + y) ∘ coordsOf S =
      coordsOf S ∘ ⇑(MeasurableEquiv.addLeft (rowOf S t)) := by
    funext x
    show t + coordsOf S x = coordsOf S (rowOf S t + x)
    rw [add_comm (rowOf S t) x, coordsOf_add_rowOf, add_comm]
  have hpre : ⇑(MeasurableEquiv.addLeft (rowOf S t)) ⁻¹' B = B := by
    ext x
    show rowOf S t + x ∈ B ↔ x ∈ B
    rw [add_comm]
    exact hB x t
  have hres : (rowHaar.restrict B).map (MeasurableEquiv.addLeft (rowOf S t)) = rowHaar.restrict B := by
    rw [← hpre, ← MeasurableEquiv.restrict_map, hpre]
    congr 1
    rw [MeasurableEquiv.coe_addLeft]
    exact map_add_left_eq_self rowHaar (rowOf S t)
  unfold pushed
  rw [Measure.map_map (measurable_const_add t) (measurable_coordsOf S), hcomp,
    ← Measure.map_map (measurable_coordsOf S) (MeasurableEquiv.addLeft (rowOf S t)).measurable, hres]

private theorem pushed_isFiniteMeasureOnCompacts (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {B : Set (Fin 3 → AdeleRing (𝓞 ℚ) ℚ)} (hB : B ⊆ intOff S) : IsFiniteMeasureOnCompacts (pushed S B) := by
  refine ⟨fun K hK => ?_⟩
  rw [pushed, Measure.map_apply (measurable_coordsOf S) hK.measurableSet,
    Measure.restrict_apply (measurable_coordsOf S hK.measurableSet)]
  obtain ⟨L, hL, hsub⟩ := exists_isCompact_superset S hK
  exact lt_of_le_of_lt (measure_mono ((inter_subset_inter_right _ hB).trans hsub)) hL.measure_lt_top

private def coordsHaar (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Measure (Coords S) :=
  Measure.addHaarMeasure (Classical.arbitrary _)

private theorem coordsHaar_isAddHaarMeasure (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    (coordsHaar S).IsAddHaarMeasure :=
  Measure.isAddHaarMeasure_addHaarMeasure _

attribute [local instance] coordsHaar_isAddHaarMeasure

private theorem pushed_eq_smul (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {B : Set (Fin 3 → AdeleRing (𝓞 ℚ) ℚ)}
    (hinv : ∀ x t, x + rowOf S t ∈ B ↔ x ∈ B) (hB : B ⊆ intOff S) :
    ∃ c : ℝ≥0, pushed S B = (c : ℝ≥0∞) • coordsHaar S := by
  haveI := pushed_isAddLeftInvariant S hinv
  haveI := pushed_isFiniteMeasureOnCompacts S hB
  refine ⟨Measure.addHaarScalarFactor (pushed S B) (coordsHaar S), ?_⟩
  rw [← ENNReal.smul_def]
  exact Measure.isAddLeftInvariant_eq_smul _ _

private theorem continuous_archCoord : Continuous archCoord := AdelicBox.continuous_ringEquiv_mixedSpace ℚ

private def finPart (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (W : ∀ v : {p // p ∈ S}, Set (v.1.adicCompletion ℚ))
    (z : FiniteAdeleRing (𝓞 ℚ) ℚ) : ℝ≥0 :=
  (∏ v : {p // p ∈ S}, (W v).indicator (fun _ => (1 : ℝ≥0)) (z v.1)) *
    if ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → z v ∈ v.adicCompletionIntegers ℚ then 1 else 0

private def testFactor (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (φ : InfiniteAdeleRing ℚ → ℝ≥0)
    (W : ∀ v : {p // p ∈ S}, Set (v.1.adicCompletion ℚ)) (a : AdeleRing (𝓞 ℚ) ℚ) : ℝ≥0 :=
  φ a.1 * finPart S W a.2

private def testFactorC (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (φ : InfiniteAdeleRing ℚ → ℝ≥0)
    (W : ∀ v : {p // p ∈ S}, Set (v.1.adicCompletion ℚ)) (a : AdeleRing (𝓞 ℚ) ℚ) : ℂ :=
  ((testFactor S φ W a : ℝ) : ℂ)

private def rowTest (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (φ : Fin 3 → InfiniteAdeleRing ℚ → ℝ≥0)
    (V : ∀ k : Fin 3 × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)) (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) : ℂ :=
  ∏ i, testFactorC S (φ i) (fun v => V (i, v)) (x i)

private theorem rowTest_eq_ofReal (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (φ : Fin 3 → InfiniteAdeleRing ℚ → ℝ≥0)
    (V : ∀ k : Fin 3 × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)) (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) :
    rowTest S φ V x = (((∏ i, testFactor S (φ i) (fun v => V (i, v)) (x i) : ℝ≥0) : ℝ) : ℂ) := by
  simp only [rowTest, testFactorC, NNReal.coe_prod, Complex.ofReal_prod]

private theorem rowTest_real (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (φ : Fin 3 → InfiniteAdeleRing ℚ → ℝ≥0)
    (V : ∀ k : Fin 3 × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)) (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) :
    0 ≤ (rowTest S φ V x).re ∧ (rowTest S φ V x).im = 0 := by
  rw [rowTest_eq_ofReal, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨NNReal.coe_nonneg _, rfl⟩

private theorem nnnorm_rowTest (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (φ : Fin 3 → InfiniteAdeleRing ℚ → ℝ≥0)
    (V : ∀ k : Fin 3 × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)) (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) :
    ‖rowTest S φ V x‖₊ = ∏ i, testFactor S (φ i) (fun v => V (i, v)) (x i) := by
  rw [rowTest_eq_ofReal, Complex.nnnorm_real, NNReal.nnnorm_eq]

private theorem re_rowTest (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (φ : Fin 3 → InfiniteAdeleRing ℚ → ℝ≥0)
    (V : ∀ k : Fin 3 × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)) (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) :
    (rowTest S φ V x).re = ((‖rowTest S φ V x‖₊ : ℝ≥0) : ℝ) := by
  rw [nnnorm_rowTest, rowTest_eq_ofReal, Complex.ofReal_re]

private theorem prod_ite_integral_eq (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) :
    (∏ i : Fin 3, (if ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → (x i).2 v ∈ v.adicCompletionIntegers ℚ then (1 : ℝ≥0)
      else 0)) = (intOff S).indicator (fun _ => (1 : ℝ≥0)) x := by
  by_cases hx : x ∈ intOff S
  · rw [indicator_of_mem hx]
    exact Finset.prod_eq_one fun i _ => if_pos fun v hv => hx v hv i
  · rw [indicator_of_notMem hx]
    have hnot : ¬ ∀ i : Fin 3, ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → (x i).2 v ∈ v.adicCompletionIntegers ℚ :=
      fun h => hx fun v hv i => h i v hv
    obtain ⟨i, hi⟩ := not_forall.1 hnot
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

private theorem nnnorm_rowTest_eq (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (φ : Fin 3 → InfiniteAdeleRing ℚ → ℝ≥0)
    (V : ∀ k : Fin 3 × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)) (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) :
    ((‖rowTest S φ V x‖₊ : ℝ≥0) : ℝ≥0∞) =
      boxTest φ V (coordsOf S x) * (intOff S).indicator (fun _ => (1 : ℝ≥0∞)) x := by
  have hNN : (∏ i, testFactor S (φ i) (fun v => V (i, v)) (x i)) =
      ((∏ i, φ i ((coordsOf S x).1 i)) *
        ∏ k, (V k).indicator (fun _ => (1 : ℝ≥0)) ((coordsOf S x).2 k)) *
          (intOff S).indicator (fun _ => (1 : ℝ≥0)) x := by
    rw [← prod_ite_integral_eq]
    simp only [testFactor, finPart, Finset.prod_mul_distrib, Fintype.prod_prod_type, mul_assoc]
    rfl
  rw [nnnorm_rowTest, hNN, ENNReal.coe_mul]
  unfold boxTest
  congr 1
  by_cases hx : x ∈ intOff S <;> simp [hx]

private def extSets (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (W : ∀ v : {p // p ∈ S}, Set (v.1.adicCompletion ℚ))
    (v : HeightOneSpectrum (𝓞 ℚ)) : Set (v.adicCompletion ℚ) :=
  if hv : v ∈ S then W ⟨v, hv⟩ else ∅

private theorem extSets_coe (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (W : ∀ v : {p // p ∈ S}, Set (v.1.adicCompletion ℚ))
    (v : {p // p ∈ S}) : extSets S W v.1 = W v := by
  show (if hv : v.1 ∈ S then W ⟨v.1, hv⟩ else ∅) = W v
  rw [dif_pos v.2]

private def localFactorC (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (W : ∀ v : {p // p ∈ S}, Set (v.1.adicCompletion ℚ))
    (v : HeightOneSpectrum (𝓞 ℚ)) (t : v.adicCompletion ℚ) : ℂ :=
  (extSets S W v).indicator (fun _ => (1 : ℂ)) t

private theorem coe_indicator_one_eq (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (W : ∀ v : {p // p ∈ S}, Set (v.1.adicCompletion ℚ)) (v : {p // p ∈ S}) (t : v.1.adicCompletion ℚ) :
    ((((W v).indicator (fun _ => (1 : ℝ≥0)) t : ℝ≥0) : ℝ) : ℂ) = localFactorC S W v.1 t := by
  unfold localFactorC
  rw [extSets_coe]
  by_cases ht : t ∈ W v <;> simp [ht]

private theorem finPart_eq_shape (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (W : ∀ v : {p // p ∈ S}, Set (v.1.adicCompletion ℚ)) (z : FiniteAdeleRing (𝓞 ℚ) ℚ) :
    ((finPart S W z : ℝ) : ℂ) = (∏ v ∈ S, localFactorC S W v (z v)) *
      (if ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → z v ∈ v.adicCompletionIntegers ℚ then (1 : ℂ) else 0) := by
  unfold finPart
  rw [← Finset.prod_coe_sort S (fun v => localFactorC S W v (z v))]
  by_cases hc : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → z v ∈ v.adicCompletionIntegers ℚ
  · rw [if_pos hc, if_pos hc, mul_one, mul_one, NNReal.coe_prod, Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun v _ => coe_indicator_one_eq S W v (z v.1)
  · rw [if_neg hc, if_neg hc, mul_zero, mul_zero, NNReal.coe_zero, Complex.ofReal_zero]

private theorem isClopen_extSets (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {W : ∀ v : {p // p ∈ S}, Set (v.1.adicCompletion ℚ)} (hW : ∀ v, W v ∈ localCompactOpens v.1)
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∈ S) : IsClopen (extSets S W v) := by
  rw [show extSets S W v = W ⟨v, hv⟩ from dif_pos hv]
  exact ⟨(hW ⟨v, hv⟩).1.isClosed, (hW ⟨v, hv⟩).2⟩

private theorem isCompact_extSets (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {W : ∀ v : {p // p ∈ S}, Set (v.1.adicCompletion ℚ)} (hW : ∀ v, W v ∈ localCompactOpens v.1)
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∈ S) : IsCompact (extSets S W v) := by
  rw [show extSets S W v = W ⟨v, hv⟩ from dif_pos hv]
  exact (hW ⟨v, hv⟩).1

private theorem testFactorC_mem_pureTensorSet (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {φ : InfiniteAdeleRing ℚ → ℝ≥0} (hφ : φ ∈ smoothFamily archCoord)
    {W : ∀ v : {p // p ∈ S}, Set (v.1.adicCompletion ℚ)} (hW : ∀ v, W v ∈ localCompactOpens v.1) :
    testFactorC S φ W ∈ NumberField.AdelicFourier.pureTensorSet ℚ := by
  obtain ⟨g, hg_smooth, hg_supp, hg_nonneg, -, rfl⟩ := hφ
  have hgC_supp : HasCompactSupport fun t => (g t : ℂ) := hg_supp.comp_left Complex.ofReal_zero
  have hgC_smooth : ContDiff ℝ (⊤ : ℕ∞) fun t => (g t : ℂ) := Complex.ofRealCLM.contDiff.comp hg_smooth
  obtain ⟨hlc, hcs⟩ :=
    NumberField.AdelicFourier.isLocallyConstant_and_hasCompactSupport_prod_mul_ite_forall_mem_adicCompletionIntegers
      ℚ S (localFactorC S W) (fun v hv => isLocallyConstant_indicator (isClopen_extSets S hW hv) 1)
      (fun v hv => hasCompactSupport_indicator (isCompact_extSets S hW hv) 1)
  refine ⟨hgC_supp.toSchwartzMap hgC_smooth, _, hlc, hcs, ?_⟩
  funext a
  show (((Real.toNNReal (g (archCoord a.1)) * finPart S W a.2 : ℝ≥0) : ℝ) : ℂ) = _
  rw [NNReal.coe_mul, Complex.ofReal_mul, Real.coe_toNNReal _ (hg_nonneg _), finPart_eq_shape]
  rfl

private def placeFun (w : InfinitePlace ℚ) (t : w.Completion) : InfiniteAdeleRing ℚ :=
  fun w' => cast (congrArg InfinitePlace.Completion (Subsingleton.elim w w')) t

private theorem placeFun_default (y : InfiniteAdeleRing ℚ) : placeFun default (y default) = y := by
  funext w'
  obtain rfl : (default : InfinitePlace ℚ) = w' := Subsingleton.elim _ _
  simp only [placeFun, cast_eq]

private def archFactorC (g : mixedEmbedding.mixedSpace ℚ → ℝ) (w : InfinitePlace ℚ) (t : w.Completion) : ℂ :=
  (g (archCoord (placeFun w t)) : ℂ)

private theorem prod_archFactorC (g : mixedEmbedding.mixedSpace ℚ → ℝ) (y : InfiniteAdeleRing ℚ) :
    (∏ w : InfinitePlace ℚ, archFactorC g w (y w)) = (g (archCoord y) : ℂ) := by
  rw [Fintype.prod_unique]
  simp only [archFactorC, placeFun_default]

private theorem exists_factorizable (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {φ : InfiniteAdeleRing ℚ → ℝ≥0}
    (hφ : φ ∈ smoothFamily archCoord) (W : ∀ v : {p // p ∈ S}, Set (v.1.adicCompletion ℚ)) :
    ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (testFactorC S φ W) S g h := by
  obtain ⟨g, -, -, hg_nonneg, -, rfl⟩ := hφ
  refine ⟨archFactorC g, localFactorC S W, fun a => ?_⟩
  show (((Real.toNNReal (g (archCoord a.1)) * finPart S W a.2 : ℝ≥0) : ℝ) : ℂ) = _
  rw [NNReal.coe_mul, Complex.ofReal_mul, Real.coe_toNNReal _ (hg_nonneg _), finPart_eq_shape]
  by_cases hmem : a ∈ NumberField.TateGlobal.integralOutside (F := ℚ) S
  · have hc : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → a.2 v ∈ v.adicCompletionIntegers ℚ := hmem
    rw [if_pos hc, mul_one, Set.indicator_of_mem hmem, prod_archFactorC]
  · have hc : ¬ ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → a.2 v ∈ v.adicCompletionIntegers ℚ := hmem
    rw [if_neg hc, mul_zero, mul_zero, Set.indicator_of_notMem hmem]

private theorem rowTest_class (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {φ : Fin 3 → InfiniteAdeleRing ℚ → ℝ≥0}
    (hφ : ∀ i, φ i ∈ smoothFamily archCoord) {V : ∀ k : Fin 3 × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)}
    (hV : ∀ k, V k ∈ localCompactOpens k.2.1) :
    ∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
      (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
      rowTest S φ V = fun x => ∏ i, Φc i (x i) :=
  ⟨fun i => testFactorC S (φ i) (fun v => V (i, v)),
    fun i => testFactorC_mem_pureTensorSet S (hφ i) fun v => hV (i, v),
    fun i => exists_factorizable S (hφ i) _, rfl⟩

private theorem smoothFamily_exists_compact {φ : InfiniteAdeleRing ℚ → ℝ≥0} (hφ : φ ∈ smoothFamily archCoord) :
    ∃ K : Set (InfiniteAdeleRing ℚ), IsCompact K ∧ MeasurableSet K ∧ (∀ a, φ a ≤ 1) ∧ ∀ a, a ∉ K → φ a = 0 := by
  obtain ⟨g, -, hg_supp, -, hg_le, rfl⟩ := hφ
  refine ⟨archCoord ⁻¹' tsupport g, isCompact_preimage_archCoord continuous_archCoord hg_supp,
    ((isClosed_tsupport g).preimage continuous_archCoord).measurableSet, fun a => ?_, fun a ha => ?_⟩
  · exact Real.toNNReal_le_one.2 (hg_le _)
  · show Real.toNNReal (g (archCoord a)) = 0
    rw [image_eq_zero_of_notMem_tsupport ha, Real.toNNReal_zero]

private theorem measurable_boxTest_coords (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {φ : Fin 3 → InfiniteAdeleRing ℚ → ℝ≥0} (hφ : ∀ i, φ i ∈ smoothFamily archCoord)
    {V : ∀ k : Fin 3 × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)} (hV : ∀ k, V k ∈ localCompactOpens k.2.1) :
    Measurable (boxTest φ V) :=
  boxTest_measurable (fun i => smoothFamily_archCoord_measurable continuous_archCoord (hφ i))
    fun k => (hV k).2.measurableSet

private theorem lintegral_boxTest_ne_top (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {φ : Fin 3 → InfiniteAdeleRing ℚ → ℝ≥0} (hφ : ∀ i, φ i ∈ smoothFamily archCoord)
    {V : ∀ k : Fin 3 × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)} (hV : ∀ k, V k ∈ localCompactOpens k.2.1) :
    ∫⁻ y, boxTest φ V y ∂coordsHaar S ≠ ⊤ := by
  choose K hKc hKm hφ₁ hφK using fun i => smoothFamily_exists_compact (hφ i)
  refine ne_top_of_le_ne_top ?_ (lintegral_boxTest_le (coordsHaar S) hφ₁ hφK hKm fun k => (hV k).2.measurableSet)
  exact ((isCompact_univ_pi hKc).prod (isCompact_univ_pi fun k => (hV k).1)).measure_lt_top.ne

private theorem exists_isCompact_rowTest_bound (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {φ : Fin 3 → InfiniteAdeleRing ℚ → ℝ≥0} (hφ : ∀ i, φ i ∈ smoothFamily archCoord)
    {V : ∀ k : Fin 3 × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)} (hV : ∀ k, V k ∈ localCompactOpens k.2.1) :
    ∃ L : Set (Fin 3 → AdeleRing (𝓞 ℚ) ℚ), IsCompact L ∧
      ∀ x, ((‖rowTest S φ V x‖₊ : ℝ≥0) : ℝ≥0∞) ≤ L.indicator (fun _ => (1 : ℝ≥0∞)) x := by
  choose K hKc hKm hφ₁ hφK using fun i => smoothFamily_exists_compact (hφ i)
  obtain ⟨L, hL, hsub⟩ :=
    exists_isCompact_superset S ((isCompact_univ_pi hKc).prod (isCompact_univ_pi fun k => (hV k).1))
  refine ⟨L, hL, fun x => ?_⟩
  rw [nnnorm_rowTest_eq]
  by_cases hx : x ∈ coordsOf S ⁻¹' ((univ.pi K) ×ˢ (univ.pi V)) ∩ intOff S
  · rw [indicator_of_mem (hsub hx)]
    calc boxTest φ V (coordsOf S x) * (intOff S).indicator (fun _ => (1 : ℝ≥0∞)) x
        ≤ ((univ.pi K) ×ˢ (univ.pi V)).indicator (fun _ => (1 : ℝ≥0∞)) (coordsOf S x) *
            (intOff S).indicator (fun _ => (1 : ℝ≥0∞)) x :=
          mul_le_mul_left (boxTest_le_indicator hφ₁ hφK V _) _
      _ ≤ 1 := by
          rw [indicator_of_mem (show coordsOf S x ∈ (univ.pi K) ×ˢ (univ.pi V) from hx.1), indicator_of_mem hx.2,
            mul_one]
  · rcases not_and_or.1 hx with hx1 | hx2
    · have h0 : boxTest φ V (coordsOf S x) = 0 :=
        le_antisymm ((boxTest_le_indicator hφ₁ hφK V _).trans_eq
          (indicator_of_notMem (show coordsOf S x ∉ (univ.pi K) ×ˢ (univ.pi V) from hx1) _)) zero_le
      rw [h0, zero_mul]
      exact zero_le
    · rw [indicator_of_notMem hx2, mul_zero]
      exact zero_le

private theorem integrable_re_rowTest (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {φ : Fin 3 → InfiniteAdeleRing ℚ → ℝ≥0} (hφ : ∀ i, φ i ∈ smoothFamily archCoord)
    {V : ∀ k : Fin 3 × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)} (hV : ∀ k, V k ∈ localCompactOpens k.2.1) :
    Integrable (fun x => (rowTest S φ V x).re) rowHaar := by
  obtain ⟨L, hL, hbound⟩ := exists_isCompact_rowTest_bound S hφ hV
  have hmeas : Measurable fun x => ((‖rowTest S φ V x‖₊ : ℝ≥0) : ℝ≥0∞) := by
    simp only [nnnorm_rowTest_eq]
    exact ((measurable_boxTest_coords S hφ hV).comp (measurable_coordsOf S)).mul
      (measurable_const.indicator (measurableSet_intOff S))
  have hre : (fun x => (rowTest S φ V x).re) = fun x => ((‖rowTest S φ V x‖₊ : ℝ≥0) : ℝ≥0∞).toReal := by
    funext x
    rw [re_rowTest, ENNReal.coe_toReal]
  rw [hre]
  refine Integrable.mono' ((integrableOn_const (C := (1 : ℝ)) hL.measure_lt_top.ne).integrable_indicator
    hL.measurableSet) hmeas.ennreal_toReal.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  beta_reduce
  rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
  by_cases hx : x ∈ L
  · rw [indicator_of_mem hx]
    have h := hbound x
    rw [indicator_of_mem hx] at h
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rwa [ENNReal.ofReal_one])
  · have h := hbound x
    rw [indicator_of_notMem hx] at h
    rw [indicator_of_notMem hx, nonpos_iff_eq_zero.1 h, ENNReal.toReal_zero]

private theorem average_identity (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (f : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℝ≥0∞)
    (C : ℝ≥0∞)
    (hid : ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
      (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
        (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
        Φ = fun x => ∏ i, Φc i (x i)) ∧
      (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧ 0 < ∫ x, (Φ x).re ∂rowHaar →
      ∫⁻ x in explicitRows S, (‖Φ x‖₊ : ℝ≥0∞) * f x ∂rowHaar = C * ∫⁻ x, (‖Φ x‖₊ : ℝ≥0∞) ∂rowHaar)
    {φ : Fin 3 → InfiniteAdeleRing ℚ → ℝ≥0} (hφ : ∀ i, φ i ∈ smoothFamily archCoord)
    {V : ∀ k : Fin 3 × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)} (hV : ∀ k, V k ∈ localCompactOpens k.2.1) :
    ∫⁻ x in explicitRows S, boxTest φ V (coordsOf S x) * (intOff S).indicator (fun _ => (1 : ℝ≥0∞)) x * f x ∂rowHaar =
      C * ∫⁻ x, boxTest φ V (coordsOf S x) * (intOff S).indicator (fun _ => (1 : ℝ≥0∞)) x ∂rowHaar := by
  simp only [← nnnorm_rowTest_eq]
  by_cases hpos : 0 < ∫ x, (rowTest S φ V x).re ∂rowHaar
  · exact hid _ ⟨rowTest_class S hφ hV, rowTest_real S φ V, hpos⟩
  · have hzero : ∫ x, (rowTest S φ V x).re ∂rowHaar = 0 :=
      le_antisymm (not_lt.1 hpos) (integral_nonneg fun x => (rowTest_real S φ V x).1)
    have hae : ∀ᵐ x ∂rowHaar, ((‖rowTest S φ V x‖₊ : ℝ≥0) : ℝ≥0∞) = 0 := by
      have h := (integral_eq_zero_iff_of_nonneg (fun x => (rowTest_real S φ V x).1)
        (integrable_re_rowTest S hφ hV)).1 hzero
      filter_upwards [h] with x hx
      have hx' : (rowTest S φ V x).re = 0 := hx
      rw [re_rowTest] at hx'
      rw [ENNReal.coe_eq_zero]
      exact_mod_cast hx'
    have hR : ∫⁻ x, ((‖rowTest S φ V x‖₊ : ℝ≥0) : ℝ≥0∞) ∂rowHaar = 0 := by
      rw [lintegral_congr_ae hae, lintegral_zero]
    have hL : ∫⁻ x in explicitRows S, ((‖rowTest S φ V x‖₊ : ℝ≥0) : ℝ≥0∞) * f x ∂rowHaar = 0 := by
      rw [← lintegral_zero (μ := rowHaar.restrict (explicitRows S))]
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae (s := explicitRows S) hae] with x hx
      simp only [hx, zero_mul]
    rw [hL, hR, mul_zero]

private theorem lintegral_test_eq (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {cγ : ℝ≥0}
    (hγ : pushed S (intOff S) = (cγ : ℝ≥0∞) • coordsHaar S) {φ : Fin 3 → InfiniteAdeleRing ℚ → ℝ≥0}
    (hφ : ∀ i, φ i ∈ smoothFamily archCoord) {V : ∀ k : Fin 3 × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)}
    (hV : ∀ k, V k ∈ localCompactOpens k.2.1) :
    ∫⁻ x, boxTest φ V (coordsOf S x) * (intOff S).indicator (fun _ => (1 : ℝ≥0∞)) x ∂rowHaar =
      cγ * ∫⁻ y, boxTest φ V y ∂coordsHaar S := by
  have h1 : ∀ x, boxTest φ V (coordsOf S x) * (intOff S).indicator (fun _ => (1 : ℝ≥0∞)) x =
      (intOff S).indicator (fun x => boxTest φ V (coordsOf S x)) x := fun x => by
    by_cases hx : x ∈ intOff S <;> simp [hx]
  simp only [h1]
  rw [lintegral_indicator (measurableSet_intOff S),
    ← lintegral_map (measurable_boxTest_coords S hφ hV) (measurable_coordsOf S)]
  change ∫⁻ y, boxTest φ V y ∂(pushed S (intOff S)) = _
  rw [hγ, lintegral_smul_measure, smul_eq_mul]

private theorem setLIntegral_test_mul_eq (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {cβ : ℝ≥0}
    (hβ : pushed S (primOff S) = (cβ : ℝ≥0∞) • coordsHaar S) {f : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℝ≥0∞}
    {fbar : Coords S → ℝ≥0∞} (hfbar : Measurable fbar) (hdesc : ∀ x ∈ explicitRows S, f x = fbar (coordsOf S x))
    {φ : Fin 3 → InfiniteAdeleRing ℚ → ℝ≥0} (hφ : ∀ i, φ i ∈ smoothFamily archCoord)
    {V : ∀ k : Fin 3 × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)} (hV : ∀ k, V k ∈ localCompactOpens k.2.1) :
    ∫⁻ x in explicitRows S, boxTest φ V (coordsOf S x) * (intOff S).indicator (fun _ => (1 : ℝ≥0∞)) x * f x ∂rowHaar =
      cβ * ∫⁻ y, boxTest φ V y * (nonzeroCoords S).indicator fbar y ∂coordsHaar S := by
  have hE : ∀ x ∈ explicitRows S,
      boxTest φ V (coordsOf S x) * (intOff S).indicator (fun _ => (1 : ℝ≥0∞)) x * f x =
        boxTest φ V (coordsOf S x) * fbar (coordsOf S x) := fun x hx => by
    have hZ : x ∈ intOff S := primOff_subset_intOff S ((mem_explicitRows_iff' S).1 hx).1
    simp only [indicator_of_mem hZ, mul_one, hdesc x hx]
  rw [setLIntegral_congr_fun (explicitRows_measurableSet S) hE,
    ← lintegral_map ((measurable_boxTest_coords S hφ hV).fun_mul hfbar) (measurable_coordsOf S)]
  have hres : rowHaar.restrict (explicitRows S) =
      (rowHaar.restrict (primOff S)).restrict (coordsOf S ⁻¹' nonzeroCoords S) := by
    rw [Measure.restrict_restrict (measurable_coordsOf S (measurableSet_nonzeroCoords S)), explicitRows_eq,
      inter_comm]
  rw [hres, ← Measure.restrict_map (measurable_coordsOf S) (measurableSet_nonzeroCoords S)]
  change ∫⁻ y in nonzeroCoords S, boxTest φ V y * fbar y ∂(pushed S (primOff S)) = _
  rw [hβ, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul,
    ← lintegral_indicator (measurableSet_nonzeroCoords S)]
  congr 1
  refine lintegral_congr fun y => ?_
  exact indicator_mul_right (nonzeroCoords S) (boxTest φ V) fbar

private theorem sigmaFinite_coordsHaar (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : SigmaFinite (coordsHaar S) :=
  inferInstance

attribute [local instance] sigmaFinite_coordsHaar

private theorem fibInt_ae_const (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {f : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℝ≥0∞} (hf : Measurable f)
    (hdesc : ∀ x ∈ explicitRows S, ∀ y ∈ explicitRows S, coordsOf S x = coordsOf S y → f x = f y)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hid : ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
      (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
        (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
        Φ = fun x => ∏ i, Φc i (x i)) ∧
      (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧ 0 < ∫ x, (Φ x).re ∂rowHaar →
      ∫⁻ x in explicitRows S, (‖Φ x‖₊ : ℝ≥0∞) * f x ∂rowHaar = C * ∫⁻ x, (‖Φ x‖₊ : ℝ≥0∞) ∂rowHaar) :
    ∃ C₁ : ℝ≥0∞, ∀ᵐ x ∂(rowHaar.restrict (explicitRows S)), f x = C₁ := by
  obtain ⟨cβ, hβ⟩ := pushed_eq_smul S (add_rowOf_mem_primOff_iff S) (primOff_subset_intOff S)
  obtain ⟨cγ, hγ⟩ := pushed_eq_smul S (add_rowOf_mem_intOff_iff S) subset_rfl

  set fbar : Coords S → ℝ≥0∞ := fun y => f (rowRep S y) with hfbar_def
  have hfbar : Measurable fbar := hf.comp (measurable_rowRep S)
  have hdesc' : ∀ x ∈ explicitRows S, f x = fbar (coordsOf S x) := fun x hx => by
    have hN : coordsOf S x ∈ nonzeroCoords S := ((mem_explicitRows_iff' S).1 hx).2
    exact hdesc x hx _ (rowRep_mem_explicitRows S hN) (coordsOf_rowRep S _).symm

  have hkey : ∀ (φ : Fin 3 → InfiniteAdeleRing ℚ → ℝ≥0) (V : ∀ k : Fin 3 × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)),
      (∀ i, φ i ∈ smoothFamily archCoord) → (∀ k, V k ∈ localCompactOpens k.2.1) →
      ∫⁻ y, boxTest φ V y * (cβ * (nonzeroCoords S).indicator fbar y) ∂coordsHaar S =
        ∫⁻ y, boxTest φ V y * (C * cγ) ∂coordsHaar S := fun φ V hφ hV => by
    have h := average_identity S f C hid hφ hV
    rw [setLIntegral_test_mul_eq S hβ hfbar hdesc' hφ hV, lintegral_test_eq S hγ hφ hV] at h
    rw [lintegral_congr fun y => mul_left_comm (boxTest φ V y) (cβ : ℝ≥0∞) ((nonzeroCoords S).indicator fbar y),
      lintegral_const_mul' _ _ ENNReal.coe_ne_top, lintegral_mul_const' _ _ (ENNReal.mul_ne_top hC ENNReal.coe_ne_top),
      h]
    ring
  have hfin : ∀ (φ : Fin 3 → InfiniteAdeleRing ℚ → ℝ≥0) (V : ∀ k : Fin 3 × {p // p ∈ S}, Set (k.2.1.adicCompletion ℚ)),
      (∀ i, φ i ∈ smoothFamily archCoord) → (∀ k, V k ∈ localCompactOpens k.2.1) →
      ∫⁻ y, boxTest φ V y * (C * cγ) ∂coordsHaar S ≠ ⊤ := fun φ V hφ hV => by
    rw [lintegral_mul_const' _ _ (ENNReal.mul_ne_top hC ENNReal.coe_ne_top)]
    exact ENNReal.mul_ne_top (lintegral_boxTest_ne_top S hφ hV) (ENNReal.mul_ne_top hC ENNReal.coe_ne_top)
  choose sQ hsQ hsQ_mono hsQ_univ using fun k : Fin 3 × {p // p ∈ S} => exists_localExhaustion k.2.1
  have hae : (fun y => (cβ : ℝ≥0∞) * (nonzeroCoords S).indicator fbar y) =ᵐ[coordsHaar S] fun _ => C * cγ :=
    ae_eq_of_boxTests (coordsHaar S) (u := fun y => (cβ : ℝ≥0∞) * (nonzeroCoords S).indicator fbar y)
      (w := fun _ => C * cγ) (measurable_const.mul (hfbar.indicator (measurableSet_nonzeroCoords S)))
      measurable_const archGenerators (archGenerate continuous_archCoord) archGenerators_piSystem archBalls
      archBalls_mem archBalls_mono archBalls_iUnion (fun k => localCompactOpens k.2.1) (fun k => localGenerate k.2.1)
      (fun k => localCompactOpens_piSystem k.2.1) sQ hsQ hsQ_mono hsQ_univ (smoothFamily archCoord)
      (fun _ hφ => smoothFamily_archCoord_measurable continuous_archCoord hφ)
      (fun _ hc => smoothFamily_approx archCoord hc) hkey hfin

  by_cases hcβ : cβ = 0
  · refine ⟨0, ?_⟩
    have hP : rowHaar (primOff S) = 0 := by
      have h := congrArg (fun m : Measure (Coords S) => m univ) hβ
      simp only [pushed, Measure.map_apply (measurable_coordsOf S) MeasurableSet.univ, preimage_univ,
        Measure.restrict_apply_univ, Measure.smul_apply, smul_eq_mul, hcβ, ENNReal.coe_zero, zero_mul] at h
      exact h
    have hE : rowHaar (explicitRows S) = 0 :=
      measure_mono_null (fun x hx => ((mem_explicitRows_iff' S).1 hx).1) hP
    rw [Measure.restrict_eq_zero.2 hE, ae_zero]
    exact Filter.eventually_bot
  · refine ⟨C * cγ / cβ, ?_⟩
    set D : Set (Coords S) := {y | y ∈ nonzeroCoords S ∧ fbar y ≠ C * cγ / cβ} with hD_def
    have hDm : MeasurableSet D :=
      (measurableSet_nonzeroCoords S).inter (hfbar (measurableSet_singleton (C * cγ / cβ))).compl
    have hD : coordsHaar S D = 0 := by
      refine measure_mono_null (fun y hy => ?_) (ae_iff.1 hae)
      intro h
      have h' : (cβ : ℝ≥0∞) * fbar y = C * cγ := by
        have h0 : (cβ : ℝ≥0∞) * (nonzeroCoords S).indicator fbar y = C * cγ := h
        rwa [indicator_of_mem hy.1] at h0
      exact hy.2 ((ENNReal.eq_div_iff (ENNReal.coe_ne_zero.2 hcβ) ENNReal.coe_ne_top).2 h')
    have hnull : rowHaar (coordsOf S ⁻¹' D ∩ primOff S) = 0 := by
      have h := congrArg (fun m : Measure (Coords S) => m D) hβ
      simp only [pushed, Measure.map_apply (measurable_coordsOf S) hDm,
        Measure.restrict_apply (measurable_coordsOf S hDm), Measure.smul_apply, smul_eq_mul, hD, mul_zero] at h
      exact h
    rw [ae_iff, Measure.restrict_apply' (explicitRows_measurableSet S)]
    refine measure_mono_null (fun x hx => ?_) hnull
    obtain ⟨hx1, hx2⟩ := hx
    refine ⟨⟨((mem_explicitRows_iff' S).1 hx2).2, ?_⟩, ((mem_explicitRows_iff' S).1 hx2).1⟩
    rw [← hdesc' x hx2]
    exact hx1

private theorem unique_of_class_averages (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ν : Measure (MulAction.orbitRel.Quotient (WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic) ↥mirabolic))
    (s : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → AdelicGL 3 (𝓞 ℚ) ℚ)
    (himage : {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
      ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j} = explicitRows S)
    (hsK : ∀ x ∈ explicitRows S, ∀ p, p ∉ S → componentAt3 (𝓞 ℚ) ℚ p (s x) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    (hsS : ∀ x ∈ explicitRows S, ∀ y ∈ explicitRows S, ∀ p ∈ S, (∀ j, evalHom p (x j) = evalHom p (y j)) →
      componentAt3 (𝓞 ℚ) ℚ p (s x) = componentAt3 (𝓞 ℚ) ℚ p (s y))
    (hsArch : ∀ x ∈ explicitRows S, ∀ y ∈ explicitRows S,
      (∀ j, AdelicLevel.adeleArch (𝓞 ℚ) ℚ (x j) = AdelicLevel.adeleArch (𝓞 ℚ) ℚ (y j)) →
      archComponent3 (𝓞 ℚ) ℚ (s x) = archComponent3 (𝓞 ℚ) ℚ (s y))
    (hmeas : ∀ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, Continuous F →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), F (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = F g) →
      letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
      Measurable fun x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ =>
        ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) ∂ν) :
    ∀ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, Continuous F →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), F (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = F g) →
      (∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) F) → ∀ C : ℝ≥0∞, C ≠ ⊤ →
      (∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
          ∫⁻ x in {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j},
              (‖Φ x‖₊ : ℝ≥0∞) *
                ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) ∂ν
              ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) =
            C * ∫⁻ x, (‖Φ x‖₊ : ℝ≥0∞)
              ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))) →
      ∃ C₁ : ℝ≥0∞,
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
          ∀ᵐ x ∂((Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).restrict
              {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j}),
            ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2)
              ∂ν = C₁) := by
  intro F hF haut hinv C hC hid
  rw [himage] at hid ⊢
  exact fibInt_ae_const S (hmeas F hF haut)
    (fun x hx y hy hxy => fibInt_eq_of_coordsOf_eq S ν s hsK hsS hsArch hF hinv hx hy hxy) C hC hid

end UniquenessHead

end UniquenessPrinciple

section Assembly

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

attribute [local instance] NumberField.AdeleRing.secondCountableTopology

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

attribute [local instance] secondCountableTopology_adelicGL3 isMulRightInvariant_adelicGLHaar

attribute [local instance] WhittakerBlock.isHaarMeasure_unipotentHaar3

attribute [local instance] WhittakerBlock.isMulRightInvariant_unipotentHaar3

private abbrev prodPins : AutomorphicForm.CarrierPins ℚ :=
  productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)

private abbrev unipInMirabolic : Subgroup ↥mirabolic := WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic

private theorem coe_mem_unipotent_of_mem {n : ↥mirabolic} (hn : n ∈ unipInMirabolic) :
    ((n : ↥mirabolic) : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ WhittakerBlock.unipotentSubgroup3 :=
  Subgroup.mem_subgroupOf.1 hn

private scoped instance locallyCompactSpace_mirabolic : LocallyCompactSpace ↥mirabolic :=
  isClosed_mirabolic.locallyCompactSpace

private abbrev fibreHaar : Measure ↥mirabolic := (Measure.haar : Measure ↥mirabolic).inv

private def fibreWeight (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (p : ↥mirabolic) : ℝ≥0∞ :=
  HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3 (p : AdelicGL 3 (𝓞 ℚ) ℚ) *
    {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g}.indicator (fun _ => (1 : ℝ≥0∞)) (p : AdelicGL 3 (𝓞 ℚ) ℚ)

private def fibreMeasure₀ (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    Measure (MulAction.orbitRel.Quotient (WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic) ↥mirabolic) :=
  Measure.map Quotient.mk'' (fibreHaar.withDensity (fibreWeight S))

private def fibreMeasure (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (c : ℝ≥0∞) :
    Measure (MulAction.orbitRel.Quotient (WhittakerBlock.unipotentSubgroup3.subgroupOf mirabolic) ↥mirabolic) :=
  c • fibreMeasure₀ S

open scoped Classical in

private def sectionMap (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) : AdelicGL 3 (𝓞 ℚ) ℚ :=
  if x ∈ explicitRows S then sec0 x else 1

private abbrev productionFibration : Measure (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  fibMeasure mirabolic sec0 modulus (weightedMeasure fibreHaar fun p : ↥mirabolic => modulus (p : AdelicGL 3 (𝓞 ℚ) ℚ))
    rowHaar rowDomain

private scoped instance sigmaCompactSpace_mirabolic : SigmaCompactSpace ↥mirabolic :=
  isClosed_mirabolic.sigmaCompactSpace

private abbrev fibreModulus (p : ↥mirabolic) : ℝ≥0∞ := modulus (p : AdelicGL 3 (𝓞 ℚ) ℚ)

private theorem measurable_fibreModulus : Measurable fibreModulus :=
  measurable_modulus.comp measurable_subtype_coe

private theorem fibreModulus_mul (p q : ↥mirabolic) : fibreModulus (p * q) = fibreModulus p * fibreModulus q :=
  modulus_mul _ _

private theorem bottomRow_coe_mul (p : ↥mirabolic) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    bottomRow ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * g) = bottomRow g :=
  bottomRow_mul_of_mem p.2 g

private theorem bottomRow_mul_eq (g h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    bottomRow (g * h) = bottomRow g ᵥ* (h : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) := by
  rw [bottomRow_mul]
  rfl

private theorem vecMul_mem_rowDomain_iff (x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    x ᵥ* (h : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) ∈ rowDomain ↔ x ∈ rowDomain := by
  refine ⟨fun hx => ?_, fun hx => vecMul_mem_rowDomain hx h⟩
  have := vecMul_mem_rowDomain hx h⁻¹
  rwa [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one] at this

private theorem fibre_shift (p₁ : ↥mirabolic) (F : ↥mirabolic → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ p, F (p * p₁) ∂(weightedMeasure fibreHaar fibreModulus) =
      fibreModulus p₁ * ∫⁻ p, F p ∂(weightedMeasure fibreHaar fibreModulus) :=
  lintegral_mul_right_weightedMeasure fibreHaar measurable_fibreModulus fibreModulus_mul (fun _ => modulus_ne_zero _)
    (fun _ => modulus_ne_top _) p₁ hF

private theorem row_shift (h : AdelicGL 3 (𝓞 ℚ) ℚ) (Ψ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ x, Ψ (x ᵥ* (h : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) ∂rowHaar = (modulus h)⁻¹ * ∫⁻ x, Ψ x ∂rowHaar :=
  lintegral_vecMul_rowHaar h Ψ hΨ

private theorem isMulRightInvariant_productionFibration : productionFibration.IsMulRightInvariant :=
  isMulRightInvariant_fibMeasure mirabolic bottomRow
    (fun x h => x ᵥ* (h : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) measurable_sec0 measurable_modulus
    (weightedMeasure fibreHaar fibreModulus) rowHaar measurableSet_rowDomain bottomRow_mul_eq
    (fun a b hab => (mul_inv_mem_mirabolic_iff a b).2 hab) (fun _ hx => bottomRow_sec0 hx) vecMul_mem_rowDomain_iff
    modulus_mul modulus_inv modulus_ne_zero modulus_ne_top (fun p₁ F hF => fibre_shift p₁ F hF) row_shift

private theorem continuous_fibreModulus : Continuous fibreModulus :=
  continuous_ofReal_ideleNorm_det.comp continuous_subtype_val

private theorem isFiniteMeasureOnCompacts_weighted {C : Set ↥mirabolic} (hC : IsCompact C) :
    weightedMeasure fibreHaar fibreModulus C < ⊤ := by
  obtain ⟨m, hm0, hmC⟩ := exists_ne_zero_le_on_of_isCompact continuous_fibreModulus (fun _ => modulus_ne_zero _) hC
  unfold weightedMeasure
  rw [withDensity_apply _ hC.isClosed.measurableSet]
  calc ∫⁻ p in C, (fibreModulus p)⁻¹ ∂fibreHaar ≤ ∫⁻ _ in C, m⁻¹ ∂fibreHaar :=
        setLIntegral_mono' hC.isClosed.measurableSet fun p hp => ENNReal.inv_le_inv.2 (hmC p hp)
    _ = m⁻¹ * fibreHaar C := setLIntegral_const C m⁻¹
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hm0)) hC.measure_lt_top

private theorem isFiniteMeasureOnCompacts_productionFibration : IsFiniteMeasureOnCompacts productionFibration := by
  haveI : IsFiniteMeasureOnCompacts (rowHaar : Measure (Fin 3 → AdeleRing (𝓞 ℚ) ℚ)) :=
    isFiniteMeasureOnCompacts_rowHaar
  refine ⟨fun {K} hK => lt_top_iff_ne_top.2 ?_⟩
  obtain ⟨m, hm0, hmK⟩ := exists_ne_zero_le_on_of_isCompact continuous_ofReal_ideleNorm_det
    (fun g => modulus_ne_zero g) hK
  refine fibMeasure_ne_top mirabolic bottomRow measurable_sec0 measurable_modulus
    (weightedMeasure fibreHaar fibreModulus) rowHaar measurableSet_rowDomain bottomRow_coe_mul
    (fun a b hab => (mul_inv_mem_mirabolic_iff a b).2 hab)
    (fun x hx => bottomRow_sec0 hx) modulus_mul modulus_inv modulus_ne_zero modulus_ne_top
    (fun p₁ F hF => fibre_shift p₁ F hF) hK.isClosed.measurableSet
    (isCompact_image_bottomRow hK).isClosed.measurableSet
    (isCompact_image_bottomRow hK).measure_lt_top.ne (fun k hk => Set.mem_image_of_mem _ hk)
    (isCompact_preimage_mirabolic (isCompact_mul_inv hK)).isClosed.measurableSet ?_
    (fun k₁ hk₁ k₂ hk₂ q hq => mem_preimage_mul_inv_of_mem hk₁ hk₂ q hq) hm0 hmK
  exact (isFiniteMeasureOnCompacts_weighted (isCompact_preimage_mirabolic (isCompact_mul_inv hK))).ne

private theorem weighted_univ_ne_zero : weightedMeasure fibreHaar fibreModulus Set.univ ≠ 0 := by
  unfold weightedMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  intro h
  rw [lintegral_eq_zero_iff (show Measurable fun p => (fibreModulus p)⁻¹ from measurable_fibreModulus.inv)] at h
  have h2 : ∀ᵐ p ∂(fibreHaar : Measure ↥mirabolic), False :=
    h.mono fun p hp => ENNReal.inv_ne_zero.2 (modulus_ne_top _) (by simpa using hp)
  have hu : (fibreHaar : Measure ↥mirabolic) Set.univ ≠ 0 := by
    show (Measure.haar : Measure ↥mirabolic).inv Set.univ ≠ 0
    rw [Measure.inv_apply, Set.inv_univ]
    exact isOpen_univ.measure_ne_zero _ Set.univ_nonempty
  exact hu (by simpa using ae_iff.1 h2)

private theorem rowHaar_rowDomain_pos : 0 < rowHaar rowDomain :=
  (pos_rowHaar_inter_explicitRows ∅ Filter.univ_mem).trans_le
    (measure_mono fun _ hx => explicitRows_subset_rowDomain ∅ hx.2)

private theorem productionFibration_ne_zero : productionFibration ≠ 0 := by
  intro h
  have h1 : ∫⁻ _ : AdelicGL 3 (𝓞 ℚ) ℚ, (1 : ℝ≥0∞) ∂productionFibration = 0 := by rw [h, lintegral_zero_measure]
  rw [lintegral_fibMeasure mirabolic measurable_sec0 measurable_modulus _ rowHaar rowDomain measurable_const] at h1
  simp only [lintegral_const, one_mul] at h1
  have hm : Measurable fun x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ =>
      (modulus (sec0 x))⁻¹ * weightedMeasure fibreHaar fibreModulus Set.univ :=
    (measurable_modulus.comp measurable_sec0).inv.mul_const _
  have h2 := (ae_restrict_iff' measurableSet_rowDomain).1 ((lintegral_eq_zero_iff hm).1 h1)
  have hall : ∀ x, (modulus (sec0 x))⁻¹ * weightedMeasure fibreHaar fibreModulus Set.univ ≠ 0 := fun x =>
    mul_ne_zero (ENNReal.inv_ne_zero.2 (modulus_ne_top _)) weighted_univ_ne_zero
  have h3 := ae_iff.1 h2
  have hnull : rowHaar rowDomain = 0 := by
    refine measure_mono_null (fun x hxD => ?_) h3
    intro himp
    exact hall x (by simpa using himp hxD)
  exact rowHaar_rowDomain_pos.ne' hnull

private theorem exists_fibration_eq_smul_haar :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      productionFibration = c • NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ := by
  haveI := isMulRightInvariant_productionFibration
  haveI := isFiniteMeasureOnCompacts_productionFibration
  exact exists_ne_zero_and_eq_smul_of_isMulRightInvariant productionFibration
    (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) productionFibration_ne_zero

private theorem shellCond_one (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : ShellCond S 1 := by
  intro p _
  refine ⟨0, 0, 0, 1, Subgroup.one_mem _, ?_⟩
  rw [map_one, mul_one]
  ext i j
  simp [Matrix.one_apply]

private theorem shellCond_sec0 (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ}
    (hx : x ∈ explicitRows S) : ShellCond S (sec0 x) := by
  have hK : ∀ p, p ∉ S → componentAt3 (𝓞 ℚ) ℚ p (sec0 x) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p := fun p hp =>
    componentAt3_sec0_mem (explicitRows_subset_rowDomain S hx) (hx.1 p hp)
  have := (shellCond_mul_right_iff S 1 (sec0 x) hK).2 (shellCond_one S)
  rwa [one_mul] at this

private theorem shellCond_coe_mul_sec0_iff (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ}
    (hx : x ∈ explicitRows S) (p : ↥mirabolic) :
    ShellCond S ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * sec0 x) ↔ ShellCond S (p : AdelicGL 3 (𝓞 ℚ) ℚ) :=
  shellCond_mul_right_iff S _ _ fun q hq => componentAt3_sec0_mem (explicitRows_subset_rowDomain S hx) (hx.1 q hq)

private theorem not_shellCond_of_notMem (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ}
    (hx : x ∈ rowDomain) (hxS : x ∉ explicitRows S) (p : ↥mirabolic) :
    ¬ ShellCond S ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * sec0 x) := by
  intro h
  have := bottomRow_mem_explicitRows_of_shellCond S h
  rw [bottomRow_coe_mul, bottomRow_sec0 hx] at this
  exact hxS this

private theorem image_eq_explicitRows (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
      ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j} = explicitRows S := by
  ext x
  constructor
  · rintro ⟨q, hq, hqx⟩
    rw [zerothShell_eq_setOf_shellCond] at hq
    have hrow : bottomRow q.out = x := funext hqx
    rw [← hrow]
    exact bottomRow_mem_explicitRows_of_shellCond S hq
  · intro hx
    refine ⟨Quotient.mk'' (sec0 x), ?_, ?_⟩
    · rw [zerothShell_eq_setOf_shellCond]
      show ShellCond S (Quotient.mk'' (sec0 x) : MulAction.orbitRel.Quotient WhittakerBlock.unipotentSubgroup3
        (AdelicGL 3 (𝓞 ℚ) ℚ)).out
      rw [prop_out_mk_iff (shellCond_mul_left_iff S)]
      exact shellCond_sec0 S hx
    · intro j
      have hb : bottomRow (Quotient.mk'' (sec0 x) : MulAction.orbitRel.Quotient WhittakerBlock.unipotentSubgroup3
          (AdelicGL 3 (𝓞 ℚ) ℚ)).out = bottomRow (sec0 x) :=
        apply_out_mk (fun n hn g => bottomRow_mul_of_mem (unipotentSubgroup3_le_mirabolic hn) g) (sec0 x)
      rw [bottomRow_sec0 (explicitRows_subset_rowDomain S hx)] at hb
      exact congrFun hb j

private theorem tendsto_sectionMap (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    Filter.Tendsto (sectionMap S) (nhds e₃) (nhds 1) := by
  intro U hU
  have hV : sec0 ⁻¹' U ∈ nhdsWithin e₃ (explicitRows S) := tendsto_sec0 S hU
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hV
  obtain ⟨V, hVn, hVU⟩ := hV
  have h1 : (1 : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ U := mem_of_mem_nhds hU
  rw [Filter.mem_map]
  filter_upwards [hVn] with x hx
  show sectionMap S x ∈ U
  unfold sectionMap
  split_ifs with hxS
  · exact hVU ⟨hx, hxS⟩
  · exact h1

private theorem sectionMap_of_mem (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ}
    (hx : x ∈ explicitRows S) : sectionMap S x = sec0 x := by
  unfold sectionMap
  rw [if_pos hx]

private theorem measurable_fibreWeight (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : Measurable (fibreWeight S) := by
  unfold fibreWeight
  refine Measurable.mul ?_ ?_
  · exact (measurable_density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.isClosed_unipotentSubgroup3
      WhittakerBlock.unipotentHaar3).comp measurable_subtype_coe
  · exact (measurable_const.indicator (measurableSet_shellCond S)).comp measurable_subtype_coe

private theorem nnnorm_W_mul {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hWinv : ∀ n ∈ WhittakerBlock.unipotentSubgroup3, ∀ g, ‖W (n * g)‖ = ‖W g‖) {n : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hn : n ∈ WhittakerBlock.unipotentSubgroup3) (g : AdelicGL 3 (𝓞 ℚ) ℚ) : ‖W (n * g)‖₊ = ‖W g‖₊ :=
  NNReal.eq (by rw [coe_nnnorm, coe_nnnorm]; exact hWinv n hn g)

private theorem lintegral_fibreMeasure (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (c : ℝ≥0∞) {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hWc : Continuous W) (hWinv : ∀ n ∈ WhittakerBlock.unipotentSubgroup3, ∀ g, ‖W (n * g)‖ = ‖W g‖)
    (h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∫⁻ q, ((‖W ((q.out : AdelicGL 3 (𝓞 ℚ) ℚ) * h)‖₊ : ℝ≥0∞) ^ 2) ∂(fibreMeasure S c) =
      c * ∫⁻ p : ↥mirabolic, fibreWeight S p * (‖W ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * h)‖₊ : ℝ≥0∞) ^ 2 ∂fibreHaar := by
  have hmeas : Measurable fun p : ↥mirabolic => (‖W ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * h)‖₊ : ℝ≥0∞) ^ 2 :=
    ((hWc.comp (continuous_subtype_val.mul continuous_const)).measurable.nnnorm.coe_nnreal_ennreal).pow_const 2
  have hinv : ∀ (n : ↥unipInMirabolic) (p : ↥mirabolic),
      (fun p : ↥mirabolic => (‖W ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * h)‖₊ : ℝ≥0∞) ^ 2) ((n : ↥mirabolic) * p) =
        (fun p : ↥mirabolic => (‖W ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * h)‖₊ : ℝ≥0∞) ^ 2) p := by
    intro n p
    simp only [Subgroup.coe_mul, mul_assoc]
    rw [nnnorm_W_mul hWinv (coe_mem_unipotent_of_mem n.2)]
  unfold fibreMeasure fibreMeasure₀
  rw [lintegral_smul_measure, smul_eq_mul,
    lintegral_out_map_mk unipInMirabolic (fibreHaar.withDensity (fibreWeight S)) hmeas hinv,
    lintegral_withDensity_eq_lintegral_mul fibreHaar (measurable_fibreWeight S) hmeas]
  rfl

private theorem measurable_fibreIntegral_sectionMap (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (c : ℝ≥0∞)
    {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hWc : Continuous W) (hWinv : ∀ n ∈ WhittakerBlock.unipotentSubgroup3, ∀ g, ‖W (n * g)‖ = ‖W g‖) :
    Measurable fun x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ =>
      ∫⁻ q, ((‖W ((q.out : AdelicGL 3 (𝓞 ℚ) ℚ) * sectionMap S x)‖₊ : ℝ≥0∞) ^ 2) ∂(fibreMeasure S c) := by
  simp_rw [lintegral_fibreMeasure S c hWc hWinv]
  refine Measurable.const_mul ?_ c
  have hsec : Measurable (sectionMap S) := by
    unfold sectionMap
    exact Measurable.ite (measurableSet_explicitRows S) measurable_sec0 measurable_const
  refine Measurable.lintegral_prod_right' (f := fun z : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) × ↥mirabolic =>
    fibreWeight S z.2 * (‖W ((z.2 : AdelicGL 3 (𝓞 ℚ) ℚ) * sectionMap S z.1)‖₊ : ℝ≥0∞) ^ 2) ?_
  refine ((measurable_fibreWeight S).comp measurable_snd).mul ?_
  refine Measurable.pow_const ?_ 2
  refine Measurable.coe_nnreal_ennreal (Measurable.nnnorm ?_)
  exact hWc.measurable.comp ((measurable_subtype_coe.comp measurable_snd).mul (hsec.comp measurable_fst))

private theorem integrand_one_eq (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    integrand W Φ 1 g = (‖W g‖₊ : ℝ≥0∞) ^ 2 * (‖Φ (bottomRow g)‖₊ : ℝ≥0∞) * modulus g := by
  simp only [integrand, Real.rpow_one]
  rfl

private abbrev blockIntegrand (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) : ℝ≥0∞ :=
  HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3 g *
    {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g}.indicator (integrand W Φ 1) g

private theorem measurable_blockIntegrand (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hWc : Continuous W) {Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ} (hΦ : Continuous Φ) :
    Measurable (blockIntegrand S W Φ) :=
  (measurable_density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.isClosed_unipotentSubgroup3
    WhittakerBlock.unipotentHaar3).mul ((measurable_integrand hWc hΦ 1).indicator (measurableSet_shellCond S))

private theorem row_value (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hWc : Continuous W)
    {Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ} (hΦ : Continuous Φ) {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ} (hx : x ∈ rowDomain) :
    (modulus (sec0 x))⁻¹ *
        ∫⁻ p : ↥mirabolic, blockIntegrand S W Φ ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * sec0 x)
          ∂(weightedMeasure fibreHaar fibreModulus) =
      (explicitRows S).indicator (fun x => (‖Φ x‖₊ : ℝ≥0∞) *
        ∫⁻ p : ↥mirabolic, HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
            ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * sec0 x) *
          {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g}.indicator (fun _ => (1 : ℝ≥0∞)) (p : AdelicGL 3 (𝓞 ℚ) ℚ) *
          (‖W ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * sec0 x)‖₊ : ℝ≥0∞) ^ 2 ∂fibreHaar) x := by
  have hmeas : Measurable fun p : ↥mirabolic => blockIntegrand S W Φ ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * sec0 x) :=
    (measurable_blockIntegrand S hWc hΦ).comp (measurable_subtype_coe.mul_const _)
  unfold weightedMeasure
  rw [lintegral_withDensity_eq_lintegral_mul fibreHaar
    (show Measurable fun p => (fibreModulus p)⁻¹ from measurable_fibreModulus.inv) hmeas]
  by_cases hxS : x ∈ explicitRows S
  · rw [Set.indicator_of_mem hxS]
    have hpt : ∀ p : ↥mirabolic,
        ((fun p : ↥mirabolic => (fibreModulus p)⁻¹) * fun p : ↥mirabolic =>
            blockIntegrand S W Φ ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * sec0 x)) p =
          ((‖Φ x‖₊ : ℝ≥0∞) * modulus (sec0 x)) *
            (HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
                ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * sec0 x) *
              {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g}.indicator (fun _ => (1 : ℝ≥0∞)) (p : AdelicGL 3 (𝓞 ℚ) ℚ) *
              (‖W ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * sec0 x)‖₊ : ℝ≥0∞) ^ 2) := by
      intro p
      simp only [Pi.mul_apply, blockIntegrand]
      by_cases hp : ShellCond S (p : AdelicGL 3 (𝓞 ℚ) ℚ)
      · have hp' : ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * sec0 x) ∈ {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} :=
          (shellCond_coe_mul_sec0_iff S hxS p).2 hp
        rw [Set.indicator_of_mem hp', Set.indicator_of_mem (show (p : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ _ from hp),
          integrand_one_eq, bottomRow_coe_mul, bottomRow_sec0 hx, modulus_mul]
        have hcancel : (fibreModulus p)⁻¹ * modulus (p : AdelicGL 3 (𝓞 ℚ) ℚ) = 1 :=
          ENNReal.inv_mul_cancel (modulus_ne_zero _) (modulus_ne_top _)
        calc (fibreModulus p)⁻¹ *
              (HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
                  ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * sec0 x) *
                ((‖W ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * sec0 x)‖₊ : ℝ≥0∞) ^ 2 * (‖Φ x‖₊ : ℝ≥0∞) *
                  (modulus (p : AdelicGL 3 (𝓞 ℚ) ℚ) * modulus (sec0 x))))
            = ((fibreModulus p)⁻¹ * modulus (p : AdelicGL 3 (𝓞 ℚ) ℚ)) * (((‖Φ x‖₊ : ℝ≥0∞) * modulus (sec0 x)) *
                (HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
                    ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * sec0 x) * 1 *
                  (‖W ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * sec0 x)‖₊ : ℝ≥0∞) ^ 2)) := by ring
          _ = _ := by rw [hcancel, one_mul]
      · have hp' : ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * sec0 x) ∉ {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g} :=
          fun h => hp ((shellCond_coe_mul_sec0_iff S hxS p).1 h)
        rw [Set.indicator_of_notMem hp', Set.indicator_of_notMem (show (p : AdelicGL 3 (𝓞 ℚ) ℚ) ∉ _ from hp)]
        simp
    simp_rw [hpt]
    have hImeas : Measurable fun p : ↥mirabolic =>
        HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
            ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * sec0 x) *
          {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g}.indicator (fun _ => (1 : ℝ≥0∞)) (p : AdelicGL 3 (𝓞 ℚ) ℚ) *
          (‖W ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * sec0 x)‖₊ : ℝ≥0∞) ^ 2 :=
      (((measurable_density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.isClosed_unipotentSubgroup3
          WhittakerBlock.unipotentHaar3).comp (measurable_subtype_coe.mul_const _)).mul
        ((measurable_const.indicator (measurableSet_shellCond S)).comp measurable_subtype_coe)).mul
        (((hWc.comp (continuous_subtype_val.mul continuous_const)).measurable.nnnorm.coe_nnreal_ennreal).pow_const 2)
    rw [lintegral_const_mul _ hImeas]
    set I := ∫⁻ p : ↥mirabolic, HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
        ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * sec0 x) *
      {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g}.indicator (fun _ => (1 : ℝ≥0∞)) (p : AdelicGL 3 (𝓞 ℚ) ℚ) *
      (‖W ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * sec0 x)‖₊ : ℝ≥0∞) ^ 2 ∂fibreHaar
    calc (modulus (sec0 x))⁻¹ * ((‖Φ x‖₊ : ℝ≥0∞) * modulus (sec0 x) * I)
        = ((modulus (sec0 x))⁻¹ * modulus (sec0 x)) * ((‖Φ x‖₊ : ℝ≥0∞) * I) := by ring
      _ = (‖Φ x‖₊ : ℝ≥0∞) * I := by rw [ENNReal.inv_mul_cancel (modulus_ne_zero _) (modulus_ne_top _), one_mul]
  · rw [Set.indicator_of_notMem hxS]
    have hzero : ∀ p : ↥mirabolic,
        ((fun p : ↥mirabolic => (fibreModulus p)⁻¹) * fun p : ↥mirabolic =>
            blockIntegrand S W Φ ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * sec0 x)) p = 0 := by
      intro p
      simp only [Pi.mul_apply, blockIntegrand]
      rw [Set.indicator_of_notMem (not_shellCond_of_notMem S hx hxS p)]
      simp
    simp_rw [hzero]
    simp

private scoped instance locallyCompactSpace_unipotent : LocallyCompactSpace ↥WhittakerBlock.unipotentSubgroup3 :=
  WhittakerBlock.isClosed_unipotentSubgroup3.locallyCompactSpace

private scoped instance sigmaCompactSpace_unipotent : SigmaCompactSpace ↥WhittakerBlock.unipotentSubgroup3 :=
  WhittakerBlock.isClosed_unipotentSubgroup3.sigmaCompactSpace

private theorem unipotentHaar3_inv_eq_self : WhittakerBlock.unipotentHaar3.inv = WhittakerBlock.unipotentHaar3 := by
  set μ := WhittakerBlock.unipotentHaar3
  have hne : μ.inv ≠ 0 := by
    intro h
    have hu : μ.inv Set.univ ≠ 0 := by
      rw [Measure.inv_apply, Set.inv_univ]
      exact isOpen_univ.measure_ne_zero μ Set.univ_nonempty
    exact hu (by rw [h, Measure.coe_zero, Pi.zero_apply])
  haveI : SecondCountableTopology ↥WhittakerBlock.unipotentSubgroup3 :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  obtain ⟨c, -, -, hc⟩ := exists_ne_zero_and_eq_smul_of_isMulRightInvariant μ.inv μ hne
  have hsq : μ = (c ^ 2) • μ := by
    calc μ = μ.inv.inv := (Measure.inv_inv μ).symm
      _ = (c • μ).inv := by rw [hc]
      _ = c • μ.inv := by rw [Measure.inv_def, Measure.inv_def, Measure.map_smul]
      _ = c • (c • μ) := by rw [← hc, hc]
      _ = (c ^ 2) • μ := by rw [smul_smul, pow_two]
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts ↥WhittakerBlock.unipotentSubgroup3) := inferInstance
  have hK0 : μ K ≠ 0 := (Measure.measure_pos_of_nonempty_interior (μ := μ) K.interior_nonempty).ne'
  have hKtop : μ K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have hc2 : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [one_pow, one_mul, hsq]
    rw [Measure.smul_apply, smul_eq_mul]
  have hc1 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective ((ENNReal.mul_left_inj hK0 hKtop).1 hc2)
  rw [hc, hc1, one_smul]

private theorem lintegral_inv_unipotentHaar3 (f : ↥WhittakerBlock.unipotentSubgroup3 → ℝ≥0∞) :
    ∫⁻ x, f x⁻¹ ∂WhittakerBlock.unipotentHaar3 = ∫⁻ x, f x ∂WhittakerBlock.unipotentHaar3 := by
  haveI : WhittakerBlock.unipotentHaar3.IsInvInvariant := ⟨unipotentHaar3_inv_eq_self⟩
  exact lintegral_inv_eq_self f

private theorem fibreHaar_mul_left_invariant (n : ↥mirabolic)
    (hn : (n : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ WhittakerBlock.unipotentSubgroup3) (F : ↥mirabolic → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ p, F (n * p) ∂fibreHaar = ∫⁻ p, F p ∂fibreHaar := by
  rw [← lintegral_map hF (measurable_const_mul n), map_mul_left_haar_inv_mirabolic n hn]

private theorem density_trade (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hWc : Continuous W)
    (hWinv : ∀ n ∈ WhittakerBlock.unipotentSubgroup3, ∀ g, ‖W (n * g)‖ = ‖W g‖) (h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∫⁻ p : ↥mirabolic, HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
          ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * h) *
        {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g}.indicator (fun _ => (1 : ℝ≥0∞)) (p : AdelicGL 3 (𝓞 ℚ) ℚ) *
        (‖W ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * h)‖₊ : ℝ≥0∞) ^ 2 ∂fibreHaar =
      ∫⁻ p : ↥mirabolic, fibreWeight S p * (‖W ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * h)‖₊ : ℝ≥0∞) ^ 2 ∂fibreHaar := by
  set φ : ↥mirabolic → ℝ≥0∞ := fun p =>
    {g : AdelicGL 3 (𝓞 ℚ) ℚ | ShellCond S g}.indicator (fun _ => (1 : ℝ≥0∞)) (p : AdelicGL 3 (𝓞 ℚ) ℚ) *
      (‖W ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * h)‖₊ : ℝ≥0∞) ^ 2 with hφ_def
  have hφm : Measurable φ :=
    ((measurable_const.indicator (measurableSet_shellCond S)).comp measurable_subtype_coe).mul
      (((hWc.comp (continuous_subtype_val.mul continuous_const)).measurable.nnnorm.coe_nnreal_ennreal).pow_const 2)
  have hφinv : ∀ n : ↥mirabolic, (n : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ WhittakerBlock.unipotentSubgroup3 →
      ∀ p, φ (n * p) = φ p := by
    intro n hn p
    simp only [hφ_def, Subgroup.coe_mul]
    congr 1
    · by_cases hp : ShellCond S (p : AdelicGL 3 (𝓞 ℚ) ℚ)
      · rw [Set.indicator_of_mem (show (n : AdelicGL 3 (𝓞 ℚ) ℚ) * p ∈ _ from (shellCond_mul_left_iff S _ hn _).2 hp),
          Set.indicator_of_mem (show (p : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ _ from hp)]
      · rw [Set.indicator_of_notMem (show (n : AdelicGL 3 (𝓞 ℚ) ℚ) * p ∉ _ from
            fun h' => hp ((shellCond_mul_left_iff S _ hn _).1 h')),
          Set.indicator_of_notMem (show (p : AdelicGL 3 (𝓞 ℚ) ℚ) ∉ _ from hp)]
    · rw [mul_assoc, nnnorm_W_mul hWinv hn]
  have hδ₁m : Measurable fun g : AdelicGL 3 (𝓞 ℚ) ℚ =>
      HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3 (g * h) :=
    (measurable_density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.isClosed_unipotentSubgroup3
      WhittakerBlock.unipotentHaar3).comp (measurable_mul_const h)
  have hδ₂m := measurable_density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.isClosed_unipotentSubgroup3
    WhittakerBlock.unipotentHaar3
  have hδ₁ : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ∫⁻ x : ↥WhittakerBlock.unipotentSubgroup3,
      HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
        ((x : AdelicGL 3 (𝓞 ℚ) ℚ) * g * h) ∂WhittakerBlock.unipotentHaar3 = 1 := by
    intro g
    simp only [mul_assoc]
    exact HaarQuotient.lintegral_density_mul_eq_one WhittakerBlock.unipotentSubgroup3
      WhittakerBlock.isClosed_unipotentSubgroup3 WhittakerBlock.unipotentHaar3 (g * h)
  have hδ₂ : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ∫⁻ x : ↥WhittakerBlock.unipotentSubgroup3,
      HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
        ((x : AdelicGL 3 (𝓞 ℚ) ℚ) * g) ∂WhittakerBlock.unipotentHaar3 = 1 := fun g =>
    HaarQuotient.lintegral_density_mul_eq_one WhittakerBlock.unipotentSubgroup3
      WhittakerBlock.isClosed_unipotentSubgroup3 WhittakerBlock.unipotentHaar3 g
  have key := lintegral_mul_density_eq WhittakerBlock.unipotentHaar3 fibreHaar unipotentSubgroup3_le_mirabolic
    (fun n hn F hF => fibreHaar_mul_left_invariant n hn F hF) lintegral_inv_unipotentHaar3 hδ₁m hδ₂m hδ₁ hδ₂ hφm hφinv
  calc _ = ∫⁻ p : ↥mirabolic,
          φ p * HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
            ((p : AdelicGL 3 (𝓞 ℚ) ℚ) * h) ∂fibreHaar := by
        refine lintegral_congr fun p => ?_
        simp only [hφ_def]
        ring
    _ = ∫⁻ p : ↥mirabolic, φ p * HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
            (p : AdelicGL 3 (𝓞 ℚ) ℚ) ∂fibreHaar := key
    _ = _ := by
        refine lintegral_congr fun p => ?_
        simp only [hφ_def, fibreWeight]
        ring

private theorem haar_eq_inv_smul_fibration {c : ℝ≥0∞} (hc0 : c ≠ 0) (hctop : c ≠ ⊤)
    (hc : productionFibration = c • NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) :
    NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ = c⁻¹ • productionFibration := by
  rw [hc, smul_smul, ENNReal.inv_mul_cancel hc0 hctop, one_smul]

private theorem block_formula (S : Finset (HeightOneSpectrum (𝓞 ℚ))) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hctop : c ≠ ⊤)
    (hc : productionFibration = c • NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hWc : Continuous (whittaker3 prodPins NumberField.StandardAddChar.psiQ F))
    (hWinv : ∀ n ∈ WhittakerBlock.unipotentSubgroup3, ∀ g,
      ‖whittaker3 prodPins NumberField.StandardAddChar.psiQ F (n * g)‖ =
        ‖whittaker3 prodPins NumberField.StandardAddChar.psiQ F g‖)
    {Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ} (hΦ : Continuous Φ) :
    WhittakerBlock.block prodPins NumberField.StandardAddChar.psiQ F Φ 1 S =
      ∫⁻ x in explicitRows S, (‖Φ x‖₊ : ℝ≥0∞) *
        ∫⁻ q, ((‖whittaker3 prodPins NumberField.StandardAddChar.psiQ F
          ((q.out : AdelicGL 3 (𝓞 ℚ) ℚ) * sectionMap S x)‖₊ : ℝ≥0∞) ^ 2) ∂(fibreMeasure S c⁻¹) ∂rowHaar := by
  set W := whittaker3 prodPins NumberField.StandardAddChar.psiQ F with hW_def
  rw [block_eq_lintegral_density_mul prodPins NumberField.StandardAddChar.psiQ F Φ 1 S (ShellCond S)
    (zerothShell_eq_setOf_shellCond S) (measurableSet_shellCond S) (shellCond_mul_left_iff S)
    (measurable_integrand hWc hΦ 1) (fun n hn g => integrand_mul_left hWinv Φ 1 n hn g)]
  rw [haar_eq_inv_smul_fibration hc0 hctop hc, lintegral_smul_measure, smul_eq_mul]
  rw [lintegral_fibMeasure mirabolic measurable_sec0 measurable_modulus _ rowHaar rowDomain
    (measurable_blockIntegrand S hWc hΦ)]
  rw [setLIntegral_congr_fun measurableSet_rowDomain fun x hx => row_value S hWc hΦ hx]
  rw [lintegral_indicator (measurableSet_explicitRows S), Measure.restrict_restrict (measurableSet_explicitRows S),
    Set.inter_eq_self_of_subset_left (explicitRows_subset_rowDomain S),
    ← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hc0)]
  refine setLIntegral_congr_fun (measurableSet_explicitRows S) fun x hx => ?_
  rw [sectionMap_of_mem S hx, lintegral_fibreMeasure S c⁻¹ hWc hWinv (sec0 x), density_trade S hWc hWinv (sec0 x)]
  ring

end Assembly

private theorem assembled
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    ∃ (P : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
      (ν : Measure (MulAction.orbitRel.Quotient (WhittakerBlock.unipotentSubgroup3.subgroupOf P) ↥P))
      (s : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → AdelicGL 3 (𝓞 ℚ) ℚ),
      (∀ F ∈ cuspFunctions ω a b Φ₀, ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
        WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ F Φ 1 S =
          (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
            ∫⁻ x in {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j},
              (‖Φ x‖₊ : ℝ≥0∞) *
                ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) ∂ν
              ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))) ∧
      (Filter.Tendsto s (nhds (fun j : Fin 3 => if j = 2 then (1 : AdeleRing (𝓞 ℚ) ℚ) else 0)) (nhds 1)) ∧
      (∀ O ∈ nhds (fun j : Fin 3 => if j = 2 then (1 : AdeleRing (𝓞 ℚ) ℚ) else 0),
      (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ;
        0 < (Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
              (O ∩ {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j}))) ∧
      (∀ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, Continuous F →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), F (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = F g) →
      (∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) F) → ∀ C : ℝ≥0∞, C ≠ ⊤ →
      (∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
          ∫⁻ x in {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j},
              (‖Φ x‖₊ : ℝ≥0∞) *
                ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) ∂ν
              ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) =
            C * ∫⁻ x, (‖Φ x‖₊ : ℝ≥0∞)
              ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))) →
      ∃ C₁ : ℝ≥0∞,
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
          ∀ᵐ x ∂((Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).restrict
              {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j}),
            ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2)
              ∂ν = C₁)) := by
  obtain ⟨c, hc0, hctop, hc⟩ := exists_fibration_eq_smul_haar
  refine ⟨mirabolic, fibreMeasure S c⁻¹, sectionMap S, ?_, tendsto_sectionMap S, ?_, ?_⟩
  · intro F hF Φ hΦ
    obtain ⟨⟨Φc, hΦc, -, rfl⟩, -, -⟩ := hΦ
    have hWc : Continuous (whittaker3 prodPins NumberField.StandardAddChar.psiQ F) :=
      continuous_whittaker3_productionPins _ NumberField.StandardAddChar.continuous_psiQ _ hF.2.1
    have hWinv := (whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul F
      ((mem_automorphicSubmodule_iff ω a b Φ₀ F).1 hF.1).1).2
    simp only [image_eq_explicitRows, whittaker3_translateRight]
    exact block_formula S hc0 hctop hc F hWc hWinv (continuous_prod_of_pureTensors hΦc)
  · intro O hO
    simp only [image_eq_explicitRows]
    exact pos_rowHaar_inter_explicitRows S hO
  · refine unique_of_class_averages S (fibreMeasure S c⁻¹) (sectionMap S) (image_eq_explicitRows S)
      (fun x hx p hp => ?_) (fun x hx y hy p _ hxy => ?_) (fun x hx y hy hxy => ?_) (fun F hFc hFaut => ?_)
    · rw [sectionMap_of_mem S hx]
      exact componentAt3_sec0_mem (explicitRows_subset_rowDomain S hx) (hx.1 p hp)
    · rw [sectionMap_of_mem S hx, sectionMap_of_mem S hy]
      exact componentAt3_sec0_congr (explicitRows_subset_rowDomain S hx) (explicitRows_subset_rowDomain S hy) p hxy
    · rw [sectionMap_of_mem S hx, sectionMap_of_mem S hy]
      exact archComponent3_sec0_congr (explicitRows_subset_rowDomain S hx) (explicitRows_subset_rowDomain S hy) hxy
    · have hWc : Continuous (whittaker3 prodPins NumberField.StandardAddChar.psiQ F) :=
        continuous_whittaker3_productionPins _ NumberField.StandardAddChar.continuous_psiQ _ hFc
      have hWinv := (whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul F hFaut).2
      simpa only [whittaker3_translateRight] using measurable_fibreIntegral_sectionMap S c⁻¹ hWc hWinv

section ConcreteFibreData

private def FibrationFacts
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (P : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
    (ν : Measure (MulAction.orbitRel.Quotient (WhittakerBlock.unipotentSubgroup3.subgroupOf P) ↥P))
    (s : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → AdelicGL 3 (𝓞 ℚ) ℚ) : Prop :=
      (∀ F ∈ cuspFunctions ω a b Φ₀, ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
        WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ F Φ 1 S =
          (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
            ∫⁻ x in {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j},
              (‖Φ x‖₊ : ℝ≥0∞) *
                ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) ∂ν
              ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))) ∧
      (Filter.Tendsto s (nhds (fun j : Fin 3 => if j = 2 then (1 : AdeleRing (𝓞 ℚ) ℚ) else 0)) (nhds 1)) ∧
      (∀ O ∈ nhds (fun j : Fin 3 => if j = 2 then (1 : AdeleRing (𝓞 ℚ) ℚ) else 0),
      (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ;
        0 < (Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
              (O ∩ {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j}))) ∧
      (∀ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, Continuous F →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), F (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = F g) →
      (∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) F) → ∀ C : ℝ≥0∞, C ≠ ⊤ →
      (∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
          ∫⁻ x in {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j},
              (‖Φ x‖₊ : ℝ≥0∞) *
                ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) ∂ν
              ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) =
            C * ∫⁻ x, (‖Φ x‖₊ : ℝ≥0∞)
              ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))) →
      ∃ C₁ : ℝ≥0∞,
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
          ∀ᵐ x ∂((Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).restrict
              {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j}),
            ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2)
              ∂ν = C₁))

private theorem fibrationFacts_concrete
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hctop : c ≠ ⊤)
    (hc : productionFibration = c • NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) :
    FibrationFacts ω a b Φ₀ S mirabolic (fibreMeasure S c⁻¹) (sectionMap S) := by
  unfold FibrationFacts
  refine ⟨?_, tendsto_sectionMap S, ?_, ?_⟩
  · intro F hF Φ hΦ
    obtain ⟨⟨Φc, hΦc, -, rfl⟩, -, -⟩ := hΦ
    have hWc : Continuous (whittaker3 prodPins NumberField.StandardAddChar.psiQ F) :=
      continuous_whittaker3_productionPins _ NumberField.StandardAddChar.continuous_psiQ _ hF.2.1
    have hWinv := (whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul F
      ((mem_automorphicSubmodule_iff ω a b Φ₀ F).1 hF.1).1).2
    simp only [image_eq_explicitRows, whittaker3_translateRight]
    exact block_formula S hc0 hctop hc F hWc hWinv (continuous_prod_of_pureTensors hΦc)
  · intro O hO
    simp only [image_eq_explicitRows]
    exact pos_rowHaar_inter_explicitRows S hO
  · refine unique_of_class_averages S (fibreMeasure S c⁻¹) (sectionMap S) (image_eq_explicitRows S)
      (fun x hx p hp => ?_) (fun x hx y hy p _ hxy => ?_) (fun x hx y hy hxy => ?_) (fun F hFc hFaut => ?_)
    · rw [sectionMap_of_mem S hx]
      exact componentAt3_sec0_mem (explicitRows_subset_rowDomain S hx) (hx.1 p hp)
    · rw [sectionMap_of_mem S hx, sectionMap_of_mem S hy]
      exact componentAt3_sec0_congr (explicitRows_subset_rowDomain S hx) (explicitRows_subset_rowDomain S hy) p hxy
    · rw [sectionMap_of_mem S hx, sectionMap_of_mem S hy]
      exact archComponent3_sec0_congr (explicitRows_subset_rowDomain S hx) (explicitRows_subset_rowDomain S hy) hxy
    · have hWc : Continuous (whittaker3 prodPins NumberField.StandardAddChar.psiQ F) :=
        continuous_whittaker3_productionPins _ NumberField.StandardAddChar.continuous_psiQ _ hFc
      have hWinv := (whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul F hFaut).2
      simpa only [whittaker3_translateRight] using measurable_fibreIntegral_sectionMap S c⁻¹ hWc hWinv

end ConcreteFibreData

section ExposedFibreData

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdeleRing.secondCountableTopology
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar
attribute [local instance] secondCountableTopology_adelicGL3 isMulRightInvariant_adelicGLHaar
attribute [local instance] WhittakerBlock.isHaarMeasure_unipotentHaar3
attribute [local instance] WhittakerBlock.isMulRightInvariant_unipotentHaar3

private theorem exposedFibration
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    ∃ (P : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
      (ν : Measure (MulAction.orbitRel.Quotient (WhittakerBlock.unipotentSubgroup3.subgroupOf P) ↥P))
      (s : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → AdelicGL 3 (𝓞 ℚ) ℚ),
      (∀ F ∈ cuspFunctions ω a b Φ₀, ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
        WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ F Φ 1 S =
          (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
            ∫⁻ x in {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j},
              (‖Φ x‖₊ : ℝ≥0∞) *
                ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) ∂ν
              ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))) ∧
      (Filter.Tendsto s (nhds (fun j : Fin 3 => if j = 2 then (1 : AdeleRing (𝓞 ℚ) ℚ) else 0)) (nhds 1)) ∧
      (∀ O ∈ nhds (fun j : Fin 3 => if j = 2 then (1 : AdeleRing (𝓞 ℚ) ℚ) else 0),
      (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ;
        0 < (Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
              (O ∩ {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j}))) ∧
      (∀ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, Continuous F →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), F (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = F g) →
      (∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) F) → ∀ C : ℝ≥0∞, C ≠ ⊤ →
      (∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
          ∫⁻ x in {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j},
              (‖Φ x‖₊ : ℝ≥0∞) *
                ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) ∂ν
              ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) =
            C * ∫⁻ x, (‖Φ x‖₊ : ℝ≥0∞)
              ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))) →
      ∃ C₁ : ℝ≥0∞,
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
          ∀ᵐ x ∂((Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).restrict
              {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j}),
            ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2)
              ∂ν = C₁)) ∧
      (
          ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      g ∈ P ↔ (fun j => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j) =
        (fun j : Fin 3 => if j = 2 then (1 : AdeleRing (𝓞 ℚ) ℚ) else 0)
      ) ∧
      (∀ x ∈ {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
          ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j},
        ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p (s x) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) ∧
      ∃ (μP : Measure ↥P) (c₀ : ℝ≥0∞),
        μP.IsMulRightInvariant ∧ μP.IsOpenPosMeasure ∧ IsFiniteMeasureOnCompacts μP ∧ c₀ ≠ 0 ∧ c₀ ≠ ⊤ ∧
          ν = c₀ •
      (Measure.map Quotient.mk''
        (μP.withDensity fun p : ↥P =>
          HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
              (p : AdelicGL 3 (𝓞 ℚ) ℚ) *
            {g : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S →
                ∃ (x y z : p.adicCompletion ℚ) (k : GL (Fin 3) (p.adicCompletion ℚ)),
                  k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p ∧
                    componentAt3 (𝓞 ℚ) ℚ p g = upperUnipotent3 x y z * k}.indicator (fun _ => (1 : ℝ≥0∞))
              (p : AdelicGL 3 (𝓞 ℚ) ℚ)) :
        Measure (MulAction.orbitRel.Quotient (WhittakerBlock.unipotentSubgroup3.subgroupOf P) ↥P)) := by
  obtain ⟨c, hc0, hctop, hc⟩ := exists_fibration_eq_smul_haar
  have hfacts := fibrationFacts_concrete ω a b Φ₀ S hc0 hctop hc
  unfold FibrationFacts at hfacts
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hfacts
  refine ⟨mirabolic, fibreMeasure S c⁻¹, sectionMap S, h₁, h₂, h₃, h₄, fun _ => Iff.rfl, ?_, ?_⟩
  · intro x hx p hp
    have hx' : x ∈ explicitRows S := by rwa [← image_eq_explicitRows S]
    rw [sectionMap_of_mem S hx']
    exact componentAt3_sec0_mem (explicitRows_subset_rowDomain S hx') (hx'.1 p hp)
  · exact ⟨fibreHaar, c⁻¹, inferInstance, inferInstance, inferInstance, ENNReal.inv_ne_zero.2 hctop,
      ENNReal.inv_ne_top.2 hc0, rfl⟩

end ExposedFibreData

end Fibration
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_whittakerBlock_one_eq_lintegral_and_eq_smul_map_withDensity_haar.Fibration"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_whittakerBlock_one_eq_lintegral_and_eq_smul_map_withDensity_haar.Fibration"

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory LanglandsTunnell.CubicInduction.SlabL2 in
open scoped ENNReal InnerProductSpace in
open LanglandsTunnell.CubicInduction Fibration in
theorem solution
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    ∃ (P : Subgroup (AdelicGL 3 (𝓞 ℚ) ℚ))
      (ν : Measure (MulAction.orbitRel.Quotient (WhittakerBlock.unipotentSubgroup3.subgroupOf P) ↥P))
      (s : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → AdelicGL 3 (𝓞 ℚ) ℚ),
      (∀ F ∈ cuspFunctions ω a b Φ₀, ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
        WhittakerBlock.block (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ F Φ 1 S =
          (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
            ∫⁻ x in {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j},
              (‖Φ x‖₊ : ℝ≥0∞) *
                ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) ∂ν
              ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))) ∧
      (Filter.Tendsto s (nhds (fun j : Fin 3 => if j = 2 then (1 : AdeleRing (𝓞 ℚ) ℚ) else 0)) (nhds 1)) ∧
      (∀ O ∈ nhds (fun j : Fin 3 => if j = 2 then (1 : AdeleRing (𝓞 ℚ) ℚ) else 0),
      (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ;
        0 < (Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
              (O ∩ {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j}))) ∧
      (∀ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, Continuous F →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), F (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = F g) →
      (∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) F) → ∀ C : ℝ≥0∞, C ≠ ⊤ →
      (∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ,
        (∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          (∀ i, ∃ g h, NumberField.TateGlobal.IsFactorizableStandardOutside (Φc i) S g h) ∧
          Φ = fun x => ∏ i, Φc i (x i)) ∧
        (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
         0 < ∫ x, (Φ x).re ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) →
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
          ∫⁻ x in {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j},
              (‖Φ x‖₊ : ℝ≥0∞) *
                ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2) ∂ν
              ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) =
            C * ∫⁻ x, (‖Φ x‖₊ : ℝ≥0∞)
              ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ))) →
      ∃ C₁ : ℝ≥0∞,
        (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
          ∀ᵐ x ∂((Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ).restrict
              {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
                ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j}),
            ∫⁻ q, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ (translateRight (s x) F) (q.out : AdelicGL 3 (𝓞 ℚ) ℚ)‖₊ : ℝ≥0∞) ^ 2)
              ∂ν = C₁)) ∧
      (
          ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      g ∈ P ↔ (fun j => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j) =
        (fun j : Fin 3 => if j = 2 then (1 : AdeleRing (𝓞 ℚ) ℚ) else 0)
      ) ∧
      (∀ x ∈ {x : Fin 3 → AdeleRing (𝓞 ℚ) ℚ | ∃ q ∈ WhittakerBlock.zerothShell S,
          ∀ j, (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j = x j},
        ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p (s x) ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) ∧
      ∃ (μP : Measure ↥P) (c₀ : ℝ≥0∞),
        μP.IsMulRightInvariant ∧ μP.IsOpenPosMeasure ∧ IsFiniteMeasureOnCompacts μP ∧ c₀ ≠ 0 ∧ c₀ ≠ ⊤ ∧
          ν = c₀ •
      (Measure.map Quotient.mk''
        (μP.withDensity fun p : ↥P =>
          HaarQuotient.density WhittakerBlock.unipotentSubgroup3 WhittakerBlock.unipotentHaar3
              (p : AdelicGL 3 (𝓞 ℚ) ℚ) *
            {g : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S →
                ∃ (x y z : p.adicCompletion ℚ) (k : GL (Fin 3) (p.adicCompletion ℚ)),
                  k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p ∧
                    componentAt3 (𝓞 ℚ) ℚ p g = upperUnipotent3 x y z * k}.indicator (fun _ => (1 : ℝ≥0∞))
              (p : AdelicGL 3 (𝓞 ℚ) ℚ)) :
        Measure (MulAction.orbitRel.Quotient (WhittakerBlock.unipotentSubgroup3.subgroupOf P) ↥P)) := by
  exact exposedFibration ω a b Φ₀ S

end S_LanglandsTunnell_CubicInduction_exists_whittakerBlock_one_eq_lintegral_and_eq_smul_map_withDensity_haar
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_whittakerBlock_one_eq_lintegral_and_eq_smul_map_withDensity_haar (solution)
