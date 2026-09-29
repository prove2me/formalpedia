-- Prove2me | solution 1 for NumberField.TateGlobal.exists_measurableSet_forall_isFundamentalDomain_range_unitsMap_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/433be5c3-c6d1-5c24-b88a-fe08702e7aee

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_AdelicKernel
import Theorems.Thm_AutomorphicForm_adelicKernelLocalFiniteness
import Theorems.Thm_MeasureTheory_exists_measurableSet_isFundamentalDomain_op_of_discreteTopology
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_exists_measurableSet_forall_isFundamentalDomain_range_unitsMap_algebraMap
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_exists_measurableSet_forall_isFundamentalDomain_range_unitsMap_algebraMap.NumberField AutomorphicForm Set"

noncomputable section

namespace NumberField
p2m_export "NumberField" "AdeleRing AdeleRing.secondCountableTopology"
namespace TateGlobal
namespace PrincipalFD
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type} [Field F] [NumberField F]

theorem centralScalar_coe (z : (AdeleRing (𝓞 F) F)ˣ) :
    ((centralScalar (𝓞 F) F z : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
      (z : AdeleRing (𝓞 F) F) • (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
  show ((Units.map (Matrix.scalar (Fin 2)).toMonoidHom z : (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))ˣ) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = _
  rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Matrix.scalar_apply,
    Matrix.smul_one_eq_diagonal]

theorem continuous_centralScalar : Continuous (centralScalar (𝓞 F) F : (AdeleRing (𝓞 F) F)ˣ → AdelicGL2 (𝓞 F) F) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have h1 : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ =>
        (z : AdeleRing (𝓞 F) F) • (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :=
      Units.continuous_val.smul continuous_const
    exact h1.congr fun z => (centralScalar_coe z).symm
  · have h1 : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ =>
        ((z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) • (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :=
      (Units.continuous_val.comp continuous_inv).smul continuous_const
    refine h1.congr fun z => ?_
    show _ = ((↑(centralScalar (𝓞 F) F z)⁻¹ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
    rw [← map_inv]
    exact (centralScalar_coe z⁻¹).symm

theorem centralScalar_principal (u : Fˣ) :
    centralScalar (𝓞 F) F (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u) =
      globalPoints (𝓞 F) F (Matrix.GeneralLinearGroup.scalar (Fin 2) u) := by
  apply Units.ext
  rw [centralScalar_coe]
  show _ = (((Matrix.GeneralLinearGroup.map (algebraMap F (AdeleRing (𝓞 F) F))
    (Matrix.GeneralLinearGroup.scalar (Fin 2) u) : GL (Fin 2) (AdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)))
  refine Matrix.ext fun i j => ?_
  rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  show _ = algebraMap F (AdeleRing (𝓞 F) F) (((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j)
  have hs : ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = (u : F) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    show ((Units.map (Matrix.scalar (Fin 2)).toMonoidHom u : (Matrix (Fin 2) (Fin 2) F)ˣ) : Matrix (Fin 2) (Fin 2) F) = _
    rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rw [hs, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  split_ifs
  · rfl
  · rw [map_zero]

variable (F) in

def principalUnits : Subgroup (AdeleRing (𝓞 F) F)ˣ :=
  (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range

theorem discreteTopology_principalUnits : DiscreteTopology (principalUnits F) := by
  obtain ⟨C, hCc, hC1⟩ := exists_compact_mem_nhds (1 : AdelicGL2 (𝓞 F) F)
  have hfin : {γ : GL (Fin 2) F | (1 : AdelicGL2 (𝓞 F) F)⁻¹ * globalPoints (𝓞 F) F γ * 1 ∈ C}.Finite :=
    AutomorphicForm.adelicKernelLocalFiniteness F C hCc 1 1

  set S : Set Fˣ := {u | globalPoints (𝓞 F) F (Matrix.GeneralLinearGroup.scalar (Fin 2) u) ∈ C} with hS
  have hSfin : S.Finite := by
    have hinj : Function.Injective (fun u : Fˣ => Matrix.GeneralLinearGroup.scalar (Fin 2) u) := by
      intro u v huv
      have h := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) huv
      simp at h
      exact Units.ext h
    refine Set.Finite.of_finite_image (f := fun u : Fˣ => Matrix.GeneralLinearGroup.scalar (Fin 2) u) ?_ hinj.injOn
    refine hfin.subset ?_
    rintro _ ⟨u, hu, rfl⟩
    simp at hu ⊢
    exact hu
  set R : Set (AdeleRing (𝓞 F) F)ˣ :=
    (fun u : Fˣ => Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u) ''
      {u | u ∈ S ∧ Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u ≠ 1} with hR
  have hRfin : R.Finite := (hSfin.subset fun u hu => hu.1).image _
  set U : Set (AdeleRing (𝓞 F) F)ˣ := (centralScalar (𝓞 F) F) ⁻¹' interior C \ R with hU
  have hUo : IsOpen U := (isOpen_interior.preimage continuous_centralScalar).sdiff hRfin.isClosed
  have h1U : (1 : (AdeleRing (𝓞 F) F)ˣ) ∈ U := by
    refine ⟨?_, ?_⟩
    · show centralScalar (𝓞 F) F 1 ∈ interior C
      rw [map_one]; exact mem_interior_iff_mem_nhds.2 hC1
    · rintro ⟨u, ⟨-, hne⟩, h1⟩; exact hne h1
  have hkey : ∀ x ∈ principalUnits F, x ∈ U → x = 1 := by
    rintro _ ⟨u, rfl⟩ ⟨hint, hnot⟩
    by_contra hne
    refine hnot ⟨u, ⟨?_, hne⟩, rfl⟩
    show globalPoints (𝓞 F) F (Matrix.GeneralLinearGroup.scalar (Fin 2) u) ∈ C
    rw [← centralScalar_principal]
    exact interior_subset hint
  apply discreteTopology_of_isOpen_singleton_one
  have hset : ({1} : Set (principalUnits F)) = ((↑) : principalUnits F → (AdeleRing (𝓞 F) F)ˣ) ⁻¹' U := by
    ext b
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro rfl; exact h1U
    · intro hb
      exact Subtype.ext (hkey b b.2 hb)
  rw [hset]
  exact hUo.preimage continuous_subtype_val

end NumberField.TateGlobal.PrincipalFD

end

open NumberField.TateGlobal.PrincipalFD in
theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ] :
    ∃ Ω : Set (AdeleRing (𝓞 F) F)ˣ, MeasurableSet Ω ∧
      ∀ ν : Measure (AdeleRing (𝓞 F) F)ˣ,
        IsFundamentalDomain
          (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω ν := by
  haveI := NumberField.AdeleRing.secondCountableTopology F
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F)ˣ :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  obtain ⟨D, hDm, hD, -⟩ :=
    MeasureTheory.exists_measurableSet_isFundamentalDomain_op_of_discreteTopology (principalUnits F)
      discreteTopology_principalUnits
  refine ⟨D⁻¹, hDm.inv, fun μ => IsFundamentalDomain.mk' hDm.inv.nullMeasurableSet fun x => ?_⟩
  obtain ⟨γ, hγ, huniq⟩ := hD x⁻¹
  refine ⟨γ⁻¹, ?_, ?_⟩
  · show ((γ⁻¹ : principalUnits F) : (AdeleRing (𝓞 F) F)ˣ) * x ∈ D⁻¹
    rw [Set.mem_inv, Subgroup.coe_inv, mul_inv_rev, inv_inv]
    exact hγ
  · intro δ hδ
    change ((δ : principalUnits F) : (AdeleRing (𝓞 F) F)ˣ) * x ∈ D⁻¹ at hδ
    rw [Set.mem_inv, mul_inv_rev] at hδ
    have := huniq δ⁻¹ (by simp at hδ ⊢; exact hδ)
    rw [← this]; exact (inv_inv δ).symm

end S_NumberField_TateGlobal_exists_measurableSet_forall_isFundamentalDomain_range_unitsMap_algebraMap
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_measurableSet_forall_isFundamentalDomain_range_unitsMap_algebraMap (solution)
