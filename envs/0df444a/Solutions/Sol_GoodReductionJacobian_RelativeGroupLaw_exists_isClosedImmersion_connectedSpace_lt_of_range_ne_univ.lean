-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_isClosedImmersion_connectedSpace_lt_of_range_ne_univ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/ec1679ac-4f70-560d-954a-78992a2be911

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_PartialAction
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_smoothOfRelativeDimension_range_eq_connectedComponent_of_perfectField
import Theorems.Thm_IsIrreducible_topologicalKrullDim_add_one_le_of_isClosed_of_ne
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_connectedSpace_lt_of_range_ne_univ
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G]
    (L : RelativeGroupLaw k f) (g : ℕ) [SmoothOfRelativeDimension g f]
    {H : Scheme.{u}} (i : H ⟶ G) [IsClosedImmersion i] (LH : RelativeGroupLaw k (i ≫ f))
    (hi : (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
        NeronModelInfra.schemeHomOverComp (LH.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
            (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))))
    (hne : Set.range i ≠ Set.univ)
    (hdim : 1 ≤ topologicalKrullDim
      ↥(connectedComponent ((LH.one (𝟙 (Spec (CommRingCat.of k)))).1 (IsLocalRing.closedPoint k)))) :
    ∃ (H' : Scheme.{u}) (i' : H' ⟶ G) (LH' : RelativeGroupLaw k (i' ≫ f)) (h : ℕ),
      IsClosedImmersion i' ∧ ConnectedSpace H' ∧ SmoothOfRelativeDimension h (i' ≫ f) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i' ≫ f)),
        NeronModelInfra.schemeHomOverComp (LH'.mul t x y) (⟨i', rfl⟩ : SchemeHomOver (i' ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i', rfl⟩ : SchemeHomOver (i' ≫ f) f))
            (NeronModelInfra.schemeHomOverComp y (⟨i', rfl⟩ : SchemeHomOver (i' ≫ f) f))) ∧
      1 ≤ h ∧ h < g := by
  classical
  haveI : PerfectField k := inferInstance
  have hsmf : Smooth f := SmoothOfRelativeDimension.smooth g f
  haveI : LocallyOfFiniteType (i ≫ f) := inferInstance
  haveI : QuasiCompact (i ≫ f) := inferInstance
  obtain ⟨G₀, i₀, L₀, n, hci, hirr, hsm, -, -, hrange, hdimG₀, hhom, -, -⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_isClosedImmersion_smoothOfRelativeDimension_range_eq_connectedComponent_of_perfectField
      k LH

  have hdim₀ : topologicalKrullDim ↥(Set.range i₀) = topologicalKrullDim G₀ :=
    (IsHomeomorph.topologicalKrullDim_eq _ (i₀.isClosedEmbedding.isEmbedding.toHomeomorph).isHomeomorph).symm
  have hdim₁ : topologicalKrullDim ↥(Set.range (i₀ ≫ i)) = topologicalKrullDim G₀ :=
    (IsHomeomorph.topologicalKrullDim_eq _ ((i₀ ≫ i).isClosedEmbedding.isEmbedding.toHomeomorph).isHomeomorph).symm
  refine ⟨G₀, i₀ ≫ i, L₀, n, inferInstance, inferInstance, hsm, ?_, ?_, ?_⟩
  ·
    intro T t x y
    have e : ∀ z : SchemeHomOver t (i₀ ≫ i ≫ f),
        NeronModelInfra.schemeHomOverComp z (⟨i₀ ≫ i, rfl⟩ : SchemeHomOver (i₀ ≫ i ≫ f) f) =
          NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp z (⟨i₀, rfl⟩ : SchemeHomOver (i₀ ≫ i ≫ f) (i ≫ f)))
            (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) :=
      fun z => Subtype.ext (Category.assoc _ _ _).symm
    change NeronModelInfra.schemeHomOverComp (L₀.mul t x y) (⟨i₀ ≫ i, rfl⟩ : SchemeHomOver (i₀ ≫ i ≫ f) f) =
      L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i₀ ≫ i, rfl⟩ : SchemeHomOver (i₀ ≫ i ≫ f) f))
        (NeronModelInfra.schemeHomOverComp y (⟨i₀ ≫ i, rfl⟩ : SchemeHomOver (i₀ ≫ i ≫ f) f))
    rw [e, e, e, hhom, hi]
  ·
    rw [← hrange, hdim₀, hdimG₀] at hdim
    exact_mod_cast hdim
  ·
    haveI : Nonempty G := ⟨(L.one (𝟙 _)).1 (IsLocalRing.closedPoint k)⟩
    haveI : IsIntegral G := AlgebraicGeometry.isIntegral_of_smooth_of_preconnectedSpace f
    have hY : IsClosed (Set.range (i₀ ≫ i)) := (i₀ ≫ i).isClosedEmbedding.isClosed_range
    have hYne : Set.range (i₀ ≫ i) ≠ Set.univ := by
      intro h
      apply hne
      apply Set.eq_univ_of_univ_subset
      rw [← h]
      rintro _ ⟨z, rfl⟩
      exact ⟨i₀ z, (Scheme.Hom.comp_apply _ _ _).symm⟩
    have h1 := IsIrreducible.topologicalKrullDim_add_one_le_of_isClosed_of_ne
      (IrreducibleSpace.isIrreducible_univ G) hY (Set.subset_univ _) hYne
    have h2 : topologicalKrullDim ↥(Set.univ : Set G) ≤ g :=
      (topologicalKrullDim_subspace_le G _).trans
        (AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_le f g)
    rw [hdim₁, hdimG₀] at h1
    have h3 : ((n : ℕ∞) : WithBot ℕ∞) + 1 ≤ ((g : ℕ∞) : WithBot ℕ∞) := h1.trans h2
    have h4 : (n : ℕ∞) + 1 ≤ (g : ℕ∞) := by
      rw [← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_le_coe] at h3
      exact h3
    have h5 : n + 1 ≤ g := by exact_mod_cast h4
    omega

end S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_connectedSpace_lt_of_range_ne_univ
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_connectedSpace_lt_of_range_ne_univ (solution)
