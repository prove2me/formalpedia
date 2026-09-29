-- Prove2me | solution 1 for NumberField.LevelArith.hasLocalInv_of_hasLocalInv_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/55e5b172-d440-59ca-a153-474302e50fd5

import Mathlib
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelInflation
import Definitions.Def_GroupCohomology_ContinuousH2Inflation
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_IdeleLocalInvariant
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_NumberField_PlaceDecomp_exists_localLevel_ringEquiv_adicCompletion
import Theorems.Thm_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass
import Theorems.Thm_ExtCitation_LocalLevel_finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq
import Theorems.Thm_IntermediateField_isSolvable_algEquiv_of_padic
import Theorems.Thm_ExtCitation_LocalLevel_isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass
import Theorems.Thm_M4aHerbrand_exists_hom_res_decomp_ideles_adicCompletion_apply
import Theorems.Thm_M4aHerbrand_div_natCard_decomp_eq_div_natCard_decomp_under_of_map_map_eq_zsmul_of_isScalarTower
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_unitsAct_map_genuineBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le
p2m_attr_erase "instance" "ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory groupCohomology ExtCitation NumberField P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField IsDedekindDomain M4aHerbrand NumberField.LevelArith P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField.LevelArith"
p2m_open_scoped "NumberField.LevelArith P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField.LevelArith NumberField.PlaceDecomp P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField.PlaceDecomp"
p2m_open_scoped "NumberField P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField"
set_option linter.unusedSectionVars false

namespace NumberField
p2m_export "NumberField" "mk place AdeleRing SUnits.sUnitsRep SUnits.val PlaceAbove.above PlaceAbove.comap_above PlaceDecomp.decomp PlaceDecomp.coe_smul_units IdeleLocalInv.HasLocalInv PlaceDecomp.exists_localLevel_ringEquiv_adicCompletion"
namespace LevelArith
p2m_export "NumberField.LevelArith" "sUnitsMaxRep sUnitsMaxRep.val levelField levelGal levelGal_apply_coe placesOverPrimesFinset"
namespace N5
p2m_open "NumberField.LevelArith NumberField"

section LevelGalFacts
variable (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [Normal ↥L ↥(levelField L F hLF)]

theorem levelGal_surjective : Function.Surjective (levelGal L F hLF) := by
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ↥L (AlgebraicClosure ℚ) := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) ↥L⟩
  intro σ
  obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective (F := ↥L) (K₁ := ↥(levelField L F hLF)) (AlgebraicClosure ℚ) σ
  refine ⟨(IntermediateField.fixingSubgroupEquiv L).symm τ, ?_⟩
  change AlgEquiv.restrictNormalHom _ ((IntermediateField.fixingSubgroupEquiv L) ((IntermediateField.fixingSubgroupEquiv L).symm τ)) = σ
  rw [MulEquiv.apply_symm_apply]
  exact hτ

end LevelGalFacts

section Tower
variable (L F F'' : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) (hLF'' : L ≤ F'')
  [Normal ↥L ↥(levelField L F hLF)] [Normal ↥L ↥(levelField L F'' hLF'')]

theorem levelField_mono (hFF'' : F ≤ F'') : levelField L F hLF ≤ levelField L F'' hLF'' := fun _ hx => hFF'' hx

theorem restrictNormalHom_levelGal
    (inst : Algebra ↥(levelField L F hLF) ↥(levelField L F'' hLF''))
    (halg : ∀ y : ↥(levelField L F hLF), ((algebraMap ↥(levelField L F hLF) ↥(levelField L F'' hLF'') y : ↥(levelField L F'' hLF'')) :
      AlgebraicClosure ℚ) = (y : AlgebraicClosure ℚ))
    [IsScalarTower ↥L ↥(levelField L F hLF) ↥(levelField L F'' hLF'')] (γ : ↥L.fixingSubgroup) :
    AlgEquiv.restrictNormalHom ↥(levelField L F hLF) (levelGal L F'' hLF'' γ) = levelGal L F hLF γ := by
  apply AlgEquiv.ext
  intro y
  apply Subtype.ext
  have h1 := AlgEquiv.restrictNormal_commutes (levelGal L F'' hLF'' γ) ↥(levelField L F hLF) y

  have h2 := congrArg (fun z : ↥(levelField L F'' hLF'') => (z : AlgebraicClosure ℚ)) h1
  beta_reduce at h2
  rw [halg, levelGal_apply_coe, halg] at h2
  rw [levelGal_apply_coe]
  exact h2

end Tower

end NumberField.LevelArith.N5

namespace NumberField
p2m_export "NumberField" "mk place AdeleRing SUnits.sUnitsRep SUnits.val PlaceAbove.above PlaceAbove.comap_above PlaceDecomp.decomp PlaceDecomp.coe_smul_units IdeleLocalInv.HasLocalInv PlaceDecomp.exists_localLevel_ringEquiv_adicCompletion"
namespace LevelArith
p2m_export "NumberField.LevelArith" "sUnitsMaxRep sUnitsMaxRep.val levelField levelGal levelGal_apply_coe placesOverPrimesFinset"
namespace N5
p2m_open "NumberField.LevelArith NumberField"

section Pullback
variable (S : Finset Nat.Primes) (L F F'' : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ ↥F] [Normal ℚ ↥F'']

theorem levelSubgroup_mono (hFF'' : F ≤ F'') : F''.fixingSubgroup.comap L.fixingSubgroup.subtype ≤ F.fixingSubgroup.comap L.fixingSubgroup.subtype :=
  Subgroup.comap_mono (IntermediateField.fixingSubgroup_antitone hFF'')

noncomputable def πmap (hFF'' : F ≤ F'') : ↥L.fixingSubgroup ⧸ F''.fixingSubgroup.comap L.fixingSubgroup.subtype →*
    ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype :=
  QuotientGroup.map _ _ (MonoidHom.id _) (levelSubgroup_mono L F F'' hFF'')

@[scoped simp] theorem πmap_mk (hFF'' : F ≤ F'') (γ : ↥L.fixingSubgroup) :
    πmap L F F'' hFF'' (QuotientGroup.mk γ) = QuotientGroup.mk γ := rfl

theorem invariants_mono (hFF'' : F ≤ F'') :
    Representation.invariants ((sUnitsMaxRep S L).ρ.comp (F.fixingSubgroup.comap L.fixingSubgroup.subtype).subtype) ≤
      Representation.invariants ((sUnitsMaxRep S L).ρ.comp (F''.fixingSubgroup.comap L.fixingSubgroup.subtype).subtype) := by
  intro m hm u
  exact hm ⟨u.1, levelSubgroup_mono L F F'' hFF'' u.2⟩

noncomputable def ψmap (hFF'' : F ≤ F'') : Rep.res (πmap L F F'' hFF'') ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶
    (sUnitsMaxRep S L).quotientToInvariants (F''.fixingSubgroup.comap L.fixingSubgroup.subtype) :=
  Rep.ofHom ⟨Submodule.inclusion (invariants_mono S L F F'' hFF''), fun g => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    refine LinearMap.ext fun z => Subtype.ext ?_
    rfl⟩

@[scoped simp] theorem ψmap_hom_apply_coe (hFF'' : F ≤ F'') (m) : (((ψmap S L F F'' hFF'').hom m :
    (sUnitsMaxRep S L).quotientToInvariants (F''.fixingSubgroup.comap L.fixingSubgroup.subtype)) : sUnitsMaxRep S L) = (m.1 : sUnitsMaxRep S L) := rfl

theorem H2π_eq_map_of_values (hFF'' : F ≤ F'')
    (f : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (f'' : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F''.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (hff'' : ∀ g h : ↥L.fixingSubgroup,
      ((f'' ((g : ↥L.fixingSubgroup ⧸ F''.fixingSubgroup.comap L.fixingSubgroup.subtype), (h : ↥L.fixingSubgroup ⧸ F''.fixingSubgroup.comap L.fixingSubgroup.subtype)) :
          (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L)
        = ((f ((g : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype), (h : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) :
          (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L)) :
    H2π _ f'' = (groupCohomology.map (πmap L F F'' hFF'') (ψmap S L F F'' hFF'') 2).hom (H2π _ f) := by
  have hf : f'' = mapCocycles₂ (πmap L F F'' hFF'') (ψmap S L F F'' hFF'') f := by
    apply cocycles₂_ext
    intro p q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective p
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    apply Subtype.ext
    rw [hff'']
    change _ = ((((mapCocycles₂ (πmap L F F'' hFF'') (ψmap S L F F'' hFF'') f : cocycles₂ _) : _ → _) (QuotientGroup.mk g, QuotientGroup.mk h) :
      (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L)
    rw [coe_mapCocycles₂]
    rfl
  rw [hf]
  change _ = (H2π _ ≫ groupCohomology.map _ _ 2).hom _
  rw [H2π_comp_map]
  rfl

end Pullback

end NumberField.LevelArith.N5
p2m_reactivate "P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField.LevelArith P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField.LevelArith.N5"
p2m_reactivate "P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField.LevelArith"
p2m_reactivate "P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField"

namespace NumberField
p2m_export "NumberField" "mk place AdeleRing SUnits.sUnitsRep SUnits.val PlaceAbove.above PlaceAbove.comap_above PlaceDecomp.decomp PlaceDecomp.coe_smul_units IdeleLocalInv.HasLocalInv PlaceDecomp.exists_localLevel_ringEquiv_adicCompletion"
namespace LevelArith
p2m_export "NumberField.LevelArith" "sUnitsMaxRep sUnitsMaxRep.val levelField levelGal levelGal_apply_coe placesOverPrimesFinset"
namespace N5
p2m_open "NumberField.LevelArith NumberField"

theorem frame_square
    (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥L]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] [IsGalois ↥L ↥(levelField L F hLF)]
    (F'' : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF'' : L ≤ F'') [FiniteDimensional ℚ ↥F''] [Normal ℚ ↥F''] [IsGalois ↥L ↥(levelField L F'' hLF'')]
    (hFF'' : F ≤ F'')
    (ι : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) →* (↥L.fixingSubgroup ⧸ (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) (hι : ∀ g : ↥L.fixingSubgroup, ι (levelGal L F hLF g) = (g : (↥L.fixingSubgroup ⧸ (F.fixingSubgroup.comap L.fixingSubgroup.subtype))))
    (φ : Rep.res ι ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶ NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))
    (hval : ∀ x, ((NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (φ.hom x) : ↥(levelField L F hLF)) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
    (ι'' : (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) →* (↥L.fixingSubgroup ⧸ (F''.fixingSubgroup.comap L.fixingSubgroup.subtype))) (hι'' : ∀ g : ↥L.fixingSubgroup, ι'' (levelGal L F'' hLF'' g) = (g : (↥L.fixingSubgroup ⧸ (F''.fixingSubgroup.comap L.fixingSubgroup.subtype))))
    (φ'' : Rep.res ι'' ((sUnitsMaxRep S L).quotientToInvariants (F''.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶ NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F'' hLF'') (placesOverPrimesFinset ↥L S))
    (hval'' : ∀ x, ((NumberField.SUnits.val ↥L ↥(levelField L F'' hLF'') (placesOverPrimesFinset ↥L S) (φ''.hom x) : ↥(levelField L F'' hLF'')) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
    [MulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ]
    (j : NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) ⟶ (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ))
    (hj : ∀ y, Additive.toMul (j.hom y) =
      Units.map (algebraMap ↥(levelField L F hLF) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) : ↥(levelField L F hLF) →* AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) (NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) y))
    [MulDistribMulAction (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) (AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF''))ˣ]
    (j'' : NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F'' hLF'') (placesOverPrimesFinset ↥L S) ⟶ (Rep.ofMulDistribMulAction (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) (AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF''))ˣ))
    (hj'' : ∀ y, Additive.toMul (j''.hom y) =
      Units.map (algebraMap ↥(levelField L F'' hLF'') (AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF'')) : ↥(levelField L F'' hLF'') →* AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF'')) (NumberField.SUnits.val ↥L ↥(levelField L F'' hLF'') (placesOverPrimesFinset ↥L S) y))
    (f : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) (f'' : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F''.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (hff'' : ∀ g h : ↥L.fixingSubgroup,
      ((f'' ((g : (↥L.fixingSubgroup ⧸ (F''.fixingSubgroup.comap L.fixingSubgroup.subtype))), (h : (↥L.fixingSubgroup ⧸ (F''.fixingSubgroup.comap L.fixingSubgroup.subtype)))) : ((sUnitsMaxRep S L).quotientToInvariants (F''.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L) = ((f ((g : (↥L.fixingSubgroup ⧸ (F.fixingSubgroup.comap L.fixingSubgroup.subtype))), (h : (↥L.fixingSubgroup ⧸ (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L))

    [Algebra ↥(levelField L F hLF) ↥(levelField L F'' hLF'')]
    (halg : ∀ y : ↥(levelField L F hLF), ((algebraMap ↥(levelField L F hLF) ↥(levelField L F'' hLF'') y : ↥(levelField L F'' hLF'')) : AlgebraicClosure ℚ) = (y : AlgebraicClosure ℚ))
    (r : (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) →* (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) (hr : ∀ γ : ↥L.fixingSubgroup, r (levelGal L F'' hLF'' γ) = levelGal L F hLF γ)
    (J : Rep.res r (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) ⟶ (Rep.ofMulDistribMulAction (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) (AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF''))ˣ))
    (hJ : ∀ x : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ, J.hom (Additive.ofMul x) = Additive.ofMul (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange ↥(levelField L F hLF) ↥(levelField L F'' hLF'')).β.toMonoidHom x)) :
    (groupCohomology.map ι'' (φ'' ≫ j'') 2).hom (H2π _ f'') = (groupCohomology.map r J 2).hom ((groupCohomology.map ι (φ ≫ j) 2).hom (H2π _ f)) := by

  have hLHS : (groupCohomology.map ι'' (φ'' ≫ j'') 2).hom (H2π _ f'') =
      (groupCohomology.map ((πmap L F F'' hFF'').comp ι'') ((Rep.resFunctor ι'').map (ψmap S L F F'' hFF'') ≫ (φ'' ≫ j'')) 2).hom (H2π _ f) := by
    rw [H2π_eq_map_of_values S L F F'' hFF'' f f'' hff'', ← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← groupCohomology.map_comp]
  have hRHS : (groupCohomology.map r J 2).hom ((groupCohomology.map ι (φ ≫ j) 2).hom (H2π _ f)) =
      (groupCohomology.map (ι.comp r) ((Rep.resFunctor r).map (φ ≫ j) ≫ J) 2).hom (H2π _ f) := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← groupCohomology.map_comp]

  have hhom : (πmap L F F'' hFF'').comp ι'' = ι.comp r := by
    apply MonoidHom.ext
    intro σ
    obtain ⟨γ, rfl⟩ := levelGal_surjective L F'' hLF'' σ
    show (πmap L F F'' hFF'') (ι'' (levelGal L F'' hLF'' γ)) = ι (r (levelGal L F'' hLF'' γ))
    rw [hι'', hr, hι, πmap_mk]

  have hcoef : ∀ z : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)), ((Rep.resFunctor ι'').map (ψmap S L F F'' hFF'') ≫ (φ'' ≫ j'')).hom z = ((Rep.resFunctor r).map (φ ≫ j) ≫ J).hom z := by
    intro z
    have eL : ((Rep.resFunctor ι'').map (ψmap S L F F'' hFF'') ≫ (φ'' ≫ j'')).hom z = j''.hom (φ''.hom ((ψmap S L F F'' hFF'').hom z)) := rfl
    have eR : ((Rep.resFunctor r).map (φ ≫ j) ≫ J).hom z = J.hom (j.hom (φ.hom z)) := rfl
    rw [eL, eR]
    apply Additive.toMul.injective
    have eJ : Additive.toMul (J.hom (j.hom (φ.hom z))) = Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange ↥(levelField L F hLF) ↥(levelField L F'' hLF'')).β.toMonoidHom (Additive.toMul (j.hom (φ.hom z))) :=
      congrArg Additive.toMul (hJ (Additive.toMul (j.hom (φ.hom z))))
    rw [eJ, hj'']
    erw [hj]
    apply Units.ext
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    rw [(M4aHerbrand.GenuineDescent.genuineBaseChange ↥(levelField L F hLF) ↥(levelField L F'' hLF'')).β_compat]
    congr 1
    apply Subtype.ext
    rw [hval'', halg, hval]
    rfl

  have hgen : ∀ (f₁ f₂ : (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) →* (↥L.fixingSubgroup ⧸ (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) (hf : f₁ = f₂) (φ₁ : Rep.res f₁ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶ (Rep.ofMulDistribMulAction (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) (AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF''))ˣ)) (φ₂ : Rep.res f₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶ (Rep.ofMulDistribMulAction (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) (AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF''))ˣ)),
      (∀ z, φ₁.hom z = φ₂.hom z) → groupCohomology.map f₁ φ₁ 2 = groupCohomology.map f₂ φ₂ 2 := by
    intro f₁ f₂ hf φ₁ φ₂ hφ
    subst hf
    have hh : φ₁ = φ₂ := Rep.hom_ext (DFunLike.ext _ _ hφ)
    rw [hh]
  rw [hLHS, hRHS, hgen _ _ hhom _ _ hcoef]

end NumberField.LevelArith.N5
p2m_reactivate "P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField.LevelArith P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField.LevelArith.N5"
p2m_reactivate "P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField.LevelArith P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField.LevelArith.N5"
p2m_reactivate "P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField.LevelArith P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField.LevelArith.N5"

namespace NumberField
p2m_export "NumberField" "mk place AdeleRing SUnits.sUnitsRep SUnits.val PlaceAbove.above PlaceAbove.comap_above PlaceDecomp.decomp PlaceDecomp.coe_smul_units IdeleLocalInv.HasLocalInv PlaceDecomp.exists_localLevel_ringEquiv_adicCompletion"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "decomp smul_def coe_smul_units exists_localLevel_ringEquiv_adicCompletion"
namespace FCFamily
p2m_open "NumberField.PlaceDecomp NumberField"

theorem exists_isBase (q : ℕ) [Fact q.Prime] (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [MulSemiringAction G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) :
    ∃ (K : IntermediateField ℚ_[q] (PadicAlgCl q)) (_ : FiniteDimensional ℚ_[q] K), ExtCitation.LocalLevel.IsBase q L G K := by
  haveI : SMulCommClass G ℚ_[q] L := ⟨fun g c x => by rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hG]⟩
  refine ⟨IntermediateField.lift (FixedPoints.intermediateField G : IntermediateField ℚ_[q] L), ?_, ?_⟩
  · exact FiniteDimensional.of_injective
      (IntermediateField.inclusion (IntermediateField.lift_le (FixedPoints.intermediateField G : IntermediateField ℚ_[q] L))).toLinearMap
      (fun a b h => (IntermediateField.inclusion
        (IntermediateField.lift_le (FixedPoints.intermediateField G : IntermediateField ℚ_[q] L))).toRingHom.injective h)
  · refine ⟨IntermediateField.lift_le _, fun x => ?_⟩
    rw [IntermediateField.mem_lift]
    exact Iff.rfl

section Solvable
open ExtCitation.LocalLevel

theorem isSolvable_layer (q : ℕ) [Fact q.Prime] (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀] (hK : IsBase q L G K₀) : Group.IsSolvable G := by
  classical
  haveI := Fintype.ofFinite G
  let E' : IntermediateField K₀ (PadicAlgCl q) := IntermediateField.extendScalars hK.le
  have memE : ∀ x : PadicAlgCl q, x ∈ E' ↔ x ∈ L := fun x => Iff.rfl
  let toL : E' → L := fun x => ⟨x.1, (memE x.1).1 x.2⟩
  let ofL : L → E' := fun y => ⟨y.1, (memE y.1).2 y.2⟩
  have hfix : ∀ (g : G) (r : K₀), g • toL (algebraMap K₀ E' r) = toL (algebraMap K₀ E' r) :=
    fun g r => (hK.mem_iff _).1 r.2 g

  let ψ₀ : G → (E' ≃ₐ[K₀] E') := fun g =>
    { toFun := fun x => ofL (g • toL x)
      invFun := fun x => ofL (g⁻¹ • toL x)
      left_inv := fun x => by
        change ofL (g⁻¹ • g • toL x) = x
        rw [← mul_smul, inv_mul_cancel, one_smul]
      right_inv := fun x => by
        change ofL (g • g⁻¹ • toL x) = x
        rw [← mul_smul, mul_inv_cancel, one_smul]
      map_mul' := fun x y => by
        change ofL (g • (toL x * toL y)) = ofL (g • toL x) * ofL (g • toL y)
        rw [smul_mul']
        rfl
      map_add' := fun x y => by
        change ofL (g • (toL x + toL y)) = ofL (g • toL x) + ofL (g • toL y)
        rw [smul_add]
        rfl
      commutes' := fun r => by
        change ofL (g • toL (algebraMap K₀ E' r)) = _
        rw [hfix] }
  have ψ₀_apply : ∀ (g : G) (x : E'), toL (ψ₀ g x) = g • toL x := fun g x => rfl
  let ψ : G →* (E' ≃ₐ[K₀] E') :=
    { toFun := ψ₀
      map_one' := by
        ext x
        change ((ofL ((1 : G) • toL x) : E') : PadicAlgCl q) = x
        rw [one_smul]
      map_mul' := fun g h => by
        ext x
        change ((ofL ((g * h) • toL x) : E') : PadicAlgCl q) = ((ofL (g • toL (ofL (h • toL x))) : E') : PadicAlgCl q)
        rw [mul_smul] }
  have hψ : Function.Injective ψ := by
    intro g h hgh
    apply FaithfulSMul.eq_of_smul_eq_smul (α := L)
    intro y
    have := congrArg (fun f : E' ≃ₐ[K₀] E' => toL (f (ofL y))) hgh
    exact this

  let eL : E' ≃ₗ[ℚ_[q]] L :=
    { toFun := toL, invFun := ofL, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
      map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  haveI : Module.Finite ℚ_[q] E' := Module.Finite.equiv eL.symm
  haveI : FiniteDimensional K₀ E' := Module.Finite.of_restrictScalars_finite ℚ_[q] K₀ E'
  have hdeg : Module.finrank K₀ E' = Fintype.card G := by
    have h1 := ExtCitation.LocalLevel.finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq q L G hG K₀ hK.le hK.mem_iff
    have h2 := Module.finrank_mul_finrank ℚ_[q] K₀ E'
    rw [LinearEquiv.finrank_eq eL, h1, Nat.card_eq_fintype_card, mul_comm] at h2
    have hpos : 0 < Module.finrank ℚ_[q] K₀ := Module.finrank_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h2
  have hcard : Fintype.card (E' ≃ₐ[K₀] E') = Module.finrank K₀ E' := by
    apply le_antisymm AlgEquiv.card_le
    rw [hdeg]
    exact Fintype.card_le_of_injective ψ hψ
  haveI : IsGalois K₀ E' := IsGalois.of_card_aut_eq_finrank K₀ E' (by rw [Nat.card_eq_fintype_card]; exact hcard)
  haveI := IntermediateField.isSolvable_algEquiv_of_padic q K₀ E'
  exact solvable_of_solvable_injective hψ

end Solvable
p2m_reactivate "P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField.LevelArith P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField.LevelArith.N5"

structure BridgeFC (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (w : HeightOneSpectrum (𝓞 F)) where
  q : ℕ
  [hq : Fact q.Prime]
  L : IntermediateField ℚ_[q] (PadicAlgCl q)
  [fd : FiniteDimensional ℚ_[q] L]
  [act : MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F w)) L]
  [faith : FaithfulSMul (↥(NumberField.PlaceDecomp.decomp E F w)) L]
  [actU : MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L)ˣ]
  Φ : w.adicCompletion F ≃+* L
  h1 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x
  h2 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L)
  h3 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : w.adicCompletion F), Φ (g • x) = g • Φ x
  hqw : ((q : ℕ) : 𝓞 F) ∈ w.asIdeal
  K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)
  [fd₀ : FiniteDimensional ℚ_[q] K₀]
  base : ExtCitation.LocalLevel.IsBase q L (↥(NumberField.PlaceDecomp.decomp E F w)) K₀
  θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L)ˣ ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ
  hθ : ∀ y : (↥L)ˣ, ((Additive.toMul (θ.hom (Additive.ofMul y)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = Φ.symm (y : L)
  u : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L)ˣ)
  hu : ExtCitation.LocalLevel.IsLocalFundamentalClass q L (↥(NumberField.PlaceDecomp.decomp E F w)) K₀ u

theorem nonempty_bridgeFC (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (w : HeightOneSpectrum (𝓞 F)) : Nonempty (BridgeFC E F w) := by
  haveI : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ E F
  haveI : Finite (F ≃ₐ[E] F) := inferInstance
  obtain ⟨q, hq, L, fd, act, faith, actU, Φ, h1, h2, h3, hqw⟩ := NumberField.PlaceDecomp.exists_localLevel_ringEquiv_adicCompletion E F w
  obtain ⟨K₀, fd₀, base⟩ := exists_isBase q L (↥(NumberField.PlaceDecomp.decomp E F w)) h1
  let ΦM : (↥L)ˣ →* (w.adicCompletion F)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom
  have hΦM : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (y : (↥L)ˣ), ΦM (g • y) = g • ΦM y := by
    intro g y
    apply Units.ext
    show Φ.symm ((g • y : (↥L)ˣ) : ↥L) = ((g • ΦM y : (w.adicCompletion F)ˣ) : w.adicCompletion F)
    rw [h2 g y, NumberField.PlaceDecomp.coe_smul_units]
    apply Φ.injective
    rw [h3 g, RingEquiv.apply_symm_apply]
    congr 1
    show (y : ↥L) = Φ (Φ.symm (y : ↥L))
    exact (Φ.apply_symm_apply _).symm
  let θ := M4aHerbrand.repHomOfMulEquivariant ΦM hΦM
  have hθ : ∀ y : (↥L)ˣ, ((Additive.toMul (θ.hom (Additive.ofMul y)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = Φ.symm (y : ↥L) :=
    fun y => rfl
  have hsolv : Group.IsSolvable (↥(NumberField.PlaceDecomp.decomp E F w)) := isSolvable_layer q L (↥(NumberField.PlaceDecomp.decomp E F w)) h1 K₀ base
  obtain ⟨u, hu⟩ := (ExtCitation.LocalLevel.existsUnique_isLocalFundamentalClass q L (↥(NumberField.PlaceDecomp.decomp E F w)) h1 h2 hsolv K₀ base).exists
  exact ⟨{ q := q, L := L, Φ := Φ, h1 := h1, h2 := h2, h3 := h3, hqw := hqw, K₀ := K₀, base := base, θ := θ, hθ := hθ, u := u, hu := hu }⟩

noncomputable def chosen (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (w : HeightOneSpectrum (𝓞 F)) : BridgeFC E F w :=
  Classical.choice (nonempty_bridgeFC E F w)

end NumberField.PlaceDecomp.FCFamily
p2m_reactivate "P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField.LevelArith P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField.LevelArith.N5"
p2m_reactivate "P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField.LevelArith P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField.LevelArith.N5"
p2m_reactivate "P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField.LevelArith P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField.LevelArith.N5"

namespace NumberField
p2m_export "NumberField" "mk place AdeleRing SUnits.sUnitsRep SUnits.val PlaceAbove.above PlaceAbove.comap_above PlaceDecomp.decomp PlaceDecomp.coe_smul_units IdeleLocalInv.HasLocalInv PlaceDecomp.exists_localLevel_ringEquiv_adicCompletion"
namespace IdeleLocalInv
p2m_export "NumberField.IdeleLocalInv" "HasLocalInv"
namespace ReadingExists
p2m_open "NumberField.IdeleLocalInv NumberField"
open NumberField.PlaceDecomp.FCFamily

set_option maxHeartbeats 6400000 in

theorem exists_eq_zsmul_map
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K] (w : HeightOneSpectrum (𝓞 K))
    (q : ℕ) [Fact q.Prime] (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    [MulSemiringAction ↥(NumberField.PlaceDecomp.decomp E K w) L] [FaithfulSMul ↥(NumberField.PlaceDecomp.decomp E K w) L]
    [MulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K w) (↥L)ˣ]
    (Φ : w.adicCompletion K ≃+* L)
    (h1 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : ℚ_[q]), g • algebraMap ℚ_[q] L y = algebraMap ℚ_[q] L y)
    (h2 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : (↥L)ˣ), ((g • y : (↥L)ˣ) : L) = g • (y : L))
    (h3 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : w.adicCompletion K), Φ (g • y) = g • Φ y)
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
    (base : ExtCitation.LocalLevel.IsBase q L ↥(NumberField.PlaceDecomp.decomp E K w) K₀)
    (θ : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K w) (↥L)ˣ ⟶
      Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K)ˣ)
    (hθ : ∀ y : (↥L)ˣ, ((Additive.toMul (θ.hom (Additive.ofMul y)) : (w.adicCompletion K)ˣ) : w.adicCompletion K) = Φ.symm (y : L))
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K w) (↥L)ˣ))
    (hu : ExtCitation.LocalLevel.IsLocalFundamentalClass q L ↥(NumberField.PlaceDecomp.decomp E K w) K₀ u)
    (X : groupCohomology (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K)ˣ) 2) :
    ∃ n : ℤ, X = n • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E K w)) θ 2).hom u := by
  haveI : FiniteDimensional E K := Module.Finite.of_restrictScalars_finite ℚ E K
  haveI : Finite (K ≃ₐ[E] K) := inferInstance
  have hsolv : Group.IsSolvable ↥(NumberField.PlaceDecomp.decomp E K w) := isSolvable_layer q L (↥(NumberField.PlaceDecomp.decomp E K w)) h1 K₀ base
  obtain ⟨-, -, hspan⟩ :=
    ExtCitation.LocalLevel.isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass
      q L (↥(NumberField.PlaceDecomp.decomp E K w)) h1 h2 hsolv K₀ base u hu

  have hres_inj : Function.Injective
      (groupCohomology.map (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))).subtype (𝟙 (Rep.res (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))).subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ))) 2).hom := by
    let eT : ↥(NumberField.PlaceDecomp.decomp E K w) →* ↥(⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))) := (Subgroup.topEquiv : ↥(⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))) ≃* ↥(NumberField.PlaceDecomp.decomp E K w)).symm.toMonoidHom
    have key : groupCohomology.map (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))).subtype (𝟙 (Rep.res (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))).subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ))) 2 ≫
        groupCohomology.map eT (𝟙 (Rep.res eT (Rep.res (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))).subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ)))) 2 = 𝟙 _ := by
      rw [← groupCohomology.map_comp]
      exact groupCohomology.map_id (B := (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ)) (n := 2)
    have hleft : ∀ y : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ),
        (groupCohomology.map eT (𝟙 (Rep.res eT (Rep.res (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))).subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ)))) 2).hom
          ((groupCohomology.map (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))).subtype (𝟙 (Rep.res (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))).subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ))) 2).hom y) = y := by
      intro y
      have hy := congrArg (fun T => (ModuleCat.Hom.hom T) y) key
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hy
      exact hy
    exact Function.LeftInverse.injective hleft

  have hθiso : ∃ θ' : (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ) ⟶ (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ), θ' ≫ θ = 𝟙 _ := by
    let ΦM : (w.adicCompletion K)ˣ →* (↥L)ˣ := Units.map Φ.toRingHom.toMonoidHom
    have hΦM : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (m : (w.adicCompletion K)ˣ), ΦM (g • m) = g • ΦM m := by
      intro g m
      apply Units.ext
      rw [h2 g (ΦM m)]
      show Φ ((g • m : (w.adicCompletion K)ˣ) : (w.adicCompletion K)) = g • Φ (m : (w.adicCompletion K))
      rw [NumberField.PlaceDecomp.coe_smul_units, h3 g]
    refine ⟨M4aHerbrand.repHomOfMulEquivariant ΦM hΦM, ?_⟩
    refine Rep.hom_ext ?_
    ext z
    rw [Rep.hom_comp, Rep.hom_id]
    show θ.hom ((M4aHerbrand.repHomOfMulEquivariant ΦM hΦM).hom z) = z
    rw [M4aHerbrand.repHomOfMulEquivariant_hom_apply]
    change Additive.ofMul (Additive.toMul (θ.hom (Additive.ofMul (ΦM (Additive.toMul z))))) = Additive.ofMul (Additive.toMul z)
    congr 1
    apply Units.ext
    have h : ((Additive.toMul (θ.hom (Additive.ofMul (ΦM (Additive.toMul z)))) : (w.adicCompletion K)ˣ) : (w.adicCompletion K)) =
        Φ.symm ((ΦM (Additive.toMul z) : (↥L)ˣ) : ↥L) := hθ (ΦM (Additive.toMul z))
    refine h.trans ?_
    show Φ.symm (Φ ((Additive.toMul z : (w.adicCompletion K)ˣ) : (w.adicCompletion K))) = ((Additive.toMul z : (w.adicCompletion K)ˣ) : (w.adicCompletion K))
    exact Φ.symm_apply_apply _

  obtain ⟨θ', hθ'⟩ := hθiso
  have hback : ∀ y : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ),
      (groupCohomology.map (MonoidHom.id (↥(NumberField.PlaceDecomp.decomp E K w))) θ 2).hom ((groupCohomology.map (MonoidHom.id (↥(NumberField.PlaceDecomp.decomp E K w))) θ' 2).hom y) = y := by
    intro y
    have hc' := congrArg (fun T => (ModuleCat.Hom.hom T) y) (groupCohomology.map_id_comp θ' θ 2)
    simp only [hθ', groupCohomology.map_id, ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply,
      LinearMap.id_apply] at hc'
    exact hc'.symm
  set X' := (groupCohomology.map (MonoidHom.id (↥(NumberField.PlaceDecomp.decomp E K w))) θ' 2).hom X with hX'
  have hmem : (groupCohomology.map (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))).subtype (𝟙 (Rep.res (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))).subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ))) 2).hom X' ∈ Submodule.span ℤ {(groupCohomology.map (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))).subtype (𝟙 (Rep.res (⊤ : Subgroup (↥(NumberField.PlaceDecomp.decomp E K w))).subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L)ˣ))) 2).hom u} := by
    rw [hspan ⊤]; trivial
  obtain ⟨n, hn⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨n, ?_⟩
  have hXu : X' = n • u := by
    apply hres_inj
    rw [map_zsmul, ← hn]
    exact int_smul_eq_zsmul _ n _
  calc X = (groupCohomology.map (MonoidHom.id (↥(NumberField.PlaceDecomp.decomp E K w))) θ 2).hom X' := (hback _).symm
    _ = n • (groupCohomology.map (MonoidHom.id (↥(NumberField.PlaceDecomp.decomp E K w))) θ 2).hom u := by rw [hXu, map_zsmul]

end NumberField.IdeleLocalInv.ReadingExists
p2m_reactivate "P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField.LevelArith P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField.LevelArith.N5"
p2m_reactivate "P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField.LevelArith P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField.LevelArith.N5"
p2m_reactivate "P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField.LevelArith P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le.NumberField.LevelArith.N5"

open NumberField.PlaceDecomp.FCFamily NumberField.IdeleLocalInv.ReadingExists in

open NumberField.PlaceDecomp.FCFamily NumberField.IdeleLocalInv.ReadingExists in

theorem solution
    (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥L]

    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] [IsGalois ↥L ↥(levelField L F hLF)] (hF : F.IsUnramifiedOutside S)
    (F'' : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF'' : L ≤ F'') [FiniteDimensional ℚ ↥F''] [Normal ℚ ↥F''] [IsGalois ↥L ↥(levelField L F'' hLF'')] (hF'' : F''.IsUnramifiedOutside S)
    (hFF'' : F ≤ F'')

    (ι : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) →* (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (_ : ∀ g : ↥L.fixingSubgroup, ι (levelGal L F hLF g) = (g : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (φ : Rep.res ι ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶
      NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))
    (_ : Function.Bijective φ.hom)
    (_ : ∀ x, ((NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (φ.hom x) : ↥(levelField L F hLF)) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
    (ι'' : (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) →* (↥L.fixingSubgroup ⧸ F''.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (_ : ∀ g : ↥L.fixingSubgroup, ι'' (levelGal L F'' hLF'' g) = (g : ↥L.fixingSubgroup ⧸ F''.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (φ'' : Rep.res ι'' ((sUnitsMaxRep S L).quotientToInvariants (F''.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶
      NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F'' hLF'') (placesOverPrimesFinset ↥L S))
    (_ : Function.Bijective φ''.hom)
    (_ : ∀ x, ((NumberField.SUnits.val ↥L ↥(levelField L F'' hLF'') (placesOverPrimesFinset ↥L S) (φ''.hom x) : ↥(levelField L F'' hLF'')) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))

    (D : IdeleGaloisDescent (𝓞 ↥(levelField L F hLF)) ↥L ↥(levelField L F hLF))
    [MulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ]
    (hactI : ∀ (g : ↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (x : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ), g • x = D.unitsAct g x)
    (j : NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) ⟶
      Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)
    (_ : ∀ y, Additive.toMul (j.hom y) =
      Units.map (algebraMap ↥(levelField L F hLF) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) : ↥(levelField L F hLF) →* AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))
        (NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) y))
    (D'' : IdeleGaloisDescent (𝓞 ↥(levelField L F'' hLF'')) ↥L ↥(levelField L F'' hLF''))
    [MulDistribMulAction (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) (AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF''))ˣ]
    (hactI'' : ∀ (g : ↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) (x : (AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF''))ˣ), g • x = D''.unitsAct g x)
    (j'' : NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F'' hLF'') (placesOverPrimesFinset ↥L S) ⟶
      Rep.ofMulDistribMulAction (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) (AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF''))ˣ)
    (_ : ∀ y, Additive.toMul (j''.hom y) =
      Units.map (algebraMap ↥(levelField L F'' hLF'') (AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF'')) : ↥(levelField L F'' hLF'') →* AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF''))
        (NumberField.SUnits.val ↥L ↥(levelField L F'' hLF'') (placesOverPrimesFinset ↥L S) y))

    (f : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (f'' : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F''.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (hff'' : ∀ g h : ↥L.fixingSubgroup,
      ((f'' ((g : ↥L.fixingSubgroup ⧸ F''.fixingSubgroup.comap L.fixingSubgroup.subtype), (h : ↥L.fixingSubgroup ⧸ F''.fixingSubgroup.comap L.fixingSubgroup.subtype)) :
          (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L)
        = ((f ((g : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype), (h : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) :
          (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L))
    (v : HeightOneSpectrum (𝓞 ↥L)) (t : AddCircle (1 : ℚ))
    (h : NumberField.IdeleLocalInv.HasLocalInv ↥L ↥(levelField L F hLF) D hactI ((groupCohomology.map ι (φ ≫ j) 2) (H2π _ f)) v t) :
    NumberField.IdeleLocalInv.HasLocalInv ↥L ↥(levelField L F'' hLF'') D'' hactI'' ((groupCohomology.map ι'' (φ'' ≫ j'') 2) (H2π _ f'')) v t := by

  have hK : levelField L F hLF ≤ levelField L F'' hLF'' := fun x hx => hFF'' hx
  letI algK : Algebra ↥(levelField L F hLF) ↥(levelField L F'' hLF'') := (IntermediateField.inclusion hK).toRingHom.toAlgebra
  haveI : IsScalarTower ↥L ↥(levelField L F hLF) ↥(levelField L F'' hLF'') := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have halg : ∀ y : ↥(levelField L F hLF), ((algebraMap ↥(levelField L F hLF) ↥(levelField L F'' hLF'') y : ↥(levelField L F'' hLF'')) : AlgebraicClosure ℚ) = (y : AlgebraicClosure ℚ) :=
    fun _ => rfl

  let res : (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) →* (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) := AlgEquiv.restrictNormalHom ↥(levelField L F hLF)
  have hres : ∀ (σ : (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF''))) (y : ↥(levelField L F hLF)), algebraMap ↥(levelField L F hLF) ↥(levelField L F'' hLF'') (res σ y) = σ (algebraMap ↥(levelField L F hLF) ↥(levelField L F'' hLF'') y) :=
    fun σ y => AlgEquiv.restrictNormal_commutes σ ↥(levelField L F hLF) y
  have hsurj : Function.Surjective res := AlgEquiv.restrictNormalHom_surjective ↥(levelField L F'' hLF'')
  let ιq : (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) ⧸ res.ker ≃* (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) := QuotientGroup.quotientKerEquivOfSurjective res hsurj
  have hιq : ∀ (g : (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF''))) (y : ↥(levelField L F hLF)),
      algebraMap ↥(levelField L F hLF) ↥(levelField L F'' hLF'') (ιq (QuotientGroup.mk g) y) = g (algebraMap ↥(levelField L F hLF) ↥(levelField L F'' hLF'') y) := fun g y => hres g y

  let J : Rep.res (ιq.toMonoidHom.comp (QuotientGroup.mk' res.ker)) (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) ⟶
      Rep.ofMulDistribMulAction (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) (AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF''))ˣ :=
    Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap _ _
      (MonoidHom.toAdditive (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange ↥(levelField L F hLF) ↥(levelField L F'' hLF'')).β.toMonoidHom)).toIntLinearMap
      (fun σ a => by
        change Additive.ofMul (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange ↥(levelField L F hLF) ↥(levelField L F'' hLF'')).β.toMonoidHom
            (Additive.toMul ((Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ).ρ (ιq (QuotientGroup.mk σ)) a))) =
          (Rep.ofMulDistribMulAction (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) (AdeleRing (𝓞 ↥(levelField L F'' hLF'')) ↥(levelField L F'' hLF''))ˣ).ρ σ
            (Additive.ofMul (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange ↥(levelField L F hLF) ↥(levelField L F'' hLF'')).β.toMonoidHom (Additive.toMul a)))
        rw [Rep.ofMulDistribMulAction_ρ_apply_apply, Rep.ofMulDistribMulAction_ρ_apply_apply, toMul_ofMul, hactI'', hactI]
        exact congrArg Additive.ofMul (M4aHerbrand.IdeleGaloisDescent.unitsAct_map_genuineBaseChange ↥L ↥(levelField L F hLF) ↥(levelField L F'' hLF'') D D'' σ (Additive.toMul a)).symm))
  have hJ : ∀ x : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ, J.hom (Additive.ofMul x) =
      Additive.ofMul (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange ↥(levelField L F hLF) ↥(levelField L F'' hLF'')).β.toMonoidHom x) := fun _ => rfl

  have hsq : (groupCohomology.map ι'' (φ'' ≫ j'') 2) (H2π _ f'') =
      (groupCohomology.map (ιq.toMonoidHom.comp (QuotientGroup.mk' res.ker)) J 2).hom ((groupCohomology.map ι (φ ≫ j) 2) (H2π _ f)) := by

    rename_i hι _ hval hι'' _ hval'' _ hj _ hj''
    exact NumberField.LevelArith.N5.frame_square S L F hLF F'' hLF'' hFF'' ι hι φ hval ι'' hι'' φ'' hval'' j hj j'' hj'' f f'' hff'' halg
      (ιq.toMonoidHom.comp (QuotientGroup.mk' res.ker))
      (fun γ => NumberField.LevelArith.N5.restrictNormalHom_levelGal L F F'' hLF hLF'' algK halg γ) J hJ

  obtain ⟨prG, hprG, w, hw, q, hq, hqw, L', fdL', actL', faithL', actUL', Φ, h1, h2, h3, K₀, fdK₀, hbase, θ, hθ, u, hu, n, hcoord, ht⟩ := h

  obtain ⟨W, hWw⟩ : ∃ W : HeightOneSpectrum (𝓞 ↥(levelField L F'' hLF'')), W.under (𝓞 ↥(levelField L F hLF)) = w :=
    ⟨NumberField.PlaceAbove.above ↥(levelField L F hLF) ↥(levelField L F'' hLF'') w,
      HeightOneSpectrum.ext (NumberField.PlaceAbove.comap_above ↥(levelField L F hLF) ↥(levelField L F'' hLF'') w)⟩
  subst hWw

  obtain ⟨prM, hprM⟩ := M4aHerbrand.exists_hom_res_decomp_ideles_adicCompletion_apply ↥L ↥(levelField L F'' hLF'') D'' hactI''
  obtain ⟨B⟩ := nonempty_bridgeFC ↥L ↥(levelField L F'' hLF'') W
  letI := B.hq; letI := B.fd; letI := B.act; letI := B.faith; letI := B.actU; letI := B.fd₀
  obtain ⟨nM, hnM⟩ := exists_eq_zsmul_map ↥L ↥(levelField L F'' hLF'') W B.q B.L B.Φ B.h1 B.h2 B.h3 B.K₀ B.base B.θ B.hθ B.u B.hu
    ((groupCohomology.map (NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F'' hLF'') W).subtype (prM W) 2).hom
      ((groupCohomology.map ι'' (φ'' ≫ j'') 2) (H2π _ f'')))

  have key := M4aHerbrand.div_natCard_decomp_eq_div_natCard_decomp_under_of_map_map_eq_zsmul_of_isScalarTower
    ↥L ↥(levelField L F hLF) ↥(levelField L F'' hLF'') res.ker ιq hιq J hJ W (prG (W.under (𝓞 ↥(levelField L F hLF)))) (hprG _) (prM W) (hprM W)
    ((groupCohomology.map ι (φ ≫ j) 2) (H2π _ f)) q L' Φ h1 h2 h3 K₀ hbase θ hθ u hu n hcoord
    B.q B.L B.Φ B.h1 B.h2 B.h3 B.K₀ B.base B.θ B.hθ B.u B.hu nM (by rw [← hsq]; exact hnM)
  refine ⟨prM, hprM, W, ?_, B.q, B.hq, B.hqw, B.L, B.fd, B.act, B.faith, B.actU, B.Φ, B.h1, B.h2, B.h3, B.K₀, B.fd₀, B.base,
    B.θ, B.hθ, B.u, B.hu, nM, hnM, ?_⟩
  ·
    rw [← hw]
    change W.asIdeal.comap _ = (W.asIdeal.comap (algebraMap (𝓞 ↥(levelField L F hLF)) (𝓞 ↥(levelField L F'' hLF'')))).comap _
    rw [Ideal.comap_comap]
    congr 1
  · rw [ht]; exact key.symm

end S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le
end P2MW
export P2MW.S_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le (solution)
