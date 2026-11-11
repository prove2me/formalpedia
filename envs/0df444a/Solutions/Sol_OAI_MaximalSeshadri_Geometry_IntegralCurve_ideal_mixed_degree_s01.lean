-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.IntegralCurve.ideal_mixed_degree_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:12:27.483148+00:00
-- url     : https://prove2.me/submissions/e14830ab-f8d8-4e75-a5c6-c2df5e4ec9a4

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_euler_pushforward_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_exists_projective_sections_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_cohomology_finite_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_lineBundle_cohomology_zero_above_two_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_projective_curve_cohomology_finite_s01

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_CohomologyIso
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.powerSection_isIso _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                       
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry

variable {X : Scheme.{0}}

lemma eulerCharacteristic_iso (f : X ⟶ Spec (CommRingCat.of ℂ))
    {M N : X.Modules} (e : M ≅ N) (d : ℕ) :
    eulerCharacteristic f d M = eulerCharacteristic f d N := by
  apply Finset.sum_congr rfl
  intro n _
  congr 2
  let := Module.compHom (cohomology M n) (baseScalars f)
  let := Module.compHom (cohomology N n) (baseScalars f)
  exact (cohomologyIso f e n).finrank_eq

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_CartierModule
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                       
section

namespace MaximalSeshadri.IdealModule

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {X Y : Scheme.{u}}

lemma equationToIdeal_app (f : Y ⟶ X) (r : Γ(X, ⊤)) (hr : (f.app ⊤) r = 0)
    (U : X.Opens) (a : Γ(X, U)) :
    (inclusion f).val.app (op U) ((equationToIdeal f r hr).val.app (op U) a) =
      X.presheaf.map (homOfLE le_top).op r * a :=
  congrArg (fun g => g.val.app (op U) a) (equationToIdeal_inclusion f r hr)

lemma isIso_equationToIdeal (f : Y ⟶ X) [QuasiCompact f]
    (r : Γ(X, ⊤)) (hr : (f.app ⊤) r = 0)
    (hprincipal : ∀ U : X.affineOpens,
      f.ker.ideal U = Ideal.span {X.presheaf.map (homOfLE le_top).op r})
    (hregular : ∀ U : X.affineOpens,
      IsLeftRegular (X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op r)) :
    IsIso (equationToIdeal f r hr) := by
  apply isIso_of_affine_app
  intro U
  have hinj : Function.Injective ((inclusion f).val.app (op U.1)) := by
    let : Mono (inclusion f).val :=
      inferInstanceAs (Mono ((Scheme.Modules.toPresheafOfModules X).map (inclusion f)))
    exact PresheafOfModules.injective_of_mono (inclusion f).val (op U.1)
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro a b hab
    apply hregular U
    have he := congrArg ((inclusion f).val.app (op U.1)) hab
    change (inclusion f).val.app (op U.1) ((equationToIdeal f r hr).val.app (op U.1) a) =
      (inclusion f).val.app (op U.1) ((equationToIdeal f r hr).val.app (op U.1) b) at he
    exact (equationToIdeal_app f r hr U.1 a).symm.trans
      (he.trans (equationToIdeal_app f r hr U.1 b))
  · intro y
    have hy : (inclusion f).val.app (op U.1) y ∈ f.ker.ideal U := by
      rw [← image_eq_ideal f U]
      exact ⟨y, rfl⟩
    rw [hprincipal U] at hy
    have hd : X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op r ∣
        (show Γ(X, U.1) from (inclusion f).val.app (op U.1) y) :=
      Ideal.mem_span_singleton.mp hy
    obtain ⟨a, ha⟩ := hd
    refine ⟨a, hinj ?_⟩
    exact (equationToIdeal_app f r hr U.1 a).trans ha.symm

end

end MaximalSeshadri.IdealModule

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_ClosedModuleExact
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                           
section

namespace MaximalSeshadri.IdealModule
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
variable {X Y : Scheme.{0}}

lemma structureMap_epi (f : X ⟶ Y) [IsClosedImmersion f] : Epi (structureMap f) := by
  let F := SheafOfModules.toSheaf Y.ringCatSheaf
  have hloc : TopCat.Presheaf.IsLocallySurjective (F.map (structureMap f)).hom := by
    apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
    intro U t y hy
    obtain ⟨_,⟨V,hA,rfl⟩,hyV,hVU⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
    obtain ⟨s,hs⟩ := f.app_surjective V hA
      (((F.obj ((Scheme.Modules.pushforward f).obj (unit X))).obj.map
        (homOfLE hVU).op) t)
    exact ⟨V,hVU,⟨s,hs⟩,hyV⟩
  let : Epi (F.map (structureMap f)) :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp hloc
  exact F.epi_of_epi_map inferInstance

theorem closedSequence_exact (f : X ⟶ Y) [IsClosedImmersion f] :
    (ShortComplex.mk (inclusion f) (structureMap f) (kernel.condition _)).ShortExact := by
  let := structureMap_epi f
  exact { exact := ShortComplex.exact_kernel _ }

end
end MaximalSeshadri.IdealModule
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_ModuleLocal
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section

namespace MaximalSeshadri.ModuleLocal
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

variable {X : Scheme.{0}} {M N : X.Modules}

lemma exact_of_local (S : ShortComplex X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      (S.map (Scheme.Modules.restrictFunctor U.ι)).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  apply (IsZero.iff_id_eq_zero _).mpr
  apply eq_zero_of_local
  intro x
  obtain ⟨U,hx,hU⟩ := h x
  have : PreservesFiniteLimits (Scheme.Modules.restrictFunctor U.ι) := by
    have : PreservesFiniteLimits
        (Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.toPresheaf U.toScheme) := by
      change PreservesFiniteLimits
        (Scheme.Modules.toPresheaf X ⋙ (Functor.whiskeringLeft _ _ _).obj U.ι.opensFunctor.op)
      have : PreservesFiniteLimits (Scheme.Modules.toPresheaf X) := inferInstance
      have : PreservesFiniteLimits
          ((Functor.whiskeringLeft _ _ Ab).obj U.ι.opensFunctor.op) := inferInstance
      exact comp_preservesFiniteLimits _ _
    exact preservesFiniteLimits_of_reflects_of_preserves _
      (Scheme.Modules.toPresheaf U.toScheme)
  have hz : IsZero ((Scheme.Modules.restrictFunctor U.ι).obj S.homology) :=
    ((ShortComplex.exact_iff_isZero_homology _).mp hU).of_iso
      (S.mapHomologyIso (Scheme.Modules.restrictFunctor U.ι)).symm
  refine ⟨U,hx,?_⟩
  rw [CategoryTheory.Functor.map_id]
  exact hz.eq_of_src _ _

end
end MaximalSeshadri.ModuleLocal

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_LineClosedUnit
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section

namespace MaximalSeshadri.LineClosedUnit
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.Frames

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

lemma framed_map (L : LineBundle Y) (U : Y.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme) :
    e.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map (map f L) ≫
      (frame f L U e).hom = IdealModule.structureMap (f ∣_ U) := by
  dsimp only [map, IdealModule.structureMap]
  have hu := OpenBaseChange.unit_compatibility f U L.sheaf
  have hn := (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit_naturality e.hom
  have hb := pullbackUnit_adjunction (f ∣_ U)
  rw [Adjunction.homEquiv_unit] at hb
  dsimp only [frame, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  simp only [← Category.assoc]
  rw [Category.assoc e.inv, hu]
  simp only [Category.assoc]
  have hec : (OpenBaseChange.leftSquare f U).hom.app L.sheaf ≫
      ((OpenBaseChange.leftSquare f U).app L.sheaf).inv = 𝟙 _ :=
    ((OpenBaseChange.leftSquare f U).app L.sheaf).hom_inv_id
  rw [← Functor.map_comp_assoc, hec]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  change e.inv ≫ (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app _ ≫
    (Scheme.Modules.pushforward (f ∣_ U)).map
      ((Scheme.Modules.pullback (f ∣_ U)).map e.hom ≫ (pullbackUnitIso (f ∣_ U)).hom) = _
  rw [Functor.map_comp]
  have hn' := congrArg (fun t => e.inv ≫ t ≫
    (Scheme.Modules.pushforward (f ∣_ U)).map (pullbackUnitIso (f ∣_ U)).hom) hn
  simp only [Category.assoc, hb] at hn'
  exact hn'.trans (e.inv_hom_id_assoc _)

theorem epi [IsClosedImmersion f] (L : LineBundle Y) : Epi (map f L) := by
  apply ModuleLocal.epi_of_local
  intro y
  obtain ⟨U,hy,⟨e⟩⟩ := L.locallyRankOne y
  refine ⟨U,hy,?_⟩
  have hg : Epi (IdealModule.structureMap (f ∣_ U)) := IdealModule.structureMap_epi _
  have he := framed_map f L U e
  have : Epi (e.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map (map f L) ≫
    (frame f L U e).hom) := he.symm ▸ hg
  have h1 : Epi ((Scheme.Modules.restrictFunctor U.ι).map (map f L) ≫
      (frame f L U e).hom) := epi_of_epi e.inv _
  exact (epi_comp_iff_of_isIso _ _).mp h1

end
end MaximalSeshadri.LineClosedUnit

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_PrincipalSequence
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
attribute [-simp] _root_.OAI.MaximalSeshadri.Frames.coefficient_scalarEnd _root_.OAI.MaximalSeshadri.Frames.endUnit_val _root_.OAI.MaximalSeshadri.Frames.moduleSectionEquiv_apply _root_.OAI.MaximalSeshadri.Projective.ratioOn_full _root_.OAI.MaximalSeshadri.Projective.ratioOn_self _root_.OAI.MaximalSeshadri.Projective.ratioUnitOn_val _root_.OAI.MaximalSeshadri.Projective.scalarEnd_one _root_.OAI.MaximalSeshadri.Projective.scalarEnd_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MaximalSeshadri.PrincipalSequence
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.Frames

variable {X Y : Scheme.{0}}

lemma scalarEnd_eq_multiply (r : Γ(X,⊤)) : scalarEnd r = IdealModule.multiply r := rfl

lemma end_regular_of_mono (a : O X ⟶ O X) [Mono a] : IsLeftRegular (endValue a) := by
  have hinj : Function.Injective (a.val.app (op ⊤)) :=
    PresheafOfModules.injective_of_mono
      ((Scheme.Modules.toPresheafOfModules X).map a) (op ⊤)
  intro r s hrs
  apply hinj
  change a.app ⊤ r = a.app ⊤ s
  rw [end_apply a ⊤ r, end_apply a ⊤ s]
  change r * endValue a = s * endValue a
  simpa only [mul_comm] using hrs

theorem exact [IsAffine Y] (f : X ⟶ Y) [IsClosedImmersion f]
    (a : O Y ⟶ O Y) [Mono a]
    (h : f.ker.ideal ⟨⊤,isAffineOpen_top Y⟩ = Ideal.span {endValue a}) :
    ∃ hz : a ≫ IdealModule.structureMap f = 0,
      (ShortComplex.mk a (IdealModule.structureMap f) hz).ShortExact := by
  let r := endValue a
  have hr : f.appTop r = 0 := by
    apply f.ideal_ker_le ⟨⊤, isAffineOpen_top Y⟩
    rw [h]
    exact Ideal.subset_span (Set.mem_singleton r)
  have hreg : IsLeftRegular r := end_regular_of_mono a
  have hprincipal (U : Y.affineOpens) : f.ker.ideal U =
      Ideal.span {Y.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op r} := by
    rw [← f.ker.map_ideal (U := U) (V := ⟨⊤,isAffineOpen_top Y⟩) (by change U.1 ≤ ⊤; exact le_top), h]
    simp only [Ideal.map_span, Set.image_singleton]
    rfl
  have hi : IsIso (IdealModule.equationToIdeal f r hr) :=
    IdealModule.isIso_equationToIdeal f r hr hprincipal
      (IdealModule.restriction_regular r hreg)
  have he : a = IdealModule.multiply r := by
    rw [← scalarEnd_eq_multiply]
    apply endValue_injective
    simp [r]
  have hz : a ≫ IdealModule.structureMap f = 0 := by
    rw [he]
    exact IdealModule.multiply_structure_zero f r hr
  refine ⟨hz,?_⟩
  let S := ShortComplex.mk a (IdealModule.structureMap f) hz
  let T := ShortComplex.mk (IdealModule.inclusion f) (IdealModule.structureMap f)
    (kernel.condition (IdealModule.structureMap f))
  let equationIso := asIso (IdealModule.equationToIdeal f r hr)
  let e : S ≅ T := ShortComplex.isoMk equationIso
    (Iso.refl _) (Iso.refl _) (by
      change IdealModule.equationToIdeal f r hr ≫ IdealModule.inclusion f = a ≫ 𝟙 _
      rw [Category.comp_id]
      exact (IdealModule.equationToIdeal_inclusion f r hr).trans he.symm) (by
      change 𝟙 (IdealModule.unit Y) ≫ IdealModule.structureMap f =
        IdealModule.structureMap f ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id])
  exact ShortComplex.shortExact_of_iso e.symm (IdealModule.closedSequence_exact f)

end
end MaximalSeshadri.PrincipalSequence

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_EulerExact
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.powerSection_isIso _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.Projective.boolChartUnique _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                    
section

namespace MaximalSeshadri.Cohomology
noncomputable section
open CategoryTheory CategoryTheory.Abelian

lemma alternatingTrunc_succ (a : ℕ → ℤ) (d : ℕ) :
    alternatingTrunc a (d+1) = alternatingTrunc a d + (-1 : ℤ)^(d+1) * a (d+1) := by
  exact Finset.sum_range_succ _ _

lemma finrank_middle_of_exact {K U V W : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V]
    (f : U →ₗ[K] V) (g : V →ₗ[K] W) (hfg : Function.Exact f g) :
    Module.finrank K V = Module.finrank K f.range + Module.finrank K g.range := by
  have hh := LinearMap.finrank_range_add_finrank_ker g
  rw [hfg.linearMap_ker_eq] at hh
  omega

universe w v u t
variable {K : Type t} [Field K] {C : Type u} [Category.{v} C] [Abelian C]
  [Linear K C] [HasExt.{w} C]

variable (E : C) {S : ShortComplex C} (hS : S.ShortExact)

include hS in
lemma cohomology_exact₂ (n : ℕ) :
    Function.Exact (cohomologyMap₁ (K := K) E (S := S) n)
      (cohomologyMap₂ (K := K) E (S := S) n) := by
  intro x
  constructor
  · exact Ext.covariant_sequence_exact₂ E hS x
  · rintro ⟨y, rfl⟩
    change (y.comp (Ext.mk₀ S.f) (add_zero n)).comp (Ext.mk₀ S.g) (add_zero n) = 0
    simp [Ext.mk₀_comp_mk₀]

lemma cohomology_exact₃ (n : ℕ) :
    Function.Exact (cohomologyMap₂ (K := K) E (S := S) n)
      (cohomologyBoundary (K := K) E hS n) := by
  intro x
  constructor
  · exact Ext.covariant_sequence_exact₃ E hS x rfl
  · rintro ⟨y, rfl⟩
    change (y.comp (Ext.mk₀ S.g) (add_zero n)).comp hS.extClass rfl = 0
    rw [Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]

lemma cohomology_exact₁ (n : ℕ) :
    Function.Exact (cohomologyBoundary (K := K) E hS n)
      (cohomologyMap₁ (K := K) E (S := S) (n+1)) := by
  intro x
  constructor
  · exact fun hx => Ext.covariant_sequence_exact₁ E hS x hx rfl
  · rintro ⟨y, rfl⟩
    change (y.comp hS.extClass rfl).comp (Ext.mk₀ S.f) (add_zero (n+1)) = 0
    rw [Ext.comp_assoc_of_third_deg_zero, hS.extClass_comp, Ext.comp_zero]

theorem extEuler_add_of_boundary_zero (d : ℕ)
    (hfinite₁ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₁ n))
    (hfinite₂ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₂ n))
    (hfinite₃ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₃ n))
    (hvan : cohomologyBoundary (K := K) E hS d = 0) :
    extEuler (K := K) E S.X₂ d =
      extEuler (K := K) E S.X₁ d + extEuler (K := K) E S.X₃ d := by
  classical
  let a (n : ℕ) : ℤ := Module.finrank K (Ext E S.X₁ n)
  let b (n : ℕ) : ℤ := Module.finrank K (Ext E S.X₂ n)
  let c (n : ℕ) : ℤ := Module.finrank K (Ext E S.X₃ n)
  let f (n : ℕ) : ℤ := Module.finrank K (cohomologyMap₁ (K := K) E (S := S) n).range
  let g (n : ℕ) : ℤ := Module.finrank K (cohomologyMap₂ (K := K) E (S := S) n).range
  let h (n : ℕ) : ℤ := Module.finrank K (cohomologyBoundary (K := K) E hS n).range
  have hB (n : ℕ) (hn : n ≤ d) : b n = f n + g n := by
    let := hfinite₂ n hn
    dsimp only [b, f, g]
    exact_mod_cast finrank_middle_of_exact _ _ (cohomology_exact₂ (K := K) E hS n)
  have hC (n : ℕ) (hn : n ≤ d) : c n = g n + h n := by
    let := hfinite₃ n hn
    dsimp only [c, g, h]
    exact_mod_cast finrank_middle_of_exact _ _ (cohomology_exact₃ (K := K) E hS n)
  have hA0 : a 0 = f 0 := by
    have : Mono S.f := hS.mono_f
    dsimp only [a, f]
    exact_mod_cast (LinearMap.finrank_range_of_inj
      (f := cohomologyMap₁ (K := K) E (S := S) 0)
      (Ext.postcomp_mk₀_injective_of_mono E S.f)).symm
  have hA (n : ℕ) (hn : n+1 ≤ d) : a (n+1) = h n + f (n+1) := by
    let := hfinite₁ (n+1) hn
    dsimp only [a, h, f]
    exact_mod_cast finrank_middle_of_exact _ _ (cohomology_exact₁ (K := K) E hS n)
  have hind (n : ℕ) (hn : n ≤ d) :
      alternatingTrunc b n - alternatingTrunc a n - alternatingTrunc c n =
        (-1 : ℤ)^(n+1) * h n := by
    induction n with
    | zero => simp [alternatingTrunc, hB 0 hn, hC 0 hn, hA0]
    | succ n ih =>
      have hi := ih (by omega)
      simp only [alternatingTrunc_succ]
      calc
        _ = (alternatingTrunc b n - alternatingTrunc a n - alternatingTrunc c n) +
          (-1 : ℤ)^(n+1) * (b (n+1) - a (n+1) - c (n+1)) := by ring
        _ = _ := by rw [hi, hB (n+1) hn, hC (n+1) hn, hA n hn, pow_succ _ (n+1)]; ring
  have hd : h d = 0 := by
    dsimp only [h]
    rw [hvan, LinearMap.range_zero]
    rw [finrank_bot]
    rfl
  have hh := hind d le_rfl
  rw [hd, mul_zero] at hh
  change alternatingTrunc b d = alternatingTrunc a d + alternatingTrunc c d
  omega

include hS in

theorem extEuler_add (d : ℕ)
    (hfinite₁ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₁ n))
    (hfinite₂ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₂ n))
    (hfinite₃ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₃ n))
    [Subsingleton (Ext E S.X₁ (d+1))] :
    extEuler (K := K) E S.X₂ d =
      extEuler (K := K) E S.X₁ d + extEuler (K := K) E S.X₃ d :=
  extEuler_add_of_boundary_zero E hS d hfinite₁ hfinite₂ hfinite₃ (Subsingleton.elim _ _)

end
end MaximalSeshadri.Cohomology

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open scoped AlgebraicGeometry
variable {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of ℂ))

lemma complexExtModule_eq (M : X.Modules) (n : ℕ) :
    complexExtModule f M n = Module.compHom (cohomology M n) (baseScalars f) := by
  apply Module.ext'
  intro r x
  let := sheafComplexLinear f
  change r • x = (baseScalars f r) • x
  rw [Ext.smul_eq_comp_mk₀ (R := ℂ), Ext.smul_eq_comp_mk₀ (R := Γ(X, ⊤))]
  rfl

lemma eulerCharacteristic_eq_extEuler (M : X.Modules) (d : ℕ) :
    eulerCharacteristic f d M =
      letI := sheafComplexLinear f
      Cohomology.extEuler (K := ℂ) (structureSheaf X) M d := by
  unfold eulerCharacteristic Cohomology.extEuler Cohomology.alternatingTrunc
  apply Finset.sum_congr rfl
  intro n hn
  have hh := complexExtModule_eq f M n
  unfold cohomologyDimension
  rw [← hh]

theorem eulerCharacteristic_add {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (d : ℕ)
    (hfinite₁ : ∀ n ≤ d, letI := Module.compHom (cohomology S.X₁ n) (baseScalars f)
      FiniteDimensional ℂ (cohomology S.X₁ n))
    (hfinite₂ : ∀ n ≤ d, letI := Module.compHom (cohomology S.X₂ n) (baseScalars f)
      FiniteDimensional ℂ (cohomology S.X₂ n))
    (hfinite₃ : ∀ n ≤ d, letI := Module.compHom (cohomology S.X₃ n) (baseScalars f)
      FiniteDimensional ℂ (cohomology S.X₃ n))
    [Subsingleton (cohomology S.X₁ (d+1))] :
    eulerCharacteristic f d S.X₂ =
      eulerCharacteristic f d S.X₁ + eulerCharacteristic f d S.X₃ := by
  let := sheafComplexLinear f
  rw [eulerCharacteristic_eq_extEuler, eulerCharacteristic_eq_extEuler,
    eulerCharacteristic_eq_extEuler]
  apply Cohomology.extEuler_add (K := ℂ) (structureSheaf X) hS d
  · intro n hn
    have hh := complexExtModule_eq f S.X₁ n
    change @FiniteDimensional ℂ (cohomology S.X₁ n) _ _ (complexExtModule f S.X₁ n)
    rw [hh]
    exact hfinite₁ n hn
  · intro n hn
    have hh := complexExtModule_eq f S.X₂ n
    change @FiniteDimensional ℂ (cohomology S.X₂ n) _ _ (complexExtModule f S.X₂ n)
    rw [hh]
    exact hfinite₂ n hn
  · intro n hn
    have hh := complexExtModule_eq f S.X₃ n
    change @FiniteDimensional ℂ (cohomology S.X₃ n) _ _ (complexExtModule f S.X₃ n)
    rw [hh]
    exact hfinite₃ n hn

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_SurfaceCurveDegree
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets
open MaximalSeshadri.LocalComparison MaximalSeshadri.NodalLocal
open scoped Topology

theorem IntegralCurve.cohomology_finite (S : Surface) (C : IntegralCurve S)
    (A : LineBundle S.scheme) (hA : LineBundle.IsAmple S.scheme A)
    (L : LineBundle C.scheme) (n : ℕ) :
    letI := Module.compHom (cohomology L.sheaf n)
      (baseScalars (C.embedding ≫ S.structureMap))
    Module.Finite ℂ (cohomology L.sheaf n) := by
  obtain ⟨σ,hσ,M,a,ha,hc⟩ := C.exists_projective_sections_s01 S A hA
  let := hσ
  let := hc
  let : IsClosedImmersion (sectionsMorphism
    ((C.embedding ≫ S.structureMap).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) a ha) := hc
  exact projective_curve_cohomology_finite_s01 (C.embedding ≫ S.structureMap)
    C.dimension a ha L n

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_OpenChartDegree
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                         
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.ProjectiveBertini MaximalSeshadri.Projective MaximalSeshadri.Frames
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets
open MaximalSeshadri.LocalComparison MaximalSeshadri.NodalLocal
open scoped Topology

variable {X Y : Scheme.{0}}

lemma chart_topIso_naturality (j : Y ⟶ X) (U : X.Opens) :
    U.topIso.hom ≫ j.app U ≫ (j ⁻¹ᵁ U).topIso.inv = (j ∣_ U).appTop := by
  have H := (arrowResLEAppIso j U (j ⁻¹ᵁ U) le_rfl).hom.w
  change U.topIso.hom ≫ j.appLE U (j ⁻¹ᵁ U) le_rfl =
    (j.resLE U (j ⁻¹ᵁ U) le_rfl).appTop ≫ (j ⁻¹ᵁ U).topIso.hom at H
  rw [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appLE_eq_app] at H
  apply (cancel_mono (j ⁻¹ᵁ U).topIso.hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using H

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_SurfaceEuler
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem IntegralCurve.pushforward_cohomology_finite (S : Surface) (C : IntegralCurve S)
    (A : LineBundle S.scheme) (hA : A.IsAmple) (L : LineBundle C.scheme) (n : ℕ) :
    letI := Module.compHom (cohomology ((Scheme.Modules.pushforward C.embedding).obj L.sheaf) n)
      (baseScalars S.structureMap)
    Module.Finite ℂ (cohomology ((Scheme.Modules.pushforward C.embedding).obj L.sheaf) n) := by
  let := Module.compHom (cohomology L.sheaf n) (baseScalars (C.embedding ≫ S.structureMap))
  let := Module.compHom (cohomology ((Scheme.Modules.pushforward C.embedding).obj L.sheaf) n)
    (baseScalars S.structureMap)
  let := C.cohomology_finite S A hA L n
  exact Module.Finite.equiv (ClosedPushforward.cohomologyEquiv C.embedding S.structureMap L.sheaf n)

end
end MaximalSeshadri.Geometry

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_ArbitraryCartierEuler
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
attribute [-simp] _root_.OAI.MaximalSeshadri.Projective.scalarEnd_one _root_.OAI.MaximalSeshadri.Projective.scalarEnd_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section

namespace MaximalSeshadri.CartierSequence
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

variable {X Y : Scheme.{0}}

lemma restriction_principal_closed (f : Y ⟶ X) [IsClosedImmersion f] (U : X.affineOpens)
    (r : Γ(U.1.toScheme,⊤))
    (hI : f.ker.ideal U = Ideal.span {U.1.topIso.hom r}) :
    (f ∣_ U.1).ker.ideal ⟨⊤,isAffineOpen_top U.1.toScheme⟩ = Ideal.span {r} := by
  ext z
  rw [Scheme.Hom.ker_apply,RingHom.mem_ker]
  change (f ∣_ U.1).appTop z = 0 ↔ z ∈ Ideal.span {r}
  have hz : (f ∣_ U.1).appTop z = 0 ↔ U.1.topIso.hom z ∈ f.ker.ideal U := by
    rw [Scheme.Hom.ker_apply,RingHom.mem_ker]
    rw [← chart_topIso_naturality]
    simp only [CommRingCat.comp_apply]
    change (f ⁻¹ᵁ U.1).topIso.inv ((f.app U.1) (U.1.topIso.hom z)) = 0 ↔
      (f.app U.1) (U.1.topIso.hom z) = 0
    exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (f ⁻¹ᵁ U.1).topIso.inv).injective)
  rw [hz,hI,Ideal.mem_span_singleton,Ideal.mem_span_singleton]
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨U.1.topIso.inv a,?_⟩
    have h := congrArg U.1.topIso.inv ha
    simpa only [map_mul,U.1.topIso.hom_inv_id_apply] using h
  · rintro ⟨a,ha⟩
    refine ⟨U.1.topIso.hom a,?_⟩
    simpa only [map_mul] using congrArg U.1.topIso.hom ha

theorem exact_closed {Y : Scheme.{0}} (f : Y ⟶ X) [IsClosedImmersion f]
    (M N : LineBundle X) (φ : M.sheaf ⟶ N.sheaf) [Mono φ]
        (heq : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ d : N.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        f.ker.ideal U = Ideal.span {U.1.topIso.hom
          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom))}) :
    ∃ hz : φ ≫ LineClosedUnit.map f N = 0,
      (ShortComplex.mk φ (LineClosedUnit.map f N) hz).ShortExact := by
  have local_exact (U : X.affineOpens)
      (e : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
      (d : N.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
      (hI : f.ker.ideal U = Ideal.span {U.1.topIso.hom
        (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom))}) :=
    PrincipalSequence.exact (f ∣_ U.1)
      (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom)
      (restriction_principal_closed f U _ hI)
  have hz : φ ≫ LineClosedUnit.map f N = 0 := by
    apply ModuleLocal.eq_zero_of_local
    intro x
    obtain ⟨U,hx,e,d,hI⟩ := heq x
    obtain ⟨hzero,hex⟩ := local_exact U e d hI
    refine ⟨U.1,hx,?_⟩
    apply (cancel_epi e.inv).mp
    apply (cancel_mono (LineClosedUnit.frame f N U.1 d).hom).mp
    rw [Functor.map_comp,comp_zero,zero_comp]
    rw [Category.assoc,Category.assoc]
    rw [← d.hom_inv_id_assoc ((Scheme.Modules.restrictFunctor U.1.ι).map
      (LineClosedUnit.map f N))]
    simp only [Category.assoc]
    rw [LineClosedUnit.framed_map]
    exact ((Category.assoc e.inv _ _).trans
      (congrArg (e.inv ≫ ·) (Category.assoc _ _ _))).symm.trans hzero
  refine ⟨hz,{ exact := ?_, epi_g := LineClosedUnit.epi _ _ }⟩
  apply ModuleLocal.exact_of_local
  intro x
  obtain ⟨U,hx,e,d,hI⟩ := heq x
  obtain ⟨hzero,hex⟩ := local_exact U e d hI
  refine ⟨U.1,hx,?_⟩
  let S := (ShortComplex.mk φ (LineClosedUnit.map f N) hz).map
    (Scheme.Modules.restrictFunctor U.1.ι)
  let T := ShortComplex.mk (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom)
    (IdealModule.structureMap (f ∣_ U.1)) hzero
  let ee : S ≅ T := ShortComplex.isoMk e d (LineClosedUnit.frame f N U.1 d)
    (by simp [S,T]; exact e.hom_inv_id_assoc _) (by
      change d.hom ≫ IdealModule.structureMap (f ∣_ U.1) =
        (Scheme.Modules.restrictFunctor U.1.ι).map (LineClosedUnit.map f N) ≫ _
      rw [← LineClosedUnit.framed_map f N U.1 d]
      exact d.hom_inv_id_assoc _)
  exact ShortComplex.exact_of_iso ee.symm hex.exact

end
end MaximalSeshadri.CartierSequence

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem IntegralCurve.cartier_euler_difference (S : Surface) (A : LineBundle S.scheme) (hA : A.IsAmple)
    (M N : LineBundle S.scheme) (φ : M.sheaf ⟶ N.sheaf) [Mono φ]
    (C : IntegralCurve S)
    (heq : ∀ x : S.scheme, ∃ U : S.scheme.affineOpens, x ∈ U.1 ∧
      ∃ e : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ d : N.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        C.embedding.ker.ideal U = Ideal.span {U.1.topIso.hom
          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom))}) :
    eulerCharacteristic S.structureMap 2 N.sheaf - eulerCharacteristic S.structureMap 2 M.sheaf =
      eulerCharacteristic (C.embedding ≫ S.structureMap) 1
        ((Scheme.Modules.pullback C.embedding).obj N.sheaf) := by
  let P := N.pullback C.embedding
  let : Subsingleton (cohomology M.sheaf (2+1)) := ⟨fun x y =>
    (S.lineBundle_cohomology_zero_above_two_s01 A hA M 0 x).trans
      (S.lineBundle_cohomology_zero_above_two_s01 A hA M 0 y).symm⟩
  obtain ⟨hz,hseq⟩ := CartierSequence.exact_closed C.embedding M N φ heq
  have he := eulerCharacteristic_add S.structureMap hseq 2
    (fun n _ => S.cohomology_finite_s01 A hA M n)
    (fun n _ => S.cohomology_finite_s01 A hA N n)
    (fun n _ => C.pushforward_cohomology_finite S A hA P n)
  change eulerCharacteristic S.structureMap 2 N.sheaf =
    eulerCharacteristic S.structureMap 2 M.sheaf +
      eulerCharacteristic S.structureMap 2 ((Scheme.Modules.pushforward C.embedding).obj P.sheaf) at he
  rw [C.euler_pushforward_s01 S A hA P] at he
  exact sub_eq_iff_eq_add.mpr (he.trans (add_comm _ _))

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_LocalAlgebra_IdealEquation
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section

namespace MaximalSeshadri.InvertibleLocal
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.Frames

variable {X : Scheme.{0}}

lemma presented_frame_equation (I : X.IdealSheafData) (J : LineBundle X)
    (ι : J.sheaf ⟶ O X) (h : PresentsPullbackIdeal I (𝟙 X) J ι)
    (U : X.affineOpens) (e : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    I.ideal U = Ideal.span {U.1.topIso.hom (endValue (e.inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map ι ≫
        (Scheme.Modules.restrictUnitIso U.1.ι).hom))} := by
  let g : O U.1.toScheme ⟶ O U.1.toScheme :=
    e.inv ≫ restrictedInclusion J ι U.1.ι
  have H : ((I.comap (𝟙 X)).comap U.1.ι).ideal ⟨⊤,isAffineOpen_top _⟩ =
      Ideal.span {endValue g} := by
    change _ = Ideal.span {UnitEndomorphism.equation g ⊤}
    rw [← UnitEndomorphism.image_principal g ⊤,
      ← restricted_image_on_chart J ι h U.1.ι ⟨⊤,isAffineOpen_top _⟩ U
        (by simpa only [Scheme.Opens.ι_image_top,Scheme.Hom.id_preimage] using
          (le_rfl : U.1 ≤ U.1))]
    ext r
    change (∃ s, (restrictedInclusion J ι U.1.ι).val.app (op ⊤) s = r) ↔
      ∃ s, (restrictedInclusion J ι U.1.ι).val.app (op ⊤) (e.inv.val.app (op ⊤) s) = r
    constructor
    · rintro ⟨s,hs⟩
      refine ⟨e.hom.val.app (op ⊤) s,?_⟩
      have ht : e.inv.val.app (op ⊤) (e.hom.val.app (op ⊤) s) = s :=
        congrArg (fun k : J.sheaf.restrict U.1.ι ⟶ J.sheaf.restrict U.1.ι =>
          k.val.app (op ⊤) s) e.hom_inv_id
      rw [ht]; exact hs
    · rintro ⟨s,hs⟩
      exact ⟨e.inv.val.app (op ⊤) s,hs⟩
  rw [Scheme.IdealSheafData.comap_id,IdealPullback.comap_ι_top] at H
  have H' := congrArg (Ideal.map U.1.topIso.hom.hom) H
  rw [Ideal.map_map,Ideal.map_span,Set.image_singleton] at H'
  have hi : U.1.topIso.hom.hom.comp U.1.topIso.inv.hom = RingHom.id _ := by
    ext x; exact U.1.topIso.inv_hom_id_apply x
  rw [hi,Ideal.map_id] at H'
  exact H'

end
end MaximalSeshadri.InvertibleLocal

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_TensorInclusion
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames

variable {X : Scheme.{0}}

lemma tensor_inclusion_framed (J M : LineBundle X) (ι : J.sheaf ⟶ O X)
    (U : X.Opens) (e : J.sheaf.restrict U.ι ≅ O U.toScheme)
    (f : M.sheaf.restrict U.ι ≅ O U.toScheme) :
    (tensorFrame J M U e f).inv ≫
        (Scheme.Modules.restrictFunctor U.ι).map (tensorInclusion J M ι) ≫ f.hom =
      (e.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map ι ≫
        (Scheme.Modules.restrictUnitIso U.ι).hom) ≫ (tensorUnitTwist M U f).inv := by
  let restrictionFunctor : X.Modules ⥤ U.toScheme.Modules :=
    Scheme.Modules.restrictFunctor U.ι
  let unitRestriction : restrictionFunctor.obj (O X) ≅ O U.toScheme :=
    Scheme.Modules.restrictUnitIso U.ι
  let sourceUnit : moduleTensor X (O X) M.sheaf ≅ M.sheaf :=
    moduleTensorUnit M.sheaf
  let targetUnit : moduleTensor U.toScheme (O U.toScheme) (O U.toScheme) ≅
      O U.toScheme := moduleTensorUnit (O U.toScheme)
  let sourceRestriction : restrictionFunctor.obj (moduleTensor X J.sheaf M.sheaf) ≅
      moduleTensor U.toScheme (restrictionFunctor.obj J.sheaf)
        (restrictionFunctor.obj M.sheaf) := moduleTensorRestrict U J.sheaf M.sheaf
  let targetRestriction : restrictionFunctor.obj (moduleTensor X (O X) M.sheaf) ≅
      moduleTensor U.toScheme (restrictionFunctor.obj (O X))
        (restrictionFunctor.obj M.sheaf) := moduleTensorRestrict U (O X) M.sheaf
  let tensorMap : moduleTensor X J.sheaf M.sheaf ⟶ moduleTensor X (O X) M.sheaf :=
    moduleTensorMap ι (𝟙 M.sheaf)
  let inclusion : moduleTensor X J.sheaf M.sheaf ⟶ M.sheaf := tensorInclusion J M ι
  let frame : restrictionFunctor.obj (moduleTensor X J.sheaf M.sheaf) ≅
      O U.toScheme := tensorFrame J M U e f
  let twist : O U.toScheme ≅ O U.toScheme := tensorUnitTwist M U f
  let scalar : O U.toScheme ⟶ O U.toScheme :=
    e.inv ≫ restrictionFunctor.map ι ≫ unitRestriction.hom
  have inclusion_eq : inclusion = tensorMap ≫ sourceUnit.hom := rfl
  have naturality : restrictionFunctor.map tensorMap ≫ targetRestriction.hom =
      sourceRestriction.hom ≫ moduleTensorMap (restrictionFunctor.map ι)
        (𝟙 (restrictionFunctor.obj M.sheaf)) := by
    have naturality' : restrictionFunctor.map tensorMap ≫ targetRestriction.hom =
        sourceRestriction.hom ≫ moduleTensorMap (restrictionFunctor.map ι)
          (restrictionFunctor.map (𝟙 M.sheaf)) :=
      moduleTensorRestrict_natural U ι (𝟙 M.sheaf)
    simpa only [restrictionFunctor.map_id] using naturality'
  change frame.inv ≫ restrictionFunctor.map inclusion ≫ f.hom = scalar ≫ twist.inv
  apply (cancel_mono twist.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have frame_inv : frame.inv =
      (targetUnit.inv ≫ moduleTensorMap (X := U.toScheme) e.inv f.inv) ≫
        sourceRestriction.inv := rfl
  have twist_hom : twist.hom = f.inv ≫
      restrictionFunctor.map sourceUnit.inv ≫ targetRestriction.hom ≫
      moduleTensorMap unitRestriction.hom f.hom ≫ targetUnit.hom := rfl
  rw [frame_inv, twist_hom]
  rw [inclusion_eq, restrictionFunctor.map_comp]
  simp only [Category.assoc, f.hom_inv_id_assoc]
  rw [← restrictionFunctor.map_comp_assoc sourceUnit.hom sourceUnit.inv,
    sourceUnit.hom_inv_id,
    restrictionFunctor.map_id, Category.id_comp]
  rw [← Category.assoc (restrictionFunctor.map tensorMap), naturality]
  simp only [Category.assoc, sourceRestriction.inv_hom_id_assoc]
  rw [← Category.assoc (moduleTensorMap (X := U.toScheme) e.inv f.inv),
    ← moduleTensorMap_comp (X := U.toScheme), Category.comp_id,
    ← Category.assoc (moduleTensorMap (X := U.toScheme) _ _),
    ← moduleTensorMap_comp (X := U.toScheme), f.inv_hom_id]
  have hscalar : moduleTensorMap scalar (𝟙 (O U.toScheme)) ≫ targetUnit.hom =
      targetUnit.hom ≫ scalar := by
    exact (moduleTensorUnit_scalar (X := U.toScheme) scalar (𝟙 (O U.toScheme))).trans
      (congrArg (fun morphism : O U.toScheme ⟶ O U.toScheme =>
        targetUnit.hom ≫ morphism) (Category.comp_id scalar))
  rw [Category.assoc e.inv, hscalar, targetUnit.inv_hom_id_assoc]

theorem tensorInclusion_mono (J M : LineBundle X) (ι : J.sheaf ⟶ O X) [Mono ι] :
    Mono (tensorInclusion J M ι) := by
  apply ModuleLocal.mono_of_local
  intro x
  obtain ⟨U,hx,⟨e⟩,⟨f⟩⟩ := common_affine_frames J M x
  refine ⟨U.1,hx,?_⟩
  have : CategoryTheory.Limits.PreservesFiniteLimits
      (Scheme.Modules.restrictFunctor U.1.ι) := by
    have : CategoryTheory.Limits.PreservesFiniteLimits
        (Scheme.Modules.restrictFunctor U.1.ι ⋙ Scheme.Modules.toPresheaf U.1.toScheme) := by
      change CategoryTheory.Limits.PreservesFiniteLimits
        (Scheme.Modules.toPresheaf X ⋙ (Functor.whiskeringLeft _ _ _).obj U.1.ι.opensFunctor.op)
      have : CategoryTheory.Limits.PreservesFiniteLimits
          (Scheme.Modules.toPresheaf X) := inferInstance
      have : CategoryTheory.Limits.PreservesFiniteLimits
          ((Functor.whiskeringLeft _ _ Ab).obj U.1.ι.opensFunctor.op) := inferInstance
      exact CategoryTheory.Limits.comp_preservesFiniteLimits _ _
    exact CategoryTheory.Limits.preservesFiniteLimits_of_reflects_of_preserves _
      (Scheme.Modules.toPresheaf U.1.toScheme)
  have hm : Mono ((tensorFrame J M U.1 e f).inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map (tensorInclusion J M ι) ≫ f.hom) := by
    let restrictionFunctor : X.Modules ⥤ U.1.toScheme.Modules :=
      Scheme.Modules.restrictFunctor U.1.ι
    let unitRestriction : restrictionFunctor.obj (O X) ≅ O U.1.toScheme :=
      Scheme.Modules.restrictUnitIso U.1.ι
    let twist : O U.1.toScheme ≅ O U.1.toScheme := tensorUnitTwist M U.1 f
    have restricted_mono : Mono (restrictionFunctor.map ι) := inferInstance
    have scalar_mono : Mono ((e.inv ≫ restrictionFunctor.map ι ≫ unitRestriction.hom) ≫
        twist.inv) := inferInstance
    exact (congrArg (fun morphism : O U.1.toScheme ⟶ O U.1.toScheme => Mono morphism)
      (tensor_inclusion_framed J M ι U.1 e f)).mpr scalar_mono
  exact (mono_comp_iff_of_mono _ f.hom).mp
    ((mono_comp_iff_of_isIso (tensorFrame J M U.1 e f).inv _).mp hm)

lemma tensor_inclusion_ideal (J M : LineBundle X) (ι : J.sheaf ⟶ O X)
    (U : X.affineOpens) (e : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (f : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    Ideal.span {U.1.topIso.hom (endValue ((tensorFrame J M U.1 e f).inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map (tensorInclusion J M ι) ≫ f.hom))} =
    Ideal.span {U.1.topIso.hom (endValue (e.inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map ι ≫
        (Scheme.Modules.restrictUnitIso U.1.ι).hom))} := by
  let scalar : O U.1.toScheme ⟶ O U.1.toScheme := e.inv ≫
    (Scheme.Modules.restrictFunctor U.1.ι).map ι ≫
      (Scheme.Modules.restrictUnitIso U.1.ι).hom
  let twist : O U.1.toScheme ≅ O U.1.toScheme := tensorUnitTwist M U.1 f
  have framed : (tensorFrame J M U.1 e f).inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map (tensorInclusion J M ι) ≫ f.hom =
      scalar ≫ twist.inv := tensor_inclusion_framed J M ι U.1 e f
  refine (congrArg (fun morphism : O U.1.toScheme ⟶ O U.1.toScheme =>
    Ideal.span {U.1.topIso.hom (endValue morphism)}) framed).trans ?_
  change Ideal.span {U.1.topIso.hom (endValue (scalar ≫ twist.inv))} =
    Ideal.span {U.1.topIso.hom (endValue scalar)}
  rw [endValue_comp, map_mul, ← Ideal.span_singleton_mul_span_singleton]
  have hu : IsUnit (endValue twist.inv) :=
    (end_isIso_iff twist.inv).mp inferInstance
  rw [Ideal.span_singleton_eq_top.mpr (hu.map U.1.topIso.hom.hom), Ideal.mul_top]

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_CurveIdealDegree
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem IntegralCurve.ideal_euler_difference (S : Surface)
    (A : LineBundle S.scheme) (hA : A.IsAmple) (C : IntegralCurve S)
    (J : LineBundle S.scheme) (ι : J.sheaf ⟶ O S.scheme)
    (h : PresentsPullbackIdeal C.embedding.ker (𝟙 S.scheme) J ι)
    (M : LineBundle S.scheme) :
    eulerCharacteristic S.structureMap 2 M.sheaf -
      eulerCharacteristic S.structureMap 2 (J.tensor M).sheaf =
      eulerCharacteristic (C.embedding ≫ S.structureMap) 1
        ((Scheme.Modules.pullback C.embedding).obj M.sheaf) := by
  have : Mono ι := h.1
  have := tensorInclusion_mono J M ι
  apply C.cartier_euler_difference S A hA (J.tensor M) M (tensorInclusion J M ι)
  intro x
  obtain ⟨U,hx,⟨e⟩,⟨f⟩⟩ := common_affine_frames J M x
  refine ⟨U,hx,tensorFrame J M U.1 e f,f,?_⟩
  rw [tensor_inclusion_ideal]
  exact InvertibleLocal.presented_frame_equation C.embedding.ker J ι h U e

lemma mixedEuler_comm (S : Surface) (L M : LineBundle S.scheme) :
    mixedEuler S L M = mixedEuler S M L := by
  have h := eulerCharacteristic_iso S.structureMap (moduleTensorComm L.sheaf M.sheaf) 2
  unfold mixedEuler
  change eulerCharacteristic S.structureMap 2 (L.tensor M).sheaf =
    eulerCharacteristic S.structureMap 2 (M.tensor L).sheaf at h
  rw [h]
  ring

theorem IntegralCurve.ideal_mixed_degree_s01_oai (S : Surface)
    (A : LineBundle S.scheme) (hA : A.IsAmple) (C : IntegralCurve S)
    (J : LineBundle S.scheme) (ι : J.sheaf ⟶ O S.scheme)
    (h : PresentsPullbackIdeal C.embedding.ker (𝟙 S.scheme) J ι)
    (M : LineBundle S.scheme) :
    mixedEuler S M J = -curveDegree S M C := by
  have hM := C.ideal_euler_difference S A hA J ι h M
  have hO := C.ideal_euler_difference S A hA J ι h (A.pow 0)
  have he := eulerCharacteristic_iso S.structureMap (moduleTensorRightUnit J.sheaf) 2
  have hp := eulerCharacteristic_iso (C.embedding ≫ S.structureMap)
    (pullbackUnitIso C.embedding) 1
  rw [mixedEuler_comm]
  change eulerCharacteristic S.structureMap 2 (O S.scheme) -
    eulerCharacteristic S.structureMap 2 (moduleTensor S.scheme J.sheaf (O S.scheme)) =
      eulerCharacteristic (C.embedding ≫ S.structureMap) 1
        ((Scheme.Modules.pullback C.embedding).obj (O S.scheme)) at hO
  change eulerCharacteristic S.structureMap 2 (moduleTensor S.scheme J.sheaf (O S.scheme)) =
    eulerCharacteristic S.structureMap 2 J.sheaf at he
  rw [he,hp] at hO
  unfold mixedEuler curveDegree
  dsimp only [O] at *
  linarith

end
end MaximalSeshadri.Geometry

end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.IntegralCurve.ideal_mixed_degree_s01_oai := @OAI.MaximalSeshadri.Geometry.IntegralCurve.ideal_mixed_degree_s01_oai
