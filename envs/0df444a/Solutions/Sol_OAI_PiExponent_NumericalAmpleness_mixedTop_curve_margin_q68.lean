-- Prove2me | solution 1 for OAI.PiExponent.NumericalAmpleness.mixedTop_curve_margin_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:39:33.489721+00:00
-- url     : https://prove2.me/submissions/bae9dfef-4b8c-41b4-b9af-06529e22a3fc

import Mathlib
import Definitions.Def_OAIQ068A043
import Theorems.Thm_OAI_PiExponent_CurveCycle_tensor_euler_margin_q68
import Theorems.Thm_OAI_PiExponent_NumericalAmpleness_mixedTop_power_cartier_restriction_q68
import Theorems.Thm_OAI_PiExponent_NumericalAmpleness_regular_ample_sectionZero_dimension_q68

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_AmpleAllPowersGeneration
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.AmpleGlobalGeneration
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem ample_eventual_global_generators [NoetherianSpace X]
    (L : LineBundle X) (hL : L.IsAmple) (M : X.Modules) [M.IsFinitePresentation] :
    ∃ N : ℕ, ∀ n ≥ N,
      ∃ G : ((moduleTwistFunctor L n).obj M).GeneratingSections, G.IsFiniteType := by
  classical
  obtain ⟨d, hd, l, s, hcover, haffine, _⟩ := L.ample_common_degree_cover hL
  have hresidue (r : Fin d) : ∃ N : ℕ, ∀ n ≥ N,
      ∃ G : ((moduleTwistFunctor (L.pow d) n).obj
        ((moduleTwistFunctor L r.val).obj M)).GeneratingSections, G.IsFiniteType := by
    let := PiExponent.FiniteGlobalPresentation.moduleTwist_isFinitePresentation L r.val M
    exact eventual_global_generators_of_section_cover (L.pow d)
      ((moduleTwistFunctor L r.val).obj M) s hcover haffine
  choose N hN using hresidue
  let B := Finset.univ.sup N
  refine ⟨d * B, fun n hn => ?_⟩
  let r : Fin d := ⟨n % d, Nat.mod_lt n hd⟩
  have hB : B ≤ n / d := (Nat.le_div_iff_mul_le hd).mpr (by
    simpa only [Nat.mul_comm] using hn)
  have hr : N r ≤ n / d := (Finset.le_sup (f := N) (Finset.mem_univ r)).trans hB
  obtain ⟨G, hG⟩ := hN r (n / d) hr
  let : G.IsFiniteType := hG
  let e : ((moduleTwistFunctor (L.pow d) (n / d)).obj
      ((moduleTwistFunctor L r.val).obj M)) ≅ (moduleTwistFunctor L n).obj M :=
    moduleTwistPowerMulIso L ((moduleTwistFunctor L r.val).obj M) d (n / d) ≪≫
      eqToIso (by
        change (moduleTwistFunctor L (n % d) ⋙
          moduleTwistFunctor L (d * (n / d))).obj M = _
        rw [← moduleTwistFunctor_add, Nat.mod_add_div])
  exact ⟨SheafOfModules.GeneratingSections.equivOfIso e G, ⟨hG.finite⟩⟩

theorem ample_eventual_power_global_generators [NoetherianSpace X]
    (L : LineBundle X) (hL : L.IsAmple) :
    ∃ N : ℕ, ∀ n ≥ N,
      ∃ G : (modulePow X L.sheaf n).GeneratingSections, G.IsFiniteType := by
  let : (structureSheaf X).IsFinitePresentation :=
    PiExponent.GeometrySupport.LineBundleCoherent.structureSheaf_isFinitePresentation
  obtain ⟨N, hN⟩ := ample_eventual_global_generators L hL (structureSheaf X)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨G, hG⟩ := hN n hn
  let : G.IsFiniteType := hG
  exact ⟨SheafOfModules.GeneratingSections.equivOfIso (moduleTwistUnitIso L n) G,
    ⟨hG.finite⟩⟩

end
end PiExponent.AmpleGlobalGeneration

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_LineAmpleOperations
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentSeshadri.Geometry
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames PiExponentSeshadri.TensorPure
variable {X : Scheme.{0}}

theorem LineBundle.IsAmple.pow {L : LineBundle X} (hL : L.IsAmple) (d : ℕ) (hd : 0 < d) :
    (L.pow d).IsAmple := by
  intro x V hx
  obtain ⟨n,hn,s,hs,hsub,ha⟩ := hL x V hx
  let e : ((L.pow n).pow d).sheaf ≅ ((L.pow d).pow n).sheaf :=
    linePowerMul L n d ≪≫ eqToIso (congrArg (fun j => (L.pow j).sheaf) (Nat.mul_comm n d)) ≪≫
      (linePowerMul L d n).symm
  let t := powerSection s d ≫ e.hom
  have ht : sectionOpen X t = sectionOpen X s := by
    exact (PiExponent.AmpleIso.sectionOpen_postcomp_iso (powerSection s d) e).trans
      ((L.pow n).sectionOpen_power s hd)
  exact ⟨n, hn, t, ht.symm ▸ hs, ht.le.trans hsub, ht.symm ▸ ha⟩

end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_GeneratorsSectionCover
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeneratorsSectionCover
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.SectionOpens
variable {X : Scheme.{0}}

private lemma epi_iso_comp {C : Type*} [Category C] {A B D E : C}
    (i : A ≅ B) (f : B ⟶ D) (e : D ≅ E) [Epi f] :
    Epi (i.hom ≫ f ≫ e.hom) := inferInstance

theorem free_sum_projection_inclusion {ι : Type} [Fintype ι] [DecidableEq ι] :
    (∑ i : ι, freeProjection (X := X) i ≫ schemeInclusion i) =
      𝟙 (schemeFree X ι) := by
  apply (SheafOfModules.isColimitFreeCofan ι).hom_ext
  intro j
  change schemeInclusion j.as ≫ _ = schemeInclusion j.as ≫ _
  simp only [Preadditive.comp_sum, ← Category.assoc, free_inclusion_projection]
  simp only [ite_comp, Category.id_comp, zero_comp, Fintype.sum_ite_eq, Category.comp_id]

lemma hom_sum_app {M N : X.Modules} {ι : Type} (S : Finset ι)
    (f : ι → (M ⟶ N)) (V : X.Opens) (z : Γ(M,V)) :
    (∑ i ∈ S, f i).app V z = ∑ i ∈ S, (f i).app V z := by
  classical
  induction S using Finset.induction_on with
  | empty => rfl
  | @insert a S ha ih =>
    simp only [Finset.sum_insert ha, Scheme.Modules.Hom.add_app]
    change (f a).app V z + (∑ i ∈ S, f i).app V z = _
    rw [ih]

theorem unit_epimorphism_cover {ι : Type} [Finite ι]
    (f : schemeFree X ι ⟶ O X) [Epi f] :
    (⨆ i : ι, isoOpen (schemeInclusion i ≫ f)) = ⊤ := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  apply top_unique
  intro x _
  let F : X.Modules ⥤ _ := SheafOfModules.toSheaf X.ringCatSheaf
  have : F.PreservesEpimorphisms :=
    inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).PreservesEpimorphisms
  have hFf : Epi (F.map f) := F.map_epi f
  have hloc : TopCat.Presheaf.IsLocallySurjective (F.map f).hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi _).mpr hFf
  obtain ⟨V, hV, ⟨z, hz⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff _).mp hloc ⊤ (1 : Γ(X,⊤)) x trivial
  change Scheme.Modules.Hom.app f V z = X.presheaf.map (homOfLE hV).op (1 : Γ(X,⊤)) at hz
  rw [map_one] at hz
  have he : (∑ i : ι, freeProjection (X := X) i ≫ (schemeInclusion i ≫ f)) = f := by
    simp only [← Category.assoc]
    rw [← Preadditive.sum_comp, free_sum_projection_inclusion, Category.id_comp]
  have hsum : (∑ i : ι, Scheme.Modules.Hom.app (schemeInclusion i ≫ f) V
      (Scheme.Modules.Hom.app (freeProjection (X := X) i) V z)) = (1 : Γ(X,V)) := by
    exact (hom_sum_app Finset.univ
      (fun i => freeProjection (X := X) i ≫ (schemeInclusion i ≫ f)) V z).symm.trans
      ((congrArg (fun q : (schemeFree X ι : X.Modules) ⟶ O X =>
        Scheme.Modules.Hom.app q V z) he).trans hz)
  have hsum' : (∑ i : ι, X.presheaf.germ V x hxV
      (Scheme.Modules.Hom.app (schemeInclusion i ≫ f) V (Scheme.Modules.Hom.app (freeProjection (X := X) i) V z))) = 1 := by
    exact (map_sum (X.presheaf.germ V x hxV).hom _ _).symm.trans
      ((congrArg (X.presheaf.germ V x hxV) hsum).trans (X.presheaf.germ V x hxV).hom.map_one)
  obtain ⟨i, _, hi⟩ := IsLocalRing.exists_of_isUnit_sum (hsum' ▸ isUnit_one)
  have hc : IsUnit (X.presheaf.germ ⊤ x trivial
      (endValue (schemeInclusion i ≫ f))) := by
    let si : O X ⟶ O X := schemeInclusion i ≫ f
    let a : Γ(X,V) := Scheme.Modules.Hom.app (freeProjection (X := X) i) V z
    have ht := end_apply si V a
    have hi' : IsUnit (X.presheaf.germ V x hxV
        (a * (show Γ(X,V) from si.app V (1 : Γ(X,V))))) := ht ▸ hi
    have hc' : IsUnit (X.presheaf.germ V x hxV
        (show Γ(X,V) from si.app V (1 : Γ(X,V)))) := by
      rw [map_mul] at hi'
      exact isUnit_of_mul_isUnit_right hi'
    have hcoeff := congrArg (fun z : Γ(X,V) => X.presheaf.germ V x hxV z)
      (end_naturality si V)
    rw [X.presheaf.germ_res_apply] at hcoeff
    exact hcoeff ▸ hc'
  apply Opens.mem_iSup.mpr
  refine ⟨i, ?_⟩
  erw [isoOpen_eq_basicOpen (Iso.refl (O X))]
  change x ∈ X.basicOpen (endValue (schemeInclusion i ≫ f))
  exact (X.mem_basicOpen (endValue (schemeInclusion i ≫ f)) x (show x ∈ (⊤ : X.Opens) from trivial)).mpr hc

theorem generators_sectionOpen_cover (L : LineBundle X)
    (G : L.sheaf.GeneratingSections) [G.IsFiniteType] :
    (⨆ i : G.I, sectionOpen X (generatorSection L G i)) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
  let F : SheafOfModules X.ringCatSheaf ⥤ SheafOfModules U.toScheme.ringCatSheaf :=
    Scheme.Modules.restrictFunctor U.ι
  have : PreservesColimitsOfSize.{0,0} F :=
    inferInstanceAs (PreservesColimitsOfSize.{0,0} (Scheme.Modules.restrictFunctor U.ι))
  let η := (Scheme.Modules.restrictUnitIso U.ι).symm
  let f : schemeFree U.toScheme G.I ⟶ O U.toScheme :=
    (SheafOfModules.mapFreeIso F G.I η).hom ≫ F.map G.π ≫ e.hom
  have hπ : Epi (F.map G.π) := @Functor.map_epi _ _ _ _ F _ _ _ G.π G.epi
  have : Epi f := @epi_iso_comp _ _ _ _ _ _
    (SheafOfModules.mapFreeIso F G.I η) (F.map G.π) e hπ
  let : Finite G.I := (inferInstance : G.IsFiniteType).finite
  have hf := unit_epimorphism_cover f
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp
    (show (⟨x,hx⟩ : U.toScheme) ∈ ⨆ i : G.I, isoOpen (schemeInclusion i ≫ f) by
      rw [hf]; trivial)
  have he : schemeInclusion i ≫ f =
      restrictSection U.ι (generatorSection L G i) ≫ e.hom := by
    dsimp only [f, generatorSection, restrictSection]
    erw [← Category.assoc, ← Category.assoc, SheafOfModules.ιFree_mapFreeIso_hom]
    erw [F.map_comp]
    exact Category.assoc _ _ _
  erw [he, isoOpen_postcomp, isoOpen_restrictSection] at hi
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

theorem exists_fin_section_cover (L : LineBundle X)
    (G : L.sheaf.GeneratingSections) [G.IsFiniteType] :
    ∃ k : ℕ, ∃ s : Fin k → GlobalSections X L.sheaf,
      (⨆ i, sectionOpen X (s i)) = ⊤ := by
  let : Finite G.I := (inferInstance : G.IsFiniteType).finite
  let : Fintype G.I := Fintype.ofFinite G.I
  let e := (Fintype.equivFin G.I).symm
  exact ⟨Fintype.card G.I, fun i => generatorSection L G (e i),
    (e.iSup_comp (g := fun i => sectionOpen X (generatorSection L G i))).trans
      (generators_sectionOpen_cover L G)⟩

theorem ample_eventual_fin_section_cover [NoetherianSpace X]
    (L : LineBundle X) (hL : L.IsAmple) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ k : ℕ,
      ∃ s : Fin k → GlobalSections X (modulePow X L.sheaf n),
        (⨆ i, sectionOpen X (s i)) = ⊤ := by
  obtain ⟨N, hN⟩ := AmpleGlobalGeneration.ample_eventual_power_global_generators L hL
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨G, hG⟩ := hN n hn
  let : G.IsFiniteType := hG
  exact @exists_fin_section_cover X (L.pow n) G hG

end
end PiExponent.GeneratorsSectionCover

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_NumericalMarginRestriction
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveBlowupImage.imageMap_isDominant _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.moduleTensorRightFunctor_additive _root_.OAI.PiExponentSeshadri.Geometry.moduleTensorRightFunctor_preservesZero _root_.OAI.PiExponentSeshadri.Geometry.moduleTwistFunctor_additive _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry

theorem curveDegree_mapClosed {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of ℂ))
    (L : LineBundle X) (i : Y ⟶ X) [IsClosedImmersion i] (C : IntegralCurve Y) :
    curveDegree p L (C.mapClosed i) = curveDegree (i ≫ p) (L.pullback i) C := by
  unfold curveDegree IntegralCurve.mapClosed LineBundle.pullback
  simp only [Category.assoc]
  congr 1
  exact eulerCharacteristic_iso (C.embedding ≫ i ≫ p)
    ((Scheme.Modules.pullbackComp C.embedding i).app L.sheaf).symm 1

theorem uniform_curve_margin_restrict {X Y : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L H : LineBundle X) (ε : ℝ)
    (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ))
    (i : Y ⟶ X) [IsClosedImmersion i] :
    ∀ C : IntegralCurve Y,
      ε * (curveDegree (i ≫ p) (H.pullback i) C : ℝ) ≤
        (curveDegree (i ≫ p) (L.pullback i) C : ℝ) := by
  intro C
  simpa only [curveDegree_mapClosed] using hmargin (C.mapClosed i)

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_RegularSectionMono
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

theorem affine_scalar_regular_on_open [IsAffine X] (r : Γ(X, ⊤))
    (hr : r ∈ nonZeroDivisors Γ(X, ⊤)) (U : X.Opens) :
    Function.Injective (fun a : Γ(X, U) =>
      X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r * a) := by
  intro a b hab
  apply TopCat.Presheaf.section_ext X.sheaf U a b
  intro x hx
  let : Algebra Γ(X, ⊤) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, trivial⟩ : (⊤ : X.Opens))
  have : IsLocalization.AtPrime (X.presheaf.stalk x)
      ((isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩).asIdeal :=
    (isAffineOpen_top X).isLocalization_stalk ⟨x, trivial⟩
  have hreg : X.presheaf.germ ⊤ x trivial r ∈ nonZeroDivisors (X.presheaf.stalk x) :=
    IsLocalization.nonZeroDivisors_le_comap
      (((isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩).asIdeal.primeCompl) (X.presheaf.stalk x) hr
  have h := congrArg (fun v : Γ(X, U) => X.presheaf.germ U x hx v) hab
  simp only [map_mul, TopCat.Presheaf.germ_res_apply] at h
  exact (isRegular_iff_mem_nonZeroDivisors.mpr hreg).left h

theorem scalarEnd_mono_of_regular [IsAffine X] (r : Γ(X, ⊤))
    (hr : r ∈ nonZeroDivisors Γ(X, ⊤)) : Mono (scalarEnd r) := by
  have hm : Mono (scalarEnd r).val := by
    apply PresheafOfModules.mono_of_injective
    intro U
    exact affine_scalar_regular_on_open r hr U.unop
  exact (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map hm

theorem framed_section_mono_of_regular [IsAffine X] {M : X.Modules}
    (e : M ≅ O X) (s : O X ⟶ M)
    (hr : coefficient e s ∈ nonZeroDivisors Γ(X, ⊤)) : Mono s := by
  have he : s ≫ e.hom = scalarEnd (coefficient e s) := by
    apply endValue_injective
    rw [endValue_scalarEnd]
    rfl
  have hm : Mono (s ≫ e.hom) := by
    rw [he]
    exact scalarEnd_mono_of_regular _ hr
  exact (mono_comp_iff_of_mono s e.hom).mp hm

theorem section_mono_of_regular_affine_frames (L : LineBundle X)
    (s : GlobalSections X L.sheaf)
    (H : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        coefficient e (restrictSection U.1.ι s) ∈
          nonZeroDivisors Γ(U.1.toScheme, ⊤)) : Mono s := by
  apply CoherentTwist.mono_of_local
  intro x
  obtain ⟨U, hx, e, he⟩ := H x
  have : IsAffine U.1.toScheme := U.2
  have hm : Mono (restrictSection U.1.ι s) := framed_section_mono_of_regular e _ he
  refine ⟨U.1, hx, ?_⟩
  let : IsIso (Scheme.Modules.restrictUnitIso U.1.ι).inv :=
    (Scheme.Modules.restrictUnitIso U.1.ι).isIso_inv
  exact (mono_comp_iff_of_isIso (Scheme.Modules.restrictUnitIso U.1.ι).inv _).mp hm

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_AssociatedPrimeAvoidance
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.AssociatedPrimeAvoidance
noncomputable section
open scoped BigOperators

theorem exists_regular_combination
    {K ι J : Type*} [Field K] [Infinite K] [Finite ι] [Fintype J]
    (R : ι → Type*) [∀ i, CommRing (R i)] [∀ i, Algebra K (R i)]
    [∀ i, IsNoetherianRing (R i)] (a : ∀ i, J → R i)
    (hspan : ∀ i, Ideal.span (Set.range (a i)) = ⊤) :
    ∃ c : J → K, ∀ i, (∑ j, c j • a i j) ∈ nonZeroDivisors (R i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let (i : ι) : Fintype (associatedPrimes (R i) (R i)) :=
    (associatedPrimes.finite (R i) (R i)).fintype
  let B := (i : ι) × associatedPrimes (R i) (R i)
  let L (i : ι) : (J → K) →ₗ[K] R i := Fintype.linearCombination K (a i)
  let bad (b : B) : Submodule K (J → K) :=
    (b.2.val.restrictScalars K).comap (L b.1)
  have hbad : ∀ b : B, bad b ≠ ⊤ := by
    intro b hb
    apply b.2.property.isPrime.ne_top
    apply top_unique
    rw [← hspan b.1]
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    have hm : Pi.single j (1 : K) ∈ bad b := by
      rw [hb]
      trivial
    change Fintype.linearCombination K (a b.1) (Pi.single j 1) ∈ b.2.val at hm
    rw [Fintype.linearCombination_apply_single, one_smul] at hm
    exact hm
  obtain ⟨c, hc⟩ := Submodule.exists_forall_notMem_of_forall_ne_top bad hbad
  refine ⟨c, fun i => ?_⟩
  by_contra hn
  have hz : (∑ j, c j • a i j) ∈ (nonZeroDivisors (R i) : Set (R i))ᶜ := hn
  rw [← biUnion_associatedPrimes_eq_compl_nonZeroDivisors (R i)] at hz
  obtain ⟨P, hP, hmem⟩ := Set.mem_iUnion₂.mp hz
  apply hc ⟨i, ⟨P, hP⟩⟩
  change (∑ j, c j • a i j) ∈ P
  exact hmem

end
end PiExponent.GeometrySupport.AssociatedPrimeAvoidance

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_RegularSectionChoice
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

theorem finite_affine_frame_cover [CompactSpace X] (L : LineBundle X) :
    ∃ l : ℕ, ∃ U : Fin l → X.affineOpens,
      (⨆ i, (U i).1) = ⊤ ∧
      Nonempty (∀ i, L.sheaf.restrict (U i).1.ι ≅ O (U i).1.toScheme) := by
  classical
  have h (x : X) : ∃ U : X.affineOpens, x ∈ U.1 ∧
      Nonempty (L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) := by
    obtain ⟨U, hx, he, _⟩ := common_affine_frames L L x
    exact ⟨U, hx, he⟩
  choose U hx e using h
  obtain ⟨I,hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => ((U x).1 : Set X)) (fun x => (U x).1.isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x,hx x⟩)
  let E := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I, fun j => U (E j).val, ?_, ?_⟩
  · apply top_unique
    intro x _
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hI (show x ∈ Set.univ from trivial))
    obtain ⟨hi,hx⟩ := Set.mem_iUnion.mp hi
    apply Opens.mem_iSup.mpr
    refine ⟨E.symm ⟨i,hi⟩,?_⟩
    change x ∈ (U (E (E.symm ⟨i,hi⟩)).val).1
    rw [Equiv.apply_symm_apply]
    exact hx
  · exact ⟨fun j => (e (E j).val).some⟩

theorem coefficients_span_top_of_section_cover (L : LineBundle X) {k : ℕ}
    (s : Fin k → GlobalSections X L.sheaf)
    (hs : (⨆ j, sectionOpen X (s j)) = ⊤)
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    Ideal.span (Set.range (fun j => coefficient e (restrictSection U.1.ι (s j)))) = ⊤ := by
  have : IsAffine U.1.toScheme := U.2
  have hc : (⨆ j, U.1.toScheme.basicOpen (coefficient e (restrictSection U.1.ι (s j)))) = ⊤ := by
    exact (iSup_congr fun j => (preimage_isoOpen (s j) U.1.ι e).symm).trans
      (U.1.ι.iSup_preimage_eq_top hs)
  apply (isAffineOpen_top U.1.toScheme).iSup_basicOpen_eq_self_iff.mp
  apply top_unique
  intro x _
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ j,
    U.1.toScheme.basicOpen (coefficient e (restrictSection U.1.ι (s j))) by rw [hc]; trivial)
  exact Opens.mem_iSup.mpr ⟨⟨_, Set.mem_range_self j⟩, hj⟩

private theorem iso_inv_map_comp {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B : C} {T : D} (e : F.obj A ≅ T) (f : A ⟶ A) (s : A ⟶ B) :
    e.inv ≫ F.map (f ≫ s) = ((e.inv ≫ F.map f) ≫ e.hom) ≫ e.inv ≫ F.map s := by
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

theorem localCoefficient_scalar (L : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme)
    (r : Γ(X, ⊤)) (s : GlobalSections X L.sheaf) :
    coefficient e (restrictSection U.ι (scalarEnd r ≫ s)) =
      U.ι.appTop r * coefficient e (restrictSection U.ι s) := by
  have hscalar : restrictSection U.ι (scalarEnd r) ≫
      (Scheme.Modules.restrictUnitIso U.ι).hom = scalarEnd (U.ι.appTop r) := by
    apply endValue_injective
    erw [endValue_restrict U.ι (scalarEnd r), endValue_scalarEnd, endValue_scalarEnd]
  have hrestrict : restrictSection U.ι (scalarEnd r ≫ s) =
      scalarEnd (U.ι.appTop r) ≫ restrictSection U.ι s := by
    rw [← hscalar]
    exact iso_inv_map_comp (Scheme.Modules.restrictFunctor U.ι)
      (Scheme.Modules.restrictUnitIso U.ι) (scalarEnd r) s
  rw [hrestrict]
  change endValue (scalarEnd (U.ι.appTop r) ≫ restrictSection U.ι s ≫ e.hom) = _
  rw [endValue_comp, endValue_scalarEnd]
  rfl

theorem localCoefficient_linearCombination (L : LineBundle X) {k : ℕ}
    (a : ℂ →+* Γ(X, ⊤)) (s : Fin k → GlobalSections X L.sheaf) (c : Fin k → ℂ)
    (U : X.Opens) (e : L.sheaf.restrict U.ι ≅ O U.toScheme) :
    coefficient e (restrictSection U.ι (sectionLinearCombination L a s c)) =
      ∑ j, U.ι.appTop (a (c j)) * coefficient e (restrictSection U.ι (s j)) := by
  change localCoefficientAddHom L U e (∑ j, scalarEnd (a (c j)) ≫ s j) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact localCoefficient_scalar L U e _ _

theorem exists_mono_linearCombination_of_finite_cover [IsNoetherian X]
    (L : LineBundle X) {k : ℕ} (a : ℂ →+* Γ(X, ⊤))
    (s : Fin k → GlobalSections X L.sheaf)
    (hs : (⨆ j, sectionOpen X (s j)) = ⊤) :
    ∃ c : Fin k → ℂ, Mono (sectionLinearCombination L a s c) := by
  classical
  obtain ⟨l, U, hU, ⟨e⟩⟩ := finite_affine_frame_cover L
  let R (i : Fin l) : Type := Γ((U i).1.toScheme, ⊤)
  have hAff (i : Fin l) : IsAffine (U i).1.toScheme := (U i).2
  let alg (i : Fin l) : Algebra ℂ (R i) := ((U i).1.ι.appTop.hom.comp a).toAlgebra
  let (i : Fin l) : Algebra ℂ (R i) := alg i
  have hNoeth (i : Fin l) : IsNoetherianRing (R i) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top (U i).1.toScheme⟩
  let b (i : Fin l) (j : Fin k) : R i := coefficient (e i) (restrictSection (U i).1.ι (s j))
  have hb (i : Fin l) : Ideal.span (Set.range (b i)) = ⊤ :=
    coefficients_span_top_of_section_cover L s hs (U i) (e i)
  obtain ⟨c, hc⟩ := GeometrySupport.AssociatedPrimeAvoidance.exists_regular_combination (K := ℂ) (ι := Fin l) (J := Fin k) R b hb
  refine ⟨c, section_mono_of_regular_affine_frames L _ ?_⟩
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ i, (U i).1 by rw [hU]; trivial)
  refine ⟨U i, hi, e i, ?_⟩
  rw [localCoefficient_linearCombination]
  simpa only [R, b, Algebra.smul_def, RingHom.algebraMap_toAlgebra, RingHom.comp_apply] using hc i

theorem exists_mono_section_of_finite_cover [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X) {k : ℕ}
    (s : Fin k → GlobalSections X L.sheaf)
    (hs : (⨆ j, sectionOpen X (s j)) = ⊤) :
    ∃ t : GlobalSections X L.sheaf, Mono t := by
  obtain ⟨c, hc⟩ := exists_mono_linearCombination_of_finite_cover L (baseScalars p) s hs
  exact ⟨sectionLinearCombination L (baseScalars p) s c, hc⟩

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_MixedEulerAlgebra
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}}

theorem LineIsoInvariant.tensorDifference {f : LineBundle X → ℤ} (hf : LineIsoInvariant f)
    (L : LineBundle X) : LineIsoInvariant (tensorDifference L f) := by
  intro M N e
  change f (L.tensor M) - f M = f (L.tensor N) - f N
  rw [hf (L.tensor M) (L.tensor N) (moduleTensorIso (Iso.refl L.sheaf) e), hf M N e]

theorem LineIsoInvariant.mixedDifference {f : LineBundle X → ℤ} (hf : LineIsoInvariant f)
    (ls : List (LineBundle X)) : LineIsoInvariant (mixedDifference ls f) := by
  induction ls with
  | nil => exact hf
  | cons L ls ih => exact ih.tensorDifference L

theorem tensorDifference_commute (L B : LineBundle X) (f : LineBundle X → ℤ)
    (hf : LineIsoInvariant f) :
    tensorDifference L (tensorDifference B f) = tensorDifference B (tensorDifference L f) := by
  funext M
  simp only [tensorDifference]
  rw [hf _ _ (tensorTwistSwapIso B L M)]
  ring

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_MixedEulerDimension
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open PiExponent.SectionZeroIdeal PiExponent.ProjectiveO1

theorem lineEuler_isoInvariant {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (r : ℕ) :
    LineIsoInvariant (lineEuler p r) := by
  intro L M e
  exact eulerCharacteristic_iso p e r

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_MixedEulerPolarization
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem mixedDifference_perm {ls ks : List (LineBundle X)} (h : ls.Perm ks)
    (f : LineBundle X → ℤ) (hf : LineIsoInvariant f) :
    mixedDifference ls f = mixedDifference ks f := by
  induction h with
  | nil => rfl
  | cons L h ih => exact congrArg (tensorDifference L) ih
  | swap A B ls => exact tensorDifference_commute B A _ (hf.mixedDifference ls)
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_MixedEulerPositivity
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal

theorem exists_positive_power_regular_section {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (A : LineBundle X) (hA : A.IsAmple) :
    ∃ n : ℕ, 0 < n ∧ ∃ s : GlobalSections X (A.pow n).sheaf, Mono s := by
  obtain ⟨N, hN⟩ := GeneratorsSectionCover.ample_eventual_fin_section_cover A hA
  obtain ⟨k, s, hs⟩ := hN (N+1) (by omega)
  obtain ⟨t, ht⟩ := exists_mono_section_of_finite_cover p (A.pow (N+1)) s hs
  exact ⟨N+1, by omega, t, ht⟩

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_MixedEulerCurveMargin
attribute [-instance] _root_.OAI.PiExponent.CurveBlowupImage.imageMap_isDominant _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal

theorem mixedTop_curve_margin_aux (d : ℕ) :
    ∀ {X : Scheme.{0}} [IsNoetherian X] [Nonempty X]
      (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
      (H L : LineBundle X), H.IsAmple →
      topologicalKrullDim X = ((d+1 : ℕ) : WithBot ℕ∞) →
      ∀ ε : ℝ, (∀ C : IntegralCurve X,
        ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ)) →
      ∀ ls : List (LineBundle X), ls.length = d →
      (∀ A ∈ ls, A.IsAmple) →
      ε * (mixedTop (lineEuler p (d+1)) (H :: ls) : ℝ) ≤
        (mixedTop (lineEuler p (d+1)) (L :: ls) : ℝ) := by
  induction d with
  | zero =>
    intro X _ _ p _ H L hH hdim ε hmargin ls hlen hamp
    have hz : ls = [] := List.length_eq_zero_iff.mp hlen
    subst ls
    exact CurveCycle.tensor_euler_margin_q68 p hdim.le H hH L H
      (structureLineBundle X) (structureLineBundle X) ε hmargin
  | succ d ih =>
    intro X _ _ p _ H L hH hdim ε hmargin ls hlen hamp
    cases ls with
    | nil => simp at hlen
    | cons A ls =>
      have hlen' : ls.length = d := by simpa using hlen
      have hA : A.IsAmple := hamp A (by simp)
      obtain ⟨n, hn, s, hs⟩ := exists_positive_power_regular_section p A hA
      let := hs
      let D := zeroIdeal (A.pow n) s
      let j := D.subschemeι
      have hd := regular_ample_sectionZero_dimension_q68 p (A.pow n) (hA.pow n hn) s (d+1) hdim
      let : Nonempty D.subscheme := hd.1
      let : IsLocallyNoetherian D.subscheme := LocallyOfFiniteType.isLocallyNoetherian j
      let : CompactSpace D.subscheme := QuasiCompact.compactSpace_of_compactSpace j
      let : IsNoetherian D.subscheme := {}
      have hHD := LineBundle.IsAmple.pullback_closedImmersion H hH j
      have hm := ih (j ≫ p) (H.pullback j) (L.pullback j) hHD hd.2 ε
        (uniform_curve_margin_restrict p L H ε hmargin j)
        (ls.map (fun B => B.pullback j)) (by simpa using hlen') (by
          intro B hB
          obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hB
          exact LineBundle.IsAmple.pullback_closedImmersion C (hamp C (by simp [hC])) j)
      have hrestrict (B : LineBundle X) :
          (n : ℤ) * mixedTop (lineEuler p (d+1+1)) (B :: A :: ls) =
            mixedTop (lineEuler (j ≫ p) (d+1))
              (B.pullback j :: ls.map (fun C => C.pullback j)) := by
        have he := mixedTop_power_cartier_restriction_q68 p H hH (d+1)
          (by simpa only [Nat.cast_add, Nat.cast_one] using hdim.le)
          A n s (B :: ls) (by simp [hlen'])
        have hswap := congrFun
          (mixedDifference_perm (List.Perm.swap B A ls) (lineEuler p (d+1+1))
            (lineEuler_isoInvariant p (d+1+1))) (structureLineBundle X)
        change mixedTop (lineEuler p (d+1+1)) (A :: B :: ls) =
          mixedTop (lineEuler p (d+1+1)) (B :: A :: ls) at hswap
        rw [hswap] at he
        exact he
      rw [← hrestrict H, ← hrestrict L] at hm
      push_cast at hm
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      apply (mul_le_mul_iff_right₀ hnR).mp
      nlinarith [hm]

theorem mixedTop_curve_margin_q68_oai {X : Scheme.{0}} [IsNoetherian X] [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X = ((d+1 : ℕ) : WithBot ℕ∞))
    (ε : ℝ) (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ))
    (ls : List (LineBundle X)) (hlen : ls.length = d) (hamp : ∀ A ∈ ls, A.IsAmple) :
    ε * (mixedTop (lineEuler p (d+1)) (H :: ls) : ℝ) ≤
      (mixedTop (lineEuler p (d+1)) (L :: ls) : ℝ) :=
  mixedTop_curve_margin_aux d p H L hH hdim ε hmargin ls hlen hamp

end
end PiExponent.NumericalAmpleness

end OAI
end

theorem solution : type_of% @OAI.PiExponent.NumericalAmpleness.mixedTop_curve_margin_q68_oai := @OAI.PiExponent.NumericalAmpleness.mixedTop_curve_margin_q68_oai
