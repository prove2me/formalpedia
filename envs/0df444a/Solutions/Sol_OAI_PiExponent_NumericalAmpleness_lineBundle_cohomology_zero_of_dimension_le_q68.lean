-- Prove2me | solution 1 for OAI.PiExponent.NumericalAmpleness.lineBundle_cohomology_zero_of_dimension_le_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:24:17.525518+00:00
-- url     : https://prove2.me/submissions/2bef0a41-910b-43f6-a26b-04ceda6369cd

import Mathlib
import Definitions.Def_OAIQ068A035
import Definitions.Def_OAIQ068A042
import Theorems.Thm_OAI_PiExponent_GeometrySupport_NoetherianAmpleSerreVanishing_ample_serre_tensor_vanishing_q68

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
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_SerrePowerDescent
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.SerrePowerDescent
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open PiExponentSeshadri.Geometry

variable {X : Scheme.{0}}

theorem ext_zero_of_iso {M N : X.Modules} (e : M ≅ N) (q : ℕ)
    (h : ∀ x : Ext.{1} (structureSheaf X) M q, x = 0) :
    ∀ x : Ext.{1} (structureSheaf X) N q, x = 0 := by
  let E := (extFunctorObj (structureSheaf X) q).mapIso e
  intro x
  obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso E.hom).surjective x
  exact (congrArg E.hom (h y)).trans E.hom.hom.map_zero

end
end PiExponent.GeometrySupport.SerrePowerDescent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_NakaiCohomology
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem cohomologyMap_bijective_of_quotient_vanishing
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (n : ℕ) (hprev : ∀ z : cohomology S.X₃ n, z = 0)
    (hnext : ∀ z : cohomology S.X₃ (n+1), z = 0) :
    Function.Bijective (cohomologyMap p S.f (n+1)) := by
  let := Module.compHom (cohomology S.X₁ (n+1)) (baseScalars p)
  let := Module.compHom (cohomology S.X₂ (n+1)) (baseScalars p)
  constructor
  · apply (injective_iff_map_eq_zero (cohomologyMap p S.f (n+1))).mpr
    intro a ha
    obtain ⟨b,hb⟩ := Ext.covariant_sequence_exact₁ (structureSheaf X) hS a ha rfl
    rw [hprev b, Ext.zero_comp] at hb
    exact hb.symm
  · intro b
    exact Ext.covariant_sequence_exact₂ (structureSheaf X) hS b (hnext _)

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CartierPowerFrames
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CartierPowerFrames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

theorem cartierPowerMultiply_ideal (L : LineBundle X) (s : GlobalSections X L.sheaf)
    (n : ℕ) (U : X.affineOpens)
    (e : L.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme) :
    Ideal.span {U.1.topIso.hom (endValue ((modulePowFrame U.1 e n).inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map
        (PiExponent.NumericalAmpleness.cartierPowerMultiply L s n) ≫
      (modulePowFrame U.1 e (n+1)).hom))} =
    Ideal.span {U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))} :=
  tensor_multiply_ideal L.sheaf (modulePow X L.sheaf n) s U e (modulePowFrame U.1 e n)
end
end PiExponent.CartierPowerFrames

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_SectionCartierRegular
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal
variable {X : Scheme.{0}}

private lemma mono_iso_inv_comp_p2 {C : Type*} [Category C] {A B D : C}
    (e : A ≅ B) (f : A ⟶ D) [Mono f] : Mono (e.inv ≫ f) := inferInstance

theorem cartierPowerMultiply_mono_of_mono (L : LineBundle X)
    (s : GlobalSections X L.sheaf) [Mono s] (n : ℕ) :
    Mono (cartierPowerMultiply L s n) := by
  have hm : Mono (moduleTensorMap s (𝟙 (modulePow X L.sheaf n))) :=
    moduleTensorMap_mono s (L.pow n)
  exact @mono_iso_inv_comp_p2 X.Modules _ _ _ _
    (moduleTensorUnit (modulePow X L.sheaf n)) _ hm

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CartierMixedEuler
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroIdeal PiExponent.CartierPowerFrames
variable {X : Scheme.{0}}

private lemma framed_map {C : Type*} [Category C] {A B P Q T O : C}
    (r : A ≅ P) (r' : B ≅ Q) (e : P ≅ T) (e' : Q ≅ T) (u : T ≅ O)
    (m : A ⟶ B) (p : P ⟶ Q) (b : T ⟶ T) (a : O ⟶ O)
    (hn : m ≫ r'.hom = r.hom ≫ p) (ht : p ≫ e'.hom = e.hom ≫ b)
    (hs : b ≫ u.hom = u.hom ≫ a) :
    (r ≪≫ e ≪≫ u).inv ≫ m ≫ (r' ≪≫ e' ≪≫ u).hom = a := by
  simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc]
  rw [← Category.assoc m r'.hom, hn]
  simp only [Category.assoc]
  rw [← Category.assoc p e'.hom, ht]
  simp only [Category.assoc]
  rw [hs]
  simp

lemma tensorMap_framed (A B M : X.Modules) (φ : A ⟶ B) (U : X.Opens)
    (e : A.restrict U.ι ≅ O U.toScheme)
    (e' : B.restrict U.ι ≅ O U.toScheme)
    (f : M.restrict U.ι ≅ O U.toScheme) :
    (_root_.OAI.PiExponent.CartierPowerFrames.tensorFrame A M U e f).inv ≫
      (Scheme.Modules.restrictFunctor U.ι).map (moduleTensorMap φ (𝟙 M)) ≫
        (_root_.OAI.PiExponent.CartierPowerFrames.tensorFrame B M U e' f).hom =
      e.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map φ ≫ e'.hom := by
  let F := Scheme.Modules.restrictFunctor U.ι
  let R := moduleTensorRestrict U A M
  let R' := moduleTensorRestrict U B M
  let E := moduleTensorIso e f
  let E' := moduleTensorIso e' f
  let T := moduleTensorUnit (O U.toScheme)
  let c := e.inv ≫ F.map φ ≫ e'.hom
  let p := moduleTensorMap (F.map φ) (𝟙 (M.restrict U.ι))
  have he : F.map φ ≫ e'.hom = e.hom ≫ c := by
    simp [c]
  have hn : F.map (moduleTensorMap φ (𝟙 M)) ≫ R'.hom = R.hom ≫ p :=
    (moduleTensorRestrict_natural U φ (𝟙 M)).trans
      (congrArg (fun q => R.hom ≫ moduleTensorMap (F.map φ) q) (F.map_id M))
  have h₁ := (moduleTensorMap_comp (F.map φ) e'.hom (𝟙 (M.restrict U.ι)) f.hom).symm.trans
    (congrArg (moduleTensorMap (F.map φ ≫ e'.hom)) (Category.id_comp f.hom))
  have h₂ := (moduleTensorMap_comp e.hom c f.hom (𝟙 (O U.toScheme))).symm.trans
    (congrArg (moduleTensorMap (e.hom ≫ c)) (Category.comp_id f.hom))
  have ht : p ≫ E'.hom = E.hom ≫ moduleTensorMap c (𝟙 (O U.toScheme)) :=
    h₁.trans ((congrArg (fun q : F.obj A ⟶ O U.toScheme => moduleTensorMap q f.hom)
      he).trans h₂.symm)
  have hs : moduleTensorMap c (𝟙 (O U.toScheme)) ≫ T.hom = T.hom ≫ c :=
    (moduleTensorUnit_scalar (X := U.toScheme) c (𝟙 (O U.toScheme))).trans
      (congrArg (fun q => T.hom ≫ q) (Category.comp_id c))
  simpa only [_root_.OAI.PiExponent.CartierPowerFrames.tensorFrame] using!
    framed_map R R' E E' T (F.map (moduleTensorMap φ (𝟙 M))) p _ c hn ht hs

theorem mixedCartierPowerMultiply_mono (L M : LineBundle X)
    (s : GlobalSections X L.sheaf) [Mono s] (n : ℕ) :
    Mono (mixedCartierPowerMultiply L M s n) := by
  let := cartierPowerMultiply_mono_of_mono L s n
  exact moduleTensorMap_mono (cartierPowerMultiply L s n) M

theorem mixedCartierPower_zeroIdeal_frames (L M : LineBundle X)
    (s : GlobalSections X L.sheaf) (n : ℕ) :
    ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : ((L.pow n).tensor M).sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ e' : ((L.pow (n+1)).tensor M).sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        (zeroIdeal L s).ideal U = Ideal.span {U.1.topIso.hom
          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map
            (mixedCartierPowerMultiply L M s n) ≫ e'.hom))} := by
  intro x
  obtain ⟨U, hx, ⟨e⟩, ⟨f⟩⟩ := common_affine_frames L M x
  refine ⟨U, hx,
    _root_.OAI.PiExponent.CartierPowerFrames.tensorFrame (L.pow n).sheaf M.sheaf U.1 (modulePowFrame U.1 e n) f,
    _root_.OAI.PiExponent.CartierPowerFrames.tensorFrame (L.pow (n+1)).sheaf M.sheaf U.1 (modulePowFrame U.1 e (n+1)) f, ?_⟩
  simp only [mixedCartierPowerMultiply]
  have hframe := tensorMap_framed (L.pow n).sheaf (L.pow (n+1)).sheaf M.sheaf
    (cartierPowerMultiply L s n) U.1 (modulePowFrame U.1 e n)
    (modulePowFrame U.1 e (n+1)) f
  exact ((zeroIdeal_on_frame L s U e).trans (cartierPowerMultiply_ideal L s n U e).symm).trans
    (congrArg (fun g : O U.1.toScheme ⟶ O U.1.toScheme =>
      Ideal.span {U.1.topIso.hom (endValue g)}) hframe.symm)

theorem regular_mixedCartierPower_restriction_shortExact
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L M : LineBundle X)
    (s : GlobalSections X L.sheaf) [Mono s] (n : ℕ) :
    ∃ hz : mixedCartierPowerMultiply L M s n ≫
        PiExponentSeshadri.LineClosedUnit.map (zeroIdeal L s).subschemeι ((L.pow (n+1)).tensor M) = 0,
      (ShortComplex.mk (mixedCartierPowerMultiply L M s n)
        (PiExponentSeshadri.LineClosedUnit.map (zeroIdeal L s).subschemeι
          ((L.pow (n+1)).tensor M)) hz).ShortExact := by
  let := mixedCartierPowerMultiply_mono L M s n
  exact PiExponentSeshadri.CartierSequence.exact p ((L.pow n).tensor M) ((L.pow (n+1)).tensor M)
    (mixedCartierPowerMultiply L M s n) (zeroIdeal L s)
    (mixedCartierPower_zeroIdeal_frames L M s n)

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_LineCohomologyDimension
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal

theorem lineBundle_cohomology_zero_of_dimension_le_q68_oai (d : ℕ) :
    ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
      (H : LineBundle X), H.IsAmple → ∀ (M : LineBundle X),
      topologicalKrullDim X ≤ d → ∀ q : ℕ, d < q →
      ∀ z : cohomology M.sheaf q, z = 0 := by
  induction d with
  | zero =>
    intro X p hp H hH M hdim q hq
    let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
    let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
    let : IsNoetherian X := {}
    let : Finite X := finite_of_dim_le_zero hdim
    let : IsAffine X := proper_finite_scheme_isAffine p
    let := PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation M
    let : M.sheaf.IsQuasicoherent :=
      (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M.sheaf).choose.isQuasicoherent
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
    exact PiExponentSeshadri.AffineSchemeCohomology.affine_ext_zero X M.sheaf k
  | succ d ih =>
    intro X p hp H hH M hdim q hq
    let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
    let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
    let : IsNoetherian X := {}
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    have hk : d < k := by omega
    obtain ⟨N,hN⟩ := GeneratorsSectionCover.ample_eventual_fin_section_cover H hH
    let a := N+1
    obtain ⟨l,t,ht⟩ := hN a (by omega)
    let A := H.pow a
    have hA : A.IsAmple := hH.pow a (by omega)
    obtain ⟨s,hs⟩ := exists_mono_section_of_finite_cover p A t ht
    let : Mono s := hs
    let i := (zeroIdeal A s).subschemeι
    have hdimD : topologicalKrullDim (zeroIdeal A s).subscheme ≤ d :=
      regular_sectionZero_dimension_le A s d (by simpa only [Nat.cast_add,Nat.cast_one] using hdim)
    let F : ℕ → X.Modules := fun n => ((A.pow n).tensor M).sheaf
    let Q : ℕ → X.Modules := fun n => (Scheme.Modules.pushforward i).obj
      ((Scheme.Modules.pullback i).obj ((A.pow (n+1)).tensor M).sheaf)
    have hQ (n j : ℕ) (hj : d < j) : ∀ z : cohomology (Q n) j, z = 0 := by
      have hD := ih (i ≫ p) (H.pullback i) (hH.pullback_closedImmersion H i)
        ((((A.pow (n+1)).tensor M).pullback i)) hdimD j hj
      let e := ClosedImmersionSerreTransfer.cohomologyLinearEquiv i p
        ((Scheme.Modules.pullback i).obj ((A.pow (n+1)).tensor M).sheaf) j
      intro z
      obtain ⟨w,rfl⟩ := e.surjective z
      exact (congrArg e (hD w)).trans e.map_zero
    have hstep (n : ℕ) : Function.Bijective
        (cohomologyMap p (mixedCartierPowerMultiply A M s n) (k+1)) := by
      obtain ⟨hz,hS⟩ := regular_mixedCartierPower_restriction_shortExact p A M s n
      exact cohomologyMap_bijective_of_quotient_vanishing p _ hS k
        (hQ n k hk) (hQ n (k+1) (by omega))
    let := PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation M
    obtain ⟨K,hK⟩ := GeometrySupport.NoetherianAmpleSerreVanishing.ample_serre_tensor_vanishing_q68
      p A hA M.sheaf
    have hzeroK : ∀ z : cohomology (F K) (k+1), z = 0 :=
      GeometrySupport.SerrePowerDescent.ext_zero_of_iso
        (moduleTensorComm M.sheaf (A.pow K).sheaf) (k+1) (hK K le_rfl (k+1) (by omega))
    have hback : ∀ n : ℕ, (∀ z : cohomology (F n) (k+1), z = 0) →
        ∀ z : cohomology (F 0) (k+1), z = 0 := by
      intro n
      induction n with
      | zero => exact fun h => h
      | succ n ihn =>
        intro hn
        apply ihn
        intro z
        apply (hstep n).injective
        rw [map_zero]
        exact hn _
    exact GeometrySupport.SerrePowerDescent.ext_zero_of_iso (moduleTensorUnit M.sheaf)
      (k+1) (hback K hzeroK)

end
end PiExponent.NumericalAmpleness

end OAI
end

theorem solution : type_of% @OAI.PiExponent.NumericalAmpleness.lineBundle_cohomology_zero_of_dimension_le_q68_oai := @OAI.PiExponent.NumericalAmpleness.lineBundle_cohomology_zero_of_dimension_le_q68_oai
