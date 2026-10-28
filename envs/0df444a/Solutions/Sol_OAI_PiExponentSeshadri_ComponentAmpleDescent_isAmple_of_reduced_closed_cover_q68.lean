-- Prove2me | solution 1 for OAI.PiExponentSeshadri.ComponentAmpleDescent.isAmple_of_reduced_closed_cover_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:32:52.702786+00:00
-- url     : https://prove2.me/submissions/569dd58a-4174-4324-8ee7-a9d698d816fe

import Mathlib
import Definitions.Def_OAIQ068A045
import Theorems.Thm_OAI_PiExponentSeshadri_ComponentAmpleDescent_eventual_tensor_cohomology_zero_of_closed_pushforward_q68

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_AmpleAllPowersGeneration
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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

end
end PiExponent.AmpleGlobalGeneration

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

end
end PiExponent.GeneratorsSectionCover

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_AmpleGeneratedTensor
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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

theorem LineBundle.IsAmple.tensor_of_section_cover {H M : LineBundle X}
    (hH : H.IsAmple) {ι : Type} (s : ι → GlobalSections X M.sheaf)
    (hc : (⨆ i, sectionOpen X (s i)) = ⊤) : (H.tensor M).IsAmple := by
  intro x V hx
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp
    (show x ∈ ⨆ i, sectionOpen X (s i) by rw [hc]; trivial)
  obtain ⟨n, hn, a, hxa, haV, haa⟩ :=
    hH x (V ⊓ sectionOpen X (s i)) ⟨hx, hi⟩
  let b : GlobalSections X (M.pow n).sheaf := powerSection (s i) n
  have hb : sectionOpen X b = sectionOpen X (s i) := M.sectionOpen_power (s i) hn
  let q : GlobalSections X ((H.tensor M).pow n).sheaf :=
    tensorSection a b ≫ (lineTensorPow H M n).inv
  have hq : sectionOpen X q = sectionOpen X a := by
    change SectionOpens.isoOpen
      (tensorSection a b ≫ (lineTensorPow H M n).symm.hom) = _
    erw [SectionOpens.isoOpen_postcomp]
    calc
      SectionOpens.isoOpen (tensorSection a b) =
          sectionOpen X a ⊓ sectionOpen X b := section_open (H.pow n) (M.pow n) a b
      _ = sectionOpen X a := by
        rw [hb, inf_eq_left.mpr (haV.trans inf_le_right)]
  exact ⟨n, hn, q, hq.symm ▸ hxa, hq.le.trans (haV.trans inf_le_left), hq.symm ▸ haa⟩

theorem LineBundle.isAmple_of_inverse_twist_section_cover (L H : LineBundle X)
    (hH : H.IsAmple) {n : ℕ} (hn : 0 < n) {ι : Type}
    (s : ι → GlobalSections X (H.inverse.tensor (L.pow n)).sheaf)
    (hc : (⨆ i, sectionOpen X (s i)) = ⊤) : L.IsAmple :=
  LineBundle.IsAmple.of_pow L hn
    (PiExponent.AmpleIso.isAmple_of_sheaf_iso
      (H.tensor (H.inverse.tensor (L.pow n))) (L.pow n)
      (ampleInverseTwistCancel H L n) (hH.tensor_of_section_cover s hc))

end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ComponentAmpleDescentCover
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.ComponentAmpleDescent
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open _root_.OAI.PiExponentSeshadri.Geometry
variable {X Y Z : Scheme.{0}}

theorem eventual_pullback_twist_sections [NoetherianSpace Y]
    (f : Y ⟶ X) (K L : LineBundle X) (hL : (L.pullback f).IsAmple) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ y : Y,
      ∃ s : GlobalSections Y ((K.tensor (L.pow n)).pullback f).sheaf,
        y ∈ sectionOpen Y s := by
  have : (K.pullback f).sheaf.IsFinitePresentation :=
    PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation _
  obtain ⟨N,hN⟩ := PiExponent.AmpleGlobalGeneration.ample_eventual_global_generators
    (L.pullback f) hL (K.pullback f).sheaf
  refine ⟨N, fun n hn y => ?_⟩
  obtain ⟨G,hG⟩ := hN n hn
  let : G.IsFiniteType := hG
  let D := SheafOfModules.GeneratingSections.equivOfIso (pullbackTwistIso f K L n).symm G
  have hc := @PiExponent.GeneratorsSectionCover.generators_sectionOpen_cover Y
    ((K.tensor (L.pow n)).pullback f) D ⟨hG.finite⟩
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp
    (show y ∈ ⨆ i, sectionOpen Y
      (PiExponent.GeneratorsSectionCover.generatorSection _ D i) by rw [hc]; trivial)
  exact ⟨_,hi⟩

theorem section_cover_of_jointly_surjective
    (f : Y ⟶ X) (g : Z ⟶ X) (M : LineBundle X)
    (hcover : Set.range f ∪ Set.range g = Set.univ)
    (hf : Function.Surjective (fun s : GlobalSections X M.sheaf => pullbackSection f s))
    (hg : Function.Surjective (fun s : GlobalSections X M.sheaf => pullbackSection g s))
    (hY : ∀ y : Y, ∃ s : GlobalSections Y (M.pullback f).sheaf, y ∈ sectionOpen Y s)
    (hZ : ∀ z : Z, ∃ s : GlobalSections Z (M.pullback g).sheaf, z ∈ sectionOpen Z s) :
    (⨆ s : GlobalSections X M.sheaf, sectionOpen X s) = ⊤ := by
  apply top_unique
  intro x _
  have hx : x ∈ Set.range f ∪ Set.range g := by rw [hcover]; trivial
  rcases hx with ⟨y,rfl⟩ | ⟨z,rfl⟩
  · obtain ⟨s,hs⟩ := hY y
    obtain ⟨t,rfl⟩ := hf s
    apply Opens.mem_iSup.mpr
    refine ⟨t,?_⟩
    change y ∈ f ⁻¹ᵁ SectionOpens.isoOpen t
    exact (pullback_isoOpen_eq M t f).le hs
  · obtain ⟨s,hs⟩ := hZ z
    obtain ⟨t,rfl⟩ := hg s
    apply Opens.mem_iSup.mpr
    refine ⟨t,?_⟩
    change z ∈ g ⁻¹ᵁ SectionOpens.isoOpen t
    exact (pullback_isoOpen_eq M t g).le hs

theorem isAmple_of_eventual_restriction_surjective
    [NoetherianSpace Y] [NoetherianSpace Z]
    (f : Y ⟶ X) (g : Z ⟶ X) (L H : LineBundle X) (hH : H.IsAmple)
    (hcover : Set.range f ∪ Set.range g = Set.univ)
    (hY : (L.pullback f).IsAmple) (hZ : (L.pullback g).IsAmple)
    (hf : ∃ N : ℕ, ∀ n ≥ N, Function.Surjective
      (fun s : GlobalSections X (H.inverse.tensor (L.pow n)).sheaf => pullbackSection f s))
    (hg : ∃ N : ℕ, ∀ n ≥ N, Function.Surjective
      (fun s : GlobalSections X (H.inverse.tensor (L.pow n)).sheaf => pullbackSection g s)) :
    L.IsAmple := by
  obtain ⟨A,hA⟩ := eventual_pullback_twist_sections f H.inverse L hY
  obtain ⟨B,hB⟩ := eventual_pullback_twist_sections g H.inverse L hZ
  obtain ⟨C,hC⟩ := hf
  obtain ⟨D,hD⟩ := hg
  let n := A+B+C+D+1
  have hn : 0 < n := by omega
  have hAn : A ≤ n := by omega
  have hBn : B ≤ n := by omega
  have hCn : C ≤ n := by omega
  have hDn : D ≤ n := by omega
  exact L.isAmple_of_inverse_twist_section_cover H hH hn (fun s => s)
    (section_cover_of_jointly_surjective f g (H.inverse.tensor (L.pow n)) hcover
      (hC n hCn) (hD n hDn) (hA n hAn) (hB n hBn))

end
end PiExponentSeshadri.ComponentAmpleDescent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ComponentAmpleDescentIdeal
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.IdealModule.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.IdealModule.restrictedToClosed_isIso _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.ComponentAmpleDescent
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open IdealModule
variable {X : Scheme.{0}}

theorem ideal_le_annihilator_closedModule {I J : X.IdealSheafData}
    (h : I * J = ⊥) (U : X.affineOpens) :
    J.ideal U ≤ Module.annihilator Γ(X,U.1) Γ(closedModule I,U.1) := by
  intro a ha
  apply Module.mem_annihilator.mpr
  intro m
  have hinj : Function.Injective ((closedInclusion I).val.app (op U.1)) := by
    let : Mono (closedInclusion I).val :=
      inferInstanceAs (Mono ((Scheme.Modules.toPresheafOfModules X).map (closedInclusion I)))
    exact PresheafOfModules.injective_of_mono (closedInclusion I).val (op U.1)
  apply hinj
  have hm : (closedInclusion I).app U.1 m ∈ I.ideal U := by
    rw [← closed_image I U]
    exact ⟨m,rfl⟩
  have hp := Ideal.mul_mem_mul_rev (R := Γ(X,U.1)) hm ha
  let b : Γ(X,U.1) := (closedInclusion I).app U.1 m
  have hz : a * b = 0 := by
    have hh : I.ideal U * J.ideal U = ⊥ := congrArg (fun K : X.IdealSheafData => K.ideal U) h
    simpa only [hh,Ideal.mem_bot] using hp
  exact (((closedInclusion I).app_smul (r := a) (x := m)).trans hz).trans
    ((closedInclusion I).app U.1).hom.map_zero.symm

theorem ideal_mul_eq_bot_of_reduced_cover [IsReduced X]
    {I J : X.IdealSheafData} (h : I.support ⊔ J.support = ⊤) : I * J = ⊥ := by
  apply Scheme.IdealSheafData.support_eq_top_iff.mp
  simpa only [Scheme.IdealSheafData.support_mul] using h

theorem ideal_le_annihilator_closedModule_of_reduced_cover [IsReduced X]
    {I J : X.IdealSheafData} (h : I.support ⊔ J.support = ⊤) (U : X.affineOpens) :
    J.ideal U ≤ Module.annihilator Γ(X,U.1) Γ(closedModule I,U.1) :=
  ideal_le_annihilator_closedModule (ideal_mul_eq_bot_of_reduced_cover h) U

end
end PiExponentSeshadri.ComponentAmpleDescent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ComponentAmpleDescentLocal
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.ComponentAmpleDescent
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.IdealModule
variable {X : Scheme.{0}}

theorem closedModule_restrict_annihilated [IsReduced X]
    {I J : X.IdealSheafData} (h : I.support ⊔ J.support = ⊤) (U : X.affineOpens) :
    RingHom.ker (J.subschemeι ∣_ U.1).appTop.hom ≤
      Module.annihilator Γ(U.1.toScheme,⊤) Γ((closedModule I).restrict U.1.ι,⊤) := by
  let : IsAffine U.1.toScheme := U.2
  have hcover : (I.comap U.1.ι).support ⊔ (J.comap U.1.ι).support = ⊤ := by
    rw [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap]
    ext x
    change U.1.ι x ∈ (I.support : Set X) ∪ (J.support : Set X) ↔ True
    have hx : U.1.ι x ∈ (I.support ⊔ J.support : Closeds X) := by rw [h]; trivial
    exact iff_true_intro hx
  intro a ha
  apply Module.mem_annihilator.mpr
  intro m
  let e := closedModuleRestrictIso I U.1.ι
  have hj : a ∈ (J.comap U.1.ι).ideal ⟨⊤,isAffineOpen_top _⟩ := by
    erw [← (J.comap U.1.ι).ker_subschemeι_app ⟨⊤,isAffineOpen_top _⟩,
      ← ker_appTop_subscheme_morphismRestrict J U]
    exact ha
  have hz := Module.mem_annihilator.mp
    (ideal_le_annihilator_closedModule_of_reduced_cover hcover
      ⟨⊤,isAffineOpen_top _⟩ hj) (e.hom.app ⊤ m)
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).injective
  exact (e.hom.app_smul a m).trans (hz.trans (map_zero _).symm)

end
end PiExponentSeshadri.ComponentAmpleDescent

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
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_NakaiSectionLifting
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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
variable {X Y : Scheme.{0}}

theorem pullbackSection_surjective_of_unit_surjective (f : Y ⟶ X) (L : LineBundle X)
    (h : Function.Surjective (fun s : GlobalSections X L.sheaf =>
      s ≫ PiExponentSeshadri.LineClosedUnit.map f L)) :
    Function.Surjective (fun s : GlobalSections X L.sheaf => pullbackSection f s) := by
  intro σ
  let A := Scheme.Modules.pullbackPushforwardAdjunction f
  let e := A.homEquiv (structureSheaf X) ((Scheme.Modules.pullback f).obj L.sheaf)
  obtain ⟨s,hs⟩ := h (e ((pullbackUnitIso f).hom ≫ σ))
  have he : (Scheme.Modules.pullback f).map s = (pullbackUnitIso f).hom ≫ σ := by
    apply e.injective
    have hn := A.homEquiv_naturality_left s (𝟙 ((Scheme.Modules.pullback f).obj L.sheaf))
    simpa only [e, Category.comp_id, Adjunction.homEquiv_unit, Functor.map_id,
      Category.comp_id] using! hn.trans hs
  refine ⟨s,?_⟩
  change (pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map s = σ
  exact (congrArg (fun t : (Scheme.Modules.pullback f).obj (structureSheaf X) ⟶
      (Scheme.Modules.pullback f).obj L.sheaf => (pullbackUnitIso f).inv ≫ t) he).trans
    ((pullbackUnitIso f).inv_hom_id_assoc σ)

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ClosedThickeningSections
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite
open PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}}

attribute [local instance] OAI.PiExponentSeshadri.Geometry.instHasExtModules_solutions
theorem globalSections_surjective_of_ext_one_zero (S : ShortComplex X.Modules)
    (hS : S.ShortExact)
    (hzero : ∀ x : Abelian.Ext.{1} (structureSheaf X) S.X₁ 1, x = 0) :
    Function.Surjective (fun s : GlobalSections X S.X₂ => s ≫ S.g) := by
  intro s
  obtain ⟨a,ha⟩ := Ext.covariant_sequence_exact₃ (structureSheaf X) hS (Ext.mk₀ s)
    rfl (hzero _)
  refine ⟨Ext.homEquiv₀ a, ?_⟩
  apply (Ext.mk₀_bijective (structureSheaf X) S.X₃).injective
  rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply]
  exact ha

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ClosedSectionLifting
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentSeshadri.Geometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian


variable {X Y : Scheme.{0}}

theorem closed_line_unit_epi (f : Y ⟶ X) [IsClosedImmersion f] (M : LineBundle X) :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M.sheaf) :=
  PiExponentSeshadri.LineClosedUnit.epi f M

local instance localInst_r4712f5_1 (Z : Scheme.{0}) : HasExt.{1} Z.Modules := HasExt.standard _
theorem pullbackSection_surjective_of_kernel_cohomology_zero
    (f : Y ⟶ X) [IsClosedImmersion f] (M : LineBundle X)
    (hzero : ∀ z : cohomology
      (kernel ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M.sheaf)) 1,
      z = 0) :
    Function.Surjective (fun s : GlobalSections X M.sheaf => pullbackSection f s) := by
  let u := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M.sheaf
  have : Epi u := closed_line_unit_epi f M
  let S := ShortComplex.mk (kernel.ι u) u (kernel.condition u)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel u }
  exact PiExponent.NumericalAmpleness.pullbackSection_surjective_of_unit_surjective f M
    (globalSections_surjective_of_ext_one_zero S hS hzero)

end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ClosedUnitKernel
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentSeshadri.Geometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open PiExponentSeshadri.TensorPure


variable {X Y : Scheme.{0}}

theorem pullbackSection_surjective_of_idealTensor_cohomology_zero
    (f : Y ⟶ X) [IsClosedImmersion f] (M : LineBundle X)
    (hzero : ∀ z : cohomology
      (moduleTensor X (PiExponentSeshadri.IdealModule.idealModule f) M.sheaf) 1, z = 0) :
    Function.Surjective (fun s : GlobalSections X M.sheaf => pullbackSection f s) := by
  apply pullbackSection_surjective_of_kernel_cohomology_zero f M
  exact PiExponent.GeometrySupport.SerrePowerDescent.ext_zero_of_iso
    (closedLineUnitKernelIso f M) 1 hzero

end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ModulePullbackCoherent
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponent.FiniteGlobalPresentation

theorem pullback_isFinitePresentation {X Y : Scheme.{0}} (f : Y ⟶ X)
    (M : X.Modules) [M.IsFinitePresentation] :
    ((Scheme.Modules.pullback f).obj M).IsFinitePresentation := by
  apply isFinitePresentation_of_localPresentations
  intro y
  obtain ⟨U, hy, P, hP⟩ := exists_local_finitePresentation M (f y)
  let F : SheafOfModules U.toScheme.ringCatSheaf ⥤
      SheafOfModules (f ⁻¹ᵁ U).toScheme.ringCatSheaf :=
    Scheme.Modules.pullback (f ∣_ U)
  let : PreservesColimitsOfSize.{0,0} F :=
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).leftAdjoint_preservesColimits
  let Q := P.map F (pullbackUnitIso (f ∣_ U)).symm
  let e := (pullbackRestrictNatIso f U).app M
  exact ⟨f ⁻¹ᵁ U, hy, presentationOfIso (f ⁻¹ᵁ U).toScheme e.symm Q,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_GlobalClosedAnnihilatedDescent
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.ClosedAnnihilatedDescent
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
variable {X Y : Scheme.{0}} (f : Y ⟶ X)

theorem exists_closed_coherent_descent [IsClosedImmersion f]
    (M : X.Modules) [M.IsFinitePresentation] (h : LocallyAnnihilated f M) :
    ∃ N : Y.Modules, N.IsFinitePresentation ∧
      Nonempty ((Scheme.Modules.pushforward f).obj N ≅ M) := by
  let : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  exact ⟨(Scheme.Modules.pullback f).obj M, Geometry.pullback_isFinitePresentation f M,
    ⟨closedDescentPushforwardIso f M h⟩⟩

end
end PiExponentSeshadri.ClosedAnnihilatedDescent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ComponentAmpleDescent
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.ComponentAmpleDescent
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.IdealModule
variable {X : Scheme.{0}} [IsNoetherian X] [IsReduced X]
variable {R : Type} [CommRing R] [IsNoetherianRing R]

theorem exists_complementary_ideal_descent
    (I J : X.IdealSheafData) (hcover : I.support ⊔ J.support = ⊤) :
    ∃ N : J.subscheme.Modules, N.IsFinitePresentation ∧
      Nonempty ((Scheme.Modules.pushforward J.subschemeι).obj N ≅ closedModule I) := by
  have : (closedModule I).IsFinitePresentation := closedModule_isFinitePresentation I
  apply ClosedAnnihilatedDescent.exists_closed_coherent_descent J.subschemeι (closedModule I)
  intro U
  exact closedModule_restrict_annihilated hcover U

theorem eventual_restriction_surjective_of_complement_ample
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (K L : LineBundle X) (I J : X.IdealSheafData)
    (hcover : I.support ⊔ J.support = ⊤) (hJ : (L.pullback J.subschemeι).IsAmple) :
    ∃ B : ℕ, ∀ n ≥ B, Function.Surjective
      (fun s : GlobalSections X (K.tensor (L.pow n)).sheaf => pullbackSection I.subschemeι s) := by
  obtain ⟨N,hN,⟨e⟩⟩ := exists_complementary_ideal_descent I J hcover
  let : N.IsFinitePresentation := hN
  obtain ⟨B,hB⟩ := eventual_tensor_cohomology_zero_of_closed_pushforward_q68 p J.subschemeι
    (closedModule I) N e K L hJ
  refine ⟨B,fun n hn => ?_⟩
  exact pullbackSection_surjective_of_idealTensor_cohomology_zero I.subschemeι
    (K.tensor (L.pow n)) (hB n hn 1 (by decide))

theorem isAmple_of_reduced_closed_cover_q68_oai
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (L H : LineBundle X) (hH : H.IsAmple)
    (I J : X.IdealSheafData) (hcover : I.support ⊔ J.support = ⊤)
    (hI : (L.pullback I.subschemeι).IsAmple) (hJ : (L.pullback J.subschemeι).IsAmple) :
    L.IsAmple := by
  let : NoetherianSpace I.subscheme :=
    I.subschemeι.isClosedEmbedding.isEmbedding.isInducing.noetherianSpace
  let : NoetherianSpace J.subscheme :=
    J.subschemeι.isClosedEmbedding.isEmbedding.isInducing.noetherianSpace
  have hc : Set.range I.subschemeι ∪ Set.range J.subschemeι = Set.univ := by
    rw [I.range_subschemeι,J.range_subschemeι]
    exact congrArg (fun Z : Closeds X => (Z : Set X)) hcover
  exact isAmple_of_eventual_restriction_surjective I.subschemeι J.subschemeι L H hH hc hI hJ
    (eventual_restriction_surjective_of_complement_ample p H.inverse L I J hcover hJ)
    (eventual_restriction_surjective_of_complement_ample p H.inverse L J I
      (by simpa only [sup_comm] using hcover) hI)

end
end PiExponentSeshadri.ComponentAmpleDescent

end OAI
end

theorem solution : type_of% @OAI.PiExponentSeshadri.ComponentAmpleDescent.isAmple_of_reduced_closed_cover_q68_oai := @OAI.PiExponentSeshadri.ComponentAmpleDescent.isAmple_of_reduced_closed_cover_q68_oai
