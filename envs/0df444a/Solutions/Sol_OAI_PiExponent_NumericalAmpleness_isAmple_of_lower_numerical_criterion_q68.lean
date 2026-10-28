-- Prove2me | solution 1 for OAI.PiExponent.NumericalAmpleness.isAmple_of_lower_numerical_criterion_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:45:46.441327+00:00
-- url     : https://prove2.me/submissions/140d837a-3282-4bf9-aee0-fd7647f73e2c

import Mathlib
import Definitions.Def_OAIQ068A046
import Theorems.Thm_OAI_PiExponent_NumericalAmpleness_ample_slope_of_polynomial_pos_of_lower_criterion_q68
import Theorems.Thm_OAI_PiExponent_NumericalAmpleness_eulerSlopePolynomial_derivative_margin_q68
import Theorems.Thm_OAI_PiExponent_NumericalAmpleness_eulerSlopePolynomial_pos_of_ample_q68
import Theorems.Thm_OAI_PiExponent_NumericalAmpleness_topEuler_slopeBundle_eq_q68

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_TensorMixedSection
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.TensorPure

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

lemma mixed_value_open {M N : X.Modules} (U : X.Opens) (a : O X ⟶ M)
    (b : O U.toScheme ⟶ N.restrict U.ι) [IsIso (restrictSection U.ι a)] [IsIso b]
    (t : O X ⟶ moduleTensor X M N)
    (ht : t.app U (1 : Γ(X,U)) = pure M N U (a.app U (1 : Γ(X,U))) (openSectionEquiv N U b)) :
    U ≤ SectionOpens.isoOpen t := by
  have hi : IsIso (restrictSection U.ι t) := by
    rw [mixed_value_restrict U a b t ht]
    infer_instance
  intro x hx
  apply (SectionOpens.mem_isoOpen_iff t x).mpr
  refine ⟨U,hx,?_⟩
  let hu : IsIso (C := U.toScheme.Modules) (Scheme.Modules.restrictUnitIso U.ι).inv :=
    (Scheme.Modules.restrictUnitIso U.ι).isIso_inv
  exact (@isIso_comp_left_iff U.toScheme.Modules _ _ _ _ _ _ hu).mp hi

end PiExponentSeshadri.TensorPure

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_MixedFrameExtension
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.TensorPure
variable {X : Scheme.{0}}

theorem LineBundle.mixed_frame_extension [IsIntegral X] [CompactSpace X] (L M : LineBundle X)
    (s : O X ⟶ L.sheaf) (hD : (sectionOpen X s : Set X).Nonempty)
    (e : M.sheaf.restrict (sectionOpen X s).ι ≅ O (sectionOpen X s).toScheme) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : O X ⟶ ((L.pow (n+1)).tensor M).sheaf,
      sectionOpen X t = sectionOpen X s ∧
      t.app (sectionOpen X s) (1 : Γ(X,sectionOpen X s)) =
        pure (L.pow (n+1)).sheaf M.sheaf (sectionOpen X s)
          ((powerSection s (n+1)).app (sectionOpen X s) (1 : Γ(X,sectionOpen X s)))
          (openSectionEquiv M.sheaf (sectionOpen X s) e.inv) := by
  obtain ⟨N,hN⟩ := L.divisible_mixed_extension M s hD
    (openSectionEquiv M.sheaf (sectionOpen X s) e.inv)
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨t,ht,hv⟩ := hN n hn
  refine ⟨t,le_antisymm ht ?_,hv⟩
  have hi : IsIso (restrictSection (sectionOpen X s).ι (powerSection s (n+1))) := by
    have hs := L.sectionOpen_power s (by omega : 0 < n+1)
    exact isIso_restricted_section _ _ hs
  exact mixed_value_open (sectionOpen X s) (powerSection s (n+1)) e.inv t hv

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_AmplePositiveTwist
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.TensorPure PiExponentSeshadri.Projective
variable {X : Scheme.{0}}

theorem LineBundle.ample_framed_cover [CompactSpace X] (L M : LineBundle X)
    (hL : L.IsAmple) (a : ℕ) (ha : 0 < a) :
    ∃ d : ℕ, 0 < d ∧ a ∣ d ∧ ∃ ι : Type, ∃ _ : Fintype ι,
      ∃ s : ι → GlobalSections X (L.pow d).sheaf,
        (⨆ i, sectionOpen X (s i)) = ⊤ ∧
        (∀ i, IsAffineOpen (sectionOpen X (s i))) ∧
        (∀ i, (sectionOpen X (s i) : Set X).Nonempty) ∧
        (∀ i, Nonempty (M.sheaf.restrict (sectionOpen X (s i)).ι ≅ O (sectionOpen X (s i)).toScheme)) := by
  classical
  choose V hV e using M.locallyRankOne
  have hh (x : X) := hL x (V x) (hV x)
  choose d hd s hs hsub haff using hh
  obtain ⟨I,hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (sectionOpen X (s x) : Set X)) (fun x => (sectionOpen X (s x)).isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x,hs x⟩)
  obtain ⟨n,hn,t,ht⟩ := L.common_degree (fun i : I => d i.val)
    (fun i => hd i.val) (fun i => s i.val)
  let f := linePowerMul L n a
  let q (i : I) : GlobalSections X (L.pow (n*a)).sheaf :=
    powerSection (t i) a ≫ f.hom
  have hq (i : I) : sectionOpen X (q i) = sectionOpen X (s i.val) := by
    change SectionOpens.isoOpen (powerSection (t i) a ≫ f.hom) = _
    erw [SectionOpens.isoOpen_postcomp]
    exact ((L.pow n).sectionOpen_power (t i) ha).trans (ht i)
  refine ⟨n*a,Nat.mul_pos hn ha,dvd_mul_left a n,I,inferInstance,q,?_,?_,?_,?_⟩
  · apply top_unique
    intro x _
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hI (show x ∈ Set.univ from trivial))
    obtain ⟨hi,hx⟩ := Set.mem_iUnion.mp hi
    refine Opens.mem_iSup.mpr ⟨⟨i,hi⟩,?_⟩
    rw [hq]
    exact hx
  · intro i
    rw [hq]
    exact haff i.val
  · intro i
    rw [hq]
    exact ⟨i.val,hs i.val⟩
  · intro i
    exact ⟨Frames.restrictOpenFrame ((hq i).le.trans (hsub i.val)) (Classical.choice (e i.val))⟩

theorem LineBundle.exists_ample_twist [IsIntegral X] [CompactSpace X]
    (L M : LineBundle X) (hL : L.IsAmple) :
    ∃ d : ℕ, 0 < d ∧ ((L.pow d).tensor M).IsAmple := by
  classical
  obtain ⟨a,ha,-,ι,hi,s,hs,hsa,hsn,he⟩ := L.ample_framed_cover M hL 1 (by decide)
  choose N hN using fun i => (L.pow a).mixed_frame_extension M (s i) (hsn i)
    (Classical.choice (he i))
  let n := Finset.univ.sup N
  choose t ht hval using fun i => hN i n (Finset.le_sup (Finset.mem_univ i))
  let e := moduleTensorIso (linePowerMul L a (n+1)) (Iso.refl M.sheaf)
  let q (i : ι) : GlobalSections X ((L.pow (a*(n+1))).tensor M).sheaf :=
    t i ≫ e.hom
  have hq (i : ι) : sectionOpen X (q i) = sectionOpen X (s i) := by
    change SectionOpens.isoOpen (t i ≫ e.hom) = _
    erw [SectionOpens.isoOpen_postcomp]
    exact ht i
  refine ⟨a*(n+1),Nat.mul_pos ha (by omega),
    ((L.pow (a*(n+1))).tensor M).ample_of_affine_section_cover q ?_ ?_⟩
  · simpa only [hq] using hs
  · intro i
    rw [hq]
    exact hsa i

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_LineAmpleOperations
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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

theorem LineBundle.IsAmple.tensor {L M : LineBundle X}
    (hL : L.IsAmple) (hM : M.IsAmple) : (L.tensor M).IsAmple := by
  intro x V hx
  obtain ⟨n, hn, s, hxs, hsV, _⟩ := hL x V hx
  obtain ⟨m, hm, t, hxt, hts, hta⟩ := hM x (sectionOpen X s) hxs
  let e : ((M.pow m).pow n).sheaf ≅ (M.pow (n*m)).sheaf :=
    linePowerMul M m n ≪≫ eqToIso (congrArg (fun j => (M.pow j).sheaf) (Nat.mul_comm m n))
  let a : structureSheaf X ⟶ (L.pow (n*m)).sheaf :=
    powerSection s m ≫ (linePowerMul L n m).hom
  let b : structureSheaf X ⟶ (M.pow (n*m)).sheaf := powerSection t n ≫ e.hom
  have ha : sectionOpen X a = sectionOpen X s := by
    exact (PiExponent.AmpleIso.sectionOpen_postcomp_iso
      (powerSection s m) (linePowerMul L n m)).trans ((L.pow n).sectionOpen_power s hm)
  have hb : sectionOpen X b = sectionOpen X t := by
    exact (PiExponent.AmpleIso.sectionOpen_postcomp_iso (powerSection t n) e).trans
      ((M.pow m).sectionOpen_power t hn)
  let q := tensorSection a b ≫ (lineTensorPow L M (n*m)).inv
  have hq : sectionOpen X q = sectionOpen X t := by
    exact (PiExponent.AmpleIso.sectionOpen_postcomp_iso
      (tensorSection a b) (lineTensorPow L M (n*m)).symm).trans
        ((section_open (L.pow (n*m)) (M.pow (n*m)) a b).trans
          ((congrArg₂ (fun U V : X.Opens => U ⊓ V) ha hb).trans (inf_eq_right.mpr hts)))
  exact ⟨n*m, Nat.mul_pos hn hm, q, hq.symm ▸ hxt,
    hq.le.trans (hts.trans hsV), hq.symm ▸ hta⟩

end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_AmpleSlopeAlgebra
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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

theorem ample_tensor_nonnegative_power (A H : LineBundle X)
    (hA : A.IsAmple) (hH : H.IsAmple) (n : ℕ) : (A.tensor (H.pow n)).IsAmple := by
  cases n with
  | zero =>
    exact PiExponent.AmpleIso.isAmple_of_sheaf_iso A (A.tensor (H.pow 0))
      (moduleTensorRightUnit A.sheaf).symm hA
  | succ n => exact hA.tensor (hH.pow (n+1) (by omega))

theorem ample_slope_of_cross_le (L H : LineBundle X) (hH : H.IsAmple)
    (a b c d : ℕ) (hb : 0 < b) (hd : 0 < d) (hcross : a*d ≤ c*b)
    (hA : (slopeBundle L H a b).IsAmple) : (slopeBundle L H c d).IsAmple := by
  have hp := ample_tensor_nonnegative_power ((slopeBundle L H a b).pow d) H
    (hA.pow d hd) hH (c*b-a*d)
  apply LineBundle.IsAmple.of_pow (slopeBundle L H c d) hb
  exact PiExponent.AmpleIso.isAmple_of_sheaf_iso _ _ (slopeBundleCrossIso L H a b c d hcross) hp

theorem exists_smaller_ample_slope [IsIntegral X] [CompactSpace X]
    (L H : LineBundle X) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hA : (slopeBundle L H a b).IsAmple) :
    ∃ n : ℕ, 0 < n ∧ (slopeBundle L H (a*n-1) (b*n)).IsAmple ∧
      ((a*n-1 : ℕ) : ℚ) / (b*n : ℕ) < (a:ℚ)/b := by
  obtain ⟨n,hn,hamp⟩ := (slopeBundle L H a b).exists_ample_twist H.inverse hA
  have han := Nat.mul_pos ha hn
  have ham : (slopeBundle L H (a*n-1) (b*n)).IsAmple :=
    PiExponent.AmpleIso.isAmple_of_sheaf_iso _ _
      (moduleTensorIso (slopeBundlePowIso L H a b n) (Iso.refl _) ≪≫
        slopeBundleSubtractIso L H (a*n) (b*n) han) hamp
  refine ⟨n,hn,ham,?_⟩
  have hbq : (0:ℚ) < b := by exact_mod_cast hb
  have hnq : (0:ℚ) < n := by exact_mod_cast hn
  have hsub : ((a*n-1:ℕ):ℚ) = (a:ℚ)*n-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ a*n), Nat.cast_mul, Nat.cast_one]
  rw [hsub, Nat.cast_mul]
  apply (div_lt_div_iff₀ (mul_pos hbq hnq) hbq).mpr
  nlinarith

theorem exists_ample_slope [IsIntegral X] [CompactSpace X]
    (L H : LineBundle X) (hH : H.IsAmple) :
    ∃ a : ℕ, 0 < a ∧ (slopeBundle L H a 1).IsAmple := by
  obtain ⟨a,ha,hA⟩ := H.exists_ample_twist L hH
  refine ⟨a,ha,PiExponent.AmpleIso.isAmple_of_sheaf_iso _ _ ?_ hA⟩
  exact moduleTensorComm (H.pow a).sheaf L.sheaf ≪≫
    moduleTensorIso (moduleTensorRightUnit L.sheaf).symm (Iso.refl _)

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_AmpleSlopeTopology
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory Set
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

lemma ampleSlopes_bddBelow (L H : LineBundle X) : BddBelow (ampleSlopes L H) := by
  refine ⟨0, ?_⟩
  rintro t ⟨a,b,hb,rfl,ha⟩
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma ampleSlopes_nonempty [IsIntegral X] [CompactSpace X]
    (L H : LineBundle X) (hH : H.IsAmple) : (ampleSlopes L H).Nonempty := by
  obtain ⟨a,ha,hA⟩ := exists_ample_slope L H hH
  exact ⟨(a:ℝ)/1,a,1,by decide,by norm_num,hA⟩

lemma ampleThreshold_nonneg [IsIntegral X] [CompactSpace X]
    (L H : LineBundle X) (hH : H.IsAmple) : 0 ≤ ampleThreshold L H := by
  apply le_csInf (ampleSlopes_nonempty L H hH)
  rintro t ⟨a,b,hb,rfl,ha⟩
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem ample_of_threshold_lt [IsIntegral X] [CompactSpace X]
    (L H : LineBundle X) (hH : H.IsAmple) (a b : ℕ) (hb : 0 < b)
    (ht : ampleThreshold L H < (a:ℝ)/b) : (slopeBundle L H a b).IsAmple := by
  obtain ⟨t,htmem,htt⟩ := exists_lt_of_csInf_lt (ampleSlopes_nonempty L H hH) ht
  obtain ⟨c,e,he,rfl,hA⟩ := htmem
  apply ample_slope_of_cross_le L H hH c e a b he hb _ hA
  have hcross := (div_lt_div_iff₀ (by exact_mod_cast he : (0:ℝ)<e)
    (by exact_mod_cast hb : (0:ℝ)<b)).mp htt
  exact_mod_cast hcross.le

theorem threshold_lt_of_ample [IsIntegral X] [CompactSpace X]
    (L H : LineBundle X) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hA : (slopeBundle L H a b).IsAmple) : ampleThreshold L H < (a:ℝ)/b := by
  obtain ⟨n,hn,hsmall,hlt⟩ := exists_smaller_ample_slope L H a b ha hb hA
  have hmem : (((a*n-1:ℕ):ℝ)/(b*n:ℕ)) ∈ ampleSlopes L H :=
    ⟨a*n-1,b*n,Nat.mul_pos hb hn,rfl,hsmall⟩
  have hlt' : (((a*n-1:ℕ):ℝ)/(b*n:ℕ)) < (a:ℝ)/b := by
    have h := (Rat.cast_strictMono (K := ℝ)) hlt
    simpa only [Rat.cast_div, Rat.cast_natCast] using h
  exact (csInf_le (ampleSlopes_bddBelow L H) hmem).trans_lt hlt'

lemma slope_zero_isAmple_iff (L H : LineBundle X) (b : ℕ) (hb : 0 < b) :
    (slopeBundle L H 0 b).IsAmple ↔ L.IsAmple := by
  constructor
  · intro h
    apply LineBundle.IsAmple.of_pow L hb
    exact PiExponent.AmpleIso.isAmple_of_sheaf_iso _ _
      (moduleTensorRightUnit (L.pow b).sheaf) h
  · intro h
    exact PiExponent.AmpleIso.isAmple_of_sheaf_iso _ _
      (moduleTensorRightUnit (L.pow b).sheaf).symm (h.pow b hb)

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_AmpleThresholdPolynomial
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
open Set
open scoped Topology

theorem polynomial_pos_at_left_of_margin
    (P : Polynomial ℝ) (d : ℕ) (r ε b : ℝ) (hr : 0 ≤ r) (hε : 0 < ε)
    (hrb : r < b) (hpositive : 0 < P.eval b)
    (hderivative : ∀ t : ℝ, r < t →
      (t + ε) * P.derivative.eval t ≤ (d : ℝ) * P.eval t) :
    0 < P.eval r := by
  let Q : ℝ → ℝ := fun t => P.eval t / (t+ε)^d
  have hbase (x : ℝ) (hx : x ∈ Icc r b) : 0 < x+ε := by
    have := hx.1
    linarith
  have hderiv (x : ℝ) (hx : x ∈ Icc r b) :
      HasDerivAt Q
        ((P.derivative.eval x * (x+ε)^d -
          P.eval x * ((d:ℝ) * (x+ε)^(d-1))) / ((x+ε)^d)^2) x := by
    convert! (P.hasDerivAt x).div (((hasDerivAt_id x).add_const ε).pow d)
      (pow_ne_zero d (ne_of_gt (hbase x hx))) using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have hanti : AntitoneOn Q (Icc r b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc r b)
    · exact P.continuousOn.div ((continuous_id.add continuous_const).pow d).continuousOn
        (fun x hx => pow_ne_zero d (ne_of_gt (hbase x hx)))
    · intro x hx
      exact (hderiv x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : r < x := (show x ∈ Ioo r b by simpa only [interior_Icc] using hx).1
      have h := hderivative x hx'
      rw [(hderiv x (interior_subset hx)).deriv]
      apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
      cases d with
      | zero =>
        simp only [Nat.cast_zero, zero_mul, pow_zero, mul_one, mul_zero, sub_zero] at h ⊢
        exact nonpos_of_mul_nonpos_left (by simpa only [mul_comm] using h)
          (hbase x (interior_subset hx))
      | succ n =>
        have he : P.derivative.eval x * (x+ε)^(n+1) -
            P.eval x * ((n+1:ℕ):ℝ) * (x+ε)^n =
            (x+ε)^n * ((x+ε)*P.derivative.eval x - ((n+1:ℕ):ℝ)*P.eval x) := by
          rw [pow_succ]
          ring
        have hn : (x+ε)^n * ((x+ε)*P.derivative.eval x -
            ((n+1:ℕ):ℝ)*P.eval x) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (le_of_lt (pow_pos (hbase x (interior_subset hx)) n))
            (sub_nonpos.mpr h)
        simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel, ← mul_assoc, he] using hn
  have hle : Q b ≤ Q r := hanti ⟨le_rfl,hrb.le⟩ ⟨hrb.le,le_rfl⟩ hrb.le
  have hq : 0 < Q b := div_pos hpositive
    (pow_pos (by linarith) d)
  exact (div_pos_iff_of_pos_right (pow_pos (by linarith : 0 < r+ε) d)).mp (hq.trans_le hle)

theorem polynomial_pos_at_boundary_of_rational_margin
    (P : Polynomial ℝ) (d : ℕ) (r ε : ℝ) (hr : 0 ≤ r) (hε : 0 < ε)
    (hpositive : ∀ t : ℚ, r < (t:ℝ) → 0 < P.eval (t:ℝ))
    (hderivative : ∀ t : ℚ, r < (t:ℝ) →
      ((t:ℝ)+ε) * P.derivative.eval (t:ℝ) ≤ (d:ℝ) * P.eval (t:ℝ)) :
    0 < P.eval r := by
  have hreal (x : ℝ) : x ≤ r ∨ (x+ε)*P.derivative.eval x ≤ (d:ℝ)*P.eval x := by
    refine DenseRange.induction_on
      (Rat.denseRange_cast : DenseRange (fun q : ℚ => (q:ℝ))) x ?_ ?_
    · exact isClosed_le continuous_id continuous_const |>.union
        (isClosed_le ((continuous_id.add continuous_const).mul P.derivative.continuous)
          (continuous_const.mul P.continuous))
    · intro q
      by_cases hq : (q:ℝ) ≤ r
      · exact Or.inl hq
      · exact Or.inr (hderivative q (lt_of_not_ge hq))
  obtain ⟨b,hrb,hb⟩ := exists_rat_btwn (show r < r+1 by linarith)
  exact polynomial_pos_at_left_of_margin P d r ε (b:ℝ) hr hε hrb (hpositive b hrb)
    (fun x hx => (hreal x).resolve_left (not_le_of_gt hx))

theorem nonnegative_rat_nat_ratio (q : ℚ) (hq : 0 ≤ q) :
    ∃ a b : ℕ, 0 < b ∧ (q:ℝ) = (a:ℝ)/b := by
  refine ⟨q.num.natAbs,q.den,q.pos,?_⟩
  have hn : 0 ≤ q.num := Rat.num_nonneg.mpr hq
  rw [Rat.cast_def, Nat.cast_natAbs, abs_of_nonneg hn]

theorem exists_positive_rational_below_of_polynomial_pos
    (P : Polynomial ℝ) (r : ℝ) (hr : 0 < r) (hP : 0 < P.eval r) :
    ∃ q : ℚ, 0 < (q:ℝ) ∧ (q:ℝ) < r ∧ 0 < P.eval (q:ℝ) := by
  have hn : {t : ℝ | 0 < P.eval t} ∈ 𝓝 r :=
    P.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hP)
  obtain ⟨a,ha,hsub⟩ := exists_Ioc_subset_of_mem_nhds' hn hr
  obtain ⟨q,haq,hqr⟩ := exists_rat_btwn ha.2
  exact ⟨q,ha.1.trans_lt haq,hqr,hsub ⟨haq,hqr.le⟩⟩

end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_NumericalThresholdStep
attribute [-instance] _root_.OAI.PiExponent.CurveBlowupImage.imageMap_isDominant _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem isAmple_of_lower_criterion_of_euler_slope_polynomial [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (r : ℕ) (i : X ⟶ ProjectiveO1.projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (hlower : LowerClosedNumericalCriterion p H d)
    (ε : ℝ) (hε : 0 < ε)
    (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ))
    (P : Polynomial ℝ)
    (hP : ∀ a b : ℕ, 0 < b →
      (((fwdDiff (1:ℕ))^[d+1]
        (fun n => eulerCharacteristic p (d+1) ((slopeBundle L H a b).pow n).sheaf) 0 : ℤ):ℝ) =
        (b:ℝ)^(d+1) * P.eval ((a:ℝ)/b))
    (hPample : ∀ a b : ℕ, 0 < b → (slopeBundle L H a b).IsAmple →
      0 < P.eval ((a:ℝ)/b))
    (hPderivative : ∀ a b : ℕ, 0 < b → (slopeBundle L H a b).IsAmple →
      ((a:ℝ)/b+ε) * P.derivative.eval ((a:ℝ)/b) ≤
        ((d+1:ℕ):ℝ) * P.eval ((a:ℝ)/b)) : L.IsAmple := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let t := ampleThreshold L H
  have ht : 0 ≤ t := ampleThreshold_nonneg L H hH
  have hrat (q : ℚ) (hq : t < (q:ℝ)) : ∃ a b : ℕ, 0 < b ∧
      (q:ℝ) = (a:ℝ)/b ∧ (slopeBundle L H a b).IsAmple := by
    have hqnonneg : (0:ℚ) ≤ q := by exact_mod_cast (ht.trans hq.le)
    obtain ⟨a,b,hb,hab⟩ := nonnegative_rat_nat_ratio q hqnonneg
    exact ⟨a,b,hb,hab,ample_of_threshold_lt L H hH a b hb (hab ▸ hq)⟩
  have hpositive : ∀ q : ℚ, t < (q:ℝ) → 0 < P.eval (q:ℝ) := by
    intro q hq
    obtain ⟨a,b,hb,hab,hamp⟩ := hrat q hq
    rw [hab]
    exact hPample a b hb hamp
  have hderivative : ∀ q : ℚ, t < (q:ℝ) →
      ((q:ℝ)+ε) * P.derivative.eval (q:ℝ) ≤ ((d+1:ℕ):ℝ)*P.eval (q:ℝ) := by
    intro q hq
    obtain ⟨a,b,hb,hab,hamp⟩ := hrat q hq
    rw [hab]
    exact hPderivative a b hb hamp
  have hPt : 0 < P.eval t :=
    polynomial_pos_at_boundary_of_rational_margin P (d+1) t ε ht hε hpositive hderivative
  by_cases htzero : t = 0
  · have hpzero : 0 < P.eval ((0:ℝ)/1) := by simpa only [htzero,zero_div] using hPt
    exact (slope_zero_isAmple_iff L H 1 (by decide)).mp
      (ample_slope_of_polynomial_pos_of_lower_criterion_q68 p r i hi H L hH d hdim hlower ε hε
        hmargin P hP 0 1 (by decide) (by simpa using hpzero))
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm htzero)
    obtain ⟨q,hq0,hqt,hPq⟩ := exists_positive_rational_below_of_polynomial_pos P t htpos hPt
    have hqnonneg : (0:ℚ) ≤ q := by exact_mod_cast hq0.le
    obtain ⟨a,b,hb,hab⟩ := nonnegative_rat_nat_ratio q hqnonneg
    have ha : 0 < a := by
      have hnum : (0:ℝ) < a :=
        (div_pos_iff_of_pos_right (by exact_mod_cast hb : (0:ℝ)<b)).mp (hab ▸ hq0)
      exact_mod_cast hnum
    have hamp := ample_slope_of_polynomial_pos_of_lower_criterion_q68 p r i hi H L hH d hdim
      hlower ε hε hmargin P hP a b hb (hab ▸ hPq)
    have habove := threshold_lt_of_ample L H a b ha hb hamp
    have hbelow : (a:ℝ)/b < ampleThreshold L H := hab ▸ hqt
    exact False.elim (lt_asymm habove hbelow)

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_NumericalEulerSlopeInputs
attribute [-instance] _root_.OAI.PiExponent.CurveBlowupImage.imageMap_isDominant _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem isAmple_of_lower_numerical_criterion_q68_oai [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (r : ℕ) (i : X ⟶ ProjectiveO1.projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X = ((d+1:ℕ):WithBot ℕ∞))
    (hlower : LowerClosedNumericalCriterion p H d)
    (ε : ℝ) (hε : 0 < ε)
    (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ)) : L.IsAmple := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := {}
  exact isAmple_of_lower_criterion_of_euler_slope_polynomial p r i hi H L hH d
    (by simpa only [Nat.cast_add, Nat.cast_one] using hdim.le) hlower ε hε hmargin
    (eulerSlopePolynomial p (d+1) L H)
    (fun a b hb => topEuler_slopeBundle_eq_q68 p H hH L (d+1) hdim.le a b hb)
    (eulerSlopePolynomial_pos_of_ample_q68 p H L hH (d+1) hdim)
    (eulerSlopePolynomial_derivative_margin_q68 p H L hH d hdim ε hmargin)

end
end PiExponent.NumericalAmpleness

end OAI
end

theorem solution : type_of% @OAI.PiExponent.NumericalAmpleness.isAmple_of_lower_numerical_criterion_q68_oai := @OAI.PiExponent.NumericalAmpleness.isAmple_of_lower_numerical_criterion_q68_oai
