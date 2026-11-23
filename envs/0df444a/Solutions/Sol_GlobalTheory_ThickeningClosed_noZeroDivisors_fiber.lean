-- Prove2me | solution 1 for GlobalTheory.ThickeningClosed.noZeroDivisors_fiber
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:49:56.806366+00:00
-- url     : https://prove2.me/submissions/6af91323-566b-4bbd-ae6a-016ef78f76cb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoOfIsClosedImmersionOfThickenings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.ThickeningClosed
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ThickeningClosed
namespace _root_.GlobalTheory.ThickeningClosed
theorem _root_.solution {R C : Type} [CommRing R] [CommRing C]
    [Algebra R C] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (j : Spec (CommRingCat.of C) ⟶ X) [IsOpenImmersion j]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap R C)) = j ≫ f)
    (p : PrimeSpectrum R) [IsIntegral (f.fiber p)] : NoZeroDivisors (p.asIdeal.Fiber C) := by
  rcases subsingleton_or_nontrivial (p.asIdeal.Fiber C) with hs | hn
  · exact ⟨fun {a b} _ ↦ Or.inl (Subsingleton.elim a 0)⟩
  let e := Spec.fiberToSpecResidueFieldIso R C p
  let s := (Spec (CommRingCat.of R)).fromSpecResidueField p
  let u₁ : Spec (CommRingCat.of (p.asIdeal.Fiber C)) ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R C))) s := (Arrow.leftFunc.mapIso e).inv
  let u₂ : pullback (Spec.map (CommRingCat.ofHom (algebraMap R C))) s ⟶ pullback (j ≫ f) s :=
    (pullback.congrHom hj rfl).hom
  let u₃ : pullback (j ≫ f) s ⟶ pullback j (pullback.fst f s) :=
    (pullbackRightPullbackFstIso f s j).inv
  let u₄ : pullback j (pullback.fst f s) ⟶ f.fiber p := pullback.snd j (pullback.fst f s)
  haveI : IsOpenImmersion u₁ := show IsOpenImmersion (Arrow.leftFunc.mapIso e).inv from inferInstance
  haveI : IsOpenImmersion u₂ := show IsOpenImmersion (pullback.congrHom hj rfl).hom from inferInstance
  haveI : IsOpenImmersion u₃ := show IsOpenImmersion (pullbackRightPullbackFstIso f s j).inv from inferInstance
  haveI : IsOpenImmersion u₄ := show IsOpenImmersion (pullback.snd j (pullback.fst f s)) from inferInstance
  haveI : AlgebraicGeometry.IsIntegral (Spec (CommRingCat.of (p.asIdeal.Fiber C))) :=
    isIntegral_of_isOpenImmersion (u₁ ≫ u₂ ≫ u₃ ≫ u₄)
  haveI : IsDomain (p.asIdeal.Fiber C) :=
    (affine_isIntegral_iff (CommRingCat.of (p.asIdeal.Fiber C))).mp inferInstance
  infer_instance
end _root_.GlobalTheory.ThickeningClosed
end GlobalTheory.ThickeningClosed
