-- Prove2me | solution 1 for GlobalTheory.DegActCheck.qkExt_compat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:12:46.53887+00:00
-- url     : https://prove2.me/submissions/9527248f-c9b3-471f-af4c-814e9ec338eb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_PsiUnitOnIffInterior

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DegActCheck
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R : Type} [CommRing R] [IsDomain R]
namespace GlobalTheory.DegActCheck
theorem _root_.solution {D : Out.DegPre R} {F F' : Type} [Field F] [Algebra (FractionRing R) F]
    [Field F'] [Algebra (FractionRing R) F'] (f : F →+* F') {k : ℕ} (p : Out.QkPt D F k)
    (p' : Out.QkPt D F' k) (h : QkExt f p p') :
    f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' := by
  have h1 := Over.w p.g.b
  have h2 := Over.w p'.g.b
  rw [h.2.1] at h2
  have h3 : spMap f ≫ (Out.jFK (R := R) F ≫ Out.jK R) = Out.jFK (R := R) F' ≫ Out.jK R := by
    refine Eq.trans ?_ h2
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    exact congrArg (spMap f ≫ ·) h1.symm
  have h4 : CommRingCat.ofHom ((f.comp (algebraMap (FractionRing R) F)).comp (algebraMap R (FractionRing R))) =
      CommRingCat.ofHom ((algebraMap (FractionRing R) F').comp (algebraMap R (FractionRing R))) := by
    apply Spec.map_injective
    simp only [CommRingCat.ofHom_comp, Spec.map_comp]
    exact (Category.assoc _ _ _).trans h3
  exact IsLocalization.ringHom_ext (nonZeroDivisors R) (congrArg CommRingCat.Hom.hom h4)
end GlobalTheory.DegActCheck
