-- Prove2me | solution 1 for GlobalTheory.TorusLocal.pt_ext_of_quotients
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:46.706155+00:00
-- url     : https://prove2.me/submissions/40df2aa7-8fa3-4e59-9624-805595d3ee8f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorusLocal
open TorusNil
namespace GlobalTheory.TorusLocal
theorem _root_.solution {A C : Type} [CommRing A] [CommRing C] [Algebra A C] {N : Type}
    (I : N → Ideal C) (hI : ∀ x, (∀ i, x ∈ I i) → x = 0)
    {B : Over (Spec (CommRingCat.of A))} [IsSeparated B.hom] {a b : sp A C ⟶ B}
    (h : ∀ i, spm (Ideal.Quotient.mkₐ A (I i)) ≫ a = spm (Ideal.Quotient.mkₐ A (I i)) ≫ b) :
    a = b := by
  have : IsAffine (sp A C).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of C)))
  have hinj : Function.Injective (equalizer.ι a b).left.appTop := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hb := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of C)).hom
    apply hb.1
    refine Eq.trans (hI _ fun i => ?_) (map_zero _).symm
    have h1 : (spm (Ideal.Quotient.mkₐ A (I i))).left.appTop x = 0 := by
      rw [← equalizer.lift_ι _ (h i), Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        hx, map_zero]
    have h2 := ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I i)))) x
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    refine h2.symm.trans ?_
    refine (congrArg (Scheme.ΓSpecIso (CommRingCat.of (C ⧸ I i))).hom h1).trans (map_zero _)
  have := IsClosedImmersion.isIso_of_injective_of_isAffine hinj
  apply Over.OverMorphism.ext
  rw [← cancel_epi (equalizer.ι a b).left, ← Over.comp_left, equalizer.condition, Over.comp_left]
end GlobalTheory.TorusLocal
