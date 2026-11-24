-- Prove2me | solution 1 for GlobalTheory.SS.Translates.Ext.div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:58:38.990409+00:00
-- url     : https://prove2.me/submissions/c39fe33f-1b48-4358-ad62-e6af077eca5c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsIntegralOfIsAbelianSchemeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TranslationBySection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsOpenImmersionOfSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_StrictModelTranslatesTwistCompatible
import Theorems.Thm_GlobalTheory_SS_Translates_isPullback_j
import Theorems.Thm_GlobalTheory_SS_CompatCrit_isPullback_j
import Theorems.Thm_GlobalTheory_SS_Model_j_hom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Translates
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' A'' : Over (Sp K)}
namespace GlobalTheory.SS.Translates
namespace Ext
theorem _root_.solution {M : Model R A} {N : Model R A'} {P : Model R A''} {u : A ⟶ A'} {f' : A' ≅ A''}
    {X X' : Scheme.{0}} {i : X ⟶ M.Y.left} {g : X ⟶ P.Y.left} {i' : X' ⟶ N.Y.left} {g' : X' ⟶ P.Y.left}
    (h : Ext M P (u ≫ f'.hom) i g) (h' : Ext N P f'.hom i' g') :
    Ext M N u (pullback.fst g g' ≫ i) (pullback.snd g g' ≫ i') := by
  refine ⟨by rw [Category.assoc, ← h'.1, ← pullback.condition_assoc, h.1, Category.assoc], fun T t a e => ?_⟩
  have h1 := h.2 T (t ≫ pullback.fst g g') a (by rw [Category.assoc, e])
  have h0 : (t ≫ pullback.snd g g' ≫ i') ≫ N.Y.hom = (a ≫ A.hom) ≫ spMap (algebraMap R K) := by
    simp only [Category.assoc]
    rw [← h'.1, ← pullback.condition_assoc, h.1, ← M.j_hom, ← reassoc_of% e]
  let b := (isPullback_j N).lift _ _ h0
  have b1 : b ≫ N.j = t ≫ pullback.snd g g' ≫ i' := IsPullback.lift_fst _ _ _ _
  have b2 : b ≫ A'.hom = a ≫ A.hom := IsPullback.lift_snd _ _ _ _
  have h2 := h'.2 T (t ≫ pullback.snd g g') b (by rw [b1, Category.assoc])
  have h3 : b ≫ f'.hom.left = (a ≫ u.left) ≫ f'.hom.left := by
    apply (isPullback_j P).hom_ext
    · rw [Category.assoc, ← h2, Category.assoc, ← pullback.condition, ← Category.assoc, h1]; simp
    · simp [b2]
  have : IsIso f'.hom.left := inferInstanceAs (IsIso ((Over.forget _).map f'.hom))
  rw [← b1, (cancel_mono _).1 h3, Category.assoc]
end Ext
end GlobalTheory.SS.Translates
