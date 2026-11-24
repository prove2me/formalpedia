-- Prove2me | solution 1 for GlobalTheory.LinDescent.section_eq_one_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:45:02.503197+00:00
-- url     : https://prove2.me/submissions/13a21b96-4cc4-4511-9421-eb13a25bc31c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfIsReduced
import Theorems.Thm_GlobalTheory_FinEt_exists_algClosed_point


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LinDescent
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace GlobalTheory.LinDescent
theorem _root_.solution {S : Scheme.{0}} [IsReduced S] {B : Over S} [GrpObj B]
    (y : 𝟙_ (Over S) ⟶ B)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), toUnit (Over.mk t) ≫ y = 1) :
    y = 1 := by
  have hη : η[B].left ≫ B.hom = 𝟙 S := Over.w η[B]
  have hy : y.left ≫ B.hom = 𝟙 S := Over.w y
  have : IsImmersion (η[B].left ≫ B.hom) := hη ▸ (inferInstance : IsImmersion (𝟙 S))
  have : IsImmersion η[B].left := IsImmersion.of_comp _ B.hom
  let p : pullback y.left η[B].left ⟶ S := pullback.fst y.left η[B].left
  have : IsImmersion p := inferInstanceAs (IsImmersion (pullback.fst y.left η[B].left))
  have : Surjective p := ⟨fun s => by
    obtain ⟨k, _, _, t, ht⟩ := FinEt.exists_algClosed_point S s
    have e : t ≫ y.left = t ≫ η[B].left := congrArg (·.left) ((h k t).trans Hom.one_def)
    obtain ⟨z, hz⟩ : s ∈ Set.range t := ht.ge rfl
    refine ⟨pullback.lift t t e z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hz]
    exact congrArg (fun q : Spec (CommRingCat.of k) ⟶ S => q z) (pullback.lift_fst _ _ _)⟩
  have : IsClosedImmersion p := .of_isPreimmersion _ (by
    rw [p.surjective.range_eq]; exact isClosed_univ)
  have : IsIso p := isIso_of_isClosedImmersion_of_surjective p
  have e : p ≫ y.left = pullback.snd y.left η[B].left ≫ η[B].left := pullback.condition
  have e' : p = pullback.snd y.left η[B].left := by
    have := e =≫ B.hom
    rw [Category.assoc, Category.assoc, hy, hη] at this
    exact (Category.comp_id _).symm.trans (this.trans (Category.comp_id _))
  rw [← e', cancel_epi] at e
  rw [Hom.one_def, toUnit_unit, Category.id_comp]
  exact Over.OverMorphism.ext e
end GlobalTheory.LinDescent
