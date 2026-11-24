-- Prove2me | solution 1 for GlobalTheory.LocLift.eq_one_of_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:46:53.268854+00:00
-- url     : https://prove2.me/submissions/1e39d005-9fd3-4e37-af62-5fb2da66c33f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearEquivLift
import Theorems.Thm_GlobalTheory_LocLift_one_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Filter Topology
open GlobalTheory GlobalTheory.LocLift
noncomputable section
variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {g m : ℕ}
namespace GlobalTheory.LocLift
theorem _root_.solution [IsSeparated G.hom] {y : Sp ℂ ⟶ X} (x : Over.mk y ⟶ G)
    (hx : x.left (default : PrimeSpectrum ℂ) ∈ Set.range η[G].left) : x = 1 := by
  have hw : η[G].left ≫ G.hom = 𝟙 _ := Over.w η[G]
  haveI : IsClosedImmersion (η[G].left ≫ G.hom) := hw ▸ inferInstance
  haveI : IsClosedImmersion η[G].left := IsClosedImmersion.of_comp _ G.hom
  haveI : IsReduced (Over.mk y).left := inferInstanceAs (IsReduced (Sp ℂ))
  haveI : Surjective (pullback.fst x.left η[G].left) := ⟨fun p => by
    have : p = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    subst this
    change _ ∈ Set.range _
    rw [Scheme.Pullback.range_fst]
    exact hx⟩
  haveI := isIso_of_isClosedImmersion_of_surjective (pullback.fst x.left η[G].left)
  have e : x.left = (inv (pullback.fst x.left η[G].left) ≫ pullback.snd _ _) ≫ η[G].left := by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
  have e' : inv (pullback.fst x.left η[G].left) ≫ pullback.snd _ _ = y := by
    have := Over.w x
    rw [e, Category.assoc, hw] at this
    exact (Category.comp_id _).symm.trans this
  rw [e'] at e
  exact Over.OverMorphism.ext (e.trans (one_left y).symm)
end GlobalTheory.LocLift
