-- Prove2me | solution 1 for GlobalTheory.isFinite_graphClosure_fst_of_isFinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:02:30.542823+00:00
-- url     : https://prove2.me/submissions/66b1e94a-5750-4129-a608-f957c6a1c5f4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueLiftOfDensePart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescOfIsFiniteOfDensePart

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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {S X X' Y : Scheme.{0}} (π : X ⟶ X') (s' : X' ⟶ S)
    (p : Y ⟶ S) (f : X ⟶ Y) (h : π ≫ s' = f ≫ p) [IsFinite π] [IsSeparated p]
    [LocallyOfFiniteType p] : IsFinite (graphClosure.fst s' p π f h) := by
  have e := graphClosure.incl_fst s' p π f h
  have : IsFinite (graphClosure.incl s' p π f h ≫ graphClosure.fst s' p π f h) := by
    rw [e]; infer_instance
  have : IsFinite (graphClosure.incl s' p π f h) :=
    IsFinite.of_comp _ (graphClosure.fst s' p π f h)
  have : Surjective (graphClosure.incl s' p π f h) :=
    surjective_of_isDominant_of_isClosed_range _
      (graphClosure.incl s' p π f h).isClosedMap.isClosed_range
  have : UniversallyClosed (graphClosure.fst s' p π f h) :=
    .of_comp_surjective (graphClosure.incl s' p π f h) _
  have : IsProper (graphClosure.fst s' p π f h) := {}
  have : LocallyQuasiFinite (graphClosure.fst s' p π f h) := by
    refine .of_finite_preimage_singleton _ fun s ↦ ?_
    refine (((graphClosure.incl s' p π f h ≫ graphClosure.fst s' p π f h).finite_preimage_singleton
      s).image (graphClosure.incl s' p π f h)).subset fun x hx ↦ ?_
    obtain ⟨y, rfl⟩ := (graphClosure.incl s' p π f h).surjective x
    exact ⟨y, by simpa only [Set.mem_preimage, Scheme.Hom.comp_apply] using hx, rfl⟩
  exact .of_isProper_of_locallyQuasiFinite _
end GlobalTheory
