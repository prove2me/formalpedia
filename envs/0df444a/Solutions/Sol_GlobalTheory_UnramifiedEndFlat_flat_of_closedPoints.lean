-- Prove2me | solution 1 for GlobalTheory.UnramifiedEndFlat.flat_of_closedPoints
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:29:17.020454+00:00
-- url     : https://prove2.me/submissions/9ce662ce-3de0-46da-a92c-034de3013200

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFormallyUnramifiedGrpEnd
import Theorems.Thm_GlobalTheory_UnramifiedEndFlat_flat_stalkMap_of_specializes

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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.UnramifiedEndFlat
open IsLocalRing
namespace GlobalTheory.UnramifiedEndFlat
theorem _root_.solution {X Y : Scheme.{0}} [JacobsonSpace X] (f : X ⟶ Y)
    (hf : ∀ x : X, IsClosed {x} → (f.stalkMap x).hom.Flat) : Flat f := by
  refine Flat.of_stalkMap f fun x => ?_
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints (Z := closure {x})
    ⟨x, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  exact flat_stalkMap_of_specializes f (specializes_iff_mem_closure.mpr hy) (hf y hyc)
end GlobalTheory.UnramifiedEndFlat
