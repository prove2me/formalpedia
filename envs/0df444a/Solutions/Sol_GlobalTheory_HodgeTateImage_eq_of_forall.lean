-- Prove2me | solution 1 for GlobalTheory.HodgeTateImage.eq_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:01:38.611914+00:00
-- url     : https://prove2.me/submissions/e26471ea-cff4-4da1-95ec-c93efdc94ee5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitOfBijectiveMulNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowEqScaleAndExistsUniqueTorsion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueIsAl
import Theorems.Thm_GlobalTheory_HodgeTateImage_smod_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HodgeTateImage
open GlobalTheory.TangentPow GlobalTheory.GmPoints
variable {O : Type} [CommRing O] {G : Over (Spec (CommRingCat.of O))} [GrpObj G] {p : ℕ}
variable (χ : Tv G p)
namespace GlobalTheory.HodgeTateImage
theorem _root_.solution [IsHausdorff (Ideal.span {(p : O)}) O] {a b : O}
    (h : ∀ n, algebraMap O (O ⧸ Ideal.span {(p : O) ^ n}) a =
        algebraMap O (O ⧸ Ideal.span {(p : O) ^ n}) b) : a = b := by
  refine sub_eq_zero.mp (IsHausdorff.haus' (I := Ideal.span {(p : O)}) (a - b) fun n => ?_)
  rw [SModEq.zero, ← SModEq.sub_mem, smod_iff]
  exact h n
end GlobalTheory.HodgeTateImage
