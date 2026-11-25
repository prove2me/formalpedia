-- Prove2me | solution 1 for GlobalTheory.HodgeTateImage.existsUnique_isAl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:57:03.121088+00:00
-- url     : https://prove2.me/submissions/a0911d99-7498-4da6-880e-ebec3bf75467

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitOfBijectiveMulNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowEqScaleAndExistsUniqueTorsion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueIsAl
import Theorems.Thm_GlobalTheory_HodgeTateImage_unitAt_mul
import Theorems.Thm_GlobalTheory_HodgeTateImage_unitAt_scale
import Theorems.Thm_GlobalTheory_HodgeTateImage_pow_quot
import Theorems.Thm_GlobalTheory_HodgeTateImage_eq_of_forall
import Theorems.Thm_GlobalTheory_HodgeTateImage_exists_limit
import Theorems.Thm_GlobalTheory_HodgeTateImage_isAl_iff

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
theorem _root_.solution [IsAdicComplete (Ideal.span {(p : O)}) O] :
    ∃! f : LieG G → O, f ∈ omega G ∧ IsAl χ f := by
  choose f hf using exists_limit χ
  refine ⟨f, ⟨⟨fun x y h => eq_of_forall (p := p) fun n => ?_,
    fun a x h => eq_of_forall (p := p) fun n => ?_⟩, (isAl_iff χ f).2 hf⟩, fun g hg => ?_⟩
  · rw [map_add, hf x n _ (pow_quot n), hf y n _ (pow_quot n)]
    exact (hf _ n _ (pow_quot n)).trans (unitAt_mul χ _ x y _ rfl)
  · rw [map_mul, hf x n _ (pow_quot n)]
    exact (hf _ n _ (pow_quot n)).trans (unitAt_scale χ _ a x _ rfl)
  · funext x
    refine eq_of_forall (p := p) fun n => ?_
    rw [hf _ n _ (pow_quot n), (isAl_iff χ g).1 hg.2 x n _ (pow_quot n)]
end GlobalTheory.HodgeTateImage
