-- Prove2me | solution 1 for GlobalTheory.TorsionCharacter.isMapOf_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:48:23.251996+00:00
-- url     : https://prove2.me/submissions/7f2b5404-6476-4c3c-a26e-1074f9216aa8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_ColValMonomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsCharactersDlogMinorsGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowEqScaleAndExistsUniqueTorsion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvalOneStandardPointSelf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LieEig
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsLieCoordinates
import Theorems.Thm_GlobalTheory_ChartBaseChange_const_map
import Theorems.Thm_GlobalTheory_ChartBaseChange_exists_move
import Theorems.Thm_GlobalTheory_ChartBaseChange_germEval_oneStandardPoint_self
import Theorems.Thm_GlobalTheory_ChartBaseChange_rep_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_single_point_zero_constant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorsionCharacter
open ReciprocityTheory.ChartRestriction.G.Chart GlobalTheory.JetSer GlobalTheory.ChartBaseChange ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (IsGrpPullback isGrpPullback_pullback)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (Pt comp1)
open ReciprocityTheory.ChartRestriction.G.TB (dLin)
namespace GlobalTheory.TorsionCharacter
theorem _root_.solution {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G']
    {π : G'.left ⟶ G.left} (hπ : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R R'))) π)
    (hJ : JetAlgSt) {d : ℕ} {x : JetSer.Fam G (Fin d)} {x' : JetSer.Fam G' (Fin d)}
    (hx' : ∀ m, push hπ (x' m) = Chart.spMap (jetCoeff R R' (Fin d) m) ≫ x m)
    (f : G ⟶ G) (f' : G' ⟶ G') (α : Pt R 1 d) (hf : f'.left ≫ π = π ≫ f.left) (hα : IsMapOf x x f α) :
    IsMapOf x' x' f' (fun i => MvPowerSeries.map (algebraMap R R') (α i)) := by
  refine ⟨fun i => const_map (hα.1 i), fun n a y hy => ?_⟩
  obtain ⟨Θ, t, hΘ, ht, e⟩ := exists_move hπ hJ hx' ![a] ![y] (fun i => by fin_cases i; exact hy)
  have H := hα.2 1 _ _ (ht 0)
  have hFe : comp1 α (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R (n := 1) d 0) = α := funext fun i => germEval_oneStandardPoint_self _
  rw [hFe] at H
  refine (rep_iff hπ hJ hx' (single_point_zero_constant hy.1) hΘ H _).2 fun m => ?_
  rw [← Category.assoc, ← e 0 m]
  apply Over.OverMorphism.ext
  show ((y m).left ≫ f'.left) ≫ π = ((y m).left ≫ π) ≫ f.left
  rw [Category.assoc, Category.assoc, hf]
end GlobalTheory.TorsionCharacter
