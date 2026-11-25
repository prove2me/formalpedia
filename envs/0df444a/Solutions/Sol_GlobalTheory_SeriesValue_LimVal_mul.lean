-- Prove2me | solution 1 for GlobalTheory.SeriesValue.LimVal.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:17:58.075376+00:00
-- url     : https://prove2.me/submissions/b423d781-da6e-4a75-a0ae-de3248a081e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsAlgHomValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsLieCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueJet
import Theorems.Thm_GlobalTheory_SeriesValue_HasVal_mul
import Theorems.Thm_GlobalTheory_FamGerm_Pt1_Transl_mul
import Theorems.Thm_GlobalTheory_HodgeTateStep_HasDlog_mul


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
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SeriesValue
open ReciprocityTheory.ChartRestriction.G.Chart GlobalTheory.JetSer GlobalTheory.ChartBaseChange GlobalTheory.TorsionCharacter ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev addOf)
variable {V : Type} [CommRing V] {G : Over (Spec (CommRingCat.of V))} [GrpObj G] {d : ℕ}
variable {O : Type} [CommRing O] [Algebra V O]
variable {x : Fam G (Fin d)} {u : PS O 1 d} {A : Type} [CommRing A] [Algebra O A]
variable {p : O}
namespace GlobalTheory.SeriesValue
namespace LimVal
theorem _root_.solution (hx : IsUnivChart G d x) {L : Fin d → PS V 2 d} (hL : IsLawOf x L)
    (hu : ev (n := 2) ![fun i => MvPowerSeries.map (algebraMap V O) (L i)] u =
      ev (n := 2) ![ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt O d 0] u * ev (n := 2) ![ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt O d 1] u)
    {g g' : specV (algebraMap V O) A ⟶ G} {k k' : A}
    (h : LimVal x u p g.left k) (h' : LimVal x u p g'.left k') : LimVal x u p (g * g').left (k * k') := by
  intro R _ _ θ hp
  have := HasVal.mul hx hL hu (g := res V θ ≫ g) (g' := res V θ ≫ g') (h R θ hp) (h' R θ hp)
  rw [← MonObj.comp_mul, ← map_mul] at this
  exact this
end LimVal
end GlobalTheory.SeriesValue
