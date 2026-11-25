-- Prove2me | solution 1 for GlobalTheory.SeriesValue.limVal_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:11:00.101079+00:00
-- url     : https://prove2.me/submissions/1914a82b-bd98-4a63-befd-cd6461252119

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsAlgHomValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsLieCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueJet
import Theorems.Thm_GlobalTheory_SeriesValue_hasVal_one

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
theorem _root_.solution (hx : IsUnivChart G d x) (hu : MvPowerSeries.constantCoeff u = 1) :
    LimVal x u p (1 : specV (algebraMap V O) A ⟶ G).left (1 : A) := by
  intro R _ _ θ _
  have e : (res V θ ≫ (1 : specV (algebraMap V O) A ⟶ G)).left = (1 : specV (algebraMap V O) R ⟶ G).left := by
    rw [MonObj.comp_one]
  rw [map_one]
  have h := hasVal_one (A := R) hx hu
  rw [← e] at h
  exact h
end GlobalTheory.SeriesValue
