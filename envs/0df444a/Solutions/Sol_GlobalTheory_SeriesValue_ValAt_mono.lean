-- Prove2me | solution 1 for GlobalTheory.SeriesValue.ValAt.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:36:53.312868+00:00
-- url     : https://prove2.me/submissions/83753386-88c6-43f3-a302-eb317a68fc59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsAlgHomValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsLieCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueJet
import Theorems.Thm_GlobalTheory_SeriesValue_ValAt_succ

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
namespace GlobalTheory.SeriesValue
namespace ValAt
theorem _root_.solution (hx : IsUnivChart G d x) {m n : ℕ} (hmn : m ≤ n) {g : Spec (CommRingCat.of A) ⟶ G.left}
    {z : Fin d → A} {k : A} (h : ValAt x u m g z k) : ValAt x u n g z k := by
  induction n, hmn using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact ih.succ hx
end ValAt
end GlobalTheory.SeriesValue
