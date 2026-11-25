-- Prove2me | solution 1 for GlobalTheory.AbLaw.Cube.cube_of_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:56:45.546658+00:00
-- url     : https://prove2.me/submissions/c6d9f8f4-87c2-40c9-aed1-a82012758097

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubicalOfNormalised
import Theorems.Thm_GlobalTheory_AbLaw_Cube_exists_normalised
import Theorems.Thm_GlobalTheory_AbLaw_Cube_cubical_unique
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.Cube
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
variable [IsCommMonObj A] {L : LB A.left}
namespace GlobalTheory.AbLaw.Cube
theorem _root_.solution : GlobalFnsSt → (∀ (S : Scheme.{0}) (P : PolAV S) (M : LB P.A.left), M.IsLB →
    ∃ t : LB.Gen (Theta P.A M), t.IsGen) → CubeSt := by
  intro hG hT S _ P M _
  have := P.isAb.comm
  obtain ⟨t, ht⟩ := hT S P M.L M.isLB
  obtain ⟨t', ht', hn⟩ := exists_normalised M.isLB t ht
  exact ⟨⟨cubicalOfNormalised hG P.isAb M t' ht' hn⟩, cubical_unique hG P.isAb⟩
end GlobalTheory.AbLaw.Cube
