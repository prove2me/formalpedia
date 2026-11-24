-- Prove2me | solution 1 for GlobalTheory.AbLaw.finSec_eq_zero_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:53:04.114846+00:00
-- url     : https://prove2.me/submissions/0a0463e6-0ef5-4acd-94e9-e16f87c83deb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AbelianVarietyLineBundleSectionsFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw
namespace GlobalTheory.AbLaw
theorem _root_.solution {X : Scheme.{0}} {I : Type} (V : I → X.Opens) (hV : ⨆ i, V i = ⊤)
    {U : X.Opens} (x : Γ(X, U)) (hx : ∀ i, rs X (inf_le_left : U ⊓ V i ≤ U) x = 0) : x = 0 := by
  refine X.sheaf.eq_of_locally_eq' (fun i => U ⊓ V i) U (fun i => homOfLE inf_le_left) ?_ x 0 ?_
  · rw [← inf_iSup_eq, hV, inf_top_eq]
  · intro i
    exact (hx i).trans (map_zero (rs X (inf_le_left : U ⊓ V i ≤ U))).symm
end GlobalTheory.AbLaw
