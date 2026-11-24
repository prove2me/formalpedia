-- Prove2me | solution 1 for GlobalTheory.IsSmoothBlowupSeq.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:50:12.931275+00:00
-- url     : https://prove2.me/submissions/1128e27d-d6c5-46b6-9d43-38956e23e05a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
namespace GlobalTheory
namespace _root_.GlobalTheory.IsSmoothBlowupSeq
theorem _root_.solution {S Y Y' : Scheme.{0}} {f : Y ⟶ S} {B B' : Set Y} {s : Y' ⟶ Y}
    (h : _root_.GlobalTheory.IsSmoothBlowupSeq f B s) (hB : B ⊆ B') : _root_.GlobalTheory.IsSmoothBlowupSeq f B' s := by
  induction h with
  | id => exact .id
  | step J π _ hsm hsupp hbl ih =>
    exact .step J π ih hsm (hsupp.trans (Set.preimage_mono hB)) hbl
end _root_.GlobalTheory.IsSmoothBlowupSeq
end GlobalTheory
