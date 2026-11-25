-- Prove2me | solution 1 for GlobalTheory.T.isIso_restrict_or_exists_smooth_blowup_centre_over
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:24:32.234842+00:00
-- url     : https://prove2.me/submissions/90a24bf8-d9ac-4b44-a47e-83ff27b0ddd4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIsoNearOrCentreMeets
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIsoNearOrCentreMeetsStatement
import Theorems.Thm_GlobalTheory_isIso_near_or_centre_meets


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {S Y : Scheme.{0}} (f : Y ⟶ S) (B : Set Y) (y : Y) {Y' : Scheme.{0}} (s : Y' ⟶ Y), GlobalTheory.IsSmoothBlowupSeq f B s → (∃ U : Y.Opens, y ∈ U ∧ IsIso (s ∣_ U)) ∨ ∃ (Y₁ : Scheme.{0}) (s₁ : Y₁ ⟶ Y) (J : Y₁.IdealSheafData) (U : Y.Opens) (y₁ : Y₁), GlobalTheory.IsSmoothBlowupSeq f B s₁ ∧ Smooth (J.subschemeι ≫ s₁ ≫ f) ∧ (J.support : Set Y₁) ⊆ s₁ ⁻¹' B ∧ y ∈ U ∧ IsIso (s₁ ∣_ U) ∧ y₁ ∈ J.support ∧ s₁ y₁ = y := by
  first | exact @GlobalTheory.isIso_near_or_centre_meets | exact GlobalTheory.isIso_near_or_centre_meets | (intros; apply GlobalTheory.isIso_near_or_centre_meets <;> assumption)
end _root_.GlobalTheory.T
