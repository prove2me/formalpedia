-- Prove2me | solution 1 for GlobalTheory.T.exists_lift_of_isReduced_of_mem_ker_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:16:10.542463+00:00
-- url     : https://prove2.me/submissions/0c34a51d-2372-44ec-b8ad-86a045dda03e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LiftOfReducedOfSupport
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LiftOfReducedOfSupportStatement
import Theorems.Thm_GlobalTheory_lift_of_reduced_of_support


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
theorem _root_.solution : ∀ {X Y T : Scheme.{0}} (i : X ⟶ Y) [IsClosedImmersion i] [IsReduced T] (g : T ⟶ Y), (∀ t, g t ∈ i.ker.support) → ∃ h : T ⟶ X, h ≫ i = g := by
  first | exact @GlobalTheory.lift_of_reduced_of_support | exact GlobalTheory.lift_of_reduced_of_support | (intros; apply GlobalTheory.lift_of_reduced_of_support <;> assumption)
end _root_.GlobalTheory.T
