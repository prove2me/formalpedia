-- Prove2me | solution 1 for GlobalTheory.T.exists_nonempty_isIso_restrict_of_generic_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:22:37.834855+00:00
-- url     : https://prove2.me/submissions/fd51dfec-1667-4fc7-a61f-63ea8207c3cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIsoRestrictOfClosedImmersionNearGeneric
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIsoRestrictOfClosedImmersionNearGenericStatement
import Theorems.Thm_GlobalTheory_isIso_restrict_of_closedImmersion_near_generic


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
theorem _root_.solution : ∀ {W W' Y Y₁ : Scheme.{0}} [IsIntegral W] [IsIntegral W'] (i : W ⟶ Y) [IsClosedImmersion i] (h : W' ⟶ W) (c : W' ⟶ Y₁) [IsClosedImmersion c] (s₁ : Y₁ ⟶ Y) (U : Y.Opens), IsIso (s₁ ∣_ U) → h ≫ i = c ≫ s₁ → i (genericPoint W) ∈ U → (∃ w', h w' = genericPoint W) → ∃ U' : W.Opens, (U' : Set W).Nonempty ∧ IsIso (h ∣_ U') := by
  first | exact @GlobalTheory.isIso_restrict_of_closedImmersion_near_generic | exact GlobalTheory.isIso_restrict_of_closedImmersion_near_generic | (intros; apply GlobalTheory.isIso_restrict_of_closedImmersion_near_generic <;> assumption)
end _root_.GlobalTheory.T
