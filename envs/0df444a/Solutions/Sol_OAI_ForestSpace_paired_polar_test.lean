-- Prove2me | solution 1 for OAI.ForestSpace.paired_polar_test
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:49:44.087227+00:00
-- url     : https://prove2.me/submissions/fb9bfe69-6ce3-4fa5-ba09-5250c2ad2fca

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ForestSpace/Polar.lean:L76-L98
-- (upload_full_project.md Phase 4): solution for node OAI.ForestSpace.paired_polar_test. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired
import Definitions.Def_OAI_Analysis_ForestSpace_Norm
import Definitions.Def_OAI_Analysis_ForestSpace_Completion
import Definitions.Def_OAI_Analysis_ForestSpace_Polar
import Theorems.Thm_OAI_ForestSpace_norm_rawRestriction

-- ---- from OAI.Analysis.ForestSpace.Polar ----
namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section PolarTests
variable {V : Type} [PartialOrder V]

/-- The cancellation of the same gate correction in the two dual evaluations. -/
 theorem paired_polar_test (H : Set V) {x y : FullDual V}
    (hx : Annihilates x Hᶜ) (hy : Annihilates y H)
    {f k c : TestVector V} (hf : SupportedOn f H) (hk : SupportedOn k Hᶜ)
    (hc : SupportedOn c Hᶜ) (s d : ℝ)
    (hp : ‖f + s • (c + k)‖ ≤ d) (hm : ‖f + s • (c - k)‖ ≤ d) :
    x (f : J V) + s * y (k : J V) ≤ (‖x+y‖ + ‖x-y‖) / 2 * d := by
  have hb (z : FullDual V) (u : TestVector V) (hu : ‖u‖ ≤ d) :
      rawRestriction z u ≤ ‖z‖ * d := by
    calc
      rawRestriction z u ≤ |rawRestriction z u| := le_abs_self _
      _ ≤ ‖z‖ * ‖u‖ := by
        simpa only [Real.norm_eq_abs, norm_rawRestriction] using (rawRestriction z).le_opNorm u
      _ ≤ ‖z‖ * d := mul_le_mul_of_nonneg_left hu (norm_nonneg _)
  have hp' := hb (x+y) (f+s•(c+k)) hp
  have hm' := hb (x-y) (f+s•(c-k)) hm
  have he : rawRestriction (x+y) (f+s•(c+k)) + rawRestriction (x-y) (f+s•(c-k)) =
      2 * (x (f : J V) + s * y (k : J V)) := by
    simp only [map_add, map_sub, map_smul, rawRestriction_apply,
      _root_.add_apply, _root_.sub_apply, smul_eq_mul,
      hx k hk, hx c hc, hy f hf]
    ring
  linarith

end PolarTests

section CoordinateCompletion
variable {W : Type} [PartialOrder W]
variable {V : Type} [PartialOrder V]

end CoordinateCompletion

end

end ForestSpace

end OAI

-- ---- platform node ----
open OAI OAI.ForestSpace
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.ForestSpace.paired_polar_test := @_root_.OAI.ForestSpace.paired_polar_test
