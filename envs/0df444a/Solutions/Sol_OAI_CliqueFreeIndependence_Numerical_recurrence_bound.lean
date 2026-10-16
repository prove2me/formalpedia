-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.Numerical.recurrence_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:21:06.646317+00:00
-- url     : https://prove2.me/submissions/3d50e8b1-d506-4188-9f3c-377ea019b7ba

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/Numerical.lean:L180-L196
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.Numerical.recurrence_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical

-- ---- from OAI.Combinatorics.CliqueFree.Numerical ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence

universe u v

namespace Numerical

end Numerical

end CliqueFreeIndependence

open Filter
namespace CliqueFreeIndependence.Numerical

lemma recurrence_bound {B q ε t m s : ℝ}
    (hB : 1 ≤ B) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (_hε0 : 0 ≤ ε) (hε : ε ≤ q/4) (_ht : 0 ≤ t) (hm : 0 ≤ m)
    (hs : s ≤ q/2)
    (hstep : (1-ε)*t - s*m ≤ B*(2-2*q)*m) :
    t ≤ B*(2-q)*m := by
  have hB0 : 0 ≤ B := by linarith
  have hb : 0 ≤ B*(2-q) := mul_nonneg hB0 (by linarith)
  have hb2 : B*(2-q) ≤ 2*B := by nlinarith
  have hnum : B*(2-2*q)+s ≤ (1-ε)*(B*(2-q)) := by
    have he : ε * (B*(2-q)) ≤ (q/4)*(2*B) :=
      mul_le_mul hε hb2 hb (by positivity)
    nlinarith [mul_nonneg (sub_nonneg.2 hB) hq0]
  have hpos : 0 < 1-ε := by linarith
  apply (mul_le_mul_iff_right₀ hpos).1
  have hh := mul_le_mul_of_nonneg_right hnum hm
  nlinarith only [hh,hstep]

end CliqueFreeIndependence.Numerical

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.Numerical
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Filter


theorem solution : type_of% @_root_.OAI.CliqueFreeIndependence.Numerical.recurrence_bound := @_root_.OAI.CliqueFreeIndependence.Numerical.recurrence_bound
