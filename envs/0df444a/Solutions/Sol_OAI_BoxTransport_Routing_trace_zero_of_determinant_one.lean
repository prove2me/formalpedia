-- Prove2me | solution 1 for OAI.BoxTransport.Routing.trace_zero_of_determinant_one
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T13:32:15.372164+00:00
-- url     : https://prove2.me/submissions/45534af7-ed23-42fd-8a8a-1745c83d78e6

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BoxTransport/Flow.lean:L546-L562
-- (upload_full_project.md Phase 4): solution for node OAI.BoxTransport.Routing.trace_zero_of_determinant_one. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BalancedBoxRouting
import Definitions.Def_OAI_Analysis_BoxTransport_Geometry
import Definitions.Def_OAI_Analysis_BoxTransport_Flow

-- ---- from OAI.Analysis.BoxTransport.Flow ----
namespace OAI

/-! Localized solenoidal moving fields and their unique global flows. -/

noncomputable section
open scoped Topology
open scoped BigOperators ContDiff

namespace BoxTransport.Routing
theorem trace_zero_of_determinant_one {d : ℝ → Space} {l : Space} {t : ℝ}
    (hd : ∀ j, HasDerivAt (fun s => d s j) (l j * d t j) t)
    (hdet : ∀ s, ∏ j : Fin 3, d s j = 1) : ∑ j : Fin 3, l j = 0 := by
  have he : (fun s => d s 0 * d s 1 * d s 2) = fun _ => (1 : ℝ) := by
    funext s
    simpa only [Fin.prod_univ_three] using hdet s
  have hp := ((hd 0).mul (hd 1)).mul (hd 2)
  change HasDerivAt (fun s => d s 0 * d s 1 * d s 2) _ t at hp
  rw [he] at hp
  have hz := hp.unique (hasDerivAt_const t (1 : ℝ))
  dsimp only [Pi.mul_apply] at hz
  have ht : d t 0 * d t 1 * d t 2 = 1 := by
    simpa only [Fin.prod_univ_three] using hdet t
  rw [Fin.sum_univ_three]
  calc
    l 0 + l 1 + l 2 = (l 0 + l 1 + l 2) * (d t 0 * d t 1 * d t 2) := by rw [ht, mul_one]
    _ = 0 := by nlinarith only [hz]

end BoxTransport.Routing

end

end OAI

-- ---- platform node ----
open OAI OAI.BoxTransport OAI.BoxTransport.Routing
open scoped Topology
open scoped BigOperators ContDiff


theorem solution : type_of% @_root_.OAI.BoxTransport.Routing.trace_zero_of_determinant_one := @_root_.OAI.BoxTransport.Routing.trace_zero_of_determinant_one
