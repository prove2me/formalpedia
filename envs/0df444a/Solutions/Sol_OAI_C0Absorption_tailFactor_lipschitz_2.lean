-- Prove2me | solution 2 for OAI.C0Absorption.tailFactor_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:54:35.037518+00:00
-- url     : https://prove2.me/submissions/0ecbaf68-8d2c-4383-8276-b54cddf5df7e

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Coordinates.lean:L319-L336
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.tailFactor_lipschitz. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates

-- ---- from OAI.Analysis.C0Absorption.Coordinates ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

namespace C0Absorption
noncomputable section

theorem tailFactor_lipschitz {c : ℝ} (hc : 0 < c) (N : ℕ) :
    LipschitzWith ⟨c⁻¹, inv_nonneg.mpr hc.le⟩ (tailFactor c N) := by
  have ht : LipschitzWith ⟨c⁻¹, inv_nonneg.mpr hc.le⟩ (fun s => (2 : ℝ)-tau N s/c) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    rw [Real.dist_eq]
    change |(2-tau N s/c)-(2-tau N t/c)| ≤ c⁻¹ * dist s t
    calc
      _ = |tau N s-tau N t| / c := by
        rw [← abs_neg, neg_sub, show (2-tau N t/c)-(2-tau N s/c) = (tau N s-tau N t)/c by ring,
          abs_div, abs_of_pos hc]
      _ ≤ dist s t/c := div_le_div_of_nonneg_right
        (by simpa [Real.dist_eq] using (tau_lipschitz N).dist_le_mul s t) hc.le
      _ = _ := by ring
  have hh := (LipschitzWith.const (1 : ℝ)).min (ht.max (LipschitzWith.const (0 : ℝ)))
  change LipschitzWith _ (fun s => min 1 (max (2-tau N s/c) 0))
  apply hh.weaken
  exact max_le bot_le (max_le le_rfl bot_le)

end
end C0Absorption

end OAI

-- ---- platform node ----
open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty


theorem solution : type_of% @_root_.OAI.C0Absorption.tailFactor_lipschitz := @_root_.OAI.C0Absorption.tailFactor_lipschitz
