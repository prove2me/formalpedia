-- Prove2me | solution 2 for OAI.C0Absorption.localG_sup
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:51:31.364543+00:00
-- url     : https://prove2.me/submissions/66183ad4-99ea-433d-a73a-7e335cce2e96

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Localization.lean:L358-L373
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.localG_sup. The node keeps its source
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

-- ---- from OAI.Analysis.C0Absorption.Localization ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

open Set Filter Topology

noncomputable section

theorem localG_sup {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ)
    (u : X → ℝ) (A : ℝ) (hu : ∀ x, |u x| ≤ A) (x : X) :
    |localG q ε u x| ≤ A := by
  have ha := cutoff_nonneg q ε x
  have ha' := cutoff_le_one q ε x
  have heq : localG q ε u x = (1-cutoff q ε x)*u x+cutoff q ε x*u q := by
    rw [localG_eq, localR_eq]; ring
  rw [heq]
  calc
    |(1-cutoff q ε x)*u x+cutoff q ε x*u q|
        ≤ |(1-cutoff q ε x)*u x|+|cutoff q ε x*u q| := abs_add_le _ _
    _ = (1-cutoff q ε x)*|u x|+cutoff q ε x*|u q| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg (by linarith : 0 ≤ 1-cutoff q ε x)]
    _ ≤ (1-cutoff q ε x)*A+cutoff q ε x*A := add_le_add
      (mul_le_mul_of_nonneg_left (hu x) (by linarith)) (mul_le_mul_of_nonneg_left (hu q) ha)
    _ = A := by ring

end

end
end C0Absorption

end OAI

-- ---- platform node ----
open OAI OAI.C0Absorption
open scoped BigOperators NNReal ENNReal
open Finset
open Set Filter Topology


theorem solution : type_of% @_root_.OAI.C0Absorption.localG_sup := @_root_.OAI.C0Absorption.localG_sup
