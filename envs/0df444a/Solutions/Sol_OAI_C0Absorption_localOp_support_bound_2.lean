-- Prove2me | solution 2 for OAI.C0Absorption.localOp_support_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:53:00.34128+00:00
-- url     : https://prove2.me/submissions/db86fecf-99de-469f-ab14-d95d2227c902

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Localization.lean:L435-L449
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.localOp_support_bound. The node keeps its source
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

theorem localOp_nonzero_old {X : Type*} [PseudoMetricSpace X] (isG : Bool) (q : X)
    {ε : ℝ} (hε : 0 < ε) (u : X → ℝ) (x : X) (hx : localOp isG q ε u x ≠ 0) :
    ∃ y, u y ≠ 0 ∧ dist x y ≤ ε := by
  by_cases hu : u x = 0
  · refine ⟨q, ?_, ?_⟩
    · intro hq
      cases isG <;> simp [localOp, localGLinear, localRLinear, localG, hu, hq] at hx
    · have ha : cutoff q ε x ≠ 0 := by
        intro ha
        cases isG
        · change localR q ε u x ≠ 0 at hx
          simp [localR_eq, ha] at hx
        · change localG q ε u x ≠ 0 at hx
          simp [localG_eq, localR_eq, hu, ha] at hx
      exact (dist_lt_of_cutoff_ne_zero q hε x ha).le
  · exact ⟨x, hu, by simpa using hε.le⟩

theorem localOp_support_bound {X : Type*} [PseudoMetricSpace X] (isG : Bool) (q : X)
    {ε : ℝ} (hε : 0 < ε) (u v : X → ℝ) {K : ℝ≥0} (hv : LipschitzWith K v)
    (a : ℝ) (ha : ∀ x ∈ tsupport u, v x ≤ a) :
    ∀ x ∈ tsupport (localOp isG q ε u), v x ≤ a+ε*K := by
  have hclosed : IsClosed {x | v x ≤ a+ε*K} := isClosed_le hv.continuous continuous_const
  apply closure_minimal _ hclosed
  intro x hx
  obtain ⟨y, hy, hd⟩ := localOp_nonzero_old isG q hε u x hx
  have hb := ha y (subset_tsupport u hy)
  have hd' := hv.dist_le_mul x y
  rw [Real.dist_eq] at hd'
  have hle : v x-v y ≤ K*ε := (le_abs_self _).trans (hd'.trans
    (mul_le_mul_of_nonneg_left hd K.coe_nonneg))
  change v x ≤ a+ε*K
  nlinarith

end

end
end C0Absorption

end OAI

-- ---- platform node ----
open OAI OAI.C0Absorption
open scoped BigOperators NNReal ENNReal
open Finset
open Set Filter Topology


theorem solution : type_of% @_root_.OAI.C0Absorption.localOp_support_bound := @_root_.OAI.C0Absorption.localOp_support_bound
