-- Prove2me | solution 1 for OAI.MatchingEntropy.entropy_barrier_ge_id
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:34:54.705893+00:00
-- url     : https://prove2.me/submissions/0fd68819-ec2b-4ed4-9ddc-e9fcc586784f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/PerfectMatching/Main.lean:L24-L46
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingEntropy.entropy_barrier_ge_id. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Calculus
import Definitions.Def_OAI_Combinatorics_PerfectMatching_SecondVariation
import Definitions.Def_OAI_Combinatorics_PerfectMatching_OddCuts
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Coupling
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Contraction
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Polytope
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Face
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Covariance
import Definitions.Def_OAI_Combinatorics_PerfectMatching_MatchingCovariance

-- ---- from OAI.Combinatorics.PerfectMatching.Main ----
namespace OAI

/-!
The nonlinear entropy defect bound
`F - H ≤ 8m (1 - exp (-F/m))` for finite loopless multigraphs on `2m` vertices,
and the perfect matching count bound `[k exp (-8 (1 - 1/k))]^m`,
with its coarse bound `(exp (-8) k)^m`, when the entire edge set
is partitioned into `k ≥ 1` perfect matchings.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

open Matrix

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- The small-entropy regime of the nonlinear barrier function. -/
theorem entropy_barrier_ge_id {t : ℝ} (ht : 0 ≤ t) (h8 : t ≤ Real.log 8) :
    t ≤ 8 * (1-Real.exp (-t)) := by
  have he : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr ht
  have he8 : Real.exp t ≤ 8 := by
    have hh := Real.exp_le_exp.mpr h8
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 8)] at hh
    exact hh
  have hlog := Real.log_le_sub_one_of_pos (Real.exp_pos t)
  rw [Real.log_exp] at hlog
  have hin := Real.exp_neg t
  rw [hin]
  have hp := Real.exp_pos t
  apply (mul_le_mul_iff_right₀ hp).mp
  have hmain : t * Real.exp t ≤ 8 * (Real.exp t - 1) := by
    have : t ≤ Real.exp t - 1 := hlog
    nlinarith
  have hprod : Real.exp t * (8*(1-(Real.exp t)⁻¹)) = 8*(Real.exp t-1) := by
    field_simp [hp.ne']
  calc
    Real.exp t * t = t * Real.exp t := mul_comm _ _
    _ ≤ 8 * (Real.exp t-1) := hmain
    _ = _ := hprod.symm

end MatchingEntropy

end

end OAI

-- ---- platform node ----
open OAI OAI.MatchingEntropy
open scoped BigOperators Topology
open Filter
open Matrix
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem solution {t : ℝ} (ht : 0 ≤ t) (h8 : t ≤ Real.log 8) :
    t ≤ 8 * (1-Real.exp (-t)) := by
  first
    | exact OAI.MatchingEntropy.entropy_barrier_ge_id ht h8
    | exact OAI.MatchingEntropy.entropy_barrier_ge_id
    | (apply OAI.MatchingEntropy.entropy_barrier_ge_id <;> assumption)
    | (intros; apply OAI.MatchingEntropy.entropy_barrier_ge_id <;> assumption)
