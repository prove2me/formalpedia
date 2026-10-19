-- Prove2me | solution 1 for OAI.Problem313.graphVariance_eq_mean_mul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:26:31.497393+00:00
-- url     : https://prove2.me/submissions/e34d04e4-14c5-4ef5-b135-23fd2465721b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/Probability.lean:L60-L76
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.graphVariance_eq_mean_mul. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting
import Definitions.Def_OAI_Combinatorics_SharpThreshold_GraphBlockCapture
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Permutation
import Definitions.Def_OAI_Combinatorics_SharpThreshold_InfluenceReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockRestrictionSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbits
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Probability

-- ---- from OAI.Combinatorics.SharpThreshold.Probability ----
namespace OAI

noncomputable section
namespace Problem313

theorem graphWeight_sum {n : ℕ} (p : ℝ) :
    (∑ x : GraphConfig n, graphWeight p x) = 1 := by
  classical
  unfold graphWeight
  rw [← Fintype.prod_sum (fun (_ : GraphEdge n) (b : Bool) => if b = true then p else 1 - p)]
  simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
  simp

theorem graphVariance_eq_mean_mul {n : ℕ} (p : ℝ) (f : GraphConfig n → Bool) :
    graphVariance p f = graphMean p f * (1 - graphMean p f) := by
  classical
  let m := graphMean p f
  change (∑ x : GraphConfig n, graphWeight p x * (boolReal (f x) - m) ^ 2) = m * (1 - m)
  calc
    (∑ x : GraphConfig n, graphWeight p x * (boolReal (f x) - m) ^ 2) =
        ∑ x : GraphConfig n,
          ((1 - 2 * m) * (graphWeight p x * boolReal (f x)) + m ^ 2 * graphWeight p x) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [sub_sq, mul_add, mul_sub, boolReal_sq]
      ring
    _ = (1 - 2 * m) * m + m ^ 2 := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, graphWeight_sum, mul_one]
      rfl
    _ = m * (1 - m) := by ring

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313


theorem solution : type_of% @_root_.OAI.Problem313.graphVariance_eq_mean_mul := @_root_.OAI.Problem313.graphVariance_eq_mean_mul
