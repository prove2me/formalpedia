-- Prove2me | solution 2 for OAI.LipschitzCounterexample.SeparatingStages.support_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:13:42.068888+00:00
-- url     : https://prove2.me/submissions/35245a87-d563-4746-ad26-e4b7b109c975

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/SeparatingCoordinates.lean:L104-L118
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.SeparatingStages.support_disjoint. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertDecomposition
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_InverseTails
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotRadii
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEmbedding
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RadialBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BanachAssembly
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GlobalInverse
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MovingSlots
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteApproximants
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparatingCoordinates

-- ---- from OAI.Analysis.LipschitzEquivalence.SeparatingCoordinates ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uIndex uOtherIndex

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal

namespace LipschitzCounterexample.SeparatingStages

theorem psi_nonneg (t : ℝ) : 0 ≤ psi t := expNegInvGlue.nonneg _

theorem psi_ne_zero_iff {t : ℝ} : psi t ≠ 0 ↔ |t| < 1 := by
  rw [← psi_pos_iff]
  constructor
  · intro h; exact lt_of_le_of_ne (psi_nonneg t) (Ne.symm h)
  · exact ne_of_gt

theorem normalized_support {k : ℕ} {t : CubeSpace k} {a : Label k}
    (ha : normalized k t a ≠ 0) (j : Fin k) : |(k : ℝ)*t j - (a j : ℤ)| < 1 := by
  have hG : G k t a ≠ 0 := by
    intro hz
    apply ha
    change ‖G k t‖⁻¹ * G k t a = 0
    rw [hz, mul_zero]
  rw [G_apply, Finset.prod_ne_zero_iff] at hG
  exact psi_ne_zero_iff.mp (hG j (Finset.mem_univ _))

theorem support_disjoint {k : ℕ} (hk : 0 < k) {s t : CubeSpace k} (j : Fin k)
    (hst : 2/(k : ℝ) < |s j-t j|) (a : Label k) :
    normalized k s a = 0 ∨ normalized k t a = 0 := by
  by_contra h
  push Not at h
  have hs := abs_lt.mp (normalized_support h.1 j)
  have ht := abs_lt.mp (normalized_support h.2 j)
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hmul : 2 < |s j-t j| *(k : ℝ) := (div_lt_iff₀ hk').mp hst
  rw [abs_sub_comm] at hst
  rcases le_total (s j) (t j) with hj | hj
  · rw [abs_of_nonpos (sub_nonpos.mpr hj)] at hmul
    nlinarith
  · rw [abs_of_nonneg (sub_nonneg.mpr hj)] at hmul
    nlinarith

end LipschitzCounterexample.SeparatingStages

namespace LipschitzCounterexample.SeparatingStages
open scoped ENNReal NNReal

end LipschitzCounterexample.SeparatingStages

namespace LipschitzCounterexample.SeparatingStages
open scoped ENNReal NNReal

section Embed
variable {ι : Type uIndex} {κ : Type uOtherIndex} [Fintype ι] [Fintype κ]
open Classical

end Embed
end LipschitzCounterexample.SeparatingStages

namespace LipschitzCounterexample.SeparatingStages
open scoped ENNReal NNReal

end LipschitzCounterexample.SeparatingStages

end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.SeparatingStages
open scoped BigOperators InnerProductSpace Topology ENNReal


theorem solution : type_of% @_root_.OAI.LipschitzCounterexample.SeparatingStages.support_disjoint := @_root_.OAI.LipschitzCounterexample.SeparatingStages.support_disjoint
