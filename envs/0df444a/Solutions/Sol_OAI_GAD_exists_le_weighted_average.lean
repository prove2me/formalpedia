-- Prove2me | solution 1 for OAI.GAD.exists_le_weighted_average
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:53:33.636222+00:00
-- url     : https://prove2.me/submissions/54115990-1384-4db9-948a-133f1df2a20d

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/FinitePacking.lean:L56-L70
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.exists_le_weighted_average. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Pinching
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_GramMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ScalarDeficit
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ThermalEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TensorEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PureRecursion
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_StateEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_EntropyContinuity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_BlockFactors
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Naimark
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_HolevoInformation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_EnsembleBounds
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PhaseStates
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PhaseProducts
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_CapacityConverse
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_SequentialMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TypicalSets
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TypicalProjectors
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_SequentialDecoder

-- ---- from OAI.InformationTheory.AmplitudeDamping.FinitePacking ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

universe u_1 u_2 u_3

section
open scoped BigOperators
namespace GAD
variable {α : Type u_1} [Fintype α]

/-- A finite average cannot be strictly below every sampled value. -/
theorem exists_le_weighted_average (q : α → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hs : ∑ a, q a=1) (f : α → ℝ) : ∃ a, f a ≤ ∑ b, q b*f b := by
  by_contra! h
  obtain ⟨a,ha⟩ : ∃ a, 0 < q a := by
    by_contra! hz
    have hzero : ∀ a, q a=0 := fun a ↦ le_antisymm (hz a) (hq a)
    simp only [hzero,Finset.sum_const_zero] at hs
    norm_num at hs
  have hh : (∑ b, q b*(∑ c, q c*f c)) < ∑ b, q b*f b := by
    apply Finset.sum_lt_sum
    · intro b _; exact mul_le_mul_of_nonneg_left (h b).le (hq b)
    · exact ⟨a,Finset.mem_univ a,mul_lt_mul_of_pos_left (h a) ha⟩
  rw [← Finset.sum_mul,hs,one_mul] at hh
  exact lt_irrefl _ hh

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_2} {α : Type u_3} [Fintype ι] [Fintype α] [DecidableEq ι]

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.GAD.exists_le_weighted_average := @_root_.OAI.GAD.exists_le_weighted_average
