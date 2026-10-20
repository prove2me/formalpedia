-- Prove2me | solution 2 for OAI.LipschitzCounterexample.LocalLipschitz.weightedRemainder_lipschitzOn
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:32:15.52688+00:00
-- url     : https://prove2.me/submissions/8cab5962-a234-4ea6-b613-debdc9683579

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/CompactLipschitz.lean:L124-L157
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.LocalLipschitz.weightedRemainder_lipschitzOn. The node keeps its source
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
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlowAngles
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RotatingStages
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBijection
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalOrthogonality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparableCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLipschitz

-- ---- from OAI.Analysis.LipschitzEquivalence.CompactLipschitz ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uM uI

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.LocalLipschitz
variable {M : Type uM} {I : Type uI} [MetricSpace M] [Fintype I]

end LipschitzCounterexample.LocalLipschitz

namespace LipschitzCounterexample.LocalLipschitz
variable {M : Type uM} {I : Type uI} [MetricSpace M] [Fintype I]

omit [MetricSpace M] in
theorem weightedRemainder_sub (d : M → ℝ) (z : I → M) (φ : I → M → ℝ) (x y : M) :
    weightedRemainder d z φ x-weightedRemainder d z φ y =
      (1-∑ j,φ j x)*(d x-d y)+∑ j,(φ j x-φ j y)*(d (z j)-d y) := by
  simp only [weightedRemainder, sub_mul, mul_sub, one_mul, Finset.sum_sub_distrib,
    Finset.sum_mul]
  have h₁ : ∑ j, d x * φ j x = ∑ j, φ j x * d x := Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have h₂ : ∑ j, d y * φ j y = ∑ j, φ j y * d y := Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have h₃ : ∑ j, d (z j) * φ j x = ∑ j, φ j x * d (z j) := Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have h₄ : ∑ j, d (z j) * φ j y = ∑ j, φ j y * d (z j) := Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [h₁,h₂,h₃,h₄]
  ring

theorem weightedRemainder_lipschitzOn (d : M → ℝ) (z : I → M) (φ : I → M → ℝ)
    {K O : Set M} {A B ε : ℝ≥0}
    (hd : LipschitzOnWith A d O) (hφ : ∀ j, LipschitzWith B (φ j))
    (hsum : ∀ x, (∑ j,φ j x) ∈ Icc (0 : ℝ) 1)
    (hsmall : ∀ x ∈ K, |d x| ≤ ε) (hzsmall : ∀ j, |d (z j)| ≤ ε) :
    LipschitzOnWith (A+2*Fintype.card I*B*ε) (weightedRemainder d z φ) (K ∩ O) := by
  classical
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [Real.dist_eq,weightedRemainder_sub]
  have hxφ : |1-∑ j,φ j x| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (hsum x).2)]
    linarith [(hsum x).1]
  have hfirst : |(1-∑ j,φ j x)*(d x-d y)| ≤ (A : ℝ)*dist x y := by
    rw [abs_mul]
    calc
      _ ≤ 1*|d x-d y| := mul_le_mul_of_nonneg_right hxφ (abs_nonneg _)
      _ ≤ (A : ℝ)*dist x y := by simpa only [one_mul,Real.dist_eq] using hd.dist_le_mul x hx.2 y hy.2
  have hterm (j : I) : |(φ j x-φ j y)*(d (z j)-d y)| ≤
      (B : ℝ)*dist x y*(2*(ε : ℝ)) := by
    rw [abs_mul]
    have hl := (hφ j).dist_le_mul x y
    rw [Real.dist_eq] at hl
    exact mul_le_mul hl ((abs_sub _ _).trans (by linarith [hzsmall j,hsmall y hy.1]))
      (abs_nonneg _) (by positivity)
  have hsecond : |∑ j,(φ j x-φ j y)*(d (z j)-d y)| ≤
      (Fintype.card I : ℝ)*((B : ℝ)*dist x y*(2*(ε : ℝ))) := by
    calc
      _ ≤ ∑ j,|(φ j x-φ j y)*(d (z j)-d y)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : I, (B : ℝ)*dist x y*(2*(ε : ℝ)) := Finset.sum_le_sum (fun j _ => hterm j)
      _ = _ := by simp
  refine (abs_add_le _ _).trans ?_
  simp only [NNReal.coe_add,NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_ofNat]
  nlinarith
end LipschitzCounterexample.LocalLipschitz

namespace LipschitzCounterexample.LocalGeometry
variable {M : Type uM} {I : Type uI} [MetricSpace M] [Fintype I]

end LipschitzCounterexample.LocalGeometry

end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.LocalLipschitz
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set


theorem solution.{uM,uI} : type_of% @_root_.OAI.LipschitzCounterexample.LocalLipschitz.weightedRemainder_lipschitzOn.{uM,uI} := @_root_.OAI.LipschitzCounterexample.LocalLipschitz.weightedRemainder_lipschitzOn.{uM,uI}
