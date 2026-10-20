-- Prove2me | solution 1 for OAI.LipschitzCounterexample.LocalLipschitz.weightedRemainder_lipschitzOn
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:26:48.726962+00:00
-- url     : https://prove2.me/submissions/0bc92c0a-c524-43f7-8aa7-b8397dde7197

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

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.LocalLipschitz
universe uM uI
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set
variable {M : Type uM} {I : Type uI} [MetricSpace M] [Fintype I]


theorem solution (d : M → ℝ) (z : I → M) (φ : I → M → ℝ)
    {K O : Set M} {A B ε : ℝ≥0}
    (hd : LipschitzOnWith A d O) (hφ : ∀ j, LipschitzWith B (φ j))
    (hsum : ∀ x, (∑ j,φ j x) ∈ Icc (0 : ℝ) 1)
    (hsmall : ∀ x ∈ K, |d x| ≤ ε) (hzsmall : ∀ j, |d (z j)| ≤ ε) :
    LipschitzOnWith (A+2*Fintype.card I*B*ε) (weightedRemainder d z φ) (K ∩ O) := by
  classical
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  set S : M → ℝ := fun x => ∑ j, φ j x with hS
  have hW : ∀ w, weightedRemainder d z φ w = d w * (1 - S w) + ∑ j, d (z j) * φ j w := by
    intro w
    simp only [weightedRemainder, hS, sub_mul, Finset.sum_sub_distrib]
    rw [mul_sub, Finset.mul_sum]
    ring
  have hφd : ∀ j, |φ j x - φ j y| ≤ B * dist x y := by
    intro j; have := (hφ j).dist_le_mul x y; rwa [Real.dist_eq] at this
  have hdd : |d x - d y| ≤ A * dist x y := by
    have := hd.dist_le_mul x hx.2 y hy.2; rwa [Real.dist_eq] at this
  have hSd : |S y - S x| ≤ Fintype.card I * (B * dist x y) := by
    simp only [hS, ← Finset.sum_sub_distrib]
    calc |∑ j, (φ j y - φ j x)| ≤ ∑ j, |φ j y - φ j x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : I, (B * dist x y : ℝ) := Finset.sum_le_sum (fun j _ => by rw [abs_sub_comm]; exact hφd j)
      _ = _ := by simp
  have h3 : |∑ j, d (z j) * φ j x - ∑ j, d (z j) * φ j y| ≤ Fintype.card I * (ε * (B * dist x y)) := by
    rw [← Finset.sum_sub_distrib]
    calc |∑ j, (d (z j) * φ j x - d (z j) * φ j y)| ≤ ∑ j, |d (z j) * φ j x - d (z j) * φ j y| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : I, (ε * (B * dist x y) : ℝ) := Finset.sum_le_sum (fun j _ => by
          rw [← mul_sub, abs_mul]
          exact mul_le_mul (hzsmall j) (hφd j) (abs_nonneg _) ε.coe_nonneg)
      _ = _ := by simp
  have hSx := hsum x
  have h1 : |(d x - d y) * (1 - S x)| ≤ A * dist x y := by
    rw [abs_mul]
    have : |1 - S x| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hSx.1, hSx.2]
    calc |d x - d y| * |1 - S x| ≤ (A * dist x y) * 1 := mul_le_mul hdd this (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have h2 : |d y * (S y - S x)| ≤ ε * (Fintype.card I * (B * dist x y)) := by
    rw [abs_mul]; exact mul_le_mul (hsmall y hy.1) hSd (abs_nonneg _) ε.coe_nonneg
  rw [Real.dist_eq, hW, hW]
  have e : d x * (1 - S x) + ∑ j, d (z j) * φ j x - (d y * (1 - S y) + ∑ j, d (z j) * φ j y) =
      (d x - d y) * (1 - S x) + d y * (S y - S x) + (∑ j, d (z j) * φ j x - ∑ j, d (z j) * φ j y) := by ring
  rw [e]
  calc _ ≤ |(d x - d y) * (1 - S x)| + |d y * (S y - S x)| + |∑ j, d (z j) * φ j x - ∑ j, d (z j) * φ j y| :=
        abs_add_three _ _ _
    _ ≤ A * dist x y + ε * (Fintype.card I * (B * dist x y)) + Fintype.card I * (ε * (B * dist x y)) := by
        linarith
    _ = ((A + 2 * Fintype.card I * B * ε : ℝ≥0) : ℝ) * dist x y := by push_cast; ring

