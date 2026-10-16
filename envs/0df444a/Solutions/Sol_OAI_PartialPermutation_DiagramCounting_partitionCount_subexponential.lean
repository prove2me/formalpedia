-- Prove2me | solution 1 for OAI.PartialPermutation.DiagramCounting.partitionCount_subexponential
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:26:21.677978+00:00
-- url     : https://prove2.me/submissions/21bb6885-aa1f-4565-a7f3-79cca9391ada

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/PartitionAsymptotics.lean:L11-L45
-- (upload_full_project.md Phase 4): solution for node OAI.PartialPermutation.DiagramCounting.partitionCount_subexponential. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_PartialPermutation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SchurAverage
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ModuleTransport
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Components
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CentralKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CompleteKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RegularRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Plancherel
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TrivialRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ConvolutionKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ComponentGeometry
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SmallKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ProjectionCovers
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Restriction
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_IsotypicMatrices
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_IsotypicKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Equivalences
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SymmetricTransfer
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_StandardTableaux
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RankFillings
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_DiagonalBounds
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_FillingExtensions
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Interleavings
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RowBounds
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Truncation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TailBounds
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_DiagramCounts
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_DeficitCounts

-- ---- from OAI.RepresentationTheory.PartialPermutation.DiagramCounts ----
namespace OAI

section
namespace PartialPermutation
namespace DiagramCounting
noncomputable section
open Finset

lemma no_large_corner (n m : ℕ) (hn : n < (m+1)*(m+1)) (μ : Shape n)
    {i j : ℕ} (h : (i,j) ∈ μ.1) : i < m ∨ j < m := by
  by_contra hh
  push Not at hh
  have hcorner : (m,m) ∈ μ.1 := μ.1.isLowerSet hh h
  have hc := rectangle_card_le μ.1 m m hcorner
  rw [μ.2] at hc
  omega

lemma shortCode_injective (n m : ℕ) (hn : n < (m+1)*(m+1)) :
    Function.Injective (shortCode n m) := by
  intro μ ν he
  have hr : ∀ i : Fin m, μ.1.rowLen i = ν.1.rowLen i := by
    intro i
    exact congrArg (fun z : (Fin m → Fin (n+1)) × (Fin m → Fin (n+1)) => (z.1 i).val) he
  have hc : ∀ j : Fin m, μ.1.colLen j = ν.1.colLen j := by
    intro j
    exact congrArg (fun z : (Fin m → Fin (n+1)) × (Fin m → Fin (n+1)) => (z.2 j).val) he
  apply Subtype.ext
  apply YoungDiagram.ext
  apply Finset.ext
  rintro ⟨i,j⟩
  constructor
  · intro h
    rcases no_large_corner n m hn μ h with hi | hj
    · apply ν.1.mem_iff_lt_rowLen.mpr
      rw [← hr ⟨i,hi⟩]
      exact μ.1.mem_iff_lt_rowLen.mp h
    · apply ν.1.mem_iff_lt_colLen.mpr
      rw [← hc ⟨j,hj⟩]
      exact μ.1.mem_iff_lt_colLen.mp h
  · intro h
    rcases no_large_corner n m hn ν h with hi | hj
    · apply μ.1.mem_iff_lt_rowLen.mpr
      rw [hr ⟨i,hi⟩]
      exact ν.1.mem_iff_lt_rowLen.mp h
    · apply μ.1.mem_iff_lt_colLen.mpr
      rw [hc ⟨j,hj⟩]
      exact ν.1.mem_iff_lt_colLen.mp h

lemma partitionCount_le_shortCode (n m : ℕ) (hn : n < (m+1)*(m+1)) :
    partitionCount n ≤ (n+1)^(2*m) := by
  have h := Fintype.card_le_of_injective (shortCode n m) (shortCode_injective n m hn)
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ← pow_add,
    ← two_mul, partitionCount] using h

lemma partitionCount_le_sqrt (n : ℕ) : partitionCount n ≤ (n+1)^(2*n.sqrt) :=
  partitionCount_le_shortCode n n.sqrt (Nat.lt_succ_sqrt n)

end
end DiagramCounting
end PartialPermutation
end

end OAI

-- ---- from OAI.RepresentationTheory.PartialPermutation.PartitionAsymptotics ----
namespace OAI

section
namespace PartialPermutation
namespace DiagramCounting
noncomputable section
open Finset
open Filter in

lemma partitionCount_subexponential (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, (partitionCount n : ℝ) ≤ Real.exp (δ*n) := by
  have hl := (isLittleO_log_rpow_atTop (show (0:ℝ)<1/2 by norm_num)).bound
    (show 0 < δ/4 by positivity)
  have ht : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n => le_add_of_nonneg_right (show (0:ℝ)≤1 by norm_num))
      tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually hl, eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hn1' : (1:ℝ) ≤ n := by exact_mod_cast hn1
  have hs : 0 ≤ Real.sqrt (n+1) := Real.sqrt_nonneg _
  have hsq := Real.sq_sqrt (show (0:ℝ)≤n+1 by positivity)
  have hl0 : 0 ≤ Real.log ((n:ℝ)+1) := Real.log_nonneg (by linarith)
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hl0,
    ← Real.sqrt_eq_rpow,abs_of_nonneg hs] at hn
  have hnrt : (n.sqrt:ℝ) ≤ Real.sqrt (n+1) := by
    have h := Nat.sqrt_le n
    have hr : (n.sqrt:ℝ)^2 ≤ n := by simpa only [pow_two] using (show (n.sqrt:ℝ)*(n.sqrt:ℝ)≤n by exact_mod_cast h)
    nlinarith [show (0:ℝ)≤n.sqrt by positivity]
  have hexp : (2*(n.sqrt:ℝ))*Real.log ((n:ℝ)+1) ≤ δ*n := by
    calc
      _ ≤ (2*Real.sqrt (n+1))*((δ/4)*Real.sqrt (n+1)) :=
        mul_le_mul (by linarith) hn hl0 (by positivity)
      _ = δ/2*((n:ℝ)+1) := by nlinarith
      _ ≤ δ*n := by nlinarith
  calc
    (partitionCount n : ℝ) ≤ ((n+1)^(2*n.sqrt):ℕ) := by
      exact_mod_cast partitionCount_le_sqrt n
    _ = Real.exp ((2*(n.sqrt:ℝ))*Real.log ((n:ℝ)+1)) := by
      push_cast
      rw [show (2:ℝ)*(n.sqrt:ℝ)=((2*n.sqrt:ℕ):ℝ) by push_cast; rfl,
        Real.exp_nat_mul, Real.exp_log (by positivity)]
    _ ≤ Real.exp (δ*n) := Real.exp_le_exp.mpr hexp

end
end DiagramCounting
end PartialPermutation

end

end OAI

-- ---- platform node ----
open OAI OAI.PartialPermutation OAI.PartialPermutation.DiagramCounting
open Finset


theorem solution : type_of% @_root_.OAI.PartialPermutation.DiagramCounting.partitionCount_subexponential := @_root_.OAI.PartialPermutation.DiagramCounting.partitionCount_subexponential
