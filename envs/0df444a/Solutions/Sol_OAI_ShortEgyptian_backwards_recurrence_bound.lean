-- Prove2me | solution 1 for OAI.ShortEgyptian.backwards_recurrence_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:52:17.696253+00:00
-- url     : https://prove2.me/submissions/a737f365-f315-4d8a-9a40-b3c5e34e3c20

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/RecurrenceUnrolling.lean:L17-L50
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.backwards_recurrence_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeProducts
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_HammingDistance
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SamplePartitions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ProductCorrelations
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_LevelSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListConstruction
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleGeometry
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ResidueSystem
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TerminalScale
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DescentSets
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_MomentRecurrence

-- ---- from OAI.NumberTheory.ShortEgyptian.RecurrenceUnrolling ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical

lemma nat_rpow_le_self (k : ℕ) {α : ℝ} (ha : 0 < α) (ha' : α ≤ 1) : (k:ℝ)^α ≤ k := by
  by_cases hk : k = 0
  · simp only [hk,Nat.cast_zero,Real.zero_rpow ha.ne',le_refl]
  · exact Real.rpow_le_self_of_one_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk) ha'

lemma backwards_recurrence_bound (f : ℕ → ℝ) (d : ℕ) (α c γ b : ℝ)
    (ha : 0 < α) (ha' : α ≤ 1) (hg : 0 ≤ γ) (hb : 0 ≤ b)
    (hfix : c+γ*α=γ) (hf : ∀ j, 0 ≤ f j) (hend : f d=0)
    (hrec : ∀ j, j < d → f j ≤ Real.exp (-b)+Real.exp c*(f (j+1))^α) :
    f 0 ≤ (d:ℝ)*Real.exp (γ-b*α^d) := by
  have hind (k : ℕ) (hk : k ≤ d) : f (d-k) ≤ (k:ℝ)*Real.exp (γ-b*α^k) := by
    induction k with
    | zero => simpa only [Nat.sub_zero,Nat.cast_zero,zero_mul,hend] using (le_refl (0:ℝ))
    | succ k ih =>
      have hk' : k ≤ d := by omega
      have ih := ih hk'
      have hj : d-(k+1) < d := by omega
      have heq : d-(k+1)+1=d-k := by omega
      have hstep := hrec (d-(k+1)) hj
      rw [heq] at hstep
      have hp := Real.rpow_le_rpow (hf (d-k)) ih ha.le
      rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.exp_nonneg _),←Real.exp_mul] at hp
      have he : Real.exp c*((k:ℝ)^α*Real.exp ((γ-b*α^k)*α)) =
          (k:ℝ)^α*Real.exp (γ-b*α^(k+1)) := by
        rw [←mul_assoc,mul_comm (Real.exp c),mul_assoc,←Real.exp_add]
        congr 2
        rw [pow_succ]
        nlinarith [hfix]
      have hpow : α^(k+1) ≤ 1 := pow_le_one₀ ha.le ha'
      have heps : Real.exp (-b) ≤ Real.exp (γ-b*α^(k+1)) :=
        Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hpow hb])
      calc
        _ ≤ Real.exp (-b)+Real.exp c*(f (d-k))^α := hstep
        _ ≤ Real.exp (-b)+Real.exp c*((k:ℝ)^α*Real.exp ((γ-b*α^k)*α)) := by gcongr
        _ = Real.exp (-b)+(k:ℝ)^α*Real.exp (γ-b*α^(k+1)) := by rw [he]
        _ ≤ Real.exp (γ-b*α^(k+1))+(k:ℝ)*Real.exp (γ-b*α^(k+1)) :=
          add_le_add heps (mul_le_mul_of_nonneg_right (nat_rpow_le_self k ha ha') (Real.exp_nonneg _))
        _ = _ := by push_cast; ring
  simpa only [Nat.sub_self] using hind d le_rfl

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Finset Classical


theorem solution : type_of% @_root_.OAI.ShortEgyptian.backwards_recurrence_bound := @_root_.OAI.ShortEgyptian.backwards_recurrence_bound
