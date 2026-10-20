-- Prove2me | solution 1 for OAI.MetricEntropyDuality.ProfileMixtures.dilated_level_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T22:57:40.614783+00:00
-- url     : https://prove2.me/submissions/c3aacc14-f636-478f-8089-1327c8b10765

import Mathlib
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Monotone.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Definitions.Def_MetricEntropyDuality
import Definitions.Def_OAI_Analysis_MetricEntropy_FormDimension
import Definitions.Def_OAI_Analysis_MetricEntropy_Parameters
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricIndex
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricForms
import Definitions.Def_OAI_Analysis_MetricEntropy_Basic
import Definitions.Def_OAI_Analysis_MetricEntropy_EntropyPair
import Definitions.Def_OAI_Analysis_MetricEntropy_SupportPolar
import Definitions.Def_OAI_Analysis_MetricEntropy_PolarCover
import Definitions.Def_OAI_Analysis_MetricEntropy_CoordinateTransport
import Definitions.Def_OAI_Analysis_MetricEntropy_DirectionTuples
import Definitions.Def_OAI_Analysis_MetricEntropy_FiniteProductCounting
import Definitions.Def_OAI_Analysis_MetricEntropy_DirectionSampling
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricMultiplicity
import Definitions.Def_OAI_Analysis_MetricEntropy_FormPolynomials
import Definitions.Def_OAI_Analysis_MetricEntropy_PolynomialZeroBound
import Definitions.Def_OAI_Analysis_MetricEntropy_FormContraction
import Definitions.Def_OAI_Analysis_MetricEntropy_PartitionGraph
import Definitions.Def_OAI_Analysis_MetricEntropy_FieldGraphSeparation
import Definitions.Def_OAI_Analysis_MetricEntropy_LogProfile
import Definitions.Def_OAI_Analysis_MetricEntropy_GraphProfile
import Definitions.Def_OAI_Analysis_MetricEntropy_FiniteFieldRows
import Definitions.Def_OAI_Analysis_MetricEntropy_GreedyPivots
import Definitions.Def_OAI_Analysis_MetricEntropy_CompressionLevels
import Definitions.Def_OAI_Analysis_MetricEntropy_ProfileMixtures

open OAI OAI.MetricEntropyDuality OAI.MetricEntropyDuality.ProfileMixtures
universe uX uY uι uLabel uJ
open scoped BigOperators
variable {X : Type uX} {Y : Type uY} {ι : Type uι} {Label : ι → Type uLabel} [Fintype Y]
lemma h51m_steps (d h : ℕ) :
    (∑ j ∈ Finset.range h,
      if d ≤ j then Real.log ((j : ℝ) + 2) - Real.log ((j : ℝ) + 1) else 0) =
      Real.log ((h : ℝ) + 1) - Real.log (((min d h : ℕ) : ℝ) + 1) := by
  induction h with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases hd : d ≤ n
    · rw [if_pos hd, min_eq_left hd, min_eq_left (by omega : d ≤ n + 1)]
      push_cast; ring
    · rw [if_neg hd, min_eq_right (by omega : n ≤ d), min_eq_right (by omega : n + 1 ≤ d)]
      push_cast; ring
lemma h51m_dilation {h : ℕ} (hh : 0 < h) (d : ℕ∞) :
    (∑ j ∈ Finset.range h,
      if d ≤ ((3 * j + 2 : ℕ) : ℕ∞) then LogProfile.gamma h j else 0) ≤
      LogProfile.phi h d + Real.log 3 / Real.log ((h : ℝ) + 1) := by
  open LogProfile in
  have hh1 : (1:ℝ) ≤ h := by exact_mod_cast hh
  have hL : 0 < Real.log ((h : ℝ) + 1) := Real.log_pos (by linarith)
  have hl3 : 0 < Real.log 3 / Real.log ((h : ℝ) + 1) := div_pos (Real.log_pos (by norm_num)) hL
  induction d using ENat.recTopCoe with
  | top =>
    have : ∀ j ∈ Finset.range h, (if (⊤ : ℕ∞) ≤ ((3 * j + 2 : ℕ) : ℕ∞) then gamma h j else 0) = 0 := by
      intro j _; rw [if_neg]; rw [top_le_iff]; exact ENat.coe_ne_top _
    rw [Finset.sum_congr rfl this, Finset.sum_const_zero, phi_top]; linarith
  | coe n =>
    have hcond : ∀ j : ℕ, ((n : ℕ∞) ≤ ((3 * j + 2 : ℕ) : ℕ∞)) ↔ n / 3 ≤ j := by
      intro j; rw [Nat.cast_le]; omega
    have hsum : (∑ j ∈ Finset.range h, if (n : ℕ∞) ≤ ((3 * j + 2 : ℕ) : ℕ∞) then gamma h j else 0) =
        (Real.log ((h : ℝ) + 1) - Real.log (((min (n/3) h : ℕ) : ℝ) + 1)) / Real.log ((h : ℝ) + 1) := by
      rw [← h51m_steps, Finset.sum_div]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [hcond, gamma]
      split_ifs <;> simp
    rw [hsum, phi_coe]
    have hmax := le_max_right 0 (1 - Real.log ((n : ℝ) + 1) / Real.log ((h : ℝ) + 1))
    by_cases hm : n / 3 ≤ h
    · rw [min_eq_left hm]
      have hlog : Real.log ((n : ℝ) + 1) ≤ Real.log (((n/3 : ℕ) : ℝ) + 1) + Real.log 3 := by
        rw [← Real.log_mul (by positivity) (by norm_num)]
        apply Real.log_le_log (by positivity)
        have : n + 1 ≤ (n / 3 + 1) * 3 := by omega
        have : ((n : ℝ) + 1) ≤ (((n/3 : ℕ) : ℝ) + 1) * 3 := by exact_mod_cast this
        linarith
      have : (Real.log ((h : ℝ) + 1) - Real.log (((n/3 : ℕ) : ℝ) + 1)) / Real.log ((h : ℝ) + 1) ≤
          (1 - Real.log ((n : ℝ) + 1) / Real.log ((h : ℝ) + 1)) + Real.log 3 / Real.log ((h : ℝ) + 1) := by
        rw [div_le_iff₀ hL]
        field_simp
        linarith
      linarith
    · rw [min_eq_right (by omega)]
      simp only [sub_self, zero_div]
      have := le_max_left 0 (1 - Real.log ((n : ℝ) + 1) / Real.log ((h : ℝ) + 1))
      linarith

theorem solution (L : (i : ι) → X → Label i) (v : Y → X)
    (T : Y → Finset ι) (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y)
    (hmass : ∑ y, μ y ≤ 1) {h : ℕ} (hh : 0 < h) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hprofile : Real.log 3 / Real.log ((h : ℝ) + 1) ≤ θ) (x : X) :
    (∑ j : Fin h, LogProfile.gamma h j.val *
      CompressionLevels.levelValue L v T μ (3 * j.val + 2) x) ≤
        profileMixture L v T h μ x + θ := by
  have hc0 : 0 ≤ Real.log 3 / Real.log ((h : ℝ) + 1) := by
    have hh1 : (1:ℝ) ≤ h := by exact_mod_cast hh
    exact div_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg (by linarith))
  unfold CompressionLevels.levelValue profileMixture
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hy : ∀ y, ∑ j : Fin h, LogProfile.gamma h j.val *
      (μ y * CompressionLevels.ballIndicator L (T y) (3 * j.val + 2) x (v y)) ≤
      μ y * LogProfile.phi h (PartitionGraph.distance L (T y) x (v y)) +
        μ y * (Real.log 3 / Real.log ((h : ℝ) + 1)) := by
    intro y
    have := h51m_dilation hh (PartitionGraph.distance L (T y) x (v y))
    rw [← Fin.sum_univ_eq_sum_range (fun j => if PartitionGraph.distance L (T y) x (v y) ≤
      ((3 * j + 2 : ℕ) : ℕ∞) then LogProfile.gamma h j else 0) h] at this
    have h2 := mul_le_mul_of_nonneg_left this (hμ y)
    rw [Finset.mul_sum, mul_add] at h2
    refine le_trans (le_of_eq ?_) h2
    refine Finset.sum_congr rfl (fun j _ => ?_)
    unfold CompressionLevels.ballIndicator PartitionGraph.near
    split_ifs <;> ring
  calc _ ≤ ∑ y, (μ y * LogProfile.phi h (PartitionGraph.distance L (T y) x (v y)) +
        μ y * (Real.log 3 / Real.log ((h : ℝ) + 1))) := Finset.sum_le_sum (fun y _ => hy y)
    _ = (∑ y, μ y * LogProfile.phi h (PartitionGraph.distance L (T y) x (v y))) +
        (∑ y, μ y) * (Real.log 3 / Real.log ((h : ℝ) + 1)) := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ (∑ y, μ y * LogProfile.phi h (PartitionGraph.distance L (T y) x (v y))) + θ := by
        have : (∑ y, μ y) * (Real.log 3 / Real.log ((h : ℝ) + 1)) ≤ θ := by
          calc (∑ y, μ y) * (Real.log 3 / Real.log ((h : ℝ) + 1)) ≤ 1 * (Real.log 3 / Real.log ((h : ℝ) + 1)) :=
                mul_le_mul_of_nonneg_right hmass hc0
            _ ≤ θ := by linarith
        linarith

