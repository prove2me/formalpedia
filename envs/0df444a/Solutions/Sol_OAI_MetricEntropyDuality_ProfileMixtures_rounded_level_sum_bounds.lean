-- Prove2me | solution 1 for OAI.MetricEntropyDuality.ProfileMixtures.rounded_level_sum_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T22:57:50.379628+00:00
-- url     : https://prove2.me/submissions/66c176bb-cee2-4a5d-af08-50538b9aeeeb

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
theorem h51b_tele (n : ℕ) : ∀ m : ℕ, (∑ j ∈ Finset.range m,
    if n ≤ j then (Real.log ((j:ℝ) + 2) - Real.log ((j:ℝ) + 1)) else 0) =
      if n ≤ m then Real.log ((m:ℝ) + 1) - Real.log ((n:ℝ) + 1) else 0
  | 0 => by
    by_cases h : n ≤ 0
    · have : n = 0 := by omega
      subst this
      simp
    · simp [h]
  | m + 1 => by
    rw [Finset.sum_range_succ, h51b_tele n m]
    by_cases h1 : n ≤ m
    · rw [if_pos h1, if_pos h1, if_pos (by omega)]
      push_cast
      ring
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : n = m + 1
      · subst h2
        simp
      · rw [if_neg (by omega)]
        simp

theorem h51b_Lpos {h : ℕ} (hh : 0 < h) : 0 < Real.log ((h : ℝ) + 1) :=
  Real.log_pos (by
    have : (1:ℝ) ≤ h := by exact_mod_cast hh
    linarith)

open OAI.MetricEntropyDuality.LogProfile in
theorem h51b_phi_sum {h : ℕ} (hh : 0 < h) (d : ℕ∞) :
    LogProfile.phi h d = ∑ j ∈ Finset.range h,
      if d ≤ (j : ℕ∞) then LogProfile.gamma h j else 0 := by
  have hL : 0 < Real.log ((h : ℝ) + 1) := Real.log_pos (by
    have : (1:ℝ) ≤ h := by exact_mod_cast hh
    linarith)
  induction d using ENat.recTopCoe with
  | top => simp
  | coe n =>
    rw [phi_coe]
    have hterm : ∀ j ∈ Finset.range h, (if (n : ℕ∞) ≤ (j : ℕ∞) then gamma h j else 0) =
        (if n ≤ j then (Real.log ((j:ℝ) + 2) - Real.log ((j:ℝ) + 1)) else 0) /
          Real.log ((h : ℝ) + 1) := by
      intro j _
      by_cases hj : n ≤ j <;> simp [hj, gamma]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, h51b_tele]
    by_cases hnh : n ≤ h
    · rw [if_pos hnh]
      have hle : Real.log ((n:ℝ) + 1) ≤ Real.log ((h:ℝ) + 1) := by
        apply Real.log_le_log (by positivity)
        have : (n:ℝ) ≤ h := by exact_mod_cast hnh
        linarith
      rw [max_eq_right]
      · field_simp
      · rw [sub_nonneg, div_le_one hL]
        exact hle
    · rw [if_neg hnh, zero_div]
      apply max_eq_left
      rw [sub_nonpos, le_div_iff₀ hL, one_mul]
      apply Real.log_le_log (by positivity)
      have : (h:ℝ) ≤ n := by exact_mod_cast (le_of_lt (not_le.mp hnh))
      linarith

theorem h51b_gamma_nonneg (h j : ℕ) : 0 ≤ LogProfile.gamma h j := by
  unfold LogProfile.gamma
  have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j
  have hh : (0:ℝ) ≤ h := Nat.cast_nonneg h
  exact div_nonneg (sub_nonneg.mpr (Real.log_le_log (by positivity) (by linarith)))
    (Real.log_nonneg (by linarith))

theorem h51b_gamma_sum {h : ℕ} (hh : 0 < h) :
    ∑ j ∈ Finset.range h, LogProfile.gamma h j = 1 := by
  have t := h51b_tele 0 h
  simp only [Nat.zero_le, if_true, Nat.cast_zero, zero_add, Real.log_one, sub_zero] at t
  unfold LogProfile.gamma
  rw [← Finset.sum_div, t, div_self (h51b_Lpos hh).ne']

theorem h51b_dil {h : ℕ} (hh : 0 < h) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hprofile : Real.log 3 / Real.log ((h : ℝ) + 1) ≤ θ) (d : ℕ∞) :
    (∑ j ∈ Finset.range h, if d ≤ ((3 * j + 2 : ℕ) : ℕ∞) then LogProfile.gamma h j else 0) ≤
      LogProfile.phi h d + θ := by
  have hL := h51b_Lpos hh
  induction d using ENat.recTopCoe with
  | top =>
    have : ∀ j ∈ Finset.range h, (if (⊤ : ℕ∞) ≤ ((3 * j + 2 : ℕ) : ℕ∞)
        then LogProfile.gamma h j else 0) = 0 :=
      fun j _ => if_neg (by rw [top_le_iff]; exact ENat.coe_ne_top _)
    rw [Finset.sum_congr rfl this, Finset.sum_const_zero, LogProfile.phi_top]
    linarith
  | coe n =>
    have hterm : ∀ j ∈ Finset.range h, (if (n : ℕ∞) ≤ ((3 * j + 2 : ℕ) : ℕ∞)
        then LogProfile.gamma h j else 0) =
        (if n / 3 ≤ j then (Real.log ((j:ℝ) + 2) - Real.log ((j:ℝ) + 1)) else 0) /
          Real.log ((h:ℝ) + 1) := by
      intro j _
      have e : ((n : ℕ∞) ≤ ((3 * j + 2 : ℕ) : ℕ∞)) ↔ n / 3 ≤ j := by
        rw [Nat.cast_le]
        omega
      by_cases hj : n / 3 ≤ j
      · rw [if_pos (e.mpr hj), if_pos hj]
        rfl
      · rw [if_neg (fun h' => hj (e.mp h')), if_neg hj, zero_div]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, h51b_tele]
    have hphi : 1 - Real.log ((n:ℝ) + 1) / Real.log ((h:ℝ) + 1) ≤ LogProfile.phi h n := by
      rw [LogProfile.phi_coe]
      exact le_max_right _ _
    have hphi0 : 0 ≤ LogProfile.phi h n := by
      rw [LogProfile.phi_coe]
      exact le_max_left _ _
    split_ifs with hc
    · have h3 : Real.log ((n:ℝ) + 1) ≤ Real.log 3 + Real.log (((n / 3 : ℕ) : ℝ) + 1) := by
        rw [← Real.log_mul (by norm_num) (by positivity)]
        apply Real.log_le_log (by positivity)
        have h5 : n + 1 ≤ 3 * (n / 3 + 1) := by omega
        have h6 : ((n + 1 : ℕ) : ℝ) ≤ ((3 * (n / 3 + 1) : ℕ) : ℝ) := by exact_mod_cast h5
        push_cast at h6
        linarith
      rw [sub_div, div_self hL.ne']
      have h4 : (Real.log ((n:ℝ) + 1) - Real.log (((n / 3 : ℕ) : ℝ) + 1)) /
          Real.log ((h:ℝ) + 1) ≤ θ := by
        calc _ ≤ Real.log 3 / Real.log ((h:ℝ) + 1) :=
              div_le_div_of_nonneg_right (by linarith) hL.le
          _ ≤ θ := hprofile
      rw [sub_div] at h4
      linarith
    · rw [zero_div]
      linarith

theorem solution (L : (i : ι) → X → Label i) (v : Y → X)
    (T : Y → Finset ι) (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y)
    (hmass : ∑ y, μ y ≤ 1) {h : ℕ} (hh : 0 < h) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hprofile : Real.log 3 / Real.log ((h : ℝ) + 1) ≤ θ)
    (x : X) (assigned rounded : Fin h → ℝ)
    (hlower : ∀ j, CompressionLevels.levelValue L v T μ j.val x - 2 * θ ≤ assigned j)
    (hupper : ∀ j, assigned j ≤ CompressionLevels.levelValue L v T μ (3 * j.val + 2) x)
    (hround : ∀ j, 0 ≤ assigned j - rounded j ∧ assigned j - rounded j ≤ θ) :
    profileMixture L v T h μ x - 3 * θ ≤
        ∑ j : Fin h, LogProfile.gamma h j.val * rounded j ∧
      (∑ j : Fin h, LogProfile.gamma h j.val * rounded j) ≤
        profileMixture L v T h μ x + θ := by
  have hL := h51b_Lpos hh
  have hγ := h51b_gamma_nonneg h
  have hsumF : ∑ j : Fin h, LogProfile.gamma h j.val = 1 := by
    rw [← h51b_gamma_sum hh, Finset.sum_range]
  have hexp : profileMixture L v T h μ x =
      ∑ j : Fin h, LogProfile.gamma h j.val * CompressionLevels.levelValue L v T μ j.val x := by
    rw [← Finset.sum_range (fun j => LogProfile.gamma h j * CompressionLevels.levelValue L v T μ j x)]
    unfold profileMixture CompressionLevels.levelValue
    simp_rw [h51b_phi_sum hh, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun y _ => ?_
    unfold CompressionLevels.ballIndicator PartitionGraph.near
    by_cases hd : PartitionGraph.distance L (T y) x (v y) ≤ (j : ℕ∞) <;> simp [hd, mul_comm]
  have hexp3 : ∑ j : Fin h, LogProfile.gamma h j.val *
      CompressionLevels.levelValue L v T μ (3 * j.val + 2) x =
      ∑ y, μ y * ∑ j ∈ Finset.range h,
        (if PartitionGraph.distance L (T y) x (v y) ≤ ((3 * j + 2 : ℕ) : ℕ∞)
          then LogProfile.gamma h j else 0) := by
    rw [← Finset.sum_range (fun j => LogProfile.gamma h j *
      CompressionLevels.levelValue L v T μ (3 * j + 2) x)]
    unfold CompressionLevels.levelValue
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun j _ => ?_
    unfold CompressionLevels.ballIndicator PartitionGraph.near
    by_cases hd : PartitionGraph.distance L (T y) x (v y) ≤ ((3 * j + 2 : ℕ) : ℕ∞) <;>
      simp [hd, mul_comm]
  constructor
  · have low : ∑ j : Fin h, LogProfile.gamma h j.val *
        (CompressionLevels.levelValue L v T μ j.val x - 3 * θ) ≤
        ∑ j : Fin h, LogProfile.gamma h j.val * rounded j := by
      refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (hγ _)
      have := hlower j
      have := hround j
      linarith [this.1]
    have e : ∑ j : Fin h, LogProfile.gamma h j.val *
        (CompressionLevels.levelValue L v T μ j.val x - 3 * θ) =
        (∑ j : Fin h, LogProfile.gamma h j.val * CompressionLevels.levelValue L v T μ j.val x) -
          3 * θ * ∑ j : Fin h, LogProfile.gamma h j.val := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, hsumF, ← hexp] at low
    linarith
  · have up : ∑ j : Fin h, LogProfile.gamma h j.val * rounded j ≤
        ∑ j : Fin h, LogProfile.gamma h j.val *
          CompressionLevels.levelValue L v T μ (3 * j.val + 2) x := by
      refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (hγ _)
      have := hupper j
      have := hround j
      linarith [this.1]
    rw [hexp3] at up
    have up2 : ∑ y, μ y * ∑ j ∈ Finset.range h,
        (if PartitionGraph.distance L (T y) x (v y) ≤ ((3 * j + 2 : ℕ) : ℕ∞)
          then LogProfile.gamma h j else 0) ≤
        ∑ y, μ y * (LogProfile.phi h (PartitionGraph.distance L (T y) x (v y)) + θ) :=
      Finset.sum_le_sum fun y _ =>
        mul_le_mul_of_nonneg_left (h51b_dil hh hθ0 hprofile _) (hμ y)
    have e2 : ∑ y, μ y * (LogProfile.phi h (PartitionGraph.distance L (T y) x (v y)) + θ) =
        profileMixture L v T h μ x + θ * ∑ y, μ y := by
      unfold profileMixture
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun y _ => by ring
    have : θ * ∑ y, μ y ≤ θ := by nlinarith
    linarith

