-- Prove2me | solution 1 for OAI.MetricEntropyDuality.exists_compressionCode
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T23:04:20.581539+00:00
-- url     : https://prove2.me/submissions/88ef2310-6e8c-44c1-9f07-1640d9fd8028

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
import Definitions.Def_OAI_Analysis_MetricEntropy_LabelEncoding
import Definitions.Def_OAI_Analysis_MetricEntropy_CompressionCode
import Definitions.Def_OAI_Analysis_MetricEntropy_WeightRounding
import Definitions.Def_OAI_Analysis_MetricEntropy_CompressionDecoder
import Definitions.Def_OAI_Analysis_MetricEntropy_GroupedWeights
import Definitions.Def_OAI_Analysis_MetricEntropy_SignedCompression
import Theorems.Thm_OAI_MetricEntropyDuality_CompressionLevels_levelValue_sub_two_mul_le_assignedValue
import Theorems.Thm_OAI_MetricEntropyDuality_ProfileMixtures_rounded_level_sum_bounds
import Theorems.Thm_OAI_MetricEntropyDuality_exists_profile_pivots
import Theorems.Thm_OAI_MetricEntropyDuality_CompressionLevels_assignedIndicator_le_ballIndicator
import Theorems.Thm_OAI_MetricEntropyDuality_roundWeight_sum_error

open OAI OAI.MetricEntropyDuality
universe uX uY uLabel
open scoped BigOperators Classical
open CompressionLevels ProfileMixtures
variable {X : Type uX} {Y : Type uY} [Fintype X] [Nonempty X] [Fintype Y]
variable {u q h s : ℕ} {Label : Fin u → Type uLabel}
set_option maxHeartbeats 1000000 in

theorem solution
    (L : (i : Fin u) → X → Label i) (E : FixedLabels L q)
    (v : Y → X) (T : Y → Finset (Fin u)) (μ : Y → ℝ)
    (hμ : ∀ y, 0 ≤ μ y) (hmass : ∑ y, μ y ≤ 1)
    (hu : 0 < u) (hh : 0 < h) (hs : 0 < s)
    (θ : ℝ) (hθ : 0 < θ) (hsθ : 1 ≤ (s : ℝ) * θ)
    (hprofile : Real.log 3 / Real.log ((h : ℝ) + 1) ≤ θ)
    (hcomp : ∀ y, ((Finset.univ \ T y).card : ℝ) ≤ θ * (u : ℝ)) :
    ∃ code : CompressionCode u q h s (weightCodeSize (roundingStep θ s u)),
      ∀ x, profileMixture L v T h μ x - 3 * θ ≤ compressionDecode L E h s θ code x ∧
        compressionDecode L E h s θ code x ≤ profileMixture L v T h μ x + θ := by
  obtain ⟨i, centers, assigned, homit, hassign, hrem⟩ :=
    exists_profile_pivots L v T μ hμ hmass hu θ hθ s hsθ hcomp h
  set δ := roundingStep θ s u with hδdef
  have hδ : 0 < δ := by rw [hδdef]; unfold roundingStep; positivity
  let rep : Fin h → Fin s → X := fun j k => E.representative i (E.encode i (centers j k))
  have hrep : ∀ j k, L i (rep j k) = L i (centers j k) := fun j k => E.label_representative_encode i _
  let W : Fin h → Fin s → Finset (Fin u) → ℝ := fun j k S =>
    ∑ y, if assigned j y = some k ∧ T y = S then μ y else 0
  have hW0 : ∀ j k S, 0 ≤ W j k S := fun j k S =>
    Finset.sum_nonneg (fun y _ => by split_ifs; exact hμ y; exact le_refl 0)
  have hW1 : ∀ j k S, W j k S ≤ 1 := fun j k S =>
    le_trans (Finset.sum_le_sum (fun y _ => show (if assigned j y = some k ∧ T y = S then μ y else 0) ≤ μ y by
      split_ifs; exact le_refl _; exact hμ y)) hmass
  let code : CompressionCode u q h s (weightCodeSize δ) :=
    (i, fun j k => E.encode i (centers j k), fun j k S => weightCode δ (W j k S) hδ (hW0 j k S) (hW1 j k S))
  refine ⟨code, fun x => ?_⟩
  let A : Fin h → ℝ := fun j => assignedValue L T (rep j) (assigned j) μ j.val x
  let R : Fin h → ℝ := fun j => ∑ k : Fin s, ∑ S : Finset (Fin u),
    roundWeight δ (W j k S) * ballIndicator L S (2 * j.val + 1) x (rep j k)
  have hb01 : ∀ (S : Finset (Fin u)) (n : ℕ) (z : X), 0 ≤ ballIndicator L S n x z ∧ ballIndicator L S n x z ≤ 1 := by
    intro S n z; unfold ballIndicator; split_ifs <;> norm_num
  -- grouping identity
  have hgroup : ∀ j, A j = ∑ k : Fin s, ∑ S : Finset (Fin u),
      W j k S * ballIndicator L S (2 * j.val + 1) x (rep j k) := by
    intro j
    simp only [A, W, assignedValue, Finset.sum_mul]
    rw [Finset.sum_comm]
    conv_rhs => arg 2; ext k; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    unfold assignedIndicator
    cases hy : assigned j y with
    | none => simp
    | some k0 =>
      simp only [ite_mul, zero_mul, Option.some.injEq]
      rw [Finset.sum_eq_single (T y)]
      · rw [Finset.sum_eq_single k0]
        · simp
        · intro k _ hk; rw [if_neg]; exact fun h => hk h.1.symm
        · simp
      · intro S _ hS; apply Finset.sum_eq_zero; intro k _; rw [if_neg]; exact fun h => hS h.2.symm
      · simp
  have hround : ∀ j, 0 ≤ A j - R j ∧ A j - R j ≤ θ := by
    intro j
    have := roundWeight_sum_error (I := Fin s × Finset (Fin u)) δ hδ
      (fun p => W j p.1 p.2) (fun p => ballIndicator L p.2 (2 * j.val + 1) x (rep j p.1))
      (fun p => hW0 j p.1 p.2) (fun p => (hb01 _ _ _).1) (fun p => (hb01 _ _ _).2)
    simp only [Fintype.sum_prod_type] at this
    rw [hgroup j]
    refine ⟨this.1, le_trans this.2 (le_of_eq ?_)⟩
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_finset, Fintype.card_fin, hδdef]
    unfold roundingStep
    push_cast
    field_simp
  have hlower : ∀ j : Fin h, levelValue L v T μ j.val x - 2 * θ ≤ A j := fun j =>
    levelValue_sub_two_mul_le_assignedValue L v T μ hμ i j.val (centers j) (rep j) (assigned j)
      (hassign j) (hrep j) (by convert homit) (fun x => by convert hrem j x) x
  have hupper : ∀ j : Fin h, A j ≤ levelValue L v T μ (3 * j.val + 2) x := by
    intro j
    simp only [A, assignedValue, levelValue]
    apply Finset.sum_le_sum; intro y _
    exact mul_le_mul_of_nonneg_left (assignedIndicator_le_ballIndicator L v T i j.val (centers j) (rep j)
      (assigned j) (hassign j) (hrep j) x y) (hμ y)
  have hmain := rounded_level_sum_bounds L v T μ hμ hmass hh hθ.le hprofile x A R hlower hupper hround
  have hdec : compressionDecode L E h s θ code x = ∑ j : Fin h, LogProfile.gamma h j.val * R j := by
    simp only [compressionDecode, code, R, rep]
    rfl
  rw [hdec]
  exact hmain

