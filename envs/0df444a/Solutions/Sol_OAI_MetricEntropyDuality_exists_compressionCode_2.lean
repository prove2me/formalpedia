-- Prove2me | solution 2 for OAI.MetricEntropyDuality.exists_compressionCode
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:20:12.87799+00:00
-- url     : https://prove2.me/submissions/37cdb830-9b7c-4a69-99d2-c29b46fd9f49

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/Compression.lean:L30-L101
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.exists_compressionCode. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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
import Theorems.Thm_OAI_MetricEntropyDuality_CompressionLevels_assignedIndicator_le_ballIndicator
import Theorems.Thm_OAI_MetricEntropyDuality_CompressionLevels_levelValue_sub_two_mul_le_assignedValue
import Theorems.Thm_OAI_MetricEntropyDuality_ProfileMixtures_rounded_level_sum_bounds
import Theorems.Thm_OAI_MetricEntropyDuality_exists_profile_pivots
import Theorems.Thm_OAI_MetricEntropyDuality_roundWeight_sum_error

-- ---- from OAI.Analysis.MetricEntropy.CompressionLevels ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uX uY uK uι uLabel

/-!
# Graph-ball comparison at one compression level

Columns omitted by the common index and retained columns left uncovered
each contribute at most `θ`. Assigned columns are compared using the actual
partition graph and replacement pivots with the same selected label.
Graph distances remain extended distances throughout.
-/

noncomputable section

namespace MetricEntropyDuality.CompressionLevels

open scoped BigOperators Classical

variable {X : Type uX} {Y : Type uY} {K : Type uK} {ι : Type uι} {Label : ι → Type uLabel}

theorem ballIndicator_nonneg (L : (i : ι) → X → Label i) (T : Finset ι)
    (j : ℕ) (x v : X) : 0 ≤ ballIndicator L T j x v := by
  unfold ballIndicator
  split_ifs <;> simp

theorem ballIndicator_le_one (L : (i : ι) → X → Label i) (T : Finset ι)
    (j : ℕ) (x v : X) : ballIndicator L T j x v ≤ 1 := by
  unfold ballIndicator
  split_ifs <;> simp

section Weighted

variable [Fintype Y]

/-- The upper comparison uses the genuine radius `3*j+2` in each column graph. -/
theorem assignedValue_le_levelValue
    (L : (i : ι) → X → Label i) (v : Y → X) (T : Y → Finset ι)
    (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y) (i : ι) (j : ℕ)
    (centers rep : K → X) (assignment : Y → Option K)
    (hassign : ∀ y k, assignment y = some k →
      i ∈ T y ∧ PartitionGraph.near L (T y) j (centers k) (v y))
    (hrep : ∀ k, L i (rep k) = L i (centers k)) (x : X) :
    assignedValue L T rep assignment μ j x ≤ levelValue L v T μ (3 * j + 2) x := by
  exact Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
    (assignedIndicator_le_ballIndicator L v T i j centers rep assignment
      hassign hrep x y) (hμ y)

end Weighted

end MetricEntropyDuality.CompressionLevels

end

end OAI

-- ---- from OAI.Analysis.MetricEntropy.WeightRounding ----
namespace OAI

universe uI

/-!
# Finite codes for downward rounding of grouped weights

For a positive mesh `δ`, a weight in `[0, 1]` is rounded down to
`δ * floor (w / δ)`. Its integer coefficient is an actual element of
`Fin (floor (1 / δ) + 1)`, including the possible endpoint `w = 1`.
The error estimates apply to every indicator with values in `[0, 1]`.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators

theorem roundingStep_pos {θ : ℝ} {s u : ℕ} (hθ : 0 < θ) (hs : 0 < s) :
    0 < roundingStep θ s u :=
  div_pos hθ (mul_pos (Nat.cast_pos.mpr hs) (pow_pos (by norm_num) _))

theorem slotTag_card (s u : ℕ) :
    (Fintype.card (Fin s × Finset (Fin u)) : ℝ) = (s : ℝ) * 2 ^ u := by
  simp

/-- The actual number of slot/subset pairs times the mesh equals the prescribed
per-level error. -/
theorem card_mul_roundingStep (θ : ℝ) {s u : ℕ} (hs : 0 < s) :
    (Fintype.card (Fin s × Finset (Fin u)) : ℝ) * roundingStep θ s u = θ := by
  rw [slotTag_card, roundingStep]
  exact mul_div_cancel₀ θ
    (ne_of_gt (mul_pos (Nat.cast_pos.mpr hs) (pow_pos (by norm_num) _)))

/-- The total loss at a single level is at most `θ`, for the exact index type
`Fin s × Finset (Fin u)` used by the finite compression codes. -/
theorem roundWeight_level_error {θ : ℝ} {s u : ℕ} (hθ : 0 < θ) (hs : 0 < s)
    (w b : Fin s → Finset (Fin u) → ℝ)
    (hw0 : ∀ k T, 0 ≤ w k T) (hb0 : ∀ k T, 0 ≤ b k T)
    (hb1 : ∀ k T, b k T ≤ 1) :
    0 ≤ (∑ k, ∑ T, w k T * b k T) -
        ∑ k, ∑ T, roundWeight (roundingStep θ s u) (w k T) * b k T ∧
      (∑ k, ∑ T, w k T * b k T) -
        ∑ k, ∑ T, roundWeight (roundingStep θ s u) (w k T) * b k T ≤ θ := by
  have herr := roundWeight_sum_error (roundingStep θ s u) (roundingStep_pos hθ hs)
    (fun i : Fin s × Finset (Fin u) => w i.1 i.2)
    (fun i : Fin s × Finset (Fin u) => b i.1 i.2)
    (fun i => hw0 i.1 i.2) (fun i => hb0 i.1 i.2) (fun i => hb1 i.1 i.2)
  rw [card_mul_roundingStep θ hs] at herr
  simpa only [Fintype.sum_prod_type] using herr

end MetricEntropyDuality

end

end OAI

-- ---- from OAI.Analysis.MetricEntropy.GroupedWeights ----
namespace OAI

universe uY uK uT

/-!
# Grouping finite nonnegative weights

An optional slot assignment records which columns were retained. Grouping by
the assigned slot and by a tag preserves every weighted expression that only
depends on those two values. No nonemptiness assumptions are needed.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators

variable {Y : Type uY} {K : Type uK} {T : Type uT} [Fintype Y]

theorem groupedWeight_nonneg (assignment : Y → Option K) (tag : Y → T)
    (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y) (k : K) (t : T) :
    0 ≤ groupedWeight assignment tag μ k t := by
  classical
  unfold groupedWeight
  apply Finset.sum_nonneg
  intro y _
  split_ifs
  · exact hμ y
  · exact le_rfl

theorem groupedWeight_le_totalMass (assignment : Y → Option K) (tag : Y → T)
    (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y) (k : K) (t : T) :
    groupedWeight assignment tag μ k t ≤ ∑ y, μ y := by
  classical
  unfold groupedWeight
  apply Finset.sum_le_sum
  intro y _
  split_ifs
  · exact le_rfl
  · exact hμ y

theorem groupedWeight_le_one (assignment : Y → Option K) (tag : Y → T)
    (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y) (hmass : ∑ y, μ y ≤ 1)
    (k : K) (t : T) :
    groupedWeight assignment tag μ k t ≤ 1 :=
  (groupedWeight_le_totalMass assignment tag μ hμ k t).trans hmass

section FiniteGroups

variable [Fintype K] [Fintype T]

/-- Grouping is exact for arbitrary real functions of the slot and tag. -/
theorem sum_groupedWeight_mul (assignment : Y → Option K) (tag : Y → T)
    (μ : Y → ℝ) (B : K → T → ℝ) :
    (∑ k, ∑ t, groupedWeight assignment tag μ k t * B k t) =
      ∑ y, μ y * (match assignment y with
        | none => 0
        | some k => B k (tag y)) := by
  classical
  simp_rw [groupedWeight, Finset.sum_mul]
  rw [Finset.sum_comm_cycle]
  apply Finset.sum_congr rfl
  intro y _
  cases assignment y with
  | none => simp
  | some slot => simp [ite_and, ite_mul]

end FiniteGroups

end MetricEntropyDuality

end

end OAI

-- ---- from OAI.Analysis.MetricEntropy.Compression ----
namespace OAI

universe uX uY uLabel

/-!
# Uniform compression of the actual logarithmic graph matrix

A single common index is chosen for all levels. Greedy pivots are replaced
by representatives fixed from their labels, and only those labels and rounded
grouped weights enter the finite code. The resulting list has no factor
depending on the number of vertices.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators Classical
open CompressionLevels ProfileMixtures

variable {X : Type uX} {Y : Type uY} [Fintype X] [Nonempty X] [Fintype Y]
variable {u q h s : ℕ} {Label : Fin u → Type uLabel}

/-- Construct an actual finite code for a nonnegative mixture of graph
profiles, including profiles at infinite distance. -/
theorem exists_compressionCode
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
  obtain ⟨i, centers, assignment, homit, hassign, hrem⟩ :=
    exists_profile_pivots L v T μ hμ hmass hu θ hθ s hsθ hcomp h
  let rep : Fin h → Fin s → X := fun j k =>
    E.representative i (E.encode i (centers j k))
  have hrep (j : Fin h) (k : Fin s) :
      L i (rep j k) = L i (centers j k) :=
    E.label_representative_encode i (centers j k)
  let w : Fin h → Fin s → Finset (Fin u) → ℝ := fun j =>
    groupedWeight (assignment j) T μ
  have hw0 (j : Fin h) (k : Fin s) (t : Finset (Fin u)) : 0 ≤ w j k t :=
    groupedWeight_nonneg (assignment j) T μ hμ k t
  have hw1 (j : Fin h) (k : Fin s) (t : Finset (Fin u)) : w j k t ≤ 1 :=
    groupedWeight_le_one (assignment j) T μ hμ hmass k t
  let δ := roundingStep θ s u
  have hδ : 0 < δ := roundingStep_pos hθ hs
  let code : CompressionCode u q h s (weightCodeSize δ) :=
    ⟨i, (fun j k => E.encode i (centers j k)),
      fun j k t => weightCode δ (w j k t) hδ (hw0 j k t) (hw1 j k t)⟩
  refine ⟨code, ?_⟩
  intro x
  let A : Fin h → ℝ := fun j => assignedValue L T (rep j) (assignment j) μ j.val x
  let R : Fin h → ℝ := fun j =>
    ∑ k, ∑ t, roundWeight δ (w j k t) * ballIndicator L t (2 * j.val + 1) x (rep j k)
  have hgroup (j : Fin h) :
      (∑ k, ∑ t, w j k t * ballIndicator L t (2 * j.val + 1) x (rep j k)) = A j := by
    exact sum_groupedWeight_mul (assignment j) T μ
      (fun k t => ballIndicator L t (2 * j.val + 1) x (rep j k))
  have hlower (j : Fin h) : levelValue L v T μ j.val x - 2 * θ ≤ A j := by
    refine levelValue_sub_two_mul_le_assignedValue L v T μ hμ i j.val
      (centers j) (rep j) (assignment j) (hassign j) (hrep j) (θ := θ) ?_ ?_ x
    · refine le_trans (le_of_eq ?_) homit
      apply Finset.sum_congr
      · ext y
        simp only [Finset.mem_filter]
      · intro y hy
        rfl
    · intro z
      refine le_trans (le_of_eq ?_) (hrem j z)
      apply Finset.sum_congr
      · ext y
        simp only [Finset.mem_filter]
      · intro y hy
        rfl
  have hupper (j : Fin h) : A j ≤ levelValue L v T μ (3 * j.val + 2) x := by
    exact assignedValue_le_levelValue L v T μ hμ i j.val
      (centers j) (rep j) (assignment j) (hassign j) (hrep j) x
  have hround (j : Fin h) : 0 ≤ A j - R j ∧ A j - R j ≤ θ := by
    have he := roundWeight_level_error hθ hs (w j)
      (fun k t => ballIndicator L t (2 * j.val + 1) x (rep j k)) (hw0 j)
      (fun k t => ballIndicator_nonneg L t (2 * j.val + 1) x (rep j k))
      (fun k t => ballIndicator_le_one L t (2 * j.val + 1) x (rep j k))
    rw [hgroup] at he
    exact he
  have hdecode : compressionDecode L E h s θ code x =
      ∑ j : Fin h, LogProfile.gamma h j.val * R j := by
    rfl
  rw [hdecode]
  exact rounded_level_sum_bounds L v T μ hμ hmass hh hθ.le hprofile x
    A R hlower hupper hround

end MetricEntropyDuality

end

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality
open scoped BigOperators Classical
open CompressionLevels ProfileMixtures


theorem solution.{uX,uY,uLabel} : type_of% @_root_.OAI.MetricEntropyDuality.exists_compressionCode.{uX,uY,uLabel} := @_root_.OAI.MetricEntropyDuality.exists_compressionCode.{uX,uY,uLabel}
