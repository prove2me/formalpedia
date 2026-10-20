-- Prove2me | solution 2 for OAI.MetricEntropyDuality.uniform_compression
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:21:14.651356+00:00
-- url     : https://prove2.me/submissions/f0fe1776-623c-4432-ac40-9066a133e344

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/Compression.lean:L123-L147
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.uniform_compression. The node keeps its source
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
import Theorems.Thm_OAI_MetricEntropyDuality_compressionList_card_le
import Theorems.Thm_OAI_MetricEntropyDuality_exists_compressionCode

-- ---- from OAI.Analysis.MetricEntropy.CompressionCode ----
namespace OAI

universe uE

/-!
# Finite codes for uniform compression

A code records one common index, one label code for each level and pivot slot,
and one weight code for each level, pivot slot, and subset of the index set.
The decoded family is the actual image of this finite type under a fixed
decoder. Its cardinality does not depend on the decoder's target type.
-/

namespace MetricEntropyDuality

section Decode

variable {u q h s N : ℕ} {E : Type uE}

theorem mem_compressionImage (decode : CompressionCode u q h s N → E) (a : E) :
    a ∈ compressionImage decode ↔ ∃ c, decode c = a := by
  classical
  simp [compressionImage]

theorem decode_mem_compressionImage (decode : CompressionCode u q h s N → E)
    (c : CompressionCode u q h s N) : decode c ∈ compressionImage decode :=
  (mem_compressionImage decode (decode c)).2 ⟨c, rfl⟩

/-- Constant zero labels and weight codes work even if there are no levels or slots. -/
theorem compressionCode_nonempty (hu : 0 < u) (hq : 0 < q) (hN : 0 < N) :
    Nonempty (CompressionCode u q h s N) := by
  refine ⟨⟨⟨0, hu⟩, ?_, ?_⟩⟩
  · exact fun _ _ => ⟨0, hq⟩
  · exact fun _ _ _ => ⟨0, hN⟩

/-- Decode an actual code to witness that the approximant family is nonempty. -/
theorem compressionImage_nonempty (decode : CompressionCode u q h s N → E)
    (hu : 0 < u) (hq : 0 < q) (hN : 0 < N) : (compressionImage decode).Nonempty := by
  obtain ⟨c⟩ := compressionCode_nonempty (h := h) (s := s) hu hq hN
  exact ⟨decode c, decode_mem_compressionImage decode c⟩

end Decode

end MetricEntropyDuality

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

theorem weightCodeSize_pos (δ : ℝ) : 0 < weightCodeSize δ :=
  Nat.succ_pos _

end MetricEntropyDuality

end

end OAI

-- ---- from OAI.Analysis.MetricEntropy.CompressionDecoder ----
namespace OAI

universe uX uLabel

/-!
# The fixed decoded family of compression approximants

The decoder uses only shared partition data, fixed label representatives, and
the finite code. Original column centers and coefficient vectors are absent
from its arguments. Every subset of the partition indices receives a weight
slot, so the enumeration includes every admissible-family encoding.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators

variable {X : Type uX} {u q : ℕ} {Label : Fin u → Type uLabel}

/-- Every encoded construction is included in the one shared finite list. -/
theorem compressionDecode_mem_compressionList
    (L : (i : Fin u) → X → Label i) (E : FixedLabels L q) (h s : ℕ) (θ : ℝ)
    (code : CompressionCode u q h s (weightCodeSize (roundingStep θ s u))) :
    compressionDecode L E h s θ code ∈ compressionList L E h s θ :=
  decode_mem_compressionImage _ code

/-- The finite family is nonempty for positive index and label counts. The
rounded-weight alphabet is always nonempty, even at degenerate meshes. -/
theorem compressionList_nonempty
    (L : (i : Fin u) → X → Label i) (E : FixedLabels L q) (h s : ℕ) (θ : ℝ)
    (hu : 0 < u) (hq : 0 < q) : (compressionList L E h s θ).Nonempty :=
  compressionImage_nonempty _ hu hq (weightCodeSize_pos _)

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

/-- The fixed decoded list uniformly approximates every nonnegative mixture
with one-sided errors. -/
theorem compressionList_bounds
    (L : (i : Fin u) → X → Label i) (E : FixedLabels L q)
    (𝒯 : Finset (Finset (Fin u)))
    (hu : 0 < u) (hh : 0 < h) (hs : 0 < s)
    (θ : ℝ) (hθ : 0 < θ) (hsθ : 1 ≤ (s : ℝ) * θ)
    (hprofile : Real.log 3 / Real.log ((h : ℝ) + 1) ≤ θ)
    (hcomp : ∀ T ∈ 𝒯, ((Finset.univ \ T).card : ℝ) ≤ θ * (u : ℝ))
    (μ : GraphProfile.Columns X 𝒯 → ℝ)
    (hμ : ∀ y, 0 ≤ μ y) (hmass : ∑ y, μ y ≤ 1) :
    ∃ a ∈ compressionList L E h s θ, ∀ x,
      columnCombination (GraphProfile.column L 𝒯 h) μ x - 3 * θ ≤ a x ∧
        a x ≤ columnCombination (GraphProfile.column L 𝒯 h) μ x + θ := by
  obtain ⟨code, hc⟩ := exists_compressionCode L E
    (fun y : GraphProfile.Columns X 𝒯 => y.1) (fun y => y.2.val) μ hμ hmass
    hu hh hs θ hθ hsθ hprofile (fun y => hcomp y.2.val y.2.property)
  exact ⟨compressionDecode L E h s θ code,
    compressionDecode_mem_compressionList L E h s θ code, hc⟩

/-- Complete positive compression from the actual partition graph and
logarithmic profile, with a fixed list and the literal finite-code bound. -/
theorem uniform_compression
    (L : (i : Fin u) → X → Label i)
    (hlabels : ∀ i, Nat.card (Set.range (L i)) ≤ q)
    (𝒯 : Finset (Finset (Fin u)))
    (hu : 0 < u) (hq : 0 < q) (hh : 0 < h) (hs : 0 < s)
    (θ : ℝ) (hθ : 0 < θ) (hsθ : 1 ≤ (s : ℝ) * θ)
    (hprofile : Real.log 3 / Real.log ((h : ℝ) + 1) ≤ θ)
    (hcomp : ∀ T ∈ 𝒯, ((Finset.univ \ T).card : ℝ) ≤ θ * (u : ℝ)) :
    ∃ A : Finset (X → ℝ), A.Nonempty ∧
      (A.card : ℝ) ≤ (u : ℝ) * (q : ℝ) ^ (h * s) *
        (1 + (s : ℝ) * 2 ^ u / θ) ^ (h * s * 2 ^ u) ∧
      SignedCompression.PositiveApproximation (GraphProfile.column L 𝒯 h) θ A := by
  let E := FixedLabels.ofCardBound L hlabels
  refine ⟨compressionList L E h s θ,
    compressionList_nonempty L E h s θ hu hq,
    compressionList_card_le L E h s θ hθ hs, ?_⟩
  intro μ hμ hmass
  obtain ⟨a, ha, hb⟩ := compressionList_bounds L E 𝒯 hu hh hs θ hθ hsθ
    hprofile hcomp μ hμ hmass
  refine ⟨a, ha, ?_⟩
  intro x
  have hx := hb x
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end MetricEntropyDuality

end

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality
open scoped BigOperators Classical
open CompressionLevels ProfileMixtures


theorem solution.{uX,uLabel} : type_of% @_root_.OAI.MetricEntropyDuality.uniform_compression.{uX,uLabel} := @_root_.OAI.MetricEntropyDuality.uniform_compression.{uX,uLabel}
