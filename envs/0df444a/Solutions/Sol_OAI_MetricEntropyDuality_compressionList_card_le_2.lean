-- Prove2me | solution 2 for OAI.MetricEntropyDuality.compressionList_card_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:19:19.435811+00:00
-- url     : https://prove2.me/submissions/1f68cc95-6e19-465b-9c37-bc7e322d56ee

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/CompressionDecoder.lean:L72-L92
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.compressionList_card_le. The node keeps its source
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

/-- Count the common index, label slots, and subset-weight slots exactly. -/
theorem card_compressionCode (u q h s N : ℕ) :
    Fintype.card (CompressionCode u q h s N) =
      u * q ^ (h * s) * N ^ (h * s * 2 ^ u) := by
  classical
  simp only [CompressionCode, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_finset, Fintype.card_fin]
  simp only [← pow_mul, Nat.mul_assoc, Nat.mul_comm]

section Decode

variable {u q h s N : ℕ} {E : Type uE}

/-- Collisions under decoding can only reduce the number of approximants. -/
theorem card_compressionImage_le_code (decode : CompressionCode u q h s N → E) :
    (compressionImage decode).card ≤ Fintype.card (CompressionCode u q h s N) := by
  classical
  simpa only [compressionImage, Finset.card_univ] using
    (Finset.card_image_le (s := (Finset.univ : Finset (CompressionCode u q h s N)))
      (f := decode))

theorem card_compressionImage_le (decode : CompressionCode u q h s N → E) :
    (compressionImage decode).card ≤ u * q ^ (h * s) * N ^ (h * s * 2 ^ u) := by
  calc
    (compressionImage decode).card ≤ Fintype.card (CompressionCode u q h s N) :=
      card_compressionImage_le_code decode
    _ = u * q ^ (h * s) * N ^ (h * s * 2 ^ u) := card_compressionCode u q h s N

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

/-- The finite integer code count satisfies the real-valued bound used in the
compression estimate. -/
theorem weightCodeSize_le {δ : ℝ} (hδ : 0 < δ) :
    (weightCodeSize δ : ℝ) ≤ 1 + 1 / δ := by
  have hf := Nat.floor_le (div_nonneg (show (0 : ℝ) ≤ 1 by norm_num) hδ.le)
  simp only [weightCodeSize, Nat.cast_add, Nat.cast_one]
  linarith

theorem roundingStep_pos {θ : ℝ} {s u : ℕ} (hθ : 0 < θ) (hs : 0 < s) :
    0 < roundingStep θ s u :=
  div_pos hθ (mul_pos (Nat.cast_pos.mpr hs) (pow_pos (by norm_num) _))

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

/-- First count with the exact integer size of the rounded-weight alphabet. -/
theorem compressionList_card_le_nat
    (L : (i : Fin u) → X → Label i) (E : FixedLabels L q) (h s : ℕ) (θ : ℝ) :
    (compressionList L E h s θ).card ≤
      u * q ^ (h * s) * weightCodeSize (roundingStep θ s u) ^ (h * s * 2 ^ u) :=
  card_compressionImage_le _

/-- The real cardinality bound, with no factor involving the
size of `X`, original pivots, or column centers. -/
theorem compressionList_card_le
    (L : (i : Fin u) → X → Label i) (E : FixedLabels L q) (h s : ℕ) (θ : ℝ)
    (hθ : 0 < θ) (hs : 0 < s) :
    ((compressionList L E h s θ).card : ℝ) ≤
      (u : ℝ) * (q : ℝ) ^ (h * s) *
        (1 + (s : ℝ) * 2 ^ u / θ) ^ (h * s * 2 ^ u) := by
  have hsize : (weightCodeSize (roundingStep θ s u) : ℝ) ≤
      1 + (s : ℝ) * 2 ^ u / θ := by
    simpa only [roundingStep, one_div_div] using
      (weightCodeSize_le (roundingStep_pos (u := u) hθ hs))
  calc
    ((compressionList L E h s θ).card : ℝ) ≤
        (u : ℝ) * (q : ℝ) ^ (h * s) *
          (weightCodeSize (roundingStep θ s u) : ℝ) ^ (h * s * 2 ^ u) := by
      exact_mod_cast compressionList_card_le_nat L E h s θ
    _ ≤ (u : ℝ) * (q : ℝ) ^ (h * s) *
        (1 + (s : ℝ) * 2 ^ u / θ) ^ (h * s * 2 ^ u) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hsize _)
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))

end MetricEntropyDuality

end

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality
open scoped BigOperators


theorem solution.{uX,uLabel} : type_of% @_root_.OAI.MetricEntropyDuality.compressionList_card_le.{uX,uLabel} := @_root_.OAI.MetricEntropyDuality.compressionList_card_le.{uX,uLabel}
