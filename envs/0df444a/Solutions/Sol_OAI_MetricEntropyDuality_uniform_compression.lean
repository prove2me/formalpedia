-- Prove2me | solution 1 for OAI.MetricEntropyDuality.uniform_compression
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T23:05:46.27808+00:00
-- url     : https://prove2.me/submissions/12216a98-c6f2-4a3f-9c90-89d9ac340e2a

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
import Theorems.Thm_OAI_MetricEntropyDuality_exists_compressionCode
import Theorems.Thm_OAI_MetricEntropyDuality_compressionList_card_le

open OAI OAI.MetricEntropyDuality
universe uX uY uLabel
open scoped BigOperators Classical
open CompressionLevels ProfileMixtures
variable {X : Type uX} {Y : Type uY} [Fintype X] [Nonempty X] [Fintype Y]
variable {u q h s : ℕ} {Label : Fin u → Type uLabel}
lemma h51u_mem {u' q' h' s' N' : ℕ} {E' : Type*} (d : CompressionCode u' q' h' s' N' → E')
    (c : CompressionCode u' q' h' s' N') : d c ∈ compressionImage d := by
  unfold compressionImage
  exact @Finset.mem_image_of_mem _ _ (fun a b => Classical.propDecidable (a = b)) _ _ _ (Finset.mem_univ c)

theorem solution
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
  let E : FixedLabels L q := FixedLabels.ofCardBound L hlabels
  refine ⟨compressionList L E h s θ, ?_, compressionList_card_le L E h s θ hθ hs, ?_⟩
  · have hN : 0 < weightCodeSize (roundingStep θ s u) := by unfold weightCodeSize; omega
    exact ⟨_, h51u_mem (compressionDecode L E h s θ)
      (⟨0, hu⟩, fun _ _ => ⟨0, hq⟩, fun _ _ _ => ⟨0, hN⟩)⟩
  · intro μ hμ hmass
    obtain ⟨code, hcode⟩ := exists_compressionCode (Y := GraphProfile.Columns X 𝒯) L E
      (fun y => y.1) (fun y => y.2.val) μ hμ hmass hu hh hs θ hθ hsθ hprofile
      (fun y => hcomp y.2.val y.2.property)
    refine ⟨compressionDecode L E h s θ code, h51u_mem _ code, ?_⟩
    intro x
    have hcol : columnCombination (GraphProfile.column L 𝒯 h) μ x =
        profileMixture L (fun y => y.1) (fun y => y.2.val) h μ x := rfl
    rw [hcol, abs_le]
    obtain ⟨h1, h2⟩ := hcode x
    constructor <;> linarith

