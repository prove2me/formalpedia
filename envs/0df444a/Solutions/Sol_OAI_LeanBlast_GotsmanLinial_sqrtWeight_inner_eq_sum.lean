-- Prove2me | solution 1 for OAI.LeanBlast.GotsmanLinial.sqrtWeight_inner_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:17:50.550843+00:00
-- url     : https://prove2.me/submissions/5ad24f9b-6ebf-4858-b3ad-1d1454803b52

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/BlockVanishing.lean:L63-L87
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.GotsmanLinial.sqrtWeight_inner_eq_sum. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_GotsmanLinial
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BinomialMoments
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ScalarIncrements
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_HilbertSchmidt
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ProjectionBlocks
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BlockCoupling
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Commutator
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_CoordinateMultipliers
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Walsh
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_PolynomialDegree
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_SignParity
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_EdgeRecovery
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_WalshDimensions
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_WeightedGrading
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_GradingShift

-- ---- from OAI.Combinatorics.GotsmanLinial.BlockVanishing ----
namespace OAI

/-!
# Vanishing of low antidiagonal blocks

The geometric step is reduced to an explicit finite sum: multiplication on
both sides by the square root of a positive weight turns the weighted pairing
into a Fourier pairing against the signed weight.
-/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace LeanBlast.GotsmanLinial

/-- The finite pairing identity underlying the low antidiagonal cutoff.
The norm and inner product are the counting Euclidean ones. -/
theorem sqrtWeight_inner_eq_sum
    {Ω : Type*} [Fintype Ω]
    (w h : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (D : EuclideanSpace ℂ Ω →ₗ[ℂ] EuclideanSpace ℂ Ω)
    (hD : ∀ a x, D a x = (Real.sqrt (w x) : ℂ) * a x)
    (H : EuclideanSpace ℂ Ω →L[ℂ] EuclideanSpace ℂ Ω)
    (hH : ∀ a x, H a x = (h x : ℂ) * a x)
    (a b : EuclideanSpace ℂ Ω) :
    inner ℂ (D b) (H (D a)) =
      ∑ x, star (b x) * a x * ((w x : ℂ) * (h x : ℂ)) := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro x _
  rw [RCLike.inner_apply', hH, hD, hD]
  calc
    star ((Real.sqrt (w x) : ℂ) * b x) *
        ((h x : ℂ) * ((Real.sqrt (w x) : ℂ) * a x)) =
      star (b x) * a x *
        (((Real.sqrt (w x) : ℂ) * (Real.sqrt (w x) : ℂ)) * (h x : ℂ)) := by
          simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
          ring
    _ = star (b x) * a x * ((w x : ℂ) * (h x : ℂ)) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hw x)]

end LeanBlast.GotsmanLinial

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators ComplexConjugate


theorem solution : type_of% @_root_.OAI.LeanBlast.GotsmanLinial.sqrtWeight_inner_eq_sum := @_root_.OAI.LeanBlast.GotsmanLinial.sqrtWeight_inner_eq_sum
