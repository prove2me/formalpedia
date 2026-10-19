-- Prove2me | solution 1 for MIPStarRE.LDT.Preliminaries.completenessTransferSelfConsistentA
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:53:14.285361+00:00
-- url     : https://prove2.me/submissions/98982b8f-392f-470a-98d4-b0fcb8a42662

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Preliminaries/SelfConsistency/Extensions.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/SelfConsistency/Extensions.lean (solution of MIPStarRE.LDT.Preliminaries.completenessTransferSelfConsistentA);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Invertible.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Subsemigroup.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.Invertible
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.IsBotOne
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.NatCast
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Nonneg.Basic
import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finset.Attach
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Prod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.Set.Defs
import Mathlib.Data.SetLike.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.IsEmpty.Basic
import Mathlib.Logic.IsEmpty.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Logic.Unique
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.MinMax
import Mathlib.Order.Nat
import Mathlib.Order.Notation
import Mathlib.Order.RelClasses
import Mathlib.Order.SetNotation
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Continuous
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.UniformSpace.Defs
import Mathlib.Topology.UniformSpace.Real
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ConsistencyBridges
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_avgOver_abs_le_sqrt_of_pointwise
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_bipartiteSSC_implies_localSSC_liftLeft
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_question_overlap_gap_left
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_question_overlap_gap_right
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_subMeas_diagMass_le_mass
import Theorems.Thm_MIPStarRE_LDT_avgOver_mono
import Theorems.Thm_MIPStarRE_LDT_avgOver_nonneg
import Theorems.Thm_MIPStarRE_LDT_qSDD_nonneg

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.LDT.Preliminaries
open scoped BigOperators MatrixOrder Matrix ComplexOrder
open MIPStarRE.LDT
set_option backward.isDefEq.respectTransparency false
theorem _root_.solution
    {Question Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hperm : PermInvState ψ)
    (hψ : ψ.IsNormalized)
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : IdxSubMeas Question Outcome ι) (δ ε : Error) :
    BipartiteSSCRel ψ 𝒟 A δ →
    SDDRel ψ 𝒟 (IdxSubMeas.liftLeft A) (IdxSubMeas.liftLeft B) ε →
      idxSubMeasMass ψ 𝒟 (IdxSubMeas.liftLeft B) ≥
        idxSubMeasMass ψ 𝒟 (IdxSubMeas.liftLeft A) - δ - 2 * Real.sqrt ε := by
  intro hssc ⟨hε⟩
  have hlocalSSC :
      SSCRel ψ 𝒟 (IdxSubMeas.liftLeft A) δ :=
    bipartiteSSC_implies_localSSC_liftLeft ψ hperm 𝒟 A δ hssc
  rcases hlocalSSC with ⟨hδ⟩
  let diagA : Question → Error := fun q =>
    ∑ a : Outcome,
      ev ψ
        (((IdxSubMeas.liftLeft A) q).outcome a *
          ((IdxSubMeas.liftLeft A) q).outcome a)
  let defectA : Question → Error := fun q =>
    subMeasMass ψ ((IdxSubMeas.liftLeft A) q) - diagA q
  have hdefectA_avg :
      avgOver 𝒟 defectA ≤ δ := by
    calc
      avgOver 𝒟 defectA
        ≤ avgOver 𝒟 (fun q => qSSCDefect ψ ((IdxSubMeas.liftLeft A) q)) := by
            apply avgOver_mono
            intro q
            exact le_max_right 0 (defectA q)
      _ = sscError ψ 𝒟 (IdxSubMeas.liftLeft A) := by
            simp [sscError, qSSCDefect]
      _ ≤ δ := hδ
  let sdd : Question → Error := fun q =>
    qSDD ψ ((IdxSubMeas.liftLeft A) q) ((IdxSubMeas.liftLeft B) q)
  let gap : Question → Error := fun q =>
    diagA q - subMeasMass ψ ((IdxSubMeas.liftLeft B) q)
  have hgap_pointwise : ∀ q, gap q ≤ 2 * Real.sqrt (sdd q) := by
    intro q
    let diagB : Error :=
      ∑ a : Outcome,
        ev ψ
          (((IdxSubMeas.liftLeft B) q).outcome a *
            ((IdxSubMeas.liftLeft B) q).outcome a)
    let overlap : Error :=
      ∑ a : Outcome,
        ev ψ
          (((IdxSubMeas.liftLeft A) q).outcome a *
            ((IdxSubMeas.liftLeft B) q).outcome a)
    have hdiagB_le_massB :
        diagB ≤ subMeasMass ψ ((IdxSubMeas.liftLeft B) q) := by
      simpa [diagB, subMeasMass] using
        subMeas_diagMass_le_mass ψ ((IdxSubMeas.liftLeft B) q)
    have hgap_left_raw :
        |diagA q - overlap| ≤ Real.sqrt (sdd q) := by
      simpa [diagA, overlap, sdd] using
        question_overlap_gap_left ψ hψ
          ((IdxSubMeas.liftLeft A) q) ((IdxSubMeas.liftLeft B) q)
    have hgap_left :
        diagA q - overlap ≤ Real.sqrt (sdd q) := by
      linarith [abs_le.mp hgap_left_raw]
    have hgap_right_raw :
        |overlap - diagB| ≤ Real.sqrt (sdd q) := by
      simpa [diagB, overlap, sdd] using
        question_overlap_gap_right ψ hψ
          ((IdxSubMeas.liftLeft A) q) ((IdxSubMeas.liftLeft B) q)
    have hgap_right :
        overlap - diagB ≤ Real.sqrt (sdd q) := by
      linarith [abs_le.mp hgap_right_raw]
    have hdiag_gap :
        diagA q - diagB ≤ 2 * Real.sqrt (sdd q) := by
      linarith
    have hmass_gap :
        gap q ≤ diagA q - diagB := by
      dsimp [gap]
      exact sub_le_sub_left hdiagB_le_massB _
    exact le_trans hmass_gap hdiag_gap
  have hgap_avg :
      avgOver 𝒟 gap ≤ avgOver 𝒟 (fun q => 2 * Real.sqrt (sdd q)) := by
    unfold avgOver
    refine Finset.sum_le_sum ?_
    intro q hq
    exact mul_le_mul_of_nonneg_left (hgap_pointwise q) (𝒟.nonnegative q)
  have hsqrt_avg_abs :
      |avgOver 𝒟 (fun q => Real.sqrt (sdd q))| ≤
        Real.sqrt (avgOver 𝒟 sdd) := by
    exact
      avgOver_abs_le_sqrt_of_pointwise 𝒟
        (fun q => Real.sqrt (sdd q))
        sdd
        (by
          intro q
          rw [abs_of_nonneg (Real.sqrt_nonneg _)])
        (by
          intro q
          exact qSDD_nonneg ψ ((IdxSubMeas.liftLeft A) q) ((IdxSubMeas.liftLeft B) q))
        h𝒟
  have hsqrt_avg_nonneg :
      0 ≤ avgOver 𝒟 (fun q => Real.sqrt (sdd q)) :=
    avgOver_nonneg 𝒟 _ fun q => Real.sqrt_nonneg _
  have hsqrt_avg :
      avgOver 𝒟 (fun q => Real.sqrt (sdd q)) ≤
        Real.sqrt (avgOver 𝒟 sdd) := by
    simpa [abs_of_nonneg hsqrt_avg_nonneg] using hsqrt_avg_abs
  have hscale_avg :
      avgOver 𝒟 (fun q => 2 * Real.sqrt (sdd q)) =
        2 * avgOver 𝒟 (fun q => Real.sqrt (sdd q)) := by
    unfold avgOver
    calc
      ∑ q ∈ 𝒟.support, 𝒟.weight q * (2 * Real.sqrt (sdd q))
        = ∑ q ∈ 𝒟.support, 2 * (𝒟.weight q * Real.sqrt (sdd q)) := by
            refine Finset.sum_congr rfl ?_
            intro q hq
            ring
      _ = 2 * ∑ q ∈ 𝒟.support, 𝒟.weight q * Real.sqrt (sdd q) := by
            rw [← Finset.mul_sum]
  have hsdd_sqrt :
      avgOver 𝒟 (fun q => 2 * Real.sqrt (sdd q)) ≤
        2 * Real.sqrt (sddError ψ 𝒟 (IdxSubMeas.liftLeft A) (IdxSubMeas.liftLeft B)) := by
    rw [hscale_avg]
    calc
      2 * avgOver 𝒟 (fun q => Real.sqrt (sdd q))
        ≤ 2 * Real.sqrt (avgOver 𝒟 sdd) := by
            exact mul_le_mul_of_nonneg_left hsqrt_avg (by positivity)
      _ = 2 * Real.sqrt (sddError ψ 𝒟 (IdxSubMeas.liftLeft A) (IdxSubMeas.liftLeft B)) := by
            simp [sddError, sdd]
  have hsqrt_ε :
      Real.sqrt (sddError ψ 𝒟 (IdxSubMeas.liftLeft A) (IdxSubMeas.liftLeft B)) ≤
        Real.sqrt ε := by
    exact Real.sqrt_le_sqrt hε
  have hgap_total :
      avgOver 𝒟 gap ≤ 2 * Real.sqrt ε := by
    calc
      avgOver 𝒟 gap
        ≤ avgOver 𝒟 (fun q => 2 * Real.sqrt (sdd q)) := hgap_avg
      _ ≤
          2 * Real.sqrt
            (sddError ψ 𝒟 (IdxSubMeas.liftLeft A) (IdxSubMeas.liftLeft B)) := by
            exact hsdd_sqrt
      _ ≤ 2 * Real.sqrt ε := by
            exact mul_le_mul_of_nonneg_left hsqrt_ε (by positivity)
  have hsplit :
      idxSubMeasMass ψ 𝒟 (IdxSubMeas.liftLeft A) -
          idxSubMeasMass ψ 𝒟 (IdxSubMeas.liftLeft B) =
        avgOver 𝒟 defectA + avgOver 𝒟 gap := by
    unfold idxSubMeasMass subMeasMass avgOver defectA gap diagA
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro q hq
    simp [subMeasMass]
    ring
  have hfinal :
      idxSubMeasMass ψ 𝒟 (IdxSubMeas.liftLeft A) -
          idxSubMeasMass ψ 𝒟 (IdxSubMeas.liftLeft B) ≤
        δ + 2 * Real.sqrt ε := by
    rw [hsplit]
    linarith
  linarith
end MIPStarRE.LDT.Preliminaries
