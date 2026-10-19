-- Prove2me | solution 1 for MIPStarRE.Quantum.mul_eq_zero_of_nonneg_of_trace_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:38:11.61231+00:00
-- url     : https://prove2.me/submissions/d101c8b6-7a64-43f2-8e72-05a73cef67bb

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/Quantum/FiniteMatrix/TracePairing.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/Quantum/FiniteMatrix/TracePairing.lean (solution of MIPStarRE.Quantum.mul_eq_zero_of_nonneg_of_trace_mul_eq_zero);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Invertible.Defs
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Subsemigroup.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.Invertible
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Nonneg.Basic
import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.SelfAdjoint
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
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.Set.Defs
import Mathlib.Data.SetLike.Basic
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.SetNotation
import Mathlib.Tactic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Field
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
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.UniformSpace.Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPStarRE.Quantum
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise
open WithLp
set_option backward.isDefEq.respectTransparency false
variable {d : Type*} [Fintype d]
attribute [local instance] MIPStarRE.Quantum.instDecidableEq_definitions_1
local instance instNonnegSpectrumClassRealOp_1 : NonnegSpectrumClass ℝ (Op d) :=
  Matrix.instNonnegSpectrumClass (𝕜 := ℂ) (n := d)
end
end MIPStarRE.Quantum

namespace MIPStarRE.Quantum
section
open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise
open WithLp
set_option backward.isDefEq.respectTransparency false
variable {d : Type*} [Fintype d]
attribute [local instance] MIPStarRE.Quantum.instDecidableEq_definitions_1
attribute [local instance] MIPStarRE.Quantum.instNonnegSpectrumClassRealOp_1
noncomputable local instance instNonUnitalContinuousFunctionalCalculusRealOpIsSelfAdjoint_1 : NonUnitalContinuousFunctionalCalculus ℝ (Op d) IsSelfAdjoint :=
  ContinuousFunctionalCalculus.toNonUnital (R := ℝ) (A := Op d) (p := IsSelfAdjoint)
end
end MIPStarRE.Quantum

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPStarRE.Quantum
open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise
open WithLp
set_option backward.isDefEq.respectTransparency false
variable {d : Type*} [Fintype d]
attribute [local instance] MIPStarRE.Quantum.instDecidableEq_definitions_1
attribute [local instance] MIPStarRE.Quantum.instNonnegSpectrumClassRealOp_1
attribute [local instance] MIPStarRE.Quantum.instNonUnitalContinuousFunctionalCalculusRealOpIsSelfAdjoint_1
theorem _root_.solution {A B : Op d}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (htrace : Complex.re (Matrix.trace (A * B)) = 0) :
    A * B = 0 := by
  obtain ⟨Y, hY⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB
  subst B
  rw [Matrix.star_eq_conjTranspose] at htrace ⊢
  have htrace_cycle :
      Matrix.trace (A * (Yᴴ * Y)) = Matrix.trace (Y * A * Yᴴ) := by
    calc
      Matrix.trace (A * (Yᴴ * Y)) = Matrix.trace ((A * Yᴴ) * Y) := by
        simp [Matrix.mul_assoc]
      _ = Matrix.trace (Y * (A * Yᴴ)) := by
        rw [Matrix.trace_mul_comm]
      _ = Matrix.trace (Y * A * Yᴴ) := by
        simp [Matrix.mul_assoc]
  have hYA_nonneg : 0 ≤ Y * A * Yᴴ := by
    simpa [Matrix.star_eq_conjTranspose] using star_right_conjugate_nonneg hA Y
  have hYA_trace_nonneg : (0 : ℂ) ≤ Matrix.trace (Y * A * Yᴴ) :=
    (Matrix.nonneg_iff_posSemidef.mp hYA_nonneg).trace_nonneg
  have hYA_trace_re_zero : Complex.re (Matrix.trace (Y * A * Yᴴ)) = 0 := by
    simpa [htrace_cycle] using htrace
  have hYA_trace_zero : Matrix.trace (Y * A * Yᴴ) = 0 := by
    apply Complex.ext
    · exact hYA_trace_re_zero
    · simpa using (Complex.nonneg_iff.mp hYA_trace_nonneg).2.symm
  have hYA_zero : Y * A * Yᴴ = 0 :=
    (Matrix.PosSemidef.trace_eq_zero_iff
      (Matrix.nonneg_iff_posSemidef.mp hYA_nonneg)).mp hYA_trace_zero
  obtain ⟨X, hX⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA
  subst A
  rw [Matrix.star_eq_conjTranspose] at hYA_zero ⊢
  have hXY : X * Yᴴ = 0 := by
    have hself : (X * Yᴴ)ᴴ * (X * Yᴴ) = 0 := by
      simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc] using hYA_zero
    exact Matrix.conjTranspose_mul_self_eq_zero.mp hself
  calc
    (Xᴴ * X) * (Yᴴ * Y) = Xᴴ * (X * (Yᴴ * Y)) := by
      rw [Matrix.mul_assoc]
    _ = Xᴴ * ((X * Yᴴ) * Y) := by
      simp [Matrix.mul_assoc]
    _ = 0 := by
      rw [hXY, Matrix.zero_mul, Matrix.mul_zero]
end MIPStarRE.Quantum
