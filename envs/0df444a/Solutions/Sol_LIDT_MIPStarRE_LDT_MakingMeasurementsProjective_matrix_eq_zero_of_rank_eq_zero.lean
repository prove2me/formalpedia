-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.matrix_eq_zero_of_rank_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:53:52.812146+00:00
-- url     : https://prove2.me/submissions/e7b8d369-618c-4d31-8ab6-03cc4e51f648

-- Generated proof for MIPStarRE.LDT.MakingMeasurementsProjective.matrix_eq_zero_of_rank_eq_zero.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Distribution.IsProbability
end LIDT.MIPStarRE.LDT.Distribution.IsProbability
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum.Measurement
end LIDT.MIPStarRE.Quantum.Measurement

/-!
# Public helpers for the upstream LIDT interface

These finite-sum and measurement lemmas support the QPBT without modifying its LIDT dependency.
The marginal-state construction and rank-zero argument adapt the private proofs in
`LionSR/MIPStarRE`, commit `f382c801026f53a9efc260fdee707cb35e0adb15`, module
`MIPStarRE.LDT.MakingMeasurementsProjective.LocalityPreservingRepair`.
The remaining lemmas are QPBT extensions of the upstream measurement and distribution APIs.
Their proofs use the public definitions and Mathlib finite-dimensional linear algebra.
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open LIDT.MIPStarRE.Quantum.Measurement
variable {d : Type*} [Fintype d] [DecidableEq d]
variable {α β : Type*} [Fintype α] [Fintype β]







open LIDT.MIPStarRE.LDT





open LIDT.MIPStarRE.LDT.Distribution.IsProbability






open LIDT.MIPStarRE.LDT.Preliminaries

variable {p : ℕ} [Fact p.Prime]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod p) F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]







open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
open LIDT.MIPStarRE.LDT

theorem solution {m n : Type*}
    [Finite m] [Fintype n] (A : Matrix m n ℂ) (hA : A.rank = 0) :
    A = 0 := by
  let _ : Fintype m := Fintype.ofFinite m
  classical
  have hrange : A.mulVecLin.range = ⊥ := by
    rw [Matrix.rank] at hA
    exact Submodule.finrank_eq_zero.mp hA
  ext i j
  have hv : A.mulVecLin (Pi.single j 1) ∈ A.mulVecLin.range := ⟨Pi.single j 1, rfl⟩
  have hv0 : A.mulVecLin (Pi.single j 1) = 0 := by
    simpa [hrange] using hv
  have hentry := congrArg (fun w => w i) hv0
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Finset.sum_ite_eq,
    Pi.single_apply] using hentry
