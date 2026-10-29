-- Prove2me | solution 1 for MIPStarRE.QPBT.trace_mul_eq_dotProduct_basisCoord
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T20:54:55.245651+00:00
-- url     : https://prove2.me/submissions/9fbfbb48-2bda-492f-89d0-fa9a52fbe141

-- Generated proof for MIPStarRE.QPBT.trace_mul_eq_dotProduct_basisCoord.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-! # Trace and coordinate identities for self-dual bases

Blueprint `lem:downsize_field` and `lem:one`; paper
`references/qpbt-paper/04_preliminaries.tex:505-550,730-767`.
-/



open scoped BigOperators Matrix

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

-- The paper-facing interface fixes `Fintype ι`; its value is needed only for the matrix sum.

theorem solution {F K ι : Type*} [Field F] [Field K]
    [Algebra F K] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F K)
    (hself : _root_.MIPStarRE.QPBT.Basis.IsSelfDual b) (x y : K) :
    Algebra.trace F K (x * y) = dotProduct (b.equivFun x) (b.equivFun y) := by
  have htraceMatrix :
      LinearMap.BilinForm.toMatrix b (Algebra.traceForm F K) = 1 := by
    rw [← Algebra.traceMatrix_of_basis b]
    ext i j
    simpa [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.one_apply] using hself i j
  calc
    Algebra.trace F K (x * y) = Algebra.traceForm F K x y := rfl
    _ = b.repr x ⬝ᵥ
        (LinearMap.BilinForm.toMatrix b (Algebra.traceForm F K)) *ᵥ b.repr y :=
      LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec b
        (Algebra.traceForm F K) x y
    _ = dotProduct (b.equivFun x) (b.equivFun y) := by
      simp [htraceMatrix, Module.Basis.equivFun_apply]
