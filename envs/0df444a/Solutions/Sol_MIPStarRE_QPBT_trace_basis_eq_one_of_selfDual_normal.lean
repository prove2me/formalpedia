-- Prove2me | solution 1 for MIPStarRE.QPBT.trace_basis_eq_one_of_selfDual_normal
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T20:54:55.238715+00:00
-- url     : https://prove2.me/submissions/d133aa30-ec43-47d2-b98b-d95cb0c3034b

-- Generated proof for MIPStarRE.QPBT.trace_basis_eq_one_of_selfDual_normal.
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

/- Source helpers from QPBT/Algebra/SelfDualBasisTheorems.lean. -/
/-! # Trace and coordinate identities for self-dual bases

Blueprint `lem:downsize_field` and `lem:one`; paper
`references/qpbt-paper/04_preliminaries.tex:505-550,730-767`.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

-- The paper-facing interface fixes `Fintype ι`; its value is needed only for the matrix sum.




/-- The binary Frobenius automorphism preserves the field trace, as used in
`lem:one`, paper `04_preliminaries.tex:739-747`. -/
private theorem trace_sq_eq_trace {K : Type*} [Field K] [Finite K]
    [Algebra (ZMod 2) K] (x : K) :
    Algebra.trace (ZMod 2) K (x ^ 2) = Algebra.trace (ZMod 2) K x := by
  simpa [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ZMod.card] using
    (Algebra.trace_eq_of_algEquiv
      (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K) x)

-- The finite carrier is part of the fixed source-aligned interface for the binary field model.


-- The finite carrier is part of the fixed source-aligned interface for the binary field model.














-- The fixed interface supplies decidable basis indices for the multiplication-table calculation.






end MIPStarRE.QPBT

/-! # Trace and coordinate identities for self-dual bases

Blueprint `lem:downsize_field` and `lem:one`; paper
`references/qpbt-paper/04_preliminaries.tex:505-550,730-767`.
-/



open scoped BigOperators Matrix

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

-- The paper-facing interface fixes `Fintype ι`; its value is needed only for the matrix sum.






-- The finite carrier is part of the fixed source-aligned interface for the binary field model.

set_option linter.unusedFintypeInType false in

theorem solution {K : Type*} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] {k : ℕ} (hk : Odd k)
    (b : Module.Basis (Fin k) (ZMod 2) K)
    (hself : _root_.MIPStarRE.QPBT.Basis.IsSelfDual b) (hnormal : _root_.MIPStarRE.QPBT.Basis.IsNormal b) (i : Fin k) :
    Algebra.trace (ZMod 2) K (b i) = 1 := by
  obtain ⟨α, hα⟩ := hnormal
  have htrace_pow (j : ℕ) :
      Algebra.trace (ZMod 2) K (α ^ (2 ^ j)) = Algebra.trace (ZMod 2) K α := by
    induction j with
    | zero => simp
    | succ j ih =>
        rw [pow_succ, pow_mul, trace_sq_eq_trace, ih]
  let c : ZMod 2 := Algebra.trace (ZMod 2) K α
  have htrace_basis (j : Fin k) : Algebra.trace (ZMod 2) K (b j) = c := by
    rw [hα j]
    simpa [ZMod.card, c] using htrace_pow j.1
  have hc : c ≠ 0 := by
    intro hc
    have htrace_zero (z : K) : Algebra.trace (ZMod 2) K z = 0 := by
      rw [← b.sum_equivFun z, map_sum]
      simp [htrace_basis, hc]
    let i₀ : Fin k := ⟨0, hk.pos⟩
    have h := hself i₀ i₀
    rw [htrace_zero] at h
    simp at h
  have hc_one : c = 1 := by
    exact Fin.eq_one_of_ne_zero c hc
  exact (htrace_basis i).trans hc_one
