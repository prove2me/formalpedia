-- Prove2me | solution 1 for MIPStarRE.QPBT.deltaQld_mono
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:53:52.617896+00:00
-- url     : https://prove2.me/submissions/3a95feff-f290-4d63-bdbc-816e0378f0c9

-- Generated proof for MIPStarRE.QPBT.deltaQld_mono.
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
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Definitions.Def_QPBT_QPBT_Test_SoundnessDefs
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Pauli basis test soundness interface

This module contains the quantitative error function and the closed definitions
used to state Pauli basis test soundness.  The carriers are concrete
finite-dimensional vectors and matrices so that the soundness proof can use the
existing Hilbert-space API without introducing a dependency cycle.

## References

The interface supports blueprint
`thm:pauli`, with paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
The distance functionals use blueprint `def:state-distance` and
`def:povm-distance`.
-/



open scoped BigOperators Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {a a' b b' ε : ℝ}
    (ha0 : 1 ≤ a) (ha : a ≤ a') (hb : b' ≤ b) (hb' : 0 < b')
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    _root_.MIPStarRE.QPBT.deltaQld a b ε P.m P.d P.q ≤ _root_.MIPStarRE.QPBT.deltaQld a' b' ε P.m P.d P.q := by
  have hmd : (1 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) :=
    Nat.one_le_cast.mpr (Nat.mul_pos P.one_le_m P.hd)
  have hmd0 : (0 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) := by linarith
  have hq : (1 : ℝ) ≤ (P.q : ℝ) := by
    obtain ⟨k, -, hk⟩ := P.hq
    rw [hk]
    exact_mod_cast Nat.one_le_pow _ _ (by norm_num)
  unfold _root_.MIPStarRE.QPBT.deltaQld
  simp only [Real.rpow_eq_pow]
  have h1 : ((P.m * P.d : ℕ) : ℝ) ^ a ≤ ((P.m * P.d : ℕ) : ℝ) ^ a' :=
    Real.rpow_le_rpow_of_exponent_le hmd ha
  have h2 : ε ^ b ≤ ε ^ b' := Real.rpow_le_rpow_of_exponent_ge' hε0 hε1 hb'.le hb
  have h3 : (P.q : ℝ) ^ (-b) ≤ (P.q : ℝ) ^ (-b') :=
    Real.rpow_le_rpow_of_exponent_le hq (neg_le_neg hb)
  have h4 : (2 : ℝ) ^ (-(b * ((P.m * P.d : ℕ) : ℝ))) ≤
      (2 : ℝ) ^ (-(b' * ((P.m * P.d : ℕ) : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (neg_le_neg (mul_le_mul_of_nonneg_right hb hmd0))
  have hsum : 0 ≤ ε ^ b + (P.q : ℝ) ^ (-b) +
      (2 : ℝ) ^ (-(b * ((P.m * P.d : ℕ) : ℝ))) := by
    have := Real.rpow_nonneg hε0 b
    have := Real.rpow_nonneg (Nat.cast_nonneg P.q) (-b)
    have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (-(b * ((P.m * P.d : ℕ) : ℝ)))
    linarith
  exact mul_le_mul (mul_le_mul ha h1 (Real.rpow_nonneg hmd0 a) (by linarith))
    (add_le_add (add_le_add h2 h3) h4) hsum
    (mul_nonneg (by linarith) (Real.rpow_nonneg hmd0 a'))
