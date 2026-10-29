-- Prove2me | solution 1 for MIPStarRE.QPBT.anticommProb_ge_of_m_le_q
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:56:25.881325+00:00
-- url     : https://prove2.me/submissions/03ff321f-5a6e-436e-b41c-900febc51d6b

-- Generated proof for MIPStarRE.QPBT.anticommProb_ge_of_m_le_q.
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
import Definitions.Def_QPBT_QPBT_Observables_Anticommuting
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_IsAdmissibleSize_eq_two_or_eight_dvd
import Theorems.Thm_MIPStarRE_QPBT_anticommProb_eq

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.Basis
end MIPStarRE.QPBT.Basis

/- Source helpers from QPBT/Algebra/FieldBasis.lean. -/
/-!
# Finite-field bases and the fixed binary representation

The Pauli basis test uses fields of size `2^k` for odd `k`, together with a
chosen self-dual normal basis over `ZMod 2`.  This file constructs such bases
and records the resulting fixed field model for later proofs.

## References

The declarations correspond to blueprint `def:admissible-size`,
`def:dual-self-dual-normal-basis`, `def:subfields-kappa`, `def:subfield-trace`,
and `def:binary-representation`.
Their paper origin is `references/qpbt-paper/04_preliminaries.tex:433-502,653-728`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT



/-- An admissible field size is at least two, its binary exponent being odd
and therefore positive.  This is a property of blueprint
`def:admissible-size`, paper origin
`references/qpbt-paper/04_preliminaries.tex:662-667`.
-/
theorem IsAdmissibleSize.two_le {q : ℕ} (hq : _root_.MIPStarRE.QPBT.IsAdmissibleSize q) : 2 ≤ q := by
  obtain ⟨k, hk, hqk⟩ := hq
  obtain ⟨j, hj⟩ := hk
  rw [hqk, hj]
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (2 * j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)







/- The characteristic-two self-dual normal-basis construction is carried out
in the group algebra of the finite Galois group.  The transition from a normal
basis to its trace dual is a symmetric unit; odd cardinality makes its square
root unique and symmetric. -/











/-!
The paper fixes the field representation and self-dual normal basis once for
each admissible field size.  We expose that choice through a single global
selector rather than carrying a potentially different model in every game
parameter record.  Existence is a named stage-4.3 proof obligation; the
selector itself is the resulting noncomputable choice.
-/






















end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/Anticommuting.lean. -/
/-!
# Commuting and anticommuting Pauli tuples

This module defines the tuple phase used in the Pauli basis test and the
conditional uniform distributions used by its observable analysis.

## References

The definitions and probability bounds formalize blueprint
`def:anticommuting-tuple` and `fact:omega-anticomm-prob`, with paper origin
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:64-95`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section















/-! ### Auxiliary counting lemmas

The declarations of this section are formalization-only auxiliaries for the
proof of blueprint
`fact:omega-anticomm-prob`. They record the cardinalities used by the
exact computation of the anticommuting probability. -/

















/-! ### The exact anticommuting probability -/





/-- Formalization-only auxiliary: the base `1 - q^{-1}` of the exact
anticommuting probability lies in the unit interval. Blueprint
`fact:omega-anticomm-prob`. -/
private theorem base_mem_unit_interval (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    (0 : ℝ) ≤ 1 - (P.q : ℝ)⁻¹ ∧ (1 : ℝ) - (P.q : ℝ)⁻¹ ≤ 1 := by
  have hq2 : 2 ≤ P.q := P.hq.two_le
  have hqR : (2 : ℝ) ≤ (P.q : ℝ) := by exact_mod_cast hq2
  have hinv : (P.q : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hinv0 : (0 : ℝ) ≤ (P.q : ℝ)⁻¹ := by positivity
  constructor <;> linarith







/-! ### Conditional uniform distributions -/









end

end MIPStarRE.QPBT

/-!
# Commuting and anticommuting Pauli tuples

This module defines the tuple phase used in the Pauli basis test and the
conditional uniform distributions used by its observable analysis.

## References

The definitions and probability bounds formalize blueprint
`def:anticommuting-tuple` and `fact:omega-anticomm-prob`, with paper origin
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:64-95`.
-/



open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

















/-! ### Auxiliary counting lemmas

The declarations of this section are formalization-only auxiliaries for the
proof of blueprint
`fact:omega-anticomm-prob`. They record the cardinalities used by the
exact computation of the anticommuting probability. -/

















/-! ### The exact anticommuting probability -/

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (hmq : P.m ≤ P.q) :
    (2 : ℝ) ^ (-4 : ℤ) ≤ _root_.MIPStarRE.QPBT.anticommProb P := by
  obtain ⟨h0, h1⟩ := base_mem_unit_interval P
  have hq2 : 2 ≤ P.q := P.hq.two_le
  have hqR : (2 : ℝ) ≤ (P.q : ℝ) := by exact_mod_cast hq2
  have hmain : (1 : ℝ) / 8 ≤ (1 - (P.q : ℝ)⁻¹) ^ (P.m + 1) := by
    rcases P.hq.eq_two_or_eight_dvd with hq | hdvd
    · have hm : P.m ≤ 2 := hq ▸ hmq
      have hb : (1 : ℝ) - (P.q : ℝ)⁻¹ = 1 / 2 := by
        rw [hq]
        norm_num
      rw [hb]
      calc (1 : ℝ) / 8 = (1 / 2 : ℝ) ^ 3 := by norm_num
        _ ≤ (1 / 2 : ℝ) ^ (P.m + 1) :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    · obtain ⟨j, hj⟩ := hdvd
      have hj1 : 1 ≤ j := by omega
      have hjR : (P.q : ℝ) = 8 * (j : ℝ) := by
        rw [hj]
        push_cast
        ring
      have hjR0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
      have hbern : (7 : ℝ) / 8 ≤ (1 - (P.q : ℝ)⁻¹) ^ j := by
        have hle : (-2 : ℝ) ≤ -(P.q : ℝ)⁻¹ := by
          have : (0 : ℝ) ≤ (P.q : ℝ)⁻¹ := by positivity
          have h2 : (P.q : ℝ)⁻¹ ≤ 1 := by
            rw [inv_le_one₀ (by linarith)]
            linarith
          linarith
        have hb := one_add_mul_le_pow hle j
        have hrw : (1 : ℝ) + (j : ℝ) * (-(P.q : ℝ)⁻¹) = 7 / 8 := by
          rw [hjR]
          field_simp
          ring
        have hbase : (1 : ℝ) + -(P.q : ℝ)⁻¹ = 1 - (P.q : ℝ)⁻¹ := by ring
        rw [hrw, hbase] at hb
        exact hb
      have hexp : P.m + 1 ≤ 9 * j := by omega
      have hstep : (1 - (P.q : ℝ)⁻¹) ^ (9 * j) ≤ (1 - (P.q : ℝ)⁻¹) ^ (P.m + 1) :=
        pow_le_pow_of_le_one h0 h1 hexp
      have hpow : ((7 : ℝ) / 8) ^ 9 ≤ ((1 - (P.q : ℝ)⁻¹) ^ j) ^ 9 := by
        gcongr
      rw [← pow_mul, mul_comm j 9] at hpow
      have hnum : (1 : ℝ) / 8 ≤ ((7 : ℝ) / 8) ^ 9 := by norm_num
      linarith
  rw [_root_.MIPStarRE.QPBT.anticommProb_eq]
  have hconst : (2 : ℝ) ^ (-4 : ℤ) = 1 / 8 / 2 := by norm_num
  rw [hconst]
  linarith
