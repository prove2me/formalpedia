-- Prove2me | solution 1 for MIPStarRE.QPBT.reflection_pair_absorbs_parity_effect
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:04:45.969649+00:00
-- url     : https://prove2.me/submissions/8c513508-dc6c-4cbd-8201-d5c2c723d541

-- Generated proof for MIPStarRE.QPBT.reflection_pair_absorbs_parity_effect.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_PerfectStrategy_Observables

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/MagicSquareTheorems/PerfectStrategy/Observables.lean. -/
/-!
# Observables of the perfect Magic Square strategy

This module builds the operator table of `thm:ms-from-ac`.  It records the EPR
state carried by the perfect strategy, the binary reflection effects attached
to a Hermitian involution, the real Pauli matrices on the auxiliary qubit, and
the nine cell observables together with their Hermiticity, involutivity,
commutation, and constraint-product identities.

## References

The source statement is blueprint
`thm:ms-from-ac`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:654-722`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section































local notation "qubitX" => (_root_.MIPStarRE.QPBT.tauShift (K := ZMod 2) 1)
local notation "qubitZ" => (_root_.MIPStarRE.QPBT.tauPhase (K := ZMod 2) 1)





























private theorem reflectionEffect_commute_obs
    {V : Type*} [Fintype V] [DecidableEq V]
    {O P : _root_.LIDT.MIPStarRE.Quantum.Op V} (hOP : Commute O P) (a : ZMod 2) :
    Commute (_root_.MIPStarRE.QPBT.reflectionEffect O a) P := by
  rw [commute_iff_eq]
  rcases _root_.MIPStarRE.QPBT.zmod_two_eq_zero_or_one a with rfl | rfl <;>
    simp only [_root_.MIPStarRE.QPBT.reflectionEffect, if_pos, if_neg one_ne_zero]
  all_goals rw [smul_mul_assoc, mul_smul_comm]
  all_goals congr 1
  all_goals noncomm_ring [hOP.eq]

private theorem reflectionEffect_mul_obs_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (O : _root_.LIDT.MIPStarRE.Quantum.Op V) (hO : O * O = 1) :
    _root_.MIPStarRE.QPBT.reflectionEffect O 0 * O = _root_.MIPStarRE.QPBT.reflectionEffect O 0 := by
  simp only [_root_.MIPStarRE.QPBT.reflectionEffect, if_pos]
  rw [smul_mul_assoc, add_mul, one_mul, hO]
  module

private theorem reflectionEffect_mul_obs_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (O : _root_.LIDT.MIPStarRE.Quantum.Op V) (hO : O * O = 1) :
    _root_.MIPStarRE.QPBT.reflectionEffect O 1 * O = -_root_.MIPStarRE.QPBT.reflectionEffect O 1 := by
  simp only [_root_.MIPStarRE.QPBT.reflectionEffect, if_neg one_ne_zero]
  rw [smul_mul_assoc, sub_mul, one_mul, hO]
  module

private theorem mul_reflectionEffect_zero_of_eigen_pos
    {V : Type*} [Fintype V] [DecidableEq V]
    (E O : _root_.LIDT.MIPStarRE.Quantum.Op V) (hEO : E * O = E) :
    E * _root_.MIPStarRE.QPBT.reflectionEffect O 0 = E := by
  simp only [_root_.MIPStarRE.QPBT.reflectionEffect, if_pos]
  rw [mul_smul_comm, mul_add, mul_one, hEO]
  module

private theorem mul_reflectionEffect_one_of_eigen_neg
    {V : Type*} [Fintype V] [DecidableEq V]
    (E O : _root_.LIDT.MIPStarRE.Quantum.Op V) (hEO : E * O = -E) :
    E * _root_.MIPStarRE.QPBT.reflectionEffect O 1 = E := by
  simp only [_root_.MIPStarRE.QPBT.reflectionEffect, if_neg one_ne_zero]
  rw [mul_smul_comm, mul_sub, mul_one, hEO]
  module

private theorem reflection_pair_mul_observables
    {V : Type*} [Fintype V]
    (P0 P1 O0 O1 : _root_.LIDT.MIPStarRE.Quantum.Op V) (s0 s1 : ℂ)
    (h10 : Commute P1 O0)
    (h0 : P0 * O0 = s0 • P0) (h1 : P1 * O1 = s1 • P1) :
    (P0 * P1) * (O0 * O1) = (s0 * s1) • (P0 * P1) := by
  calc
    (P0 * P1) * (O0 * O1) = P0 * (P1 * O0) * O1 := by noncomm_ring
    _ = P0 * (O0 * P1) * O1 := by rw [h10.eq]
    _ = (P0 * O0) * (P1 * O1) := by noncomm_ring
    _ = (s0 • P0) * (s1 • P1) := by rw [h0, h1]
    _ = (s0 * s1) • (P0 * P1) := by rw [smul_mul_smul]



end

end MIPStarRE.QPBT

/-!
# Observables of the perfect Magic Square strategy

This module builds the operator table of `thm:ms-from-ac`.  It records the EPR
state carried by the perfect strategy, the binary reflection effects attached
to a Hermitian involution, the real Pauli matrices on the auxiliary qubit, and
the nine cell observables together with their Hermiticity, involutivity,
commutation, and constraint-product identities.

## References

The source statement is blueprint
`thm:ms-from-ac`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:654-722`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

































local notation "qubitX" => (_root_.MIPStarRE.QPBT.tauShift (K := ZMod 2) 1)
local notation "qubitZ" => (_root_.MIPStarRE.QPBT.tauPhase (K := ZMod 2) 1)

theorem solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (O0 O1 O2 : _root_.LIDT.MIPStarRE.Quantum.Op V)
    (hO0 : O0 * O0 = 1) (hO1 : O1 * O1 = 1)
    (h01 : Commute O0 O1)
    (p b0 b1 : ZMod 2)
    (hp : (p = 0 ∧ O0 * O1 * O2 = 1) ∨
      (p = 1 ∧ O0 * O1 * O2 = -1)) :
    (_root_.MIPStarRE.QPBT.reflectionEffect O0 b0 * _root_.MIPStarRE.QPBT.reflectionEffect O1 b1) *
        _root_.MIPStarRE.QPBT.reflectionEffect O2 (p - b0 - b1) =
      _root_.MIPStarRE.QPBT.reflectionEffect O0 b0 * _root_.MIPStarRE.QPBT.reflectionEffect O1 b1 := by
  rcases hp with ⟨rfl, hprod⟩ | ⟨rfl, hprod⟩
  · have hO2eq : O2 = O0 * O1 := by
      calc
        O2 = (O0 * O0) * (O1 * O1) * O2 := by rw [hO0, hO1]; simp
        _ = O0 * (O0 * O1) * O1 * O2 := by noncomm_ring
        _ = O0 * (O1 * O0) * O1 * O2 := by rw [h01.eq]
        _ = O0 * O1 * (O0 * O1 * O2) := by noncomm_ring
        _ = O0 * O1 := by rw [hprod]; simp
    rcases _root_.MIPStarRE.QPBT.zmod_two_eq_zero_or_one b0 with rfl | rfl <;>
      rcases _root_.MIPStarRE.QPBT.zmod_two_eq_zero_or_one b1 with rfl | rfl
    · apply mul_reflectionEffect_zero_of_eigen_pos
      rw [hO2eq]
      simpa using reflection_pair_mul_observables
        (_root_.MIPStarRE.QPBT.reflectionEffect O0 0) (_root_.MIPStarRE.QPBT.reflectionEffect O1 0) O0 O1 1 1
        (reflectionEffect_commute_obs h01.symm 0)
        (by simpa using reflectionEffect_mul_obs_zero O0 hO0)
        (by simpa using reflectionEffect_mul_obs_zero O1 hO1)
    · apply mul_reflectionEffect_one_of_eigen_neg
      rw [hO2eq]
      simpa using reflection_pair_mul_observables
        (_root_.MIPStarRE.QPBT.reflectionEffect O0 0) (_root_.MIPStarRE.QPBT.reflectionEffect O1 1) O0 O1 1 (-1)
        (reflectionEffect_commute_obs h01.symm 1)
        (by simpa using reflectionEffect_mul_obs_zero O0 hO0)
        (by simpa using reflectionEffect_mul_obs_one O1 hO1)
    · apply mul_reflectionEffect_one_of_eigen_neg
      rw [hO2eq]
      simpa using reflection_pair_mul_observables
        (_root_.MIPStarRE.QPBT.reflectionEffect O0 1) (_root_.MIPStarRE.QPBT.reflectionEffect O1 0) O0 O1 (-1) 1
        (reflectionEffect_commute_obs h01.symm 0)
        (by simpa using reflectionEffect_mul_obs_one O0 hO0)
        (by simpa using reflectionEffect_mul_obs_zero O1 hO1)
    · apply mul_reflectionEffect_zero_of_eigen_pos
      rw [hO2eq]
      simpa using reflection_pair_mul_observables
        (_root_.MIPStarRE.QPBT.reflectionEffect O0 1) (_root_.MIPStarRE.QPBT.reflectionEffect O1 1) O0 O1 (-1) (-1)
        (reflectionEffect_commute_obs h01.symm 1)
        (by simpa using reflectionEffect_mul_obs_one O0 hO0)
        (by simpa using reflectionEffect_mul_obs_one O1 hO1)
  · have hO2eq : O2 = -(O0 * O1) := by
      calc
        O2 = (O0 * O0) * (O1 * O1) * O2 := by rw [hO0, hO1]; simp
        _ = O0 * (O0 * O1) * O1 * O2 := by noncomm_ring
        _ = O0 * (O1 * O0) * O1 * O2 := by rw [h01.eq]
        _ = O0 * O1 * (O0 * O1 * O2) := by noncomm_ring
        _ = -(O0 * O1) := by rw [hprod]; simp
    rcases _root_.MIPStarRE.QPBT.zmod_two_eq_zero_or_one b0 with rfl | rfl <;>
      rcases _root_.MIPStarRE.QPBT.zmod_two_eq_zero_or_one b1 with rfl | rfl
    · apply mul_reflectionEffect_one_of_eigen_neg
      rw [hO2eq, mul_neg]
      have hpair := reflection_pair_mul_observables
        (_root_.MIPStarRE.QPBT.reflectionEffect O0 0) (_root_.MIPStarRE.QPBT.reflectionEffect O1 0) O0 O1 1 1
        (reflectionEffect_commute_obs h01.symm 0)
        (by simpa using reflectionEffect_mul_obs_zero O0 hO0)
        (by simpa using reflectionEffect_mul_obs_zero O1 hO1)
      rw [hpair]
      simp
    · apply mul_reflectionEffect_zero_of_eigen_pos
      rw [hO2eq, mul_neg]
      have hpair := reflection_pair_mul_observables
        (_root_.MIPStarRE.QPBT.reflectionEffect O0 0) (_root_.MIPStarRE.QPBT.reflectionEffect O1 1) O0 O1 1 (-1)
        (reflectionEffect_commute_obs h01.symm 1)
        (by simpa using reflectionEffect_mul_obs_zero O0 hO0)
        (by simpa using reflectionEffect_mul_obs_one O1 hO1)
      rw [hpair]
      simp
    · apply mul_reflectionEffect_zero_of_eigen_pos
      rw [hO2eq, mul_neg]
      have hpair := reflection_pair_mul_observables
        (_root_.MIPStarRE.QPBT.reflectionEffect O0 1) (_root_.MIPStarRE.QPBT.reflectionEffect O1 0) O0 O1 (-1) 1
        (reflectionEffect_commute_obs h01.symm 0)
        (by simpa using reflectionEffect_mul_obs_one O0 hO0)
        (by simpa using reflectionEffect_mul_obs_zero O1 hO1)
      rw [hpair]
      simp
    · apply mul_reflectionEffect_one_of_eigen_neg
      rw [hO2eq, mul_neg]
      have hpair := reflection_pair_mul_observables
        (_root_.MIPStarRE.QPBT.reflectionEffect O0 1) (_root_.MIPStarRE.QPBT.reflectionEffect O1 1) O0 O1 (-1) (-1)
        (reflectionEffect_commute_obs h01.symm 1)
        (by simpa using reflectionEffect_mul_obs_one O0 hO0)
        (by simpa using reflectionEffect_mul_obs_one O1 hO1)
      rw [hpair]
      simp
