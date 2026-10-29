-- Prove2me | solution 1 for MIPStarRE.QPBT.msCellConstraintJoint_mul
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:08:26.974893+00:00
-- url     : https://prove2.me/submissions/d137db53-1cc0-42aa-bd35-82837bc505b6

-- Generated proof for MIPStarRE.QPBT.msCellConstraintJoint_mul.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_PerfectStrategy_Measurements
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_PerfectStrategy_Observables
import Theorems.Thm_MIPStarRE_QPBT_reflection_pair_absorbs_parity_effect

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























/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): the three observables of a Magic Square
constraint multiply to `1` for the five even constraints and to `-1` for the
last one, which is the anticommuting column of the operator table. -/
theorem msConstraintObservable_product
    {V : Type*} [Fintype V] [DecidableEq V]
    (OA OB : _root_.LIDT.MIPStarRE.Quantum.Op V) (hOA : OA * OA = 1) (hOB : OB * OB = 1)
    (hac : OA * OB = -(OB * OA)) (i : Fin 6) :
    _root_.MIPStarRE.QPBT.msCellObservable OA OB (_root_.MIPStarRE.QPBT.msConstraintVars i 0) *
        _root_.MIPStarRE.QPBT.msCellObservable OA OB (_root_.MIPStarRE.QPBT.msConstraintVars i 1) *
    _root_.MIPStarRE.QPBT.msCellObservable OA OB (_root_.MIPStarRE.QPBT.msConstraintVars i 2) =
      if i = 5 then -1 else 1 := by
  have hAB := anti_mul_sq OA OB hOA hOB hac
  have hZX := anti_mul_sq qubitZ qubitX _root_.MIPStarRE.QPBT.binaryTauPhase_sq _root_.MIPStarRE.QPBT.binaryTauShift_sq (by
    rw [_root_.MIPStarRE.QPBT.binaryTauShift_mul_tauPhase]
    simp)
  fin_cases i <;>
    simp [_root_.MIPStarRE.QPBT.msConstraintVars, _root_.MIPStarRE.QPBT.msCellObservable, _root_.MIPStarRE.QPBT.heteroKron_mul, hOA, hOB,
      _root_.MIPStarRE.QPBT.binaryTauShift_sq, _root_.MIPStarRE.QPBT.binaryTauPhase_sq, _root_.MIPStarRE.QPBT.binaryTauShift_mul_tauPhase, hAB, hZX,
      _root_.MIPStarRE.QPBT.heteroKron_neg_left, _root_.MIPStarRE.QPBT.heteroKron_neg_right,
      _root_.MIPStarRE.QPBT.heteroKron_one_one]

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): the two effects of a binary projective
measurement are orthogonal idempotents: their product is the common effect when
the outcomes agree and `0` otherwise. -/
theorem binary_effect_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement (ZMod 2) V)
    (hM : _root_.MIPStarRE.QPBT.Measurement.IsProjective M)
    (a b : ZMod 2) :
    M.effect a * M.effect b = if a = b then M.effect a else 0 := by
  rcases binary_effects_orthogonal M hM with ⟨h01, h10⟩
  rcases _root_.MIPStarRE.QPBT.zmod_two_eq_zero_or_one a with rfl | rfl <;>
    rcases _root_.MIPStarRE.QPBT.zmod_two_eq_zero_or_one b with rfl | rfl <;>
      simp [(hM _).isIdempotentElem.eq, h01, h10]

















end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/MagicSquareTheorems/PerfectStrategy/Measurements.lean. -/
/-!
# Measurements of the perfect Magic Square strategy

This module turns the operator table of `thm:ms-from-ac` into a measurement
family.  It forms the joint measurement of two commuting binary projective
measurements, records the post-processing identities for injective
relabellings, encodes a constraint answer as the parity triple determined by
two freely chosen bits, and assembles the nine cell measurements into the
Magic Square measurement family, closing with the multiplication rule relating
a constraint outcome to the outcomes of its incident variables.

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





private theorem binaryJointMeasurement_mul_first
    {V : Type*} [Fintype V] [DecidableEq V]
    (M N : _root_.LIDT.MIPStarRE.Quantum.Measurement (ZMod 2) V)
    (hM : _root_.MIPStarRE.QPBT.Measurement.IsProjective M)
    (hN : _root_.MIPStarRE.QPBT.Measurement.IsProjective N)
    (hcomm : ∀ a b, Commute (M.effect a) (N.effect b))
    (ab : ZMod 2 × ZMod 2) (b : ZMod 2) :
    (_root_.MIPStarRE.QPBT.binaryJointMeasurement M N hM hN hcomm).effect ab * M.effect b =
      if ab.1 = b then
        (_root_.MIPStarRE.QPBT.binaryJointMeasurement M N hM hN hcomm).effect ab else 0 := by
  change (M.effect ab.1 * N.effect ab.2) * M.effect b =
    if ab.1 = b then M.effect ab.1 * N.effect ab.2 else 0
  calc
    (M.effect ab.1 * N.effect ab.2) * M.effect b =
        M.effect ab.1 * (N.effect ab.2 * M.effect b) := mul_assoc _ _ _
    _ = M.effect ab.1 * (M.effect b * N.effect ab.2) := by
      rw [(hcomm b ab.2).symm.eq]
    _ = (M.effect ab.1 * M.effect b) * N.effect ab.2 :=
      (mul_assoc _ _ _).symm
    _ = _ := by
      rw [_root_.MIPStarRE.QPBT.binary_effect_mul M hM]
      by_cases h : ab.1 = b
      · simp only [if_pos h]
      · simp only [if_neg h, zero_mul]

private theorem binaryJointMeasurement_mul_second
    {V : Type*} [Fintype V] [DecidableEq V]
    (M N : _root_.LIDT.MIPStarRE.Quantum.Measurement (ZMod 2) V)
    (hM : _root_.MIPStarRE.QPBT.Measurement.IsProjective M)
    (hN : _root_.MIPStarRE.QPBT.Measurement.IsProjective N)
    (hcomm : ∀ a b, Commute (M.effect a) (N.effect b))
    (ab : ZMod 2 × ZMod 2) (b : ZMod 2) :
    (_root_.MIPStarRE.QPBT.binaryJointMeasurement M N hM hN hcomm).effect ab * N.effect b =
      if ab.2 = b then
        (_root_.MIPStarRE.QPBT.binaryJointMeasurement M N hM hN hcomm).effect ab else 0 := by
  change (M.effect ab.1 * N.effect ab.2) * N.effect b =
    if ab.2 = b then M.effect ab.1 * N.effect ab.2 else 0
  rw [mul_assoc, _root_.MIPStarRE.QPBT.binary_effect_mul N hN]
  by_cases h : ab.2 = b
  · simp only [if_pos h]
  · simp only [if_neg h, mul_zero]













































private theorem msConstraintObservable_product_parity
    {V : Type*} [Fintype V] [DecidableEq V]
    (OA OB : _root_.LIDT.MIPStarRE.Quantum.Op V) (hOA : OA * OA = 1) (hOB : OB * OB = 1)
    (hac : OA * OB = -(OB * OA)) (i : Fin 6) :
    (_root_.MIPStarRE.QPBT.msParity i = 0 ∧
      _root_.MIPStarRE.QPBT.msCellObservable OA OB (_root_.MIPStarRE.QPBT.msConstraintVars i 0) *
          _root_.MIPStarRE.QPBT.msCellObservable OA OB (_root_.MIPStarRE.QPBT.msConstraintVars i 1) *
          _root_.MIPStarRE.QPBT.msCellObservable OA OB (_root_.MIPStarRE.QPBT.msConstraintVars i 2) = 1) ∨
    (_root_.MIPStarRE.QPBT.msParity i = 1 ∧
      _root_.MIPStarRE.QPBT.msCellObservable OA OB (_root_.MIPStarRE.QPBT.msConstraintVars i 0) *
          _root_.MIPStarRE.QPBT.msCellObservable OA OB (_root_.MIPStarRE.QPBT.msConstraintVars i 1) *
          _root_.MIPStarRE.QPBT.msCellObservable OA OB (_root_.MIPStarRE.QPBT.msConstraintVars i 2) = -1) := by
  have hprod := _root_.MIPStarRE.QPBT.msConstraintObservable_product OA OB hOA hOB hac i
  fin_cases i <;> simpa [_root_.MIPStarRE.QPBT.msParity] using hprod



end

end MIPStarRE.QPBT

/-!
# Measurements of the perfect Magic Square strategy

This module turns the operator table of `thm:ms-from-ac` into a measurement
family.  It forms the joint measurement of two commuting binary projective
measurements, records the post-processing identities for injective
relabellings, encodes a constraint answer as the parity triple determined by
two freely chosen bits, and assembles the nine cell measurements into the
Magic Square measurement family, closing with the multiplication rule relating
a constraint outcome to the outcomes of its incident variables.

## References

The source statement is blueprint
`thm:ms-from-ac`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:654-722`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

theorem solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (OA OB : _root_.LIDT.MIPStarRE.Quantum.Op V) (hOA : OAᴴ = OA) (hOB : OBᴴ = OB)
    (hOA_sq : OA * OA = 1) (hOB_sq : OB * OB = 1)
    (hac : OA * OB = -(OB * OA))
    (i : Fin 6) (k : Fin 3) (ab : ZMod 2 × ZMod 2) (b : ZMod 2) :
    let P := _root_.MIPStarRE.QPBT.msCellMeasurement OA OB hOA hOB hOA_sq hOB_sq hac
    (_root_.MIPStarRE.QPBT.msConstraintJoint P
        (_root_.MIPStarRE.QPBT.msCellMeasurement_projective OA OB hOA hOB hOA_sq hOB_sq hac)
        (fun i k l a b => _root_.MIPStarRE.QPBT.reflectionEffect_commute
          (_root_.MIPStarRE.QPBT.msConstraintObservable_commute OA OB hOA_sq hOB_sq hac i k l) a b)
        i).effect ab * (P (_root_.MIPStarRE.QPBT.msConstraintVars i k)).effect b =
      if _root_.MIPStarRE.QPBT.parityTriple i ab k = b then
        (_root_.MIPStarRE.QPBT.msConstraintJoint P
          (_root_.MIPStarRE.QPBT.msCellMeasurement_projective OA OB hOA hOB hOA_sq hOB_sq hac)
          (fun i k l a b => _root_.MIPStarRE.QPBT.reflectionEffect_commute
            (_root_.MIPStarRE.QPBT.msConstraintObservable_commute OA OB hOA_sq hOB_sq hac i k l) a b)
          i).effect ab else 0 := by
  let P := _root_.MIPStarRE.QPBT.msCellMeasurement OA OB hOA hOB hOA_sq hOB_sq hac
  let hP := _root_.MIPStarRE.QPBT.msCellMeasurement_projective OA OB hOA hOB hOA_sq hOB_sq hac
  let hcomm : ∀ i k l a b,
      Commute ((P (_root_.MIPStarRE.QPBT.msConstraintVars i k)).effect a)
        ((P (_root_.MIPStarRE.QPBT.msConstraintVars i l)).effect b) :=
    fun i k l a b => _root_.MIPStarRE.QPBT.reflectionEffect_commute
      (_root_.MIPStarRE.QPBT.msConstraintObservable_commute OA OB hOA_sq hOB_sq hac i k l) a b
  fin_cases k
  · change
      (_root_.MIPStarRE.QPBT.binaryJointMeasurement (P (_root_.MIPStarRE.QPBT.msConstraintVars i 0)) (P (_root_.MIPStarRE.QPBT.msConstraintVars i 1))
          (hP _) (hP _) (hcomm i 0 1)).effect ab *
          (P (_root_.MIPStarRE.QPBT.msConstraintVars i 0)).effect b =
        if ab.1 = b then
          (_root_.MIPStarRE.QPBT.binaryJointMeasurement (P (_root_.MIPStarRE.QPBT.msConstraintVars i 0)) (P (_root_.MIPStarRE.QPBT.msConstraintVars i 1))
            (hP _) (hP _) (hcomm i 0 1)).effect ab else 0
    exact binaryJointMeasurement_mul_first (P (_root_.MIPStarRE.QPBT.msConstraintVars i 0))
      (P (_root_.MIPStarRE.QPBT.msConstraintVars i 1)) (hP _) (hP _) (hcomm i 0 1) ab b
  · change
      (_root_.MIPStarRE.QPBT.binaryJointMeasurement (P (_root_.MIPStarRE.QPBT.msConstraintVars i 0)) (P (_root_.MIPStarRE.QPBT.msConstraintVars i 1))
          (hP _) (hP _) (hcomm i 0 1)).effect ab *
          (P (_root_.MIPStarRE.QPBT.msConstraintVars i 1)).effect b =
        if ab.2 = b then
          (_root_.MIPStarRE.QPBT.binaryJointMeasurement (P (_root_.MIPStarRE.QPBT.msConstraintVars i 0)) (P (_root_.MIPStarRE.QPBT.msConstraintVars i 1))
            (hP _) (hP _) (hcomm i 0 1)).effect ab else 0
    exact binaryJointMeasurement_mul_second (P (_root_.MIPStarRE.QPBT.msConstraintVars i 0))
      (P (_root_.MIPStarRE.QPBT.msConstraintVars i 1)) (hP _) (hP _) (hcomm i 0 1) ab b
  · change
      (_root_.MIPStarRE.QPBT.reflectionEffect (_root_.MIPStarRE.QPBT.msCellObservable OA OB (_root_.MIPStarRE.QPBT.msConstraintVars i 0)) ab.1 *
          _root_.MIPStarRE.QPBT.reflectionEffect (_root_.MIPStarRE.QPBT.msCellObservable OA OB (_root_.MIPStarRE.QPBT.msConstraintVars i 1)) ab.2) *
          _root_.MIPStarRE.QPBT.reflectionEffect (_root_.MIPStarRE.QPBT.msCellObservable OA OB (_root_.MIPStarRE.QPBT.msConstraintVars i 2)) b =
        if _root_.MIPStarRE.QPBT.msParity i - ab.1 - ab.2 = b then
          _root_.MIPStarRE.QPBT.reflectionEffect (_root_.MIPStarRE.QPBT.msCellObservable OA OB (_root_.MIPStarRE.QPBT.msConstraintVars i 0)) ab.1 *
            _root_.MIPStarRE.QPBT.reflectionEffect (_root_.MIPStarRE.QPBT.msCellObservable OA OB (_root_.MIPStarRE.QPBT.msConstraintVars i 1)) ab.2
        else 0
    by_cases hb : _root_.MIPStarRE.QPBT.msParity i - ab.1 - ab.2 = b
    · rw [if_pos hb]
      subst b
      exact _root_.MIPStarRE.QPBT.reflection_pair_absorbs_parity_effect
        (_root_.MIPStarRE.QPBT.msCellObservable OA OB (_root_.MIPStarRE.QPBT.msConstraintVars i 0))
        (_root_.MIPStarRE.QPBT.msCellObservable OA OB (_root_.MIPStarRE.QPBT.msConstraintVars i 1))
        (_root_.MIPStarRE.QPBT.msCellObservable OA OB (_root_.MIPStarRE.QPBT.msConstraintVars i 2))
        (_root_.MIPStarRE.QPBT.msCellObservable_sq OA OB hOA_sq hOB_sq hac _)
        (_root_.MIPStarRE.QPBT.msCellObservable_sq OA OB hOA_sq hOB_sq hac _)
        (_root_.MIPStarRE.QPBT.msConstraintObservable_commute OA OB hOA_sq hOB_sq hac i 0 1)
        (_root_.MIPStarRE.QPBT.msParity i) ab.1 ab.2
        (msConstraintObservable_product_parity OA OB hOA_sq hOB_sq hac i)
    · rw [if_neg hb]
      have habsorb := _root_.MIPStarRE.QPBT.reflection_pair_absorbs_parity_effect
        (_root_.MIPStarRE.QPBT.msCellObservable OA OB (_root_.MIPStarRE.QPBT.msConstraintVars i 0))
        (_root_.MIPStarRE.QPBT.msCellObservable OA OB (_root_.MIPStarRE.QPBT.msConstraintVars i 1))
        (_root_.MIPStarRE.QPBT.msCellObservable OA OB (_root_.MIPStarRE.QPBT.msConstraintVars i 2))
        (_root_.MIPStarRE.QPBT.msCellObservable_sq OA OB hOA_sq hOB_sq hac _)
        (_root_.MIPStarRE.QPBT.msCellObservable_sq OA OB hOA_sq hOB_sq hac _)
        (_root_.MIPStarRE.QPBT.msConstraintObservable_commute OA OB hOA_sq hOB_sq hac i 0 1)
        (_root_.MIPStarRE.QPBT.msParity i) ab.1 ab.2
        (msConstraintObservable_product_parity OA OB hOA_sq hOB_sq hac i)
      rw [← habsorb, mul_assoc]
      rw [show _root_.MIPStarRE.QPBT.reflectionEffect
          (_root_.MIPStarRE.QPBT.msCellObservable OA OB (_root_.MIPStarRE.QPBT.msConstraintVars i 2))
            (_root_.MIPStarRE.QPBT.msParity i - ab.1 - ab.2) *
          _root_.MIPStarRE.QPBT.reflectionEffect (_root_.MIPStarRE.QPBT.msCellObservable OA OB (_root_.MIPStarRE.QPBT.msConstraintVars i 2)) b = 0 by
        change
          (_root_.MIPStarRE.QPBT.reflectionMeasurement
            (_root_.MIPStarRE.QPBT.msCellObservable OA OB (_root_.MIPStarRE.QPBT.msConstraintVars i 2))
            (_root_.MIPStarRE.QPBT.msCellObservable_conjTranspose OA OB hOA hOB hac _)
            (_root_.MIPStarRE.QPBT.msCellObservable_sq OA OB hOA_sq hOB_sq hac _)).effect
              (_root_.MIPStarRE.QPBT.msParity i - ab.1 - ab.2) *
            (_root_.MIPStarRE.QPBT.reflectionMeasurement
              (_root_.MIPStarRE.QPBT.msCellObservable OA OB (_root_.MIPStarRE.QPBT.msConstraintVars i 2))
              (_root_.MIPStarRE.QPBT.msCellObservable_conjTranspose OA OB hOA hOB hac _)
              (_root_.MIPStarRE.QPBT.msCellObservable_sq OA OB hOA_sq hOB_sq hac _)).effect b = 0
        rw [_root_.MIPStarRE.QPBT.binary_effect_mul
          (_root_.MIPStarRE.QPBT.reflectionMeasurement
            (_root_.MIPStarRE.QPBT.msCellObservable OA OB (_root_.MIPStarRE.QPBT.msConstraintVars i 2))
            (_root_.MIPStarRE.QPBT.msCellObservable_conjTranspose OA OB hOA hOB hac _)
            (_root_.MIPStarRE.QPBT.msCellObservable_sq OA OB hOA_sq hOB_sq hac _))
          (_root_.MIPStarRE.QPBT.reflectionMeasurement_projective
            (_root_.MIPStarRE.QPBT.msCellObservable OA OB (_root_.MIPStarRE.QPBT.msConstraintVars i 2))
            (_root_.MIPStarRE.QPBT.msCellObservable_conjTranspose OA OB hOA hOB hac _)
            (_root_.MIPStarRE.QPBT.msCellObservable_sq OA OB hOA_sq hOB_sq hac _))
          (_root_.MIPStarRE.QPBT.msParity i - ab.1 - ab.2) b]
        simp [hb]]
      simp
