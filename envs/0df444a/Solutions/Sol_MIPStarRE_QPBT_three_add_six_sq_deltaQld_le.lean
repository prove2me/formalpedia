-- Prove2me | solution 1 for MIPStarRE.QPBT.three_add_six_sq_deltaQld_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:49:50.728827+00:00
-- url     : https://prove2.me/submissions/9697c427-128f-4f22-b350-f60cf91f62bf

-- Generated proof for MIPStarRE.QPBT.three_add_six_sq_deltaQld_le.
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

namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/Soundness/ScalarAbsorption.lean. -/
/-!
# Scalar absorption of the Naimark transfer constants

Transferring the Pauli operator distances from a Naimark dilation back to the
original spaces produces bounds of the shape `3 * δ + 6 * δ ^ 2`, where `δ` is
the Pauli soundness error `deltaQld`. This module records the purely scalar
fact that such a combination is again a Pauli soundness error, after enlarging
the universal prefactor. No strategy, measurement, or state content enters
here; the module only depends on `MIPStarRE.QPBT.Test.SoundnessDefs`.

## References

Blueprint `lem:delta-qld-scalar-absorption-support`. The source performs the
same constant bookkeeping inline when it records the error form of
`thm:pauli` at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876`.
The companion constant adjustments are `deltaQld_mono`
(`MIPStarRE/QPBT/Test/SoundnessDefs.lean`) and `sqrt_deltaQld_le`
(`MIPStarRE/QPBT/Combining/RootErrorBounds.lean`).
-/

@[expose] public section

namespace MIPStarRE.QPBT

/-- The Pauli soundness error is nonnegative whenever its prefactor and its
error argument are. The remaining two summands of the error bracket are
`rpow`s of nonnegative bases, so no admissibility hypothesis is needed. -/
theorem deltaQld_nonneg {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {a b epsilon : ℝ}
    (ha : 0 ≤ a) (hepsilon : 0 ≤ epsilon) :
    0 ≤ _root_.MIPStarRE.QPBT.deltaQld a b epsilon P.m P.d P.q := by
  have hdegree0 : (0 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 := Real.rpow_nonneg hepsilon b
  have h2 := Real.rpow_nonneg (Nat.cast_nonneg P.q) (-b)
  have h3 := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    (-(b * ((P.m * P.d : ℕ) : ℝ)))
  unfold _root_.MIPStarRE.QPBT.deltaQld
  simp only [Real.rpow_eq_pow]
  exact mul_nonneg (mul_nonneg ha (Real.rpow_nonneg hdegree0 a)) (by linarith)

/-- The shape of the absorption once the error bracket has been separated:
doubling the `rpow` exponent is dominated by raising it to `21 * a ^ 2`. -/
private theorem rpow_absorb_aux {degree tail a : ℝ}
    (hdegree : 1 ≤ degree) (htail : 0 ≤ tail) (ha : 1 ≤ a) :
    21 * (a * degree ^ a) * (a * degree ^ a * tail) ≤
      21 * a ^ 2 * degree ^ (21 * a ^ 2) * tail := by
  have hdegree0 : (0 : ℝ) < degree := lt_of_lt_of_le zero_lt_one hdegree
  have hexp : a + a ≤ 21 * a ^ 2 := by nlinarith
  have hsplit : degree ^ (a + a) = degree ^ a * degree ^ a :=
    Real.rpow_add hdegree0 a a
  have hpow : degree ^ (a + a) ≤ degree ^ (21 * a ^ 2) :=
    Real.rpow_le_rpow_of_exponent_le hdegree hexp
  have hcoeff : (0 : ℝ) ≤ 21 * a ^ 2 := by positivity
  calc 21 * (a * degree ^ a) * (a * degree ^ a * tail)
      = 21 * a ^ 2 * (degree ^ a * degree ^ a) * tail := by ring
    _ = 21 * a ^ 2 * degree ^ (a + a) * tail := by rw [hsplit]
    _ ≤ 21 * a ^ 2 * degree ^ (21 * a ^ 2) * tail :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow hcoeff) htail



end MIPStarRE.QPBT

/-!
# Scalar absorption of the Naimark transfer constants

Transferring the Pauli operator distances from a Naimark dilation back to the
original spaces produces bounds of the shape `3 * δ + 6 * δ ^ 2`, where `δ` is
the Pauli soundness error `deltaQld`. This module records the purely scalar
fact that such a combination is again a Pauli soundness error, after enlarging
the universal prefactor. No strategy, measurement, or state content enters
here; the module only depends on `MIPStarRE.QPBT.Test.SoundnessDefs`.

## References

Blueprint `lem:delta-qld-scalar-absorption-support`. The source performs the
same constant bookkeeping inline when it records the error form of
`thm:pauli` at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876`.
The companion constant adjustments are `deltaQld_mono`
(`MIPStarRE/QPBT/Test/SoundnessDefs.lean`) and `sqrt_deltaQld_le`
(`MIPStarRE/QPBT/Combining/RootErrorBounds.lean`).
-/



open MIPStarRE.QPBT

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {a b epsilon : ℝ}
    (ha : 1 ≤ a) (hb : 0 < b) (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) :
    3 * _root_.MIPStarRE.QPBT.deltaQld a b epsilon P.m P.d P.q +
        6 * _root_.MIPStarRE.QPBT.deltaQld a b epsilon P.m P.d P.q ^ 2 ≤
      _root_.MIPStarRE.QPBT.deltaQld (21 * a ^ 2) b epsilon P.m P.d P.q := by
  have hdegree : (1 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) :=
    Nat.one_le_cast.mpr (Nat.mul_pos P.one_le_m P.hd)
  have hdegree0 : (0 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) := zero_le_one.trans hdegree
  have hq : (1 : ℝ) ≤ (P.q : ℝ) := by
    obtain ⟨k, -, hk⟩ := P.hq
    rw [hk]
    exact_mod_cast Nat.one_le_pow _ _ (by norm_num)
  have ha0 : (0 : ℝ) ≤ a := zero_le_one.trans ha
  have hprefactor : (1 : ℝ) ≤ a * ((P.m * P.d : ℕ) : ℝ) ^ a :=
    one_le_mul_of_one_le_of_one_le ha (Real.one_le_rpow hdegree ha0)
  have hprefactor0 : (0 : ℝ) ≤ a * ((P.m * P.d : ℕ) : ℝ) ^ a :=
    zero_le_one.trans hprefactor
  -- The error bracket lies in `[0, 3]`: each summand is an `rpow` bounded by
  -- one on the source parameter domain.
  have htail0 : (0 : ℝ) ≤ epsilon ^ b + (P.q : ℝ) ^ (-b) +
      (2 : ℝ) ^ (-(b * ((P.m * P.d : ℕ) : ℝ))) := by
    have h1 := Real.rpow_nonneg hepsilon b
    have h2 := Real.rpow_nonneg (Nat.cast_nonneg P.q) (-b)
    have h3 := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (-(b * ((P.m * P.d : ℕ) : ℝ)))
    linarith
  have htail3 : epsilon ^ b + (P.q : ℝ) ^ (-b) +
      (2 : ℝ) ^ (-(b * ((P.m * P.d : ℕ) : ℝ))) ≤ 3 := by
    have h1 : epsilon ^ b ≤ 1 := Real.rpow_le_one hepsilon hepsilon1 hb.le
    have h2 : (P.q : ℝ) ^ (-b) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hq (neg_nonpos.mpr hb.le)
    have h3 : (2 : ℝ) ^ (-(b * ((P.m * P.d : ℕ) : ℝ))) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
        (neg_nonpos.mpr (mul_nonneg hb.le hdegree0))
    linarith
  have hnonneg : 0 ≤ _root_.MIPStarRE.QPBT.deltaQld a b epsilon P.m P.d P.q :=
    _root_.MIPStarRE.QPBT.deltaQld_nonneg ha0 hepsilon
  have hub : _root_.MIPStarRE.QPBT.deltaQld a b epsilon P.m P.d P.q ≤
      3 * (a * ((P.m * P.d : ℕ) : ℝ) ^ a) := by
    unfold _root_.MIPStarRE.QPBT.deltaQld
    simp only [Real.rpow_eq_pow]
    nlinarith [mul_nonneg hprefactor0 (sub_nonneg.mpr htail3)]
  calc 3 * _root_.MIPStarRE.QPBT.deltaQld a b epsilon P.m P.d P.q +
        6 * _root_.MIPStarRE.QPBT.deltaQld a b epsilon P.m P.d P.q ^ 2
      ≤ 21 * (a * ((P.m * P.d : ℕ) : ℝ) ^ a) *
          _root_.MIPStarRE.QPBT.deltaQld a b epsilon P.m P.d P.q := by
        nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr hub),
          mul_nonneg hnonneg (sub_nonneg.mpr hprefactor)]
    _ ≤ _root_.MIPStarRE.QPBT.deltaQld (21 * a ^ 2) b epsilon P.m P.d P.q := by
        unfold _root_.MIPStarRE.QPBT.deltaQld
        simp only [Real.rpow_eq_pow]
        exact rpow_absorb_aux hdegree htail0 ha
