-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.point_obs_anticommutator_anticomm_le_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:57:54.391519+00:00
-- url     : https://prove2.me/submissions/37ccf77c-5a86-46f4-8ab4-65e270c71674

-- Generated proof for MIPStarRE.QPBT.WinImplications.point_obs_anticommutator_anticomm_le_explicit.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Support
import Definitions.Def_QPBT_QPBT_Observables_Anticommuting
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Commuting
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_MagicSquare
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_Basic
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_Strategy_value_le_one
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_msVarObs_anticommutator_le
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_obsDist_le_of_consistencyDefect
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_obsOf_conjTranspose_mul_self
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_obs_anticommutator_avg_le
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_pointObs_eq_traceMeas_obs
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_win_magic_square_explicit
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_win_ms_cons_explicit
import Theorems.Thm_MIPStarRE_QPBT_sum_indicatorVec_mul_indicatorVec
import Theorems.Thm_MIPStarRE_QPBT_trace_basis_eq_one_of_selfDual_normal

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.Basis
end MIPStarRE.QPBT.Basis
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

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






-- The finite carrier is part of the fixed source-aligned interface for the binary field model.


-- The finite carrier is part of the fixed source-aligned interface for the binary field model.


/-- Fixed-model specialization of the trace-one assertion in blueprint
`lem:one`, paper `04_preliminaries.tex:730-765`. -/
theorem fixedFieldModel_trace_basis_eq_one {q : ℕ} (F : _root_.MIPStarRE.QPBT.FixedFieldModel q)
    (i : Fin F.basisDim) : Algebra.trace (ZMod 2) F.K (F.basis i) = 1 := by
  apply _root_.MIPStarRE.QPBT.trace_basis_eq_one_of_selfDual_normal F.basisDimOdd F.basis
  · simpa [_root_.MIPStarRE.QPBT.Basis.IsSelfDual, _root_.MIPStarRE.QPBT.IsDualBasisPair] using F.selfDual
  · simpa [_root_.MIPStarRE.QPBT.Basis.IsNormal, ZMod.card] using F.normal











-- The fixed interface supplies decidable basis indices for the multiplication-table calculation.






end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/Defs.lean. -/
/-!
# Typed strategy measurements and point observables

This file fixes a projective, possibly heterogeneous strategy for the Pauli
basis test and extracts the typed measurement families used in the analysis.
Malformed answers are folded into a fixed valid answer, so the extracted
families remain complete measurements. The winning hypothesis bounds their
original wrong-form mass by the rejection probability. `Option` is used only
for the completed line-evaluation classes.

## References

The ambient strategy convention and the observable `W^r(u)` are in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:160-190`,
corresponding to blueprint `def:strategy-observables`. The typed question
and answer forms come from blueprint `def:pauli-question-distribution` and
`def:pauli-win-predicate`, with paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1225`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section







namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}





























-- The support rewrites below elaborate the `Fintype` instance of
-- `PauliEdge × PauliSpace P`, whose nested sigma/sum instance chain exceeds the
-- default recursion depth.
































































/-- The zero-label point observable is the identity by measurement completeness. -/
theorem pointObs_zero (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (side : _root_.MIPStarRE.QPBT.PlayerSide)
    (W : _root_.MIPStarRE.QPBT.PauliKind) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    S.pointObs side W 0 u = 1 := by
  classical
  simpa [_root_.MIPStarRE.QPBT.ProjectiveSetting.pointObs, _root_.MIPStarRE.QPBT.fixedBinTrace, _root_.MIPStarRE.QPBT.phaseSign] using (S.pointMeas side W u).sum_eq_one

/-- The point observable squares to the identity. This is the assertion that
the operator in `def:strategy-observables` has eigenvalues in `{+1,-1}`;
paper `14_analysis_of_the_pauli_basis_test.tex:174-190`, blueprint
`def:strategy-observables`. -/
theorem pointObs_sq_eq_one (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (side : _root_.MIPStarRE.QPBT.PlayerSide)
    (W : _root_.MIPStarRE.QPBT.PauliKind) (r : _root_.MIPStarRE.QPBT.PauliScalar P) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    S.pointObs side W r u * S.pointObs side W r u = 1 := by
  haveI : CharP (_root_.MIPStarRE.QPBT.PauliScalar P) 2 :=
    (Algebra.charP_iff (ZMod 2) (_root_.MIPStarRE.QPBT.PauliScalar P) 2).mp (ZMod.charP 2)
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.pointObs_mul, CharTwo.add_self_eq_zero, _root_.MIPStarRE.QPBT.ProjectiveSetting.pointObs_zero]

/-- The point observable is Hermitian. This is the self-adjoint part of the
observable assertion following `eq:qld-strat-obs`, paper
`14_analysis_of_the_pauli_basis_test.tex:174-190`, blueprint
`def:strategy-observables`. -/
theorem pointObs_isHermitian (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (side : _root_.MIPStarRE.QPBT.PlayerSide)
    (W : _root_.MIPStarRE.QPBT.PauliKind) (r : _root_.MIPStarRE.QPBT.PauliScalar P) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    (S.pointObs side W r u).IsHermitian := by
  classical
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.pointObs, Matrix.IsHermitian]
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Matrix.conjTranspose_smul, _root_.MIPStarRE.QPBT.star_phaseSign]
  rw [(Matrix.nonneg_iff_posSemidef.mp
    ((S.pointMeas side W u).pos a)).isHermitian.eq]

end ProjectiveSetting

end

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

/-- Formalization-only auxiliary: the scalar carrier of an admissible parameter
tuple has characteristic two, since it is an algebra over the two-element
field. Blueprint `fact:omega-anticomm-prob`. -/
private theorem pauliScalar_charTwo (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    CharP (_root_.MIPStarRE.QPBT.PauliScalar P) 2 :=
  (Algebra.charP_iff (ZMod 2) (_root_.MIPStarRE.QPBT.PauliScalar P) 2).mp (ZMod.charP 2)

/-- Formalization-only auxiliary: the scalar carrier of an admissible parameter
tuple has exactly `q` elements. Blueprint
`fact:omega-anticomm-prob`. -/
private theorem card_pauliScalar (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    Fintype.card (_root_.MIPStarRE.QPBT.PauliScalar P) = P.q :=
  @_root_.LIDT.MIPStarRE.LDT.FieldModel.card P.q P.model.toFieldModel

/-- The phase bit of a Pauli tuple is the trace of `r_Z r_X` times the product
of the coordinate sums `1 + u_{X,i} + u_{Z,i}`. This is the closed form of
`γ(ω)` derived in the proof of blueprint
`fact:omega-anticomm-prob`. -/
private theorem gammaValue_eq_trace_prod (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (uX uZ : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (rX rZ : _root_.MIPStarRE.QPBT.PauliScalar P) :
    _root_.MIPStarRE.QPBT.gammaValue P uX uZ rX rZ =
      _root_.MIPStarRE.QPBT.fixedBinTrace P.model (rZ * (rX * ∏ i : Fin P.m, (1 + uX i + uZ i))) := by
  haveI := pauliScalar_charTwo P
  have hprod : (∑ y : _root_.MIPStarRE.QPBT.Cube P.m, _root_.MIPStarRE.QPBT.indicatorVec uX y * _root_.MIPStarRE.QPBT.indicatorVec uZ y)
      = ∏ i : Fin P.m, (1 + uX i + uZ i) :=
    _root_.MIPStarRE.QPBT.sum_indicatorVec_mul_indicatorVec uX uZ
  unfold _root_.MIPStarRE.QPBT.gammaValue
  congr 1
  rw [← hprod]
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- Formalization-only auxiliary: the field trace onto the two-element field
takes each of its two values on exactly half of the scalars. This is the final
step of the proof of blueprint
`fact:omega-anticomm-prob`. -/
private theorem two_mul_card_trace_ne (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    2 * (Finset.univ.filter
        (fun a : _root_.MIPStarRE.QPBT.PauliScalar P => _root_.MIPStarRE.QPBT.fixedBinTrace P.model a ≠ 0)).card = P.q := by
  classical
  haveI := pauliScalar_charTwo P
  have hK := card_pauliScalar P
  have hadd : ∀ a c : _root_.MIPStarRE.QPBT.PauliScalar P,
      _root_.MIPStarRE.QPBT.fixedBinTrace P.model (a + c)
        = _root_.MIPStarRE.QPBT.fixedBinTrace P.model a + _root_.MIPStarRE.QPBT.fixedBinTrace P.model c := by
    intro a c
    simp [_root_.MIPStarRE.QPBT.fixedBinTrace, _root_.MIPStarRE.QPBT.binTrace]
  obtain ⟨b, hb⟩ : ∃ b : _root_.MIPStarRE.QPBT.PauliScalar P, _root_.MIPStarRE.QPBT.fixedBinTrace P.model b = 1 := by
    have hpos : 0 < P.model.basisDim := by
      obtain ⟨j, hj⟩ := P.model.basisDimOdd
      omega
    exact ⟨P.model.basis ⟨0, hpos⟩,
      _root_.MIPStarRE.QPBT.fixedFieldModel_trace_basis_eq_one P.model ⟨0, hpos⟩⟩
  have hbb : b + b = 0 := CharTwo.add_self_eq_zero b
  have himg :
      (Finset.univ.filter
          (fun a : _root_.MIPStarRE.QPBT.PauliScalar P => _root_.MIPStarRE.QPBT.fixedBinTrace P.model a = 0)).image (fun a => a + b)
        = Finset.univ.filter
            (fun a : _root_.MIPStarRE.QPBT.PauliScalar P => ¬ (_root_.MIPStarRE.QPBT.fixedBinTrace P.model a = 0)) := by
    ext a
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨c, hc, rfl⟩
      rw [hadd, hc, hb]
      simp
    · intro ha
      refine ⟨a + b, ?_, ?_⟩
      · rw [hadd, hb]
        have hone : _root_.MIPStarRE.QPBT.fixedBinTrace P.model a = 1 := by
          revert ha
          generalize _root_.MIPStarRE.QPBT.fixedBinTrace P.model a = t
          revert t
          decide
        rw [hone]
        decide
      · rw [add_assoc, hbb, add_zero]
  have hinj : Function.Injective (fun a : _root_.MIPStarRE.QPBT.PauliScalar P => a + b) :=
    fun _ _ h => by simpa using h
  have hcard :
      (Finset.univ.filter (fun a : _root_.MIPStarRE.QPBT.PauliScalar P => _root_.MIPStarRE.QPBT.fixedBinTrace P.model a = 0)).card
        = (Finset.univ.filter
            (fun a : _root_.MIPStarRE.QPBT.PauliScalar P => ¬ (_root_.MIPStarRE.QPBT.fixedBinTrace P.model a = 0))).card := by
    rw [← himg, Finset.card_image_of_injective _ hinj]
  have hsplit :
      (Finset.univ.filter (fun a : _root_.MIPStarRE.QPBT.PauliScalar P => _root_.MIPStarRE.QPBT.fixedBinTrace P.model a = 0)).card
          + (Finset.univ.filter
              (fun a : _root_.MIPStarRE.QPBT.PauliScalar P => ¬ (_root_.MIPStarRE.QPBT.fixedBinTrace P.model a = 0))).card
        = Fintype.card (_root_.MIPStarRE.QPBT.PauliScalar P) :=
    Finset.card_filter_add_card_filter_not _
  rw [hK] at hsplit
  simp only [ne_eq]
  omega



/-- Twice the number of anticommuting tuples is `q^{m+1}(q-1)^{m+1}`. This is
the exact count established in the proof of blueprint
`fact:omega-anticomm-prob`. -/
private theorem two_mul_card_anticommuting (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    2 * (Finset.univ.filter (@_root_.MIPStarRE.QPBT.IsAnticommuting P)).card
      = P.q ^ (P.m + 1) * (P.q - 1) ^ (P.m + 1) := by
  classical
  haveI := pauliScalar_charTwo P
  have h2 : (2 : _root_.MIPStarRE.QPBT.PauliScalar P) = 0 := CharTwo.two_eq_zero
  have hK := card_pauliScalar P
  have htr0 : _root_.MIPStarRE.QPBT.fixedBinTrace P.model 0 = 0 := by
    simp [_root_.MIPStarRE.QPBT.fixedBinTrace, _root_.MIPStarRE.QPBT.binTrace]
  set N := (Finset.univ.filter
    (fun a : _root_.MIPStarRE.QPBT.PauliScalar P => _root_.MIPStarRE.QPBT.fixedBinTrace P.model a ≠ 0)).card with hNdef
  have hN : 2 * N = P.q := two_mul_card_trace_ne P
  -- the innermost sum, over the second scalar coordinate
  have hinner : ∀ c : _root_.MIPStarRE.QPBT.PauliScalar P,
      (∑ r : _root_.MIPStarRE.QPBT.PauliScalar P, if _root_.MIPStarRE.QPBT.fixedBinTrace P.model (r * c) ≠ 0 then (1 : ℕ) else 0)
        = if c = 0 then 0 else N := by
    intro c
    by_cases hc : c = 0
    · subst hc
      simp [htr0]
    · rw [if_neg hc, hNdef, Finset.card_filter]
      exact Fintype.sum_equiv (Equiv.mulRight₀ c hc)
        (fun r => if _root_.MIPStarRE.QPBT.fixedBinTrace P.model (r * c) ≠ 0 then (1 : ℕ) else 0)
        (fun a => if _root_.MIPStarRE.QPBT.fixedBinTrace P.model a ≠ 0 then (1 : ℕ) else 0)
        (fun r => rfl)
  -- the sum over the first scalar coordinate
  have hnzcard :
      (Finset.univ.filter (fun x : _root_.MIPStarRE.QPBT.PauliScalar P => ¬ (x = 0))).card = P.q - 1 := by
    have h1 : (Finset.univ.filter (fun x : _root_.MIPStarRE.QPBT.PauliScalar P => x ≠ 0))
        = Finset.univ.erase 0 := Finset.filter_ne' _ _
    simp only [ne_eq] at h1
    rw [h1, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hK]
  have hmid : ∀ dd : _root_.MIPStarRE.QPBT.PauliScalar P,
      (∑ rX : _root_.MIPStarRE.QPBT.PauliScalar P, if rX * dd = 0 then (0 : ℕ) else N)
        = if dd = 0 then 0 else (P.q - 1) * N := by
    intro dd
    by_cases hd : dd = 0
    · subst hd
      simp
    · rw [if_neg hd]
      have hcong : ∀ rX : _root_.MIPStarRE.QPBT.PauliScalar P,
          (if rX * dd = 0 then (0 : ℕ) else N) = if rX = 0 then 0 else N := by
        intro rX
        by_cases hr : rX = 0
        · simp [hr]
        · rw [if_neg (by simpa using mul_ne_zero hr hd), if_neg hr]
      rw [Finset.sum_congr rfl (fun x _ => hcong x), Finset.sum_ite]
      simp [hnzcard]
  -- the sum over the second point block
  have hDcard : ∀ uX : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P,
      (Finset.univ.filter (fun uZ : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P =>
        ¬ ((∏ i : Fin P.m, (1 + uX i + uZ i)) = 0))).card = (P.q - 1) ^ P.m := by
    intro uX
    have hset : (Finset.univ.filter (fun uZ : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P =>
        ¬ ((∏ i : Fin P.m, (1 + uX i + uZ i)) = 0)))
        = Fintype.piFinset (fun i : Fin P.m => Finset.univ.erase (1 + uX i)) := by
      ext uZ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
        Finset.mem_erase, and_true]
      constructor
      · intro h i hi
        refine h ?_
        refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
        rw [hi]
        linear_combination (1 + uX i) * h2
      · intro h hz
        rw [Finset.prod_eq_zero_iff] at hz
        obtain ⟨i, -, hi⟩ := hz
        exact h i (by linear_combination hi - (1 + uX i) * h2)
    rw [hset, Fintype.card_piFinset]
    simp [Finset.card_erase_of_mem, Finset.card_univ, hK]
  have houter : ∀ uX : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P,
      (∑ uZ : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P,
          if (∏ i : Fin P.m, (1 + uX i + uZ i)) = 0 then (0 : ℕ) else (P.q - 1) * N)
        = (P.q - 1) ^ P.m * ((P.q - 1) * N) := by
    intro uX
    rw [Finset.sum_ite]
    simp [hDcard uX]
  have step1 : ∀ (uX uZ : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (rX : _root_.MIPStarRE.QPBT.PauliScalar P),
      (∑ rZ : _root_.MIPStarRE.QPBT.PauliScalar P,
          if _root_.MIPStarRE.QPBT.IsAnticommuting ((uX, uZ, rX, rZ) : _root_.MIPStarRE.QPBT.PauliTuple P) then (1 : ℕ) else 0)
        = if rX * ∏ i : Fin P.m, (1 + uX i + uZ i) = 0 then 0 else N := by
    intro uX uZ rX
    have hcongr : ∀ rZ : _root_.MIPStarRE.QPBT.PauliScalar P,
        (if _root_.MIPStarRE.QPBT.IsAnticommuting ((uX, uZ, rX, rZ) : _root_.MIPStarRE.QPBT.PauliTuple P) then (1 : ℕ) else 0)
          = if _root_.MIPStarRE.QPBT.fixedBinTrace P.model
              (rZ * (rX * ∏ i : Fin P.m, (1 + uX i + uZ i))) ≠ 0 then 1 else 0 := by
      intro rZ
      have hiff : _root_.MIPStarRE.QPBT.IsAnticommuting ((uX, uZ, rX, rZ) : _root_.MIPStarRE.QPBT.PauliTuple P)
          ↔ _root_.MIPStarRE.QPBT.fixedBinTrace P.model
              (rZ * (rX * ∏ i : Fin P.m, (1 + uX i + uZ i))) ≠ 0 := by
        unfold _root_.MIPStarRE.QPBT.IsAnticommuting
        rw [gammaValue_eq_trace_prod]
      by_cases h : _root_.MIPStarRE.QPBT.fixedBinTrace P.model
          (rZ * (rX * ∏ i : Fin P.m, (1 + uX i + uZ i))) ≠ 0
      · rw [if_pos (hiff.mpr h), if_pos h]
      · rw [if_neg (fun hh => h (hiff.mp hh)), if_neg h]
    rw [Finset.sum_congr rfl (fun x _ => hcongr x), hinner]
  have hcount : (Finset.univ.filter (@_root_.MIPStarRE.QPBT.IsAnticommuting P)).card
      = P.q ^ P.m * ((P.q - 1) ^ P.m * ((P.q - 1) * N)) := by
    rw [Finset.card_filter]
    simp only [Fintype.sum_prod_type]
    calc (∑ uX : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P, ∑ uZ : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P,
            ∑ rX : _root_.MIPStarRE.QPBT.PauliScalar P, ∑ rZ : _root_.MIPStarRE.QPBT.PauliScalar P,
              (if _root_.MIPStarRE.QPBT.IsAnticommuting ((uX, uZ, rX, rZ) : _root_.MIPStarRE.QPBT.PauliTuple P) then (1 : ℕ) else 0))
        = ∑ _uX : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P, (P.q - 1) ^ P.m * ((P.q - 1) * N) := by
          refine Finset.sum_congr rfl fun uX _ => ?_
          rw [← houter uX]
          refine Finset.sum_congr rfl fun uZ _ => ?_
          rw [← hmid (∏ i : Fin P.m, (1 + uX i + uZ i))]
          exact Finset.sum_congr rfl fun rX _ => step1 uX uZ rX
      _ = P.q ^ P.m * ((P.q - 1) ^ P.m * ((P.q - 1) * N)) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
          congr 1
          simp [hK]
  rw [hcount]
  have hexpand : 2 * (P.q ^ P.m * ((P.q - 1) ^ P.m * ((P.q - 1) * N)))
      = P.q ^ P.m * ((P.q - 1) ^ P.m * ((P.q - 1) * (2 * N))) := by ring
  rw [hexpand, hN, pow_succ, pow_succ]
  ring





/-! ### The exact anticommuting probability -/













/-! ### Conditional uniform distributions -/





/-- The anticommuting conditional distribution is probabilistic. This is the
well-formedness companion to the conditional sampling in
blueprint `lem:qld-win-implications`. -/
theorem anticommTupleDist_isProbability (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    (_root_.MIPStarRE.QPBT.anticommTupleDist P).IsProbability := by
  refine _root_.LIDT.MIPStarRE.LDT.Distribution.uniformOnFinset_isProbability _ ?_
  rw [← Finset.card_pos]
  have hq2 : 2 ≤ P.q := P.hq.two_le
  have hcount := two_mul_card_anticommuting P
  have hpos : 0 < P.q ^ (P.m + 1) * (P.q - 1) ^ (P.m + 1) :=
    Nat.mul_pos (pow_pos (by omega) _) (pow_pos (by omega) _)
  omega



end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/WinImplications/AnticommutingObs.lean. -/
/-!
# Approximate anticommutation of the point observables on anticommuting tuples

This module carries out the anticommuting half of the proof of Equation
`eq:pts-obs-commutation` in `lem:qld-win-implications-obs`. The Magic Square
approximate anticommutation of the variable observables is read back from the
projective dilation on which it is proved, and transported to Alice's point
observables through item 7 of `lem:qld-win-implications`.

## References

The declarations support `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:342-362`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-! ## Reading the dilation back on the original space -/













/-! ## The Magic Square anticommutation on the undilated strategy -/













/-! ## Reflections and the product transfer -/











/-! ## From the Magic Square variables to the point observables -/

/-- The signed sum of the effects of a binary measurement is its observable.
Formalization-only support for `lem:povm-to-obs`, blueprint
`ch14_qpbt_observables.tex:365-382`. -/
theorem sum_phaseSign_smul_effect_eq_obsOf {ι : Type*} [Fintype ι]
    [DecidableEq ι] (M : _root_.LIDT.MIPStarRE.Quantum.Measurement (ZMod 2) ι) :
    ∑ b : ZMod 2, _root_.MIPStarRE.QPBT.phaseSign b • M.effect b = _root_.MIPStarRE.QPBT.obsOf M := by
  rw [_root_.MIPStarRE.QPBT.sum_zmod_two, _root_.MIPStarRE.QPBT.obsOf]
  have hzero : _root_.MIPStarRE.QPBT.phaseSign (0 : ZMod 2) = 1 := by simp [_root_.MIPStarRE.QPBT.phaseSign]
  have hone : _root_.MIPStarRE.QPBT.phaseSign (1 : ZMod 2) = -1 := by
    have h : (1 : ZMod 2) ≠ 0 := by decide
    simp [_root_.MIPStarRE.QPBT.phaseSign, h]
  rw [hzero, hone, one_smul, neg_one_smul]
  abel

/-- The strategy point observable is the observable of the trace-coarse-grained
point measurement. This is `def:strategy-observables` read through
`lem:povm-to-obs`, paper
`14_analysis_of_the_pauli_basis_test.tex:174-190`, blueprint
`ch14_qpbt_observables.tex:573-610`. -/
theorem pointObs_eq_obsOf {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (r : _root_.MIPStarRE.QPBT.PauliScalar P) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    S.pointObs side W r u = _root_.MIPStarRE.QPBT.obsOf (S.pointTraceMeas side W u r) := by
  rw [_root_.MIPStarRE.QPBT.WinImplications.pointObs_eq_traceMeas_obs, _root_.MIPStarRE.QPBT.WinImplications.sum_phaseSign_smul_effect_eq_obsOf]

/-- The strategy point observable is a reflection. Paper
`14_analysis_of_the_pauli_basis_test.tex:174-190`, blueprint
`ch14_qpbt_observables.tex:573-610`. -/
theorem pointObs_conjTranspose_mul_self {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (r : _root_.MIPStarRE.QPBT.PauliScalar P) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    (S.pointObs side W r u)ᴴ * S.pointObs side W r u = 1 := by
  rw [(S.pointObs_isHermitian side W r u).eq]
  exact S.pointObs_sq_eq_one side W r u



/-! ## The anticommuting half of the twisted commutation -/

/-- The unit-alphabet operator distance written as an average of squared
state-dependent norms. Formalization-only support for `def:povm-distance`,
blueprint `ch12_qpbt_games.tex:234-241`. -/
theorem opDistSq_eq_avgOver {X ι : Type*} [Fintype X] [DecidableEq X]
    [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (M N : X → _root_.LIDT.MIPStarRE.Quantum.Op ι) (ψ : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.opDistSq μ M N ψ =
      _root_.LIDT.MIPStarRE.LDT.avgOver μ (fun x => ‖_root_.MIPStarRE.QPBT.applyOperatorToState (M x - N x) ψ‖ ^ 2) := by
  unfold _root_.MIPStarRE.QPBT.opDistSq _root_.MIPStarRE.QPBT.opFamilyDistSq
  simp

/-- Every strategy value is at most one. This is an alias of the Games-layer
`MIPStarRE.QPBT.Strategy.value_le_one`, which carries the single proof; the name
is kept here so the existing callers of this layer resolve unchanged.
Formalization-only support for `def:tensor-product-value`, blueprint
`ch12_qpbt_games.tex:71-82`. -/
theorem strategy_value_le_one {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G) : S.value ≤ 1 :=
  _root_.MIPStarRE.QPBT.Strategy.value_le_one S

/-- The Magic Square value defect of a tuple is nonnegative and admissible as
an error parameter for the rigidity input. Formalization-only support for
`eq:qld-implication-ms-anticomm`, paper
`14_analysis_of_the_pauli_basis_test.tex:349-356`. -/
theorem msValueAt_defect_nonneg {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (ω : _root_.MIPStarRE.QPBT.PauliTuple P) :
    0 ≤ 1 - S.msValueAt ω ∧
      1 - (1 - S.msValueAt ω) ≤ (S.msStrategyAt ω).value := by
  have hle := _root_.MIPStarRE.QPBT.WinImplications.strategy_value_le_one (S.msStrategyAt ω)
  have heq : S.msValueAt ω = (S.msStrategyAt ω).value := rfl
  constructor
  · rw [heq]; linarith
  · rw [heq]; linarith

/-- The Magic Square variable observables induced by the test strategy at one
tuple approximately anticommute on Bob's factor, with error the tuple's Magic
Square defect. This is Equation `eq:qld-implication-ms-anticomm` before
averaging, paper `14_analysis_of_the_pauli_basis_test.tex:349-356`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem msVarBitObs_anticommutator_le {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (ω : _root_.MIPStarRE.QPBT.PauliTuple P) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιA)
          (_root_.MIPStarRE.QPBT.obsOf (S.msVarBitMeas .bob 0 ω) * _root_.MIPStarRE.QPBT.obsOf (S.msVarBitMeas .bob 4 ω) +
            _root_.MIPStarRE.QPBT.obsOf (S.msVarBitMeas .bob 4 ω) * _root_.MIPStarRE.QPBT.obsOf (S.msVarBitMeas .bob 0 ω)))
        S.toStrategy.ψ‖ ^ 2 ≤ 1183680 * (1 - S.msValueAt ω) := by
  obtain ⟨hnn, hwin⟩ := _root_.MIPStarRE.QPBT.WinImplications.msValueAt_defect_nonneg S ω
  exact _root_.MIPStarRE.QPBT.WinImplications.msVarObs_anticommutator_le (S.msStrategyAt ω) (1 - S.msValueAt ω) hnn
    hwin





/-- The observable of a binary projective measurement obtained from a strategy
measurement by two postprocessings is a reflection. Formalization-only support
for `eq:qld-implication-ms-anticomm`, blueprint
`lem:qld-win-implications-obs`. -/
theorem msVarBitObs_conjTranspose_mul_self {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (side : _root_.MIPStarRE.QPBT.PlayerSide) (j : Fin 9)
    (ω : _root_.MIPStarRE.QPBT.PauliTuple P) :
    (_root_.MIPStarRE.QPBT.obsOf (S.msVarBitMeas side j ω))ᴴ *
      _root_.MIPStarRE.QPBT.obsOf (S.msVarBitMeas side j ω) = 1 := by
  refine _root_.MIPStarRE.QPBT.WinImplications.obsOf_conjTranspose_mul_self (S.msVarBitMeas side j ω) ?_
  refine _root_.MIPStarRE.QPBT.SandwichProduct.postprocess_isProjective _
    (_root_.MIPStarRE.QPBT.SandwichProduct.postprocess_isProjective _ ?_ _) _
  cases side with
  | alice => exact S.isProjective.1 _
  | bob => exact S.isProjective.2 _

/-- The observable of a trace-coarse-grained point measurement is a
reflection. Paper `14_analysis_of_the_pauli_basis_test.tex:174-190`,
blueprint `ch14_qpbt_observables.tex:573-610`. -/
theorem pointTraceObs_conjTranspose_mul_self {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (r : _root_.MIPStarRE.QPBT.PauliScalar P) :
    (_root_.MIPStarRE.QPBT.obsOf (S.pointTraceMeas side W u r))ᴴ *
      _root_.MIPStarRE.QPBT.obsOf (S.pointTraceMeas side W u r) = 1 := by
  rw [← _root_.MIPStarRE.QPBT.WinImplications.pointObs_eq_obsOf]
  exact _root_.MIPStarRE.QPBT.WinImplications.pointObs_conjTranspose_mul_self S side W r u





end WinImplications

end

end MIPStarRE.QPBT

/-!
# Approximate anticommutation of the point observables on anticommuting tuples

This module carries out the anticommuting half of the proof of Equation
`eq:pts-obs-commutation` in `lem:qld-win-implications-obs`. The Magic Square
approximate anticommutation of the variable observables is read back from the
projective dilation on which it is proved, and transported to Alice's point
observables through item 7 of `lem:qld-win-implications`.

## References

The declarations support `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:342-362`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.WinImplications

/-! ## Reading the dilation back on the original space -/













/-! ## The Magic Square anticommutation on the undilated strategy -/













/-! ## Reflections and the product transfer -/











/-! ## From the Magic Square variables to the point observables -/









/-! ## The anticommuting half of the twisted commutation -/

theorem solution :
    ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε : ℝ) (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε), 0 ≤ ε →
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.anticommTupleDist P) (fun ω =>
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState
          (_root_.MIPStarRE.QPBT.heteroKron (S.pointObs .alice .X ω.2.2.1 ω.1 *
              S.pointObs .alice .Z ω.2.2.2 ω.2.1) (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιB) +
            _root_.MIPStarRE.QPBT.heteroKron (S.pointObs .alice .Z ω.2.2.2 ω.2.1 *
              S.pointObs .alice .X ω.2.2.1 ω.1) (1 : _root_.LIDT.MIPStarRE.Quantum.Op S.toStrategy.ιB))
          S.toStrategy.ψ‖ ^ 2) ≤
        (96 * (16 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ)) +
          3551040 * (16 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ))) * ε := by
  classical
  intro P ε S hε
  simp only [_root_.MIPStarRE.QPBT.WinImplications.pointObs_eq_obsOf]
  have hdist : ∀ W : _root_.MIPStarRE.QPBT.PauliKind,
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.anticommTupleDist P) (fun ω => ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron (ιA := S.toStrategy.ιA) (ιB := S.toStrategy.ιB)
            (_root_.MIPStarRE.QPBT.obsOf (S.pointTraceMeas .alice W (_root_.MIPStarRE.QPBT.WinImplications.selectedTuplePoint W ω)
              (_root_.MIPStarRE.QPBT.WinImplications.selectedTupleScalar W ω))) 1 -
          _root_.MIPStarRE.QPBT.heteroKron (ιA := S.toStrategy.ιA) (ιB := S.toStrategy.ιB) 1
            (_root_.MIPStarRE.QPBT.obsOf (S.msVarBitMeas .bob (_root_.MIPStarRE.QPBT.WinImplications.selectedMsVar W) ω)))
        S.toStrategy.ψ‖ ^ 2) ≤
          4 * ((16 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ)) * ε) := by
    intro W
    have h := _root_.MIPStarRE.QPBT.WinImplications.obsDist_le_of_consistencyDefect
      (ιL := S.toStrategy.ιA) (ιR := S.toStrategy.ιB) (_root_.MIPStarRE.QPBT.anticommTupleDist P)
      (fun ω => S.pointTraceMeas .alice W (_root_.MIPStarRE.QPBT.WinImplications.selectedTuplePoint W ω)
        (_root_.MIPStarRE.QPBT.WinImplications.selectedTupleScalar W ω))
      (fun ω => S.msVarBitMeas .bob (_root_.MIPStarRE.QPBT.WinImplications.selectedMsVar W) ω) S.toStrategy.ψ
      (_root_.MIPStarRE.QPBT.WinImplications.win_ms_cons_explicit P ε S hε W)
    rw [_root_.MIPStarRE.QPBT.WinImplications.opDistSq_eq_avgOver] at h
    exact h
  have hdefect : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.anticommTupleDist P)
      (fun ω => 1 - S.msValueAt ω) ≤
        (16 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ)) * ε := by
    have hprob := _root_.MIPStarRE.QPBT.anticommTupleDist_isProbability P
    have hsplit : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.anticommTupleDist P)
        (fun ω => 1 - S.msValueAt ω) =
        1 - _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.anticommTupleDist P) S.msValueAt := by
      rw [_root_.LIDT.MIPStarRE.LDT.avgOver_sub, _root_.LIDT.MIPStarRE.LDT.avgOver_const_of_isProbability _ hprob]
    rw [hsplit]
    exact le_of_abs_le (_root_.MIPStarRE.QPBT.WinImplications.win_magic_square_explicit P ε S hε)
  have hmsavg : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.anticommTupleDist P) (fun ω =>
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron (ιA := S.toStrategy.ιA) (ιB := S.toStrategy.ιB) 1
          (_root_.MIPStarRE.QPBT.obsOf (S.msVarBitMeas .bob 0 ω) * _root_.MIPStarRE.QPBT.obsOf (S.msVarBitMeas .bob 4 ω) +
            _root_.MIPStarRE.QPBT.obsOf (S.msVarBitMeas .bob 4 ω) *
              _root_.MIPStarRE.QPBT.obsOf (S.msVarBitMeas .bob 0 ω)))
        S.toStrategy.ψ‖ ^ 2) ≤
          1183680 * ((16 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ)) * ε) := by
    calc
      _ ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.anticommTupleDist P)
          (fun ω => 1183680 * (1 - S.msValueAt ω)) :=
        _root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ _ (fun ω => _root_.MIPStarRE.QPBT.WinImplications.msVarBitObs_anticommutator_le S ω)
      _ = 1183680 * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.anticommTupleDist P)
          (fun ω => 1 - S.msValueAt ω) := _root_.LIDT.MIPStarRE.LDT.avgOver_const_mul _ _ _
      _ ≤ 1183680 * ((16 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ)) * ε) :=
        mul_le_mul_of_nonneg_left hdefect (by norm_num)
  have hmain := _root_.MIPStarRE.QPBT.WinImplications.obs_anticommutator_avg_le (ιL := S.toStrategy.ιA)
    (ιR := S.toStrategy.ιB)
    (fun ω => _root_.MIPStarRE.QPBT.obsOf (S.pointTraceMeas .alice .X ω.1 ω.2.2.1))
    (fun ω => _root_.MIPStarRE.QPBT.obsOf (S.pointTraceMeas .alice .Z ω.2.1 ω.2.2.2))
    (fun ω => _root_.MIPStarRE.QPBT.obsOf (S.msVarBitMeas .bob 0 ω))
    (fun ω => _root_.MIPStarRE.QPBT.obsOf (S.msVarBitMeas .bob 4 ω)) S.toStrategy.ψ
    (fun ω => _root_.MIPStarRE.QPBT.WinImplications.pointTraceObs_conjTranspose_mul_self S .alice .X ω.1 ω.2.2.1)
    (fun ω => _root_.MIPStarRE.QPBT.WinImplications.pointTraceObs_conjTranspose_mul_self S .alice .Z ω.2.1 ω.2.2.2)
    (fun ω => _root_.MIPStarRE.QPBT.WinImplications.msVarBitObs_conjTranspose_mul_self S .bob 0 ω)
    (fun ω => _root_.MIPStarRE.QPBT.WinImplications.msVarBitObs_conjTranspose_mul_self S .bob 4 ω)
    (hdist .X) (hdist .Z) hmsavg
  exact le_trans hmain (le_of_eq (by ring))
