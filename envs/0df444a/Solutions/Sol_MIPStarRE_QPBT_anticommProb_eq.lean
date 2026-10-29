-- Prove2me | solution 1 for MIPStarRE.QPBT.anticommProb_eq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:52:45.255204+00:00
-- url     : https://prove2.me/submissions/b8870b30-f71c-438a-91b1-b7e96e929f30

-- Generated proof for MIPStarRE.QPBT.anticommProb_eq.
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
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Observables_Anticommuting
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_sum_indicatorVec_mul_indicatorVec
import Theorems.Thm_MIPStarRE_QPBT_trace_basis_eq_one_of_selfDual_normal

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

/-- Formalization-only auxiliary: the number of Pauli tuples. Blueprint
`fact:omega-anticomm-prob`. -/
private theorem card_pauliTuple (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    Fintype.card (_root_.MIPStarRE.QPBT.PauliTuple P) = P.q ^ P.m * (P.q ^ P.m * (P.q * P.q)) := by
  have hK := card_pauliScalar P
  simp [_root_.MIPStarRE.QPBT.PauliTuple, Fintype.card_prod, hK]

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

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    _root_.MIPStarRE.QPBT.anticommProb P = (1 - (P.q : ℝ)⁻¹) ^ (P.m + 1) / 2 := by
  have hq2 : 2 ≤ P.q := P.hq.two_le
  have hqR : (0 : ℝ) < (P.q : ℝ) := by
    have h : 0 < P.q := by omega
    exact_mod_cast h
  have hcast : ((2 * (Finset.univ.filter (@_root_.MIPStarRE.QPBT.IsAnticommuting P)).card : ℕ) : ℝ)
      = ((P.q ^ (P.m + 1) * (P.q - 1) ^ (P.m + 1) : ℕ) : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (two_mul_card_anticommuting P)
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
    Nat.cast_sub (by omega : 1 ≤ P.q), Nat.cast_one, Nat.cast_ofNat] at hcast
  have hval : ((Finset.univ.filter (@_root_.MIPStarRE.QPBT.IsAnticommuting P)).card : ℝ)
      = (P.q : ℝ) ^ (P.m + 1) * ((P.q : ℝ) - 1) ^ (P.m + 1) / 2 := by linarith
  have hbase : (1 : ℝ) - (P.q : ℝ)⁻¹ = ((P.q : ℝ) - 1) / (P.q : ℝ) := by
    field_simp
  rw [_root_.MIPStarRE.QPBT.anticommProb, hval, card_pauliTuple P, hbase, div_pow]
  push_cast
  field_simp
  ring
