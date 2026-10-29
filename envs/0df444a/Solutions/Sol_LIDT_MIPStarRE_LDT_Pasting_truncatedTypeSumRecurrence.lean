-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSumRecurrence
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:01:56.602006+00:00
-- url     : https://prove2.me/submissions/31c7410f-16f0-46af-95b6-27167c93388a

-- Generated proof for MIPStarRE.LDT.Pasting.truncatedTypeSumRecurrence.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib

open scoped _root_.Matrix

namespace LIDT.MIPStarRE.LDT.Pasting
end LIDT.MIPStarRE.LDT.Pasting

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Pasting/Bernoulli/TruncatedSums.lean. -/
/-!
# Section 12 pasting: Bernoulli truncated sums

Truncated type sums and their one-step recurrence.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Bernoulli recurrence weights -/

private lemma gHatTypeWeight_le {k : ℕ} (τ : GHatType k) :
    gHatTypeWeight τ ≤ k := by
  unfold gHatTypeWeight
  simpa using (Finset.card_filter_le
    (s := (Finset.univ : Finset (Fin k)))
    (p := fun i : Fin k => τ i))

private lemma gHatTypeWeight_prepend_true {k : ℕ} (τ : GHatType k) :
    gHatTypeWeight (prependTypeBit true τ) = gHatTypeWeight τ + 1 := by
  unfold gHatTypeWeight
  rw [Fin.card_filter_univ_succ]
  simp [prependTypeBit, Fin.cons_zero, Fin.cons_succ, add_comm]

private lemma gHatTypeWeight_prepend_false {k : ℕ} (τ : GHatType k) :
    gHatTypeWeight (prependTypeBit false τ) = gHatTypeWeight τ := by
  unfold gHatTypeWeight
  rw [Fin.card_filter_univ_succ]
  simp [prependTypeBit, Fin.cons_zero, Fin.cons_succ]

private lemma gHatTypeOperator_nonneg
    (G : MIPStarRE.Quantum.Op ι)
    (hGpsd : 0 ≤ G)
    (hGleOne : G ≤ 1)
    {k : ℕ} (τ : GHatType k) :
    0 ≤ gHatTypeOperator G τ := by
  have hcomm : Commute G (1 - G) :=
    (Commute.one_right G).sub_right (Commute.refl G)
  have hGpow : 0 ≤ G ^ gHatTypeWeight τ := by
    exact (Matrix.PosSemidef.pow (Matrix.nonneg_iff_posSemidef.mp hGpsd) _).nonneg
  have hIGpow : 0 ≤ (1 - G) ^ (k - gHatTypeWeight τ) := by
    exact
      (Matrix.PosSemidef.pow
        (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hGleOne)) _).nonneg
  have hcommPow : Commute (G ^ gHatTypeWeight τ) ((1 - G) ^ (k - gHatTypeWeight τ)) :=
    (hcomm.pow_left _).pow_right _
  exact Commute.mul_nonneg hGpow hIGpow hcommPow

private lemma gHatTypeOperator_prepend_true
    (G : MIPStarRE.Quantum.Op ι)
    {k : ℕ} (τ : GHatType k) :
    gHatTypeOperator G (prependTypeBit true τ) = gHatTypeOperator G τ * G := by
  have hcomm : Commute G (1 - G) :=
    (Commute.one_right G).sub_right (Commute.refl G)
  have hsub : k + 1 - (gHatTypeWeight τ + 1) = k - gHatTypeWeight τ := by
    have hweight_le : gHatTypeWeight τ ≤ k := gHatTypeWeight_le τ
    omega
  unfold gHatTypeOperator
  rw [gHatTypeWeight_prepend_true, hsub, pow_succ]
  calc
    (G ^ gHatTypeWeight τ * G) * (1 - G) ^ (k - gHatTypeWeight τ)
      = G ^ gHatTypeWeight τ * (G * (1 - G) ^ (k - gHatTypeWeight τ)) := by
          simp [mul_assoc]
    _ = G ^ gHatTypeWeight τ * ((1 - G) ^ (k - gHatTypeWeight τ) * G) := by
          rw [(hcomm.pow_right _).eq]
    _ = (G ^ gHatTypeWeight τ * (1 - G) ^ (k - gHatTypeWeight τ)) * G := by
          simp [mul_assoc]

private lemma gHatTypeOperator_prepend_false
    (G : MIPStarRE.Quantum.Op ι)
    {k : ℕ} (τ : GHatType k) :
    gHatTypeOperator G (prependTypeBit false τ) = gHatTypeOperator G τ * (1 - G) := by
  have hsub : k + 1 - gHatTypeWeight τ = k - gHatTypeWeight τ + 1 := by
    have hweight_le : gHatTypeWeight τ ≤ k := gHatTypeWeight_le τ
    omega
  unfold gHatTypeOperator
  rw [gHatTypeWeight_prepend_false, hsub, pow_succ]
  simp [mul_assoc]









/-- The full sum of type operators equals the identity.

This is the commuting binomial expansion
`∑ τ : GHatType k, G ^ |τ| * (1 - G) ^ (k - |τ|) = (G + (1 - G))^k = 1`. -/
private lemma full_gHatType_sum_eq_one
    (G : MIPStarRE.Quantum.Op ι) :
    ∀ prefixLen : ℕ, ∑ τprefix : GHatType prefixLen, gHatTypeOperator G τprefix = 1
  | 0 => by
      simp [gHatTypeOperator, gHatTypeWeight]
  | prefixLen + 1 => by
      have hsplit :
          (∑ τprefix : GHatType (prefixLen + 1),
              gHatTypeOperator G τprefix) =
            ∑ p : Bool × GHatType prefixLen,
              gHatTypeOperator G (Fin.cons p.1 p.2) := by
        exact (Fintype.sum_equiv
          ((Fin.consEquiv (fun _ : Fin (prefixLen + 1) => Bool)).symm)
          (fun τprefix => gHatTypeOperator G τprefix)
          (fun p => gHatTypeOperator G (Fin.cons p.1 p.2))
          (by
            intro τprefix
            simp))
      have hprod :
          (∑ p : Bool × GHatType prefixLen,
              gHatTypeOperator G (Fin.cons p.1 p.2)) =
            ∑ b : Bool,
              ∑ τprefix : GHatType prefixLen,
                gHatTypeOperator G (Fin.cons b τprefix) := by
        simpa using
          (Fintype.sum_prod_type'
            (f := fun b τprefix => gHatTypeOperator G (Fin.cons b τprefix)))
      calc
        ∑ τprefix : GHatType (prefixLen + 1), gHatTypeOperator G τprefix
          = ∑ p : Bool × GHatType prefixLen,
              gHatTypeOperator G (Fin.cons p.1 p.2) := hsplit
        _ = ∑ b : Bool,
              ∑ τprefix : GHatType prefixLen,
                gHatTypeOperator G (Fin.cons b τprefix) := hprod
        _ =
            (∑ τprefix : GHatType prefixLen,
              gHatTypeOperator G (Fin.cons true τprefix)) +
              ∑ τprefix : GHatType prefixLen,
                gHatTypeOperator G (Fin.cons false τprefix) := by
                rw [Fintype.sum_bool]
        _ =
            (∑ τprefix : GHatType prefixLen,
              gHatTypeOperator G (prependTypeBit true τprefix)) +
              ∑ τprefix : GHatType prefixLen,
                gHatTypeOperator G (prependTypeBit false τprefix) := by
                simp [prependTypeBit]
        _ =
            (∑ τprefix : GHatType prefixLen, gHatTypeOperator G τprefix * G) +
              ∑ τprefix : GHatType prefixLen,
                gHatTypeOperator G τprefix * (1 - G) := by
                simp_rw [gHatTypeOperator_prepend_true, gHatTypeOperator_prepend_false]
        _ =
            (∑ τprefix : GHatType prefixLen, gHatTypeOperator G τprefix) * G +
              (∑ τprefix : GHatType prefixLen,
                gHatTypeOperator G τprefix) * (1 - G) := by
                rw [Finset.sum_mul, Finset.sum_mul]
        _ = 1 * G + 1 * (1 - G) := by
              simp [full_gHatType_sum_eq_one G prefixLen]
        _ = 1 := by
              have hcancel : G + (1 - G) = (1 : MIPStarRE.Quantum.Op ι) := by
                abel
              rw [one_mul, one_mul]
              exact hcancel



end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Section 12 pasting: Bernoulli truncated sums

Truncated type sums and their one-step recurrence.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Bernoulli recurrence weights -/

theorem solution
    (G : _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (hGpsd : 0 ≤ G)
    (hGleOne : G ≤ 1)
    (d prefixLen : ℕ)
    {tailLen : ℕ} (τtail : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType tailLen) :
    (_root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d prefixLen τtail)ᴴ = _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d prefixLen τtail ∧
      0 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d prefixLen τtail ∧
      _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d prefixLen τtail ≤ 1 ∧
      _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d (prefixLen + 1) τtail =
        _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d prefixLen (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit true τtail) * G +
          _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d prefixLen (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit false τtail) * (1 - G) := by
  /-
  Paper reference: `references/ldt-paper/ld-pasting.tex`,
  `lem:truncated-type-sum-recurrence`.
  The proof is the commuting-polynomial argument in `G` and `I - G`.
  -/
  have hnonneg :
      0 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d prefixLen τtail := by
    unfold _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums
    refine Finset.sum_nonneg ?_
    intro τprefix _
    split_ifs with hcond
    · exact gHatTypeOperator_nonneg G hGpsd hGleOne τprefix
    · simp
  have hle_one :
      _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d prefixLen τtail ≤ 1 := by
    calc
      _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d prefixLen τtail
        ≤ ∑ τprefix : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType prefixLen, _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeOperator G τprefix := by
            unfold _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums
            refine Finset.sum_le_sum ?_
            intro τprefix _
            split_ifs with hcond
            · exact le_rfl
            · exact gHatTypeOperator_nonneg G hGpsd hGleOne τprefix
      _ = 1 := full_gHatType_sum_eq_one G prefixLen
  have hherm :
      (_root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d prefixLen τtail)ᴴ = _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d prefixLen τtail := by
    exact (Matrix.nonneg_iff_posSemidef.mp hnonneg).isHermitian.eq
  have hsplit :
      _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d (prefixLen + 1) τtail =
        ∑ p : Bool × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType prefixLen,
          if d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight (Fin.cons p.1 p.2) + _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τtail then
            _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeOperator G (Fin.cons p.1 p.2)
          else (0 : _root_.LIDT.MIPStarRE.Quantum.Op ι) := by
    unfold _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums
    exact (Fintype.sum_equiv
      ((Fin.consEquiv (fun _ : Fin (prefixLen + 1) => Bool)).symm)
      (fun τprefix =>
        if d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τprefix + _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τtail then
          _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeOperator G τprefix
        else (0 : _root_.LIDT.MIPStarRE.Quantum.Op ι))
      (fun p =>
        if d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight (Fin.cons p.1 p.2) + _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τtail then
          _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeOperator G (Fin.cons p.1 p.2)
        else (0 : _root_.LIDT.MIPStarRE.Quantum.Op ι))
      (by
        intro τprefix
        simp))
  have hprod :
      (∑ p : Bool × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType prefixLen,
          if d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight (Fin.cons p.1 p.2) + _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τtail then
            _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeOperator G (Fin.cons p.1 p.2)
          else (0 : _root_.LIDT.MIPStarRE.Quantum.Op ι)) =
        ∑ b : Bool,
          ∑ τprefix : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType prefixLen,
            if d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight (Fin.cons b τprefix) + _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τtail then
              _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeOperator G (Fin.cons b τprefix)
            else (0 : _root_.LIDT.MIPStarRE.Quantum.Op ι) := by
    simpa using
      (Fintype.sum_prod_type' (f := fun b τprefix =>
        if d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight (Fin.cons b τprefix) + _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τtail then
          _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeOperator G (Fin.cons b τprefix)
        else (0 : _root_.LIDT.MIPStarRE.Quantum.Op ι)))
  have htrue :
      (∑ τprefix : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType prefixLen,
          (if d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight (Fin.cons true τprefix) + _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τtail then
            _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeOperator G (Fin.cons true τprefix)
          else (0 : _root_.LIDT.MIPStarRE.Quantum.Op ι))) =
        _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d prefixLen (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit true τtail) * G := by
    calc
      (∑ τprefix : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType prefixLen,
          (if d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight (Fin.cons true τprefix) + _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τtail then
            _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeOperator G (Fin.cons true τprefix)
          else (0 : _root_.LIDT.MIPStarRE.Quantum.Op ι)))
        =
          ∑ τprefix : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType prefixLen,
            ((if d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τprefix + _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit true τtail) then
              _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeOperator G τprefix
            else (0 : _root_.LIDT.MIPStarRE.Quantum.Op ι)) * G) := by
              refine Finset.sum_congr rfl ?_
              intro τprefix _
              have hcond :
                  (d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight (Fin.cons true τprefix) + _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τtail) ↔
                    (d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τprefix +
                      _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit true τtail)) := by
                have hprefix :
                    _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight (Fin.cons true τprefix : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType (prefixLen + 1)) =
                      _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τprefix + 1 := by
                  simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit] using gHatTypeWeight_prepend_true τprefix
                rw [hprefix, gHatTypeWeight_prepend_true]
                omega
              by_cases h : d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τprefix +
                  _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit true τtail)
              · have h' :
                    d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight (Fin.cons true τprefix) +
                      _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τtail :=
                  hcond.mpr h
                rw [if_pos h', if_pos h]
                simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit] using gHatTypeOperator_prepend_true G τprefix
              · have h' :
                    ¬ d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight (Fin.cons true τprefix) +
                      _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τtail := by
                  exact fun h' => h (hcond.mp h')
                simp [h, h']
      _ = _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d prefixLen (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit true τtail) * G := by
            unfold _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums
            rw [Finset.sum_mul]
  have hfalse :
      (∑ τprefix : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType prefixLen,
          (if d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight (Fin.cons false τprefix) + _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τtail then
            _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeOperator G (Fin.cons false τprefix)
          else (0 : _root_.LIDT.MIPStarRE.Quantum.Op ι))) =
        _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d prefixLen (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit false τtail) * (1 - G) := by
    calc
      (∑ τprefix : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType prefixLen,
          (if d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight (Fin.cons false τprefix) + _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τtail then
            _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeOperator G (Fin.cons false τprefix)
          else (0 : _root_.LIDT.MIPStarRE.Quantum.Op ι)))
        =
          ∑ τprefix : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType prefixLen,
            ((if d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τprefix + _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit false τtail) then
              _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeOperator G τprefix
            else (0 : _root_.LIDT.MIPStarRE.Quantum.Op ι)) * (1 - G)) := by
              refine Finset.sum_congr rfl ?_
              intro τprefix _
              have hcond :
                  (d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight (Fin.cons false τprefix) + _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τtail) ↔
                    (d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τprefix +
                      _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit false τtail)) := by
                have hprefix :
                    _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight (Fin.cons false τprefix : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType (prefixLen + 1)) =
                      _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τprefix := by
                  simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit] using gHatTypeWeight_prepend_false τprefix
                simp [hprefix, gHatTypeWeight_prepend_false]
              by_cases h : d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τprefix +
                  _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit false τtail)
              · have h' :
                    d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight (Fin.cons false τprefix) +
                      _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τtail :=
                  hcond.mpr h
                rw [if_pos h', if_pos h]
                simpa [_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit] using gHatTypeOperator_prepend_false G τprefix
              · have h' :
                    ¬ d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight (Fin.cons false τprefix) +
                      _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τtail := by
                  exact fun h' => h (hcond.mp h')
                simp [h, h']
      _ = _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d prefixLen (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit false τtail) * (1 - G) := by
            unfold _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums
            rw [Finset.sum_mul]
  refine ⟨hherm, hnonneg, hle_one, ?_⟩
  calc
    _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d (prefixLen + 1) τtail
      = ∑ p : Bool × _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType prefixLen,
          if d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight (Fin.cons p.1 p.2) + _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τtail then
            _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeOperator G (Fin.cons p.1 p.2)
          else (0 : _root_.LIDT.MIPStarRE.Quantum.Op ι) := hsplit
    _ = ∑ b : Bool,
          ∑ τprefix : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType prefixLen,
            if d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight (Fin.cons b τprefix) + _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τtail then
              _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeOperator G (Fin.cons b τprefix)
            else (0 : _root_.LIDT.MIPStarRE.Quantum.Op ι) := hprod
    _ = (∑ τprefix : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType prefixLen,
            (if d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight (Fin.cons true τprefix) + _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τtail then
              _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeOperator G (Fin.cons true τprefix)
            else (0 : _root_.LIDT.MIPStarRE.Quantum.Op ι))) +
          (∑ τprefix : _root_.LIDT.MIPStarRE.LDT.Pasting.GHatType prefixLen,
            (if d + 1 ≤ _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight (Fin.cons false τprefix) + _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeWeight τtail then
              _root_.LIDT.MIPStarRE.LDT.Pasting.gHatTypeOperator G (Fin.cons false τprefix)
            else (0 : _root_.LIDT.MIPStarRE.Quantum.Op ι))) := by
              rw [Fintype.sum_bool]
    _ = _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d prefixLen (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit true τtail) * G +
          _root_.LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSums G d prefixLen (_root_.LIDT.MIPStarRE.LDT.Pasting.prependTypeBit false τtail) * (1 - G) := by
            rw [htrue, hfalse]
