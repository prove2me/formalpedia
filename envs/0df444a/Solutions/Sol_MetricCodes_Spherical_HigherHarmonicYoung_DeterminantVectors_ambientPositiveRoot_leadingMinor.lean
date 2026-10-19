-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors.ambientPositiveRoot_leadingMinor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/6f63e8e0-5873-47f7-86eb-ac3928bef405

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
namespace MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
theorem _root_.solution {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (p q : Fin (r + 1)) (hpq : p < q) (k : Fin (r + 1)) :
    ambientPositiveRoot h p q (leadingMinor h k) = 0 := by
  classical
  unfold leadingMinor
  by_cases hq : q.val ≤ k.val
  · let qq : Fin (k.val + 1) := ⟨q.val, by omega⟩
    let pp : Fin (k.val + 1) := ⟨p.val, by
      have hpqv : p.val < q.val := hpq
      omega⟩
    have hqq : minorIndex k qq = q := Fin.ext rfl
    have hpp : minorIndex k pp = p := Fin.ext rfl
    rw [derivation_det_singleColumn
      (ambientPositiveRoot h p q)
      (fun a b : Fin (k.val + 1) =>
        isotropicVariable h (minorIndex k a) (minorIndex k b)) qq]
    · have hcol :
          (fun a : Fin (k.val + 1) =>
            ambientPositiveRoot h p q
              (isotropicVariable h (minorIndex k a) (minorIndex k qq))) =
          (MvPolynomial.C (2 : ℂ) :
            MvPolynomial (Fin ((r + 1) * n)) ℂ) •
              (fun a : Fin (k.val + 1) =>
                isotropicVariable h (minorIndex k a) (minorIndex k pp)) := by
        funext a
        rw [ambientPositiveRoot_isotropicVariable, hqq,
          if_pos rfl, hpp]
        simp [Pi.smul_apply, Algebra.smul_def, smul_eq_mul]
      rw [hcol, Matrix.det_updateCol_smul,
        Matrix.det_updateCol_eq_zero]
      · simp
      · intro hbad
        have hvals := congrArg Fin.val hbad
        have hpqv : p.val < q.val := hpq
        change p.val = q.val at hvals
        omega
    · intro a b hb
      rw [ambientPositiveRoot_isotropicVariable]
      have hne : q ≠ minorIndex k b := by
        intro heq
        apply hb
        apply Fin.ext
        have hv := congrArg Fin.val heq
        change q.val = b.val at hv
        exact hv.symm
      simp [hne]
  · apply derivation_det_eq_zero
    intro a b
    rw [ambientPositiveRoot_isotropicVariable]
    have hne : q ≠ minorIndex k b := by
      intro heq
      have hv := congrArg Fin.val heq
      change q.val = b.val at hv
      have hb := b.isLt
      omega
    simp [hne]
end MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
