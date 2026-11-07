-- Prove2me | solution 1 for MarkmanSecant.annih_isotropic
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T04:26:54.747365+00:00
-- url     : https://prove2.me/submissions/49bf8797-5983-4576-b245-b52ad14c63b4

import Definitions.Def_MarkmanSecant
import Mathlib.Tactic.Abel

open MarkmanSecant
open scoped ExteriorAlgebra

private lemma cliff_apply {n : ℕ} (s : Spinor n) (v : VC n) :
    cliffAt s v = ExteriorAlgebra.ι ℂ (wPart v) * s +
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (H1 n)))
        (dualOf (tPart v)) s := rfl

private lemma cliff_square {n : ℕ} (s : Spinor n) (v : VC n) :
    cliffAt (cliffAt s v) v = dualOf (tPart v) (wPart v) • s := by
  simp only [cliff_apply]
  rw [map_add,
    CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_contractLeft,
    mul_add, ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul, zero_add, add_zero]
  abel

private lemma annih_quadratic {n : ℕ} (s : Spinor n) (hs : s ≠ 0)
    (v : VC n) (hv : v ∈ annih s) : tPart v ⬝ᵥ wPart v = 0 := by
  have hzero : cliffAt s v = 0 := hv
  have h := cliff_square s v
  rw [hzero] at h
  have hz : cliffAt (0 : Spinor n) v = 0 := by simp [cliff_apply]
  rw [hz] at h
  have hscalar := (smul_eq_zero.mp h.symm).resolve_right hs
  simpa [dualOf, dualLin, LinearMap.sum_apply, LinearMap.smulRight_apply, dotProduct]
    using hscalar

theorem solution (n : ℕ) (s : Spinor n) (hs : s ≠ 0)
    (v w : VC n) (hv : v ∈ annih s) (hw : w ∈ annih s) :
    pairV v w = 0 := by
  have hvv := annih_quadratic s hs v hv
  have hww := annih_quadratic s hs w hw
  have hsum := annih_quadratic s hs (v + w) ((annih s).add_mem hv hw)
  have ht : tPart (v + w) = tPart v + tPart w := rfl
  have hw' : wPart (v + w) = wPart v + wPart w := rfl
  rw [ht, hw', add_dotProduct, dotProduct_add, dotProduct_add, hvv, hww] at hsum
  simpa [pairV, add_comm] using hsum

#print axioms solution
