-- Prove2me | solution 1 for Kyprianou.Ch01.frullani_complex
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:43:12.867665+00:00
-- url     : https://prove2.me/submissions/1fddbb4d-ba1e-4892-ae32-499f350c34ea

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_complexFrullaniKernel_integrable
import Theorems.Thm_CohnElkies_integral_complexFrullaniKernel

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set CohnElkies
open scoped Topology
set_option autoImplicit false

namespace Kyprianou.Ch01

/-- Integrability of the Chapter 1 gamma-type complex Frullani kernel. -/
noncomputable def gammaFrullani_integrable_fromExisting
    (α β : ℝ) (z : ℂ) (hα : 0 < α) (hβ : 0 < β) (hz : z.re ≤ 0) :
    IntegrableOn
      (fun x : ℝ =>
        ((1 : ℂ) - Complex.exp (z * (x : ℂ))) *
          ((β : ℂ) * Complex.exp (-(α : ℂ) * (x : ℂ)) / (x : ℂ)))
      (Ioi (0 : ℝ)) := by
  have hαpos : 0 < (α : ℂ).re := by simpa using hα
  have hw : 0 < ((α : ℂ) - z).re := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  have hbase : IntegrableOn
      (CohnElkies.complexFrullaniKernel (α : ℂ) ((α : ℂ) - z))
      (Ioi (0 : ℝ)) :=
    CohnElkies.complexFrullaniKernel_integrable hαpos hw
  have heq : (fun x : ℝ =>
        ((1 : ℂ) - Complex.exp (z * (x : ℂ))) *
          ((β : ℂ) * Complex.exp (-(α : ℂ) * (x : ℂ)) / (x : ℂ))) =
        (fun x : ℝ =>
          (β : ℂ) * CohnElkies.complexFrullaniKernel
            (α : ℂ) ((α : ℂ) - z) x) := by
    funext x
    dsimp [CohnElkies.complexFrullaniKernel]
    rw [show -((α : ℂ) - z) * (x : ℂ) =
       -(α : ℂ) * (x : ℂ) + z * (x : ℂ) by ring]
    rw [Complex.exp_add]
    ring
  rw [heq]
  exact hbase.const_mul (β : ℂ)


/-- Chapter 1 Frullani complex Laplace identity from an existing proved integral. -/
noncomputable def gammaFrullani_full_fromExisting
    (α β : ℝ) (z : ℂ) (hα : 0 < α) (hβ : 0 < β) (hz : z.re ≤ 0) :
    (IntegrableOn
      (fun x : ℝ =>
        ((1 : ℂ) - Complex.exp (z * (x : ℂ))) *
          ((β : ℂ) * Complex.exp (-(α : ℂ) * (x : ℂ)) / (x : ℂ)))
      (Ioi (0 : ℝ))) ∧
      Complex.exp (-(β : ℂ) * Complex.log (1 - z / (α : ℂ))) =
        Complex.exp
          (-(∫ x in Ioi (0 : ℝ),
            ((1 : ℂ) - Complex.exp (z * (x : ℂ))) *
              ((β : ℂ) * Complex.exp (-(α : ℂ) * (x : ℂ)) / (x : ℂ)))) := by
  have hαpos : 0 < (α : ℂ).re := by simpa using hα
  have hw : 0 < ((α : ℂ) - z).re := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  have hαne : (α : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hα)
  have hqpos : 0 < (1 - z / (α : ℂ)).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.div_ofReal_re]
    have hdiv : z.re / α ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hz hα.le
    linarith
  have hqne : (1 - z / (α : ℂ)) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.zero_re] at hre
    linarith [hqpos]
  have hfactor : (α : ℂ) - z =
      (α : ℂ) * (1 - z / (α : ℂ)) := by
    field_simp <;> ring
  have hlog :
      Complex.log ((α : ℂ) - z) - Complex.log (α : ℂ) =
      Complex.log (1 - z / (α : ℂ)) := by
    rw [hfactor, Complex.log_ofReal_mul hα hqne]
    rw [← Complex.ofReal_log hα.le]
    ring
  have heq : (fun x : ℝ =>
        ((1 : ℂ) - Complex.exp (z * (x : ℂ))) *
          ((β : ℂ) * Complex.exp (-(α : ℂ) * (x : ℂ)) / (x : ℂ))) =
        (fun x : ℝ =>
          (β : ℂ) * CohnElkies.complexFrullaniKernel
            (α : ℂ) ((α : ℂ) - z) x) := by
    funext x
    dsimp [CohnElkies.complexFrullaniKernel]
    rw [show -((α : ℂ) - z) * (x : ℂ) =
       -(α : ℂ) * (x : ℂ) + z * (x : ℂ) by ring]
    rw [Complex.exp_add]
    ring
  have hint := gammaFrullani_integrable_fromExisting α β z hα hβ hz
  constructor
  · exact hint
  · rw [heq, MeasureTheory.integral_const_mul]
    rw [CohnElkies.integral_complexFrullaniKernel hαpos hw]
    rw [hlog]
    congr 1
    ring

end Kyprianou.Ch01

theorem solution
    (α β : ℝ) (z : ℂ) (hα : 0 < α) (hβ : 0 < β) (hz : z.re ≤ 0) :
    (IntegrableOn
      (fun x : ℝ =>
        ((1 : ℂ) - Complex.exp (z * (x : ℂ))) *
          ((β : ℂ) * Complex.exp (-(α : ℂ) * (x : ℂ)) / (x : ℂ)))
      (Ioi (0 : ℝ))) ∧
      Complex.exp (-(β : ℂ) * Complex.log (1 - z / (α : ℂ))) =
        Complex.exp
          (-(∫ x in Ioi (0 : ℝ),
            ((1 : ℂ) - Complex.exp (z * (x : ℂ))) *
              ((β : ℂ) * Complex.exp (-(α : ℂ) * (x : ℂ)) / (x : ℂ)))) := by
  exact Kyprianou.Ch01.gammaFrullani_full_fromExisting α β z hα hβ hz
