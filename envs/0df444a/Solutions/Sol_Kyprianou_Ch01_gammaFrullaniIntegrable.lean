-- Prove2me | solution 1 for Kyprianou.Ch01.gammaFrullaniIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:10:55.488203+00:00
-- url     : https://prove2.me/submissions/1f8e355b-979d-45e3-961c-cb257c231136

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_complexFrullaniKernel_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set CohnElkies
open scoped Topology
set_option autoImplicit false

/-- Integrability of the Chapter 1 gamma-type complex Frullani kernel. -/
theorem solution
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


