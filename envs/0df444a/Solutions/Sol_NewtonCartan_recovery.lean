-- Prove2me | solution 1 for NewtonCartan.recovery
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T06:14:23.927806+00:00
-- url     : https://prove2.me/submissions/0f67c2c7-263f-4fa0-9d7d-cbfd3803ed9a

import Definitions.Def_NewtonCartan_defs
import Theorems.Thm_NewtonCartan_sameTrajectories_geomGamma
import Theorems.Thm_NewtonCartan_exists_recovery_potential
import Mathlib.Tactic.Ring

open scoped ContDiff
open Classical
open NewtonCartan

/-! # Prop. 2.2 (Trautman recovery) — reduction
Following Malament Prop. 4.2.5 / Weatherall Prop. 2.2.

The algebraic identity `geomΓ (gaugeΓ Γt φ) φ = Γt` reduces recovery to finding a
potential `φ` for which `gaugeΓ Γt φ` is an NG connection obeying Poisson
(`exists_recovery_potential`). Trajectory agreement is then `sameTrajectories_geomGamma`.
-/

private lemma geomΓ_gaugeΓ (Γt : Conn) (φ : E → ℝ) :
    geomΓ (gaugeΓ Γt φ) φ = Γt := by
  funext x a b c
  simp [geomΓ, gaugeΓ]

theorem solution (Γt : Conn) (ρ : E → ℝ) (hΓt : IsClassical Γt) (hρ : ContDiff ℝ ∞ ρ)
    (hcurv : CurvConds Γt ρ) :
    ∃ (Γ : Conn) (φ : E → ℝ), IsNG Γ φ ∧ SameTrajectories Γ φ Γt ∧ Poisson Γ φ ρ := by
  obtain ⟨φ, hNG, hP⟩ := exists_recovery_potential Γt ρ hΓt hρ hcurv
  refine ⟨gaugeΓ Γt φ, φ, hNG, ?_, hP⟩
  -- SameTrajectories Γ φ Γt via geomΓ Γ φ = Γt
  have hST := sameTrajectories_geomGamma (gaugeΓ Γt φ) φ
  simpa [geomΓ_gaugeΓ] using hST
