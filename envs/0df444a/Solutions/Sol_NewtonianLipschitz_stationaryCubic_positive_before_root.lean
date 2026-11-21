-- Prove2me | solution 1 for NewtonianLipschitz.stationaryCubic_positive_before_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:40:23.825439+00:00
-- url     : https://prove2.me/submissions/218c93e1-4091-4aac-93b6-8856f28d4b3e

module
public import Definitions.Def_NewtonianLipschitz_CubicCandidate
public import Definitions.Def_NewtonianLipschitz_ScalarMaximum
public import Theorems.Thm_NewtonianLipschitz_candidateCriticalPoint_spec
public import Theorems.Thm_NewtonianLipschitz_stationaryCubic_strictAntiOn_unitInterval


set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution
    (x : ℝ) (hx0 : 0 ≤ x) (hxa : x < candidateCriticalPoint) :
    0 < stationaryCubic x := by
  obtain ⟨hal, har, hzero⟩ := candidateCriticalPoint_spec
  have ha : candidateCriticalPoint ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith, by linarith⟩
  have hx : x ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hx0, by linarith⟩
  have h := stationaryCubic_strictAntiOn_unitInterval hx ha hxa
  rw [hzero] at h
  exact h
end NewtonianLipschitz
