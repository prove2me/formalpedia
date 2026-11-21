-- Prove2me | solution 1 for NewtonianLipschitz.stationaryCubic_negative_after_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:40:26.596676+00:00
-- url     : https://prove2.me/submissions/a4176744-2d41-4fa7-bb8d-025c0ed55e76

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
    (x : ℝ) (hxa : candidateCriticalPoint < x) (hx1 : x ≤ 1) :
    stationaryCubic x < 0 := by
  obtain ⟨hal, har, hzero⟩ := candidateCriticalPoint_spec
  have ha : candidateCriticalPoint ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith, by linarith⟩
  have hx : x ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith, hx1⟩
  have h := stationaryCubic_strictAntiOn_unitInterval ha hx hxa
  rw [hzero] at h
  exact h
end NewtonianLipschitz
