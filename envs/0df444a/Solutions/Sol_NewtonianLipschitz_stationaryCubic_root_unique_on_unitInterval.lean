-- Prove2me | solution 1 for NewtonianLipschitz.stationaryCubic_root_unique_on_unitInterval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:28:57.136301+00:00
-- url     : https://prove2.me/submissions/83a357ee-687b-45d1-9990-f5b003129e89

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_CubicCandidate
public import Theorems.Thm_NewtonianLipschitz_stationaryCubic_strictAntiOn_unitInterval

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution
    (x y : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hpx : stationaryCubic x = 0)
    (hpy : stationaryCubic y = 0) : x = y := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · have h := stationaryCubic_strictAntiOn_unitInterval hx hy hlt
    rw [hpx, hpy] at h
    exact (lt_irrefl (0 : ℝ) h).elim
  · exact heq
  · have h := stationaryCubic_strictAntiOn_unitInterval hy hx hgt
    rw [hpx, hpy] at h
    exact (lt_irrefl (0 : ℝ) h).elim
end NewtonianLipschitz
