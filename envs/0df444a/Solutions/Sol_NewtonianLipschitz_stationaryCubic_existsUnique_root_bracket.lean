-- Prove2me | solution 1 for NewtonianLipschitz.stationaryCubic_existsUnique_root_bracket
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T04:03:44.621087+00:00
-- url     : https://prove2.me/submissions/d9774b11-5e8b-467f-94e6-88660939093a

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_CubicCandidate
public import Theorems.Thm_NewtonianLipschitz_stationaryCubic_root_unique_on_unitInterval

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution :
    ∃! t : ℝ, (9 / 50 : ℝ) ≤ t ∧ t ≤ 1 / 5 ∧
      stationaryCubic t = 0 := by
  obtain ⟨t, htl, htr, hpt⟩ := stationaryCubic_exists_root_bracket
  refine ⟨t, ⟨htl, htr, hpt⟩, ?_⟩
  intro y hy
  exact stationaryCubic_root_unique_on_unitInterval y t
    ⟨by linarith [hy.1], by linarith [hy.2.1]⟩
    ⟨by linarith, by linarith⟩ hy.2.2 hpt
end NewtonianLipschitz
