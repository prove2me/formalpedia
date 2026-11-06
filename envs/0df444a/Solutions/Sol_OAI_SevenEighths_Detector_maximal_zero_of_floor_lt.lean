-- Prove2me | solution 1 for OAI.SevenEighths.Detector.maximal_zero_of_floor_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:14:31.901935+00:00
-- url     : https://prove2.me/submissions/08caf135-122a-46ff-bfb1-741fb67e5247

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Detector
namespace OAI.SevenEighths.Detector
theorem _root_.solution {ι : Type*} (L : ι → ℂ → ℂ)
    (zeros : Finset (ι × ℂ)) {floor M : ℝ}
    (hzero : ∀ p ∈ zeros, L p.1 p.2 = 0)
    (hmax : M ∈ insert floor (zeros.image (fun p => p.2.re)))
    (hfloor : floor < M) :
    ∃ χ ρ, (χ, ρ) ∈ zeros ∧ L χ ρ = 0 ∧ ρ.re = M := by
  classical
  rcases Finset.mem_insert.mp hmax with h | h
  · exact False.elim ((ne_of_gt hfloor) h)
  · obtain ⟨⟨χ, ρ⟩, hp, heq⟩ := Finset.mem_image.mp h
    exact ⟨χ, ρ, hp, hzero _ hp, heq⟩
end OAI.SevenEighths.Detector
