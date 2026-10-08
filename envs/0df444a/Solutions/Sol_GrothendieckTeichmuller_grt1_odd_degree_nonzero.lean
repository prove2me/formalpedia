-- Prove2me | solution 1 for GrothendieckTeichmuller.grt1_odd_degree_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T12:54:24.817576+00:00
-- url     : https://prove2.me/submissions/caa18fcf-52af-4fd9-bb2f-227ab31d2ea7

import Definitions.Def_GT_grt1
import Theorems.Thm_GrothendieckTeichmuller_deligne_drinfeld_ihara
import Theorems.Thm_GrothendieckTeichmuller_ihara_deriv_commutator
import Mathlib


section
section
namespace GrothendieckTeichmuller

section
attribute [local instance] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- A generator of a free Lie algebra over `ℚ` is nonzero. -/
theorem freeLie_of_ne_zero {α : Type*} (a : α) : FreeLieAlgebra.of ℚ a ≠ 0 := by
  intro h
  have := congrArg (FreeLieAlgebra.lift ℚ (fun _ : α => (1 : ℚ))) h
  simp at this

end

theorem iharaDeriv_zero : iharaDeriv 0 = 0 := by
  have h := ihara_deriv_commutator 0 0
  rw [add_sub_cancel_right, lie_self] at h
  exact h.symm

theorem grt1_odd_degree_nonzero_oai (p : ℕ) :
    ∃ ψ : Lxy, ψ ∈ grt1 ∧ ψ ≠ 0 ∧ IsHomogeneousOfDegree (2 * p + 3) ψ := by
  obtain ⟨sigma, h1, h2, -⟩ := deligne_drinfeld_ihara
  refine ⟨sigma p, (h1 p).1, fun h0 => ?_, (h1 p).2⟩
  apply freeLie_of_ne_zero (α := ℕ) p
  apply h2
  rw [FreeLieAlgebra.lift_of_apply, h0, iharaDeriv_zero, map_zero]

end GrothendieckTeichmuller

end
end

section
open GrothendieckTeichmuller

theorem solution (p : ℕ) :
    ∃ ψ : Lxy, ψ ∈ grt1 ∧ ψ ≠ 0 ∧ IsHomogeneousOfDegree (2 * p + 3) ψ := by
  apply GrothendieckTeichmuller.grt1_odd_degree_nonzero_oai <;> assumption

end
