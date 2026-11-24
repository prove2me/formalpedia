-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.NormUnit.card_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:51:58.833594+00:00
-- url     : https://prove2.me/submissions/34d9054b-279b-4cb9-98dc-5b3b2ed4c86b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardNonzero
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_finite_of_resAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.NormUnit
variable {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}
namespace GlobalTheory.CompanionTheory.UnrDens.NormUnit
theorem _root_.solution (h : ResAlg E τ q ε) : Nat.card {x : E // τ x = x} = q := by
  have := finite_of_resAlg h
  obtain ⟨u, hu, hb⟩ := h.basis
  have hbij : Function.Bijective
      (fun p : {x : E // τ x = x} × {x : E // τ x = x} => (p.1 : E) + p.2 * u) := by
    constructor
    · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩ hxy
      simp only at hxy
      have h2 := congrArg τ hxy
      simp only [map_add, map_mul, hx, hy, hx', hy'] at h2
      have hyy : y = y' := by
        have h3 : (y - y') * (u - τ u) = 0 := by linear_combination hxy - h2
        rw [hu.mul_left_eq_zero, sub_eq_zero] at h3
        exact h3
      subst hyy
      have hxx : x = x' := by linear_combination hxy
      subst hxx
      rfl
    · intro a
      obtain ⟨x, y, hx, hy, rfl⟩ := hb a
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  have hc := Nat.card_congr (Equiv.ofBijective _ hbij)
  rw [Nat.card_prod, h.card] at hc
  have h4 : Nat.card {x : E // τ x = x} ^ 2 = q ^ 2 := by rw [sq]; exact hc
  exact Nat.pow_left_injective (by norm_num) h4
end GlobalTheory.CompanionTheory.UnrDens.NormUnit
