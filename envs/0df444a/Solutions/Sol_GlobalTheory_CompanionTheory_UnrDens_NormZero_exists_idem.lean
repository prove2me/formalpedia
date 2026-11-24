-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.NormZero.exists_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:09:26.052613+00:00
-- url     : https://prove2.me/submissions/e9154db8-1e60-4046-b31f-e2f134bd3d08

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardZero
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormZero_nontrivial_of_resAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.NormZero
variable {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}
namespace GlobalTheory.CompanionTheory.UnrDens.NormZero
theorem _root_.solution (h : ResAlg E τ q ε) (hf : ¬ IsField E) :
    ∃ e : E, e * e = e ∧ τ e = 1 - e := by
  haveI := nontrivial_of_resAlg h
  obtain ⟨a, ha0, hau⟩ : ∃ a : E, a ≠ 0 ∧ ¬ IsUnit a := by
    by_contra hc
    push_neg at hc
    refine hf ⟨exists_pair_ne E, mul_comm, fun {a} ha => ?_⟩
    obtain ⟨b, hb⟩ := (hc a ha).exists_right_inv
    exact ⟨b, hb⟩
  obtain ⟨u, hu, -⟩ := h.basis
  have hN : a * τ a = 0 := by
    by_contra hN
    have hfix : τ (a * τ a) = a * τ a := by rw [map_mul, h.inv, mul_comm]
    exact hau (isUnit_of_mul_isUnit_left (h.fixedUnit _ hfix hN))
  have htfix : τ (a + τ a) = a + τ a := by rw [map_add, h.inv, add_comm]
  by_cases ht : a + τ a = 0
  · exfalso
    have hτa : τ a = -a := by linear_combination ht
    have hfix : τ (a * (u - τ u)) = a * (u - τ u) := by
      rw [map_mul, map_sub, h.inv, hτa]
      ring
    have hne : a * (u - τ u) ≠ 0 := fun h0 => ha0 (hu.mul_left_eq_zero.1 h0)
    exact hau (isUnit_of_mul_isUnit_left (h.fixedUnit _ hfix hne))
  · obtain ⟨s, hs⟩ := (h.fixedUnit _ htfix ht).exists_right_inv
    have hτs : τ s = s := by
      have h1 : (a + τ a) * τ s = 1 := by
        have := congrArg τ hs
        rwa [map_mul, htfix, map_one] at this
      calc τ s = (s * (a + τ a)) * τ s := by rw [mul_comm s, hs, one_mul]
        _ = s * ((a + τ a) * τ s) := by ring
        _ = s := by rw [h1, mul_one]
    have hτe : τ (a * s) = 1 - a * s := by
      rw [map_mul, hτs]
      linear_combination hs
    refine ⟨a * s, ?_, hτe⟩
    linear_combination (-(s * s)) * hN + (a * s) * hs
end GlobalTheory.CompanionTheory.UnrDens.NormZero
