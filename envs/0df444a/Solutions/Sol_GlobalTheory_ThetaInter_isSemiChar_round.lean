-- Prove2me | solution 1 for GlobalTheory.ThetaInter.isSemiChar_round
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:40.87198+00:00
-- url     : https://prove2.me/submissions/58f9c13b-d689-4ff8-85b1-905c2198a2ee

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaInter
open Formalism.L2.Th1.H Complex
open scoped BigOperators ComplexConjugate
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {H : Sesq V}
variable {α : V → ℂ}
namespace GlobalTheory.ThetaInter
theorem _root_.solution (hH : IsHerm H) (s : ℝ) {A : AddSubgroup V} (hint : A ≤ dualLat H A)
    (hw : ∀ x ∈ A, ((1 + I * (s : ℂ)) / 2) • x ∈ A) (hq : ∀ x ∈ A, ∃ m : ℤ, s / 2 * (H x x).re = m) :
    IsSemiChar H A fun x => (-1 : ℂ) ^ (round (s / 2 * (H x x).re)) := by
  refine ⟨fun x _ => ?_, fun x hx y hy => ?_⟩
  · rcases Int.even_or_odd (round (s / 2 * (H x x).re)) with h | h
    · exact Or.inl h.neg_one_zpow
    · exact Or.inr h.neg_one_zpow
  · obtain ⟨a, ha⟩ := hq x hx
    obtain ⟨b, hb⟩ := hq y hy
    obtain ⟨e, he⟩ := hint hx y hy
    obtain ⟨k, hk⟩ := hint (hw x hx) y hy
    have hk' : ((H x y).im + s * (H x y).re) / 2 = k := by
      rw [← hk, altE, map_smul]
      simp
      ring
    have hs : s / 2 * (H (x + y) (x + y)).re = ((a + b + e + 2 * (k - e) : ℤ) : ℝ) := by
      simp only [map_add, LinearMap.add_apply, add_re, hH x y, conj_re]
      rw [altE] at he
      push_cast
      linarith
    simp only [hs, ha, hb, he, round_intCast]
    have h1 : (-1 : ℂ) ≠ 0 := by norm_num
    rw [zpow_add₀ h1, zpow_add₀ h1, zpow_add₀ h1, (even_two_mul _).neg_one_zpow, mul_one,
      mul_comm _ ((e : ℝ) : ℂ), Complex.ofReal_intCast, Complex.exp_int_mul, Complex.exp_pi_mul_I]
end GlobalTheory.ThetaInter
