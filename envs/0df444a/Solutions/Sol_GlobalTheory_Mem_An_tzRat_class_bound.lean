-- Prove2me | solution 1 for GlobalTheory.Mem.An.tzRat_class_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:54:25.597043+00:00
-- url     : https://prove2.me/submissions/639ac201-cf9f-4520-b5c6-83bca84e466c

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_GlobalBoundRefinements
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__IsExcRat_5b5b692fee064c30
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PrimesAPIntervalOfTzRat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.HermitianLattices.GL2PrimeSums
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.An
namespace GlobalTheory.Mem.An
theorem _root_.solution (h : TZRat) :
    ∃ C₀ Cr cr cb : ℝ, 0 < C₀ ∧ 0 < Cr ∧ 0 < cr ∧ 0 < cb ∧
      ∀ (M b : ℕ) (B : ℝ), 3 ≤ M → M % 4 ≠ 2 → Nat.Coprime b M → (M : ℝ) ≤ B →
        ∃ (θ : ℤ) (β : ℝ), θ ∈ ({-1, 0, 1} : Set ℤ) ∧
          (θ ≠ 0 → 1 / 2 ≤ β ∧ β < 1 ∧ cb / (B ^ 2 * Real.log B) ≤ 1 - β) ∧
          ∀ Y : ℝ, B ^ C₀ ≤ Y →
            |(M.totient : ℝ) * (((Icc 1 ⌊Y⌋₊).filter (fun p => p.Prime ∧ p ≡ b [MOD M])).card : ℝ)
              - Emain θ β Y| ≤ rhoErr Cr cr B Y * Emain θ β Y := by
  obtain ⟨c₂, c₃, CA, cS, h2, h3, hA, hS, H⟩ := h
  have hs3 : 0 < Real.sqrt c₃ := Real.sqrt_pos.2 h3
  refine ⟨c₂, CA, min c₃ (Real.sqrt c₃), cS, h2, hA, lt_min h3 hs3, hS, ?_⟩
  intro M b B hM hM4 hb hMB
  haveI : NeZero M := ⟨by omega⟩
  obtain ⟨-, HS, HC⟩ := H M hM hM4
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hlM : 1 / 4 ≤ Real.log M := by
    have h1 : Real.log 2 ≤ Real.log M := Real.log_le_log (by norm_num) (by linarith)
    have h2 := Real.log_two_gt_d9
    linarith
  have hlMB : Real.log M ≤ Real.log B := Real.log_le_log hM0 hMB

  have key : ∀ (θ : ℤ) (β : ℝ),
      ((θ = 0 ∧ ∀ (χ : DirichletCharacter ℂ M) (β' : ℝ), ¬ IsExcRat χ β') ∨
        ∃ χ : DirichletCharacter ℂ M, IsExcRat χ β ∧ χ (b : ZMod M) = (θ : ℂ)) →
      ∀ Y : ℝ, B ^ c₂ ≤ Y →
        |(M.totient : ℝ) * (((Icc 1 ⌊Y⌋₊).filter (fun p => p.Prime ∧ p ≡ b [MOD M])).card : ℝ)
          - Emain θ β Y| ≤ rhoErr CA (min c₃ (Real.sqrt c₃)) B Y * Emain θ β Y := by
    intro θ β hθ Y hY
    have hMY : (M : ℝ) ^ c₂ ≤ Y := le_trans (Real.rpow_le_rpow hM0.le hMB h2.le) hY
    have hY1 : 1 ≤ Y := le_trans (Real.one_le_rpow (by linarith) h2.le) hMY
    have hL : 0 ≤ Real.log Y := Real.log_nonneg hY1
    have hq := HC b θ β hb hθ Y hMY
    have hpos : 0 < CA * (Real.exp (-c₃ * Real.log Y / Real.log M) +
        Real.exp (-Real.sqrt (c₃ * Real.log Y))) := by positivity
    have hE : 0 ≤ Emain θ β Y := by
      have := le_trans (abs_nonneg _) hq
      exact (mul_nonneg_iff_of_pos_left hpos).1 this
    refine le_trans hq (mul_le_mul_of_nonneg_right ?_ hE)
    unfold rhoErr
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hA.le
    · apply Real.exp_le_exp.2
      rw [neg_mul, neg_mul, neg_div, neg_div, neg_le_neg_iff]
      have hm0 : 0 ≤ min c₃ (Real.sqrt c₃) := (lt_min h3 hs3).le
      calc min c₃ (Real.sqrt c₃) * Real.log Y / Real.log B
          ≤ min c₃ (Real.sqrt c₃) * Real.log Y / Real.log M :=
            div_le_div_of_nonneg_left (by positivity) (by linarith) hlMB
        _ ≤ c₃ * Real.log Y / Real.log M :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) hL) (by linarith)
    · apply Real.exp_le_exp.2
      rw [neg_mul, neg_le_neg_iff, Real.sqrt_mul h3.le]
      exact mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _)
  by_cases hex : ∃ (χ : DirichletCharacter ℂ M) (β : ℝ), IsExcRat χ β
  · obtain ⟨χ, β, hχ⟩ := hex
    have hu : IsUnit (b : ZMod M) := (ZMod.isUnit_iff_coprime b M).2 hb
    have hsq : χ (b : ZMod M) ^ 2 = 1 := by
      have h1 : (χ ^ 2) (b : ZMod M) = 1 := by
        rw [hχ.1]; exact MulChar.one_apply hu
      rwa [MulChar.pow_apply' χ (by norm_num)] at h1
    have hβ : 1 / 2 ≤ β ∧ β < 1 ∧ cS / (B ^ 2 * Real.log B) ≤ 1 - β := by
      refine ⟨?_, hχ.2.2.1, le_trans ?_ (HS χ β hχ)⟩
      · have h1 := hχ.2.1
        have h2 : 1 / (8 * Real.log M) ≤ 1 / 2 :=
          one_div_le_one_div_of_le (by norm_num) (by linarith)
        linarith
      · have hl0 : 0 < Real.log M := by linarith
        apply div_le_div_of_nonneg_left hS.le (by positivity)
        have hB0 : 0 < B := by linarith
        gcongr
    rcases sq_eq_one_iff.1 hsq with h1 | h1
    · exact ⟨1, β, by simp, fun _ => hβ, key 1 β (Or.inr ⟨χ, hχ, by simpa using h1⟩)⟩
    · exact ⟨-1, β, by simp, fun _ => hβ, key (-1) β (Or.inr ⟨χ, hχ, by simpa using h1⟩)⟩
  · push_neg at hex
    exact ⟨0, 0, by simp, fun h => absurd rfl h, key 0 0 (Or.inl ⟨rfl, hex⟩)⟩
end GlobalTheory.Mem.An
