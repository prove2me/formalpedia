-- Prove2me | solution 1 for GlobalTheory.Lin.primesAPInterval_of_primesRel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:43:59.821093+00:00
-- url     : https://prove2.me/submissions/c92f76d5-68a7-49ff-831b-00af7cb9de94

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_GlobalBoundRefinements
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PrimesAPIntervalOfPrimesRel
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_shortIntervalLowerBound
import Theorems.Thm_Formalism_HermitianLattices_GlobalBoundRefinements_shortIntervalImpliesProgressions_statement
import Theorems.Thm_Formalism_HermitianLattices_GlobalBoundRefinements_shortIntervalLowerBound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.HermitianLattices.GL2PrimeSums
open GlobalTheory GlobalTheory.Lin
open Finset
namespace GlobalTheory.Lin
namespace _root_.GlobalTheory.Lin
theorem _root_.solution (h : _root_.GlobalTheory.Lin.PrimesRel) :
    ∃ C₀ Cr cr c : ℝ, 0 < C₀ ∧ 0 < Cr ∧ 0 < cr ∧ 0 < c ∧ _root_.Formalism.HermitianLattices.GL2PrimeSums.PrimesAPInterval C₀ Cr cr c := by
  unfold _root_.GlobalTheory.Lin.PrimesRel at h
  obtain ⟨c₁, c₂, c₃, CA, cS, hc₁, hc₁8, hc₂, hc₃, hCA, hcS, hmain⟩ := h
  set cr := min c₃ (Real.sqrt c₃) with hcr
  have hcr0 : 0 < cr := lt_min hc₃ (Real.sqrt_pos.mpr hc₃)
  have hdata : _root_.Formalism.HermitianLattices.GlobalBoundRefinements.PrimeCountAsymptoticInProgressions c₂ CA cr cS := by
    unfold _root_.Formalism.HermitianLattices.GlobalBoundRefinements.PrimeCountAsymptoticInProgressions
    intro m a hm ha
    haveI : NeZero m := ⟨by omega⟩
    obtain ⟨huniq, hgap, hcount⟩ := hmain m hm
    have hm1 : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
    have hlogm : 0 < Real.log m := Real.log_pos hm1
    have hlog4m : Real.log m ≤ Real.log (4 * m) :=
      Real.log_le_log (by positivity) (by linarith)
    have hlog3 : 1 < Real.log m := by
      rw [Real.lt_log_iff_exp_lt (by positivity)]
      have : (3 : ℝ) ≤ m := by exact_mod_cast hm
      linarith [Real.exp_one_lt_d9]

    have hterm : ∃ (θ : ℤ) (β : ℝ), θ ∈ ({-1, 0, 1} : Set ℤ) ∧
        (θ ≠ 0 → 1 / 2 ≤ β ∧ β < 1 ∧ cS / ((4 * (m : ℝ)) ^ 2 * Real.log (4 * m)) ≤ 1 - β) ∧
        _root_.GlobalTheory.Lin.ExcData c₁ m a θ β := by
      by_cases hex : ∃ (χ : DirichletCharacter ℂ m) (β : ℝ), _root_.GlobalTheory.Lin.IsExc c₁ χ β
      · obtain ⟨χ, β, hχ⟩ := hex
        have hunit : IsUnit (a : ZMod m) := (ZMod.isUnit_iff_coprime a m).mpr ha
        have hsq : χ (a : ZMod m) ^ 2 = 1 := by
          rw [← MulChar.pow_apply' χ (by norm_num), hχ.1, MulChar.one_apply hunit]
        obtain ⟨θ, hθ, hθmem⟩ : ∃ θ : ℤ, χ (a : ZMod m) = θ ∧ θ ∈ ({-1, 0, 1} : Set ℤ) := by
          have hsq' : χ (a : ZMod m) * χ (a : ZMod m) = 1 := by rw [← pow_two]; exact hsq
          rcases mul_self_eq_one_iff.mp hsq' with h1 | h1
          · exact ⟨1, by simp [h1], by simp⟩
          · exact ⟨-1, by simp [h1], by simp⟩
        refine ⟨θ, β, hθmem, fun _ => ⟨?_, hχ.2.2.1, ?_⟩, Or.inr ⟨χ, hχ, hθ⟩⟩
        · have h1 := hχ.2.1
          have : c₁ / Real.log m ≤ 1 / 2 := by
            rw [div_le_iff₀ hlogm]
            linarith
          linarith
        · refine le_trans ?_ (hgap χ β hχ)
          apply div_le_div_of_nonneg_left hcS.le (by positivity)
          have : (m : ℝ) ^ 2 ≤ (4 * m) ^ 2 := by
            apply pow_le_pow_left₀ (by positivity)
            linarith
          exact mul_le_mul this hlog4m hlogm.le (by positivity)
      · refine ⟨0, 1 / 2, by simp, fun h0 => absurd rfl h0, Or.inl ⟨rfl, fun χ β hχ => hex ⟨χ, β, hχ⟩⟩⟩
    obtain ⟨θ, β, hθmem, hβ, hdat⟩ := hterm
    refine ⟨θ, β, fun _ => 0, hθmem, hβ,
      fun _ => ⟨le_rfl, mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))⟩, ?_⟩
    intro Y hY
    have hY1 : (m : ℝ) ^ c₂ ≤ Y := by
      refine le_trans ?_ hY
      exact Real.rpow_le_rpow (by positivity) (by linarith) hc₂.le
    have hb := hcount a θ β ha hdat Y hY1
    have hY1' : 1 ≤ Y := le_trans (Real.one_le_rpow (by linarith) hc₂.le) hY1
    have hL : 0 ≤ Real.log Y := Real.log_nonneg hY1'
    have hpos : 0 < CA * (Real.exp (-c₃ * Real.log Y / Real.log m) +
        Real.exp (-√(c₃ * Real.log Y))) := by
      positivity
    have hE : 0 ≤ _root_.Formalism.HermitianLattices.GL2PrimeSums.Emain θ β Y :=
      (mul_nonneg_iff_of_pos_left hpos).mp ((abs_nonneg _).trans hb)
    have h1 : Real.exp (-c₃ * Real.log Y / Real.log m) ≤
        Real.exp (-cr * Real.log Y / Real.log (4 * m)) := by
      rw [Real.exp_le_exp, neg_mul, neg_mul, neg_div, neg_div, neg_le_neg_iff]
      exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right (min_le_left _ _) hL)
        hlogm hlog4m
    have h2 : Real.exp (-√(c₃ * Real.log Y)) ≤ Real.exp (-cr * √(Real.log Y)) := by
      rw [Real.exp_le_exp, neg_mul, neg_le_neg_iff, Real.sqrt_mul hc₃.le]
      exact mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _)
    simp only [add_zero]
    refine hb.trans (mul_le_mul_of_nonneg_right ?_ hE)
    unfold _root_.Formalism.HermitianLattices.GL2PrimeSums.rhoErr
    rw [mul_add]
    exact add_le_add (mul_le_mul_of_nonneg_left h1 hCA.le) (mul_le_mul_of_nonneg_left h2 hCA.le)
  obtain ⟨C₀', c, hC₀', hc, hint⟩ := _root_.Formalism.HermitianLattices.GlobalBoundRefinements.shortIntervalImpliesProgressions_statement _root_.Formalism.HermitianLattices.GlobalBoundRefinements.shortIntervalLowerBound c₂ CA cr cS hc₂ hCA hcr0 hcS hdata
  exact ⟨C₀', CA, cr, c, hC₀', hCA, hcr0, hc, hint⟩
end _root_.GlobalTheory.Lin
end GlobalTheory.Lin
