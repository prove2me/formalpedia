-- Prove2me | solution 1 for GlobalTheory.Mem.An.tzRat_ratClass
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:03:43.143009+00:00
-- url     : https://prove2.me/submissions/dd256aee-a457-4e43-8da4-a5c2b9d2450d

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_GlobalBoundRefinements
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__IsExcRat_5b5b692fee064c30
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PrimesAPIntervalOfTzRat
import Theorems.Thm_GlobalTheory_Mem_An_tzRat_class_bound
import Theorems.Thm_GlobalTheory_Mem_An_card_primes_mod_half

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
    ∃ C₀ Cr cr cb : ℝ, 0 < C₀ ∧ 0 < Cr ∧ 0 < cr ∧ 0 < cb ∧ Formalism.HermitianLattices.GlobalBoundRefinements.PrimeCountAsymptoticInProgressions C₀ Cr cr cb := by
  obtain ⟨C₀, Cr, cr, cb, h0, h1, h2, h3, H⟩ := tzRat_class_bound h
  refine ⟨C₀, Cr, cr, cb, h0, h1, h2, h3, ?_⟩
  intro m a hm ha
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hl : 1 ≤ 3 * Real.log (4 * (m : ℝ)) := by
    have h1 : Real.log 2 ≤ Real.log (4 * (m : ℝ)) := Real.log_le_log (by norm_num) (by linarith)
    have h2 := Real.log_two_gt_d9
    linarith
  by_cases h4 : m % 4 = 2
  · obtain ⟨n, rfl⟩ : ∃ n, m = 2 * n := ⟨m / 2, by omega⟩
    have hn : Odd n := Nat.odd_iff.2 (by omega)
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    obtain ⟨θ, β, hθ, hβ, hE⟩ := H n a (4 * ((2 * n : ℕ) : ℝ)) (by omega) (by omega)
      (Nat.Coprime.coprime_mul_left_right ha) (by push_cast; linarith)
    refine ⟨θ, β, fun Y => (((Icc 1 ⌊Y⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD n])).card : ℝ) -
      (((Icc 1 ⌊Y⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD 2 * n])).card : ℝ), hθ, hβ, ?_, ?_⟩
    · intro Y
      obtain ⟨k1, k2⟩ := card_primes_mod_half n a ⌊Y⌋₊ hn ha
      have k1' := (Nat.cast_le (α := ℝ)).2 k1
      have k2' := (Nat.cast_le (α := ℝ)).2 k2
      rw [Nat.cast_add, Nat.cast_one] at k2'
      constructor <;> linarith
    · intro Y hY
      rw [Nat.totient_two_mul_of_odd hn, add_sub_cancel]
      exact hE Y hY
  · obtain ⟨θ, β, hθ, hβ, hE⟩ := H m a (4 * (m : ℝ)) hm h4 ha (by linarith)
    refine ⟨θ, β, fun _ => 0, hθ, hβ, fun _ => ⟨le_rfl, by linarith⟩, ?_⟩
    intro Y hY
    rw [add_zero]
    exact hE Y hY
end GlobalTheory.Mem.An
