-- Prove2me | solution 1 for GlobalTheory.Square.TwoStep.twisted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:12:14.184227+00:00
-- url     : https://prove2.me/submissions/32dc97d6-1192-4f48-ba50-009cc7b9f90d

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero
import Theorems.Thm_GlobalTheory_Square_IsAwayUnit_one
import Theorems.Thm_GlobalTheory_Square_TwoStep_vw_natCast_nonneg
import Theorems.Thm_GlobalTheory_Square_TwoStep_normAlg_coords
import Theorems.Thm_P2M_GlobalTheory_Square_TwoStep_normAlg_coords__aac41224ad99
import Theorems.Thm_GlobalTheory_Square_TwoStep_tuple
import Theorems.Thm_GlobalTheory_Square_TwoStep_numbers_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)
noncomputable section
open GlobalTheory GlobalTheory.Square
variable {K : Type} [Field K] [NumberField K] [StarRing K]
attribute [instance] Co.finX
attribute [instance] Sq.finκ
open GlobalTheory.Square.TwoStep
namespace GlobalTheory.Square.TwoStep
theorem _root_.solution (σ₀ : K →+* ℂ) (w : Pl K) {n m d Q : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (hd : d ≠ 0)
    (hQ : (Q : 𝓞 K) ∉ w.asIdeal) {er : ℝ} (her : (vw w (m : K) : ℝ) ≤ (vw w (d : K) : ℝ) + er) :
    (square K).Twisted σ₀ w (σ₀ ((n ^ 2 * m * Q : ℕ) : K) * (square K).base.c) 1 1 (fun _ => 1) (fun _ => d) (fun _ => 0)
      (fun _ => 0) er (vw w ((2 : ℕ) : K) : ℝ) (univ : Finset Unit) (fun _ => 1) (fun _ => n) := by
  have hQ0 : Q ≠ 0 := by rintro rfl; exact hQ (by simp)
  refine ⟨numbers n m Q, coords K (1 * 1), coords K (m * Q), fun _ => m, fun _ => (Q : K) ^ 2, Q, ?_, ?_,
    tuple σ₀ w hn hm hQ0, ?_, normAlg_coords' _, hQ, ?_, ?_, ?_⟩
  · simp [numbers, square]
  · have := tuple σ₀ w one_ne_zero one_ne_zero one_ne_zero
    rwa [numbers_one (K := K)] at this
  · rw [normAlg_coords]; simp
  · intro s h1 _
    have hs : s ≠ 0 := by omega
    refine ⟨one_ne_zero, Nat.cast_ne_zero.2 hd, by simp [numbers, square, hs], ?_, her⟩
    simpa using vw_natCast_nonneg w m
  · intro s h1 h2
    have hs : s = 0 := by simp only [square] at h1; omega
    subst hs
    exact ⟨⟨(Q : 𝓞 K) ^ 2, 0, 2, dvd_rfl, by simp⟩, by simp [numbers, square]⟩
  · intro i
    exact ⟨1, fun _ => n, fun _ => 1, IsAwayUnit.one Q, by simp, by simp [numbers, square]⟩
end GlobalTheory.Square.TwoStep
