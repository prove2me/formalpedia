-- Prove2me | solution 1 for GlobalTheory.Square.TwoStep.exists_twisted_ne_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:12:14.74025+00:00
-- url     : https://prove2.me/submissions/a29570c1-bf6b-429c-a945-44b6fd08dbce

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero
import Theorems.Thm_GlobalTheory_Square_TwoStep_vw_natCast_nonneg
import Theorems.Thm_GlobalTheory_Square_TwoStep_square_ok
import Theorems.Thm_GlobalTheory_Square_TwoStep_twisted

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
theorem _root_.solution (σ₀ : K →+* ℂ) (w : Pl K) :
    ∃ (S : Sq K) (cw : ℂ) (dl : ℝ), S.OK 3 2 ∧ 0 ≤ dl ∧ cw = 12 * S.base.c ∧ cw ≠ S.base.c ∧
      S.Twisted σ₀ w cw 1 1 (fun _ => 1) (fun _ => 3) (fun _ => 0) (fun _ => 0) 0 dl (univ : Finset Unit) (fun _ => 1)
        (fun _ => 2) := by
  have h1 : ((1 : ℕ) : 𝓞 K) ∉ w.asIdeal := by simpa using (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top
  have h := twisted σ₀ w (n := 2) (m := 3) (d := 3) (Q := 1) (er := 0) (by norm_num) (by norm_num) (by norm_num) h1 (by simp)
  have h12 : σ₀ ((2 ^ 2 * 3 * 1 : ℕ) : K) = 12 := by rw [map_natCast]; norm_num
  rw [h12] at h
  refine ⟨square K, _, _, square_ok, vw_natCast_nonneg w 2, rfl, ?_, by simpa using h⟩
  intro h'
  have h0 : (11 : ℂ) * (square K).base.c = 0 := by linear_combination h'
  exact mul_ne_zero (by norm_num) (square_ok (K := K)).c_ne h0
end GlobalTheory.Square.TwoStep
