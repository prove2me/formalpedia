-- Prove2me | solution 1 for GlobalTheory.Square.IsAwayUnit.ne_zero_and_vw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:13:27.825969+00:00
-- url     : https://prove2.me/submissions/dbbe6544-b233-443f-b944-ed7dc17f9c55

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero
import Theorems.Thm_GlobalTheory_Square_vw_eq_zero_of_notMem
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_mul


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
namespace GlobalTheory.Square
namespace IsAwayUnit
theorem _root_.solution {m : ℕ} {x : K} (h : IsAwayUnit m x) (w : Pl K) (hm : (m : 𝓞 K) ∉ w.asIdeal) :
    x ≠ 0 ∧ vw w x = 0 := by
  obtain ⟨a, k, k', ⟨b, hb⟩, hx⟩ := h
  have hpow : ∀ j : ℕ, (m : 𝓞 K) ^ j ∉ w.asIdeal := fun j hj => hm (w.isPrime.mem_of_pow_mem j hj)
  have ha : a ∉ w.asIdeal := fun h => hpow k' (hb ▸ w.asIdeal.mul_mem_right b h)
  have ha0 : (a : K) ≠ 0 := by
    intro h
    have : a = 0 := by exact_mod_cast h
    exact ha (this ▸ w.asIdeal.zero_mem)
  have hx0 : x ≠ 0 := by rintro rfl; rw [zero_mul] at hx; exact ha0 hx.symm
  have hk0 : (m : K) ^ k ≠ 0 := by intro h; rw [h, mul_zero] at hx; exact ha0 hx.symm
  refine ⟨hx0, ?_⟩
  have h1 := Formalism.DivisionValues.ValuationRepresentative.vw_mul w x _ hx0 hk0
  have h2 := vw_eq_zero_of_notMem w ha
  have h3 := vw_eq_zero_of_notMem w (hpow k)
  have h4 : ((((m : 𝓞 K) ^ k : 𝓞 K)) : K) = (m : K) ^ k := by simp
  rw [h4] at h3
  rw [hx, h2, h3] at h1
  omega
end IsAwayUnit
end GlobalTheory.Square
