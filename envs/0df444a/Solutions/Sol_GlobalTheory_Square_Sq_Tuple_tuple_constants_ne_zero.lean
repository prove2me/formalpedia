-- Prove2me | solution 1 for GlobalTheory.Square.Sq.Tuple.tuple_constants_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:57:14.427053+00:00
-- url     : https://prove2.me/submissions/aade2de9-e680-4b26-b67d-a61ea32aff49

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero

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
namespace Sq.Tuple
theorem _root_.solution {S : Sq K} {hd y : ℕ} {σ₀ : K →+* ℂ} {a : An (S.p + S.q)} {Z : Co K S.κ} {w : Pl K}
    {dl : ℝ} (h : S.Tuple σ₀ a Z w dl) (hS : S.OK hd y) : a.c0 ≠ 0 ∧ a.c ≠ 0 := by
  have he := hS.e0_eq
  have hle := hS.sqrt_error_le_half
  have hc0 : a.c0 ≠ 0 := by
    intro h0
    have hz : ∀ x k, Z.z x k = 0 := by
      intro x k
      have := h.bottom x k
      rw [h0, zero_mul, mul_eq_zero] at this
      rcases this with h1 | h1
      · exact (map_eq_zero σ₀).1 h1
      · exact absurd h1 hS.Om_ne
    have hn := h.norm_eq
    have : normAlg S.G Z.gam Z.z = 0 := by simp [normAlg, hz]
    rw [this, map_zero, zero_mul] at hn
    refine mul_ne_zero hS.A_ne (Finset.prod_ne_zero_iff.2 fun s hs => ?_) hn.symm
    rw [Finset.mem_Icc] at hs
    exact h.L_ne s hs.1 (by omega)
  refine ⟨hc0, fun h0 => ?_⟩
  have ht := h.tower
  rw [h0, zero_mul] at ht
  refine mul_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => h.u_ne i) hc0)
    (Finset.prod_ne_zero_iff.2 fun k hk => ?_) ht.symm
  rw [Finset.mem_range] at hk
  exact h.L_ne _ (by omega) (by omega)
end Sq.Tuple
end GlobalTheory.Square
