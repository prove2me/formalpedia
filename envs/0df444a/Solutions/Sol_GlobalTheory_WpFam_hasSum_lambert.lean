-- Prove2me | solution 1 for GlobalTheory.WpFam.hasSum_lambert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:28:14.478621+00:00
-- url     : https://prove2.me/submissions/3ff63186-7a97-43d8-981e-222598467264

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumLambertDoubleSeriesDivisors
import Theorems.Thm_GlobalTheory_WpFam_summable_lambert_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
open GlobalTheory GlobalTheory.WpFam
namespace GlobalTheory.WpFam
theorem _root_.solution : ∀ (e : ℕ) (Q : ℂ) (c : ℕ → ℕ → ℂ), ‖Q‖ < 1 → (∀ d m, ‖c d m‖ ≤ 1) → HasSum (fun k : ℕ => (∑ m ∈ k.divisors, (m : ℂ) ^ e * c (k / m) m) * Q ^ k) (∑' d : ℕ+, ∑' m : ℕ+, ((m : ℕ) : ℂ) ^ e * c d m * Q ^ ((d : ℕ) * (m : ℕ))) := by
  intro e Q c hQ hc
  have hs := summable_lambert_prod e Q c hQ hc
  rw [← hs.tsum_prod]
  have h1 := sigmaAntidiagonalEquivProd.hasSum_iff.mpr hs.hasSum
  have h2 := h1.sigma (fun n => hasSum_fintype _)
  refine (Function.Injective.hasSum_iff (g := PNat.val) PNat.coe_injective ?_).mp ?_
  · intro k hk
    have : k = 0 := by
      by_contra h
      exact hk ⟨⟨k, Nat.pos_of_ne_zero h⟩, rfl⟩
    simp [this]
  · refine HasSum.congr_fun h2 fun n => ?_
    symm
    have h3 : ∀ x : Nat.divisorsAntidiagonal (n : ℕ),
        ((fun x : ℕ+ × ℕ+ => ((x.2 : ℕ) : ℂ) ^ e * c x.1 x.2 * Q ^ ((x.1 : ℕ) * (x.2 : ℕ))) ∘
          sigmaAntidiagonalEquivProd) ⟨n, x⟩ =
        (fun y : ℕ × ℕ => (y.2 : ℂ) ^ e * c y.1 y.2 * Q ^ (y.1 * y.2)) x.1 := fun x => rfl
    rw [Finset.sum_congr rfl (fun x _ => h3 x),
      Finset.sum_coe_sort (Nat.divisorsAntidiagonal (n : ℕ))
        (fun y : ℕ × ℕ => (y.2 : ℂ) ^ e * c y.1 y.2 * Q ^ (y.1 * y.2)),
      Nat.sum_divisorsAntidiagonal' (fun a b : ℕ => (b : ℂ) ^ e * c a b * Q ^ (a * b))]
    simp only [Function.comp_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun m hm => by
      rw [Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hm)]
end GlobalTheory.WpFam
