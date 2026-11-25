-- Prove2me | solution 1 for GlobalTheory.Nef.isRat_iff_exists_ratFunc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:07:59.005345+00:00
-- url     : https://prove2.me/submissions/17586c87-111e-46ba-a5ed-bc8f3e5b297b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRatIffExistsRatFunc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef
namespace GlobalTheory.Nef
theorem _root_.solution : ∀ (F : Type) [Field F] (φ : PowerSeries F), IsRat φ ↔
    ∃ ρ : RatFunc F, algebraMap (RatFunc F) (LaurentSeries F) ρ = algebraMap (PowerSeries F) (LaurentSeries F) φ := by
  intro F _ φ
  have key : ∀ P : F[X], algebraMap (RatFunc F) (LaurentSeries F) (algebraMap F[X] (RatFunc F) P) =
      algebraMap (PowerSeries F) (LaurentSeries F) (P : PowerSeries F) := by
    intro P
    exact (RatFunc.coe_coe P).symm
  constructor
  · rintro ⟨p, q, hq, h⟩
    refine ⟨algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q, ?_⟩
    have hq' : algebraMap (PowerSeries F) (LaurentSeries F) (q : PowerSeries F) ≠ 0 := by
      rw [← key]
      exact (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))).2 hq)
    rw [map_div₀, key, key, div_eq_iff hq', ← h, map_mul, mul_comm]
  · rintro ⟨ρ, h⟩
    refine ⟨ρ.num, ρ.denom, ρ.denom_ne_zero, ?_⟩
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    change algebraMap (PowerSeries F) (LaurentSeries F) _ = algebraMap (PowerSeries F) (LaurentSeries F) _
    rw [map_mul, ← key, ← key, ← h, ← map_mul]
    congr 1
    have hd : algebraMap F[X] (RatFunc F) ρ.denom ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))).2 ρ.denom_ne_zero
    have e : ρ = algebraMap F[X] (RatFunc F) ρ.num / algebraMap F[X] (RatFunc F) ρ.denom :=
      (RatFunc.num_div_denom ρ).symm
    calc algebraMap F[X] (RatFunc F) ρ.denom * ρ
        = algebraMap F[X] (RatFunc F) ρ.denom *
            (algebraMap F[X] (RatFunc F) ρ.num / algebraMap F[X] (RatFunc F) ρ.denom) := congrArg _ e
      _ = algebraMap F[X] (RatFunc F) ρ.num := mul_div_cancel₀ _ hd
end GlobalTheory.Nef
