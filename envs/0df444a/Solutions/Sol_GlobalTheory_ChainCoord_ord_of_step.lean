-- Prove2me | solution 1 for GlobalTheory.ChainCoord.ord_of_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:58:37.842729+00:00
-- url     : https://prove2.me/submissions/b6c92c23-7bcf-475e-a9d4-c61a5e1d9adb

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PsWeightCalculus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightedOrderGePrimePowOfSumPurePowersAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainLemmaMultivariatePowerSeriesCoordinateForm
import Theorems.Thm_GlobalTheory_ChainCoord_coeff_pow_congr
import Theorems.Thm_GlobalTheory_ChainCoord_coeff_lgSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh MvPowerSeries
open GlobalTheory GlobalTheory.ChainCoord
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : ℕ} {ρ : Fin M → ℝ}
namespace GlobalTheory.ChainCoord
theorem _root_.solution {d l : ℕ} (hl : 2 ≤ l) (al : Fin d → ℕ → Fin d → C)
    (h0 : ∀ c e, al c 0 e = if c = e then 1 else 0)
    (t μ z : Fin d → MvPowerSeries (Fin M) C) (ht : ∀ c, constantCoeff (t c) = 0)
    (hμ : ∀ c, constantCoeff (μ c) = 0) (hz : ∀ e, lgSum l al t e = z e) (w : ℝ)
    (step : ∀ t' : Fin d → MvPowerSeries (Fin M) C, (∀ c, OrdGe v ρ (t' c - μ c) w) →
      ∀ N e, OrdGe v ρ (z e - (∑ n ∈ Finset.range (N + 2), ∑ c,
        MvPowerSeries.C (R := C) (al c (n + 1) e) * t' c ^ (l ^ (n + 1))) - μ e) w) :
    ∀ c, OrdGe v ρ (t c - μ c) w := by
  classical
  have key : ∀ D : ℕ, ∀ α : Fin M →₀ ℕ, Finsupp.degree α = D → ∀ c,
      (((w - ∑ m, ρ m * α m : ℝ)) : WithTop ℝ) ≤ v (coeff α (t c - μ c)) := by
    intro D
    induction D using Nat.strong_induction_on with
    | _ D ih =>
      intro α hα e
      let ν : Fin d → MvPowerSeries (Fin M) C := fun c β =>
        if Finsupp.degree β < D then coeff β (t c - μ c) else 0
      have hν : ∀ c β, coeff β (ν c) =
          if Finsupp.degree β < D then coeff β (t c - μ c) else 0 := fun _ _ => rfl
      have h1 : ∀ c, OrdGe v ρ (μ c + ν c - μ c) w := fun c β => by
        rw [add_sub_cancel_left, hν]
        split_ifs with hβ
        · exact ih _ hβ β rfl c
        · simp
      have h2 := step (fun c => μ c + ν c) h1 D e α
      have h3 : ∀ c, constantCoeff (μ c + ν c) = 0 := fun c => by
        rw [map_add, hμ, zero_add, ← coeff_zero_eq_constantCoeff_apply, hν]
        split_ifs
        · rw [coeff_zero_eq_constantCoeff_apply, map_sub, ht, hμ, sub_self]
        · rfl
      have h4 : ∀ c n, coeff α ((μ c + ν c) ^ (l ^ (n + 1))) = coeff α (t c ^ (l ^ (n + 1))) :=
        fun c n => by
          refine coeff_pow_congr (h3 c) (ht c) ?_ (fun β hβ => ?_) α hα
          · exact le_trans hl (Nat.le_self_pow (by omega) l)
          · rw [map_add, hν, if_pos hβ, map_sub]; ring
      have h5 := coeff_lgSum hl al t ht e α (D + 2 + 1) (by omega)
      rw [hz, Finset.sum_range_succ'] at h5
      simp only [h0, pow_zero, pow_one, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true] at h5
      convert h2 using 2
      simp only [map_sub, map_sum, coeff_C_mul, h4, h5]
      ring
  exact fun c α => key _ α rfl c
end GlobalTheory.ChainCoord
