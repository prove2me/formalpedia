-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.memLp_nemytskii_deriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:37:59.691395+00:00
-- url     : https://prove2.me/submissions/766a4b61-a137-4ac4-bd68-fce056386d8c

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Frechet
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Nemytskii
public import Definitions.Def_LeanPool_NemytskiiLebesgue_RealIso
public import Definitions.Def_LeanPool_NemytskiiLebesgue_IntegralFunctional
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_aestronglyMeas_nemytskii_of_aestronglyMeas
public import Theorems.Thm_NemytskiiLebesgue_memLp_nemytskii_of_growth_of_aestronglyMeasurable


set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory
open scoped ENNReal
namespace NemytskiiLebesgue
namespace IsCaratheodory
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ}
    {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ)} (hf' : IsCaratheodory f' μ)
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {b : Ω → ℝ} (hbq : MemLp b ↱q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfbCp : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, ‖f' ω ξ‖ ≤ b ω + C * ‖ξ‖ ^ (p - 1))
    {u : Ω → ℝ^m} (hup : MemLp u ↱p μ) :
    MemLp (fun ω : Ω => f' ω (u ω)) ↱q μ :=
  have hp : 1 ≤ p :=
    hpq.lt.le
  have hq : 1 ≤ q :=
    hpq.symm.lt.le
  memLp_nemytskii_of_growth_of_aestronglyMeasurable
    (zero_lt_one.trans_le (ENNReal.ofReal_one ▸ ENNReal.ofReal_le_ofReal hp))
    ENNReal.ofReal_ne_top
    (ENNReal.ofReal_one ▸ ENNReal.ofReal_le_ofReal hq)
    ENNReal.ofReal_ne_top
    hbq
    hC
    (by
      simp_all only [ENNReal.toReal_div]
      change ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, ‖f' ω ξ‖ ≤ |b ω| + C * ‖ξ‖ ^ ((↱p).toReal / (↱q).toReal)
      filter_upwards [hfbCp] with ω hω ξ using
        le_trans
          (hω ξ)
          (add_le_add (le_abs_self _) (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _)
            le_rfl (by linarith)) hC))
        |> le_trans <| by simp [hpq.div_conj_eq_sub_one,
            ENNReal.toReal_ofReal (zero_le_one.trans hp),
            ENNReal.toReal_ofReal (zero_le_one.trans hq)]
    )
    hup
    (hf'.aestronglyMeas_nemytskii_of_aestronglyMeas hup.aestronglyMeasurable)
end IsCaratheodory
end NemytskiiLebesgue
