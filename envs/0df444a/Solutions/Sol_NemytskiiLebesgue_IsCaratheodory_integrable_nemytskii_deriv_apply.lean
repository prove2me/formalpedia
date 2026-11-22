-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.integrable_nemytskii_deriv_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:38:48.480942+00:00
-- url     : https://prove2.me/submissions/6b831d2d-74e1-4462-9f3c-fc0d984535b0

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Frechet
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Nemytskii
public import Definitions.Def_LeanPool_NemytskiiLebesgue_RealIso
public import Definitions.Def_LeanPool_NemytskiiLebesgue_IntegralFunctional
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_memLp_nemytskii_deriv
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_fst
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_norm
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_snd


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
    {m : ℕ} {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ)} (hf' : IsCaratheodory f' μ)
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {b : Ω → ℝ} (hbq : MemLp b ↱q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hf'bCp : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, ‖f' ω ξ‖ ≤ b ω + C * ‖ξ‖ ^ (p - 1))
    {u : Ω → ℝ^m} (hup : MemLp u ↱p μ)
    {v : Ω → ℝ^m} (hvp : MemLp v ↱p μ) :
    Integrable (fun ω : Ω => (f' ω (u ω)) (v ω)) μ := by
  have f'_u_in_Lq : MemLp (fun ω : Ω => f' ω (u ω)) ↱q μ := by
    apply_rules [memLp_nemytskii_deriv]
  have integrabl : Integrable (fun ω : Ω => ‖f' ω (u ω)‖ * ‖v ω‖) μ := by
    convert! f'_u_in_Lq.norm.integrable_mul hvp.norm using 1
    exact hpq.symm.ennrealOfReal
  apply integrabl.mono'
  · have cont : Continuous (fun p : (ℝ^m →L[ℝ] ℝ) × ℝ^m => p.fst p.snd) := by
      fun_prop
    exact cont.comp_aestronglyMeasurable (f'_u_in_Lq.aestronglyMeasurable.prodMk
      hvp.aestronglyMeasurable)
  · exact Filter.Eventually.of_forall ↓(ContinuousLinearMap.le_opNorm _ _)
end IsCaratheodory
end NemytskiiLebesgue
