-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.integralFunctional_frechet_deriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:41:17.264747+00:00
-- url     : https://prove2.me/submissions/33332f7d-ed11-4a6c-b64e-20de22e711ca

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Frechet
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Nemytskii
public import Definitions.Def_LeanPool_NemytskiiLebesgue_RealIso
public import Definitions.Def_LeanPool_NemytskiiLebesgue_IntegralFunctional
public import Theorems.Thm_NemytskiiLebesgue_hasFDerivAt_outR1_outR1nested
public import Theorems.Thm_NemytskiiLebesgue_outR1nested_growth
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_integrable_nemytskii_deriv_apply
public import Theorems.Thm_NemytskiiLebesgue_norm_integral_le_eLpNorm_one_toReal
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_eLpNorm_frechet_remainder_le_ofReal_mul_eLpNorm
public import Theorems.Thm_NemytskiiLebesgue_eLpNorm_realLIE


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
    {f : Ω → ℝ^m → ℝ} (hf : IsCaratheodory f μ)
    {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ)} (hf' : IsCaratheodory f' μ)
    (hff' : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, HasFDerivAt (f ω) (f' ω ξ) ξ)
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {b : Ω → ℝ} (h0b : 0 ≤ᵐ[μ] b) (hbq : MemLp b ↱q μ)
    {C : ℝ} (hC : 0 < C)
    (hf'bCp : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, ‖f' ω ξ‖ ≤ b ω + C * ‖ξ‖ ^ (p - 1))
    {u : Ω → ℝ^m} (hup : MemLp u ↱p μ) :
    (∀ v : Ω → ℝ^m, MemLp v ↱p μ →
      Integrable (fun ω : Ω => (f' ω (u ω)) (v ω)) μ) ∧
    (∀ ε > 0, ∃ δ > 0, ∀ l : Ω → ℝ^m,
      MemLp l ↱p μ →
        eLpNorm l ↱p μ ≤ ↱δ →
          ‖∫ ω : Ω, (f ω (u ω + l ω) - f ω (u ω) - (f' ω (u ω)) (l ω)) ∂μ‖ ≤
            ε * (eLpNorm l ↱p μ).toReal) := by
  constructor
  · exact ↓(hf'.integrable_nemytskii_deriv_apply hpq hbq hC.le hf'bCp hup)
  · have nemytskii_bound : ∀ ε > 0, ∃ δ > 0, ∀ l : Ω → ℝ^m,
        MemLp l ↱p μ → eLpNorm l ↱p μ ≤ ↱δ →
          eLpNorm (fun ω : Ω => NemytskiiLebesgue.outR1 f ω (u ω + l ω) - NemytskiiLebesgue.outR1 f
            ω (u ω) - NemytskiiLebesgue.outR1nested f' ω (u ω) (l ω)) ↱(1 : ℝ) μ ≤
          ↱ε * eLpNorm l ↱p μ := by
      apply hf.outR1.eLpNorm_frechet_remainder_le_ofReal_mul_eLpNorm hf'.outR1nested
        (hasFDerivAt_outR1_outR1nested hff') hpq.lt.le hpq.symm.lt.le hpq.symm h0b hbq hC _ hup
      rw [hpq.div_conj_eq_sub_one]
      exact outR1nested_growth f' hf'bCp
    intro ε hε
    obtain ⟨δ, hδ, hbound⟩ := nemytskii_bound ε hε
    use δ, hδ
    intro l hl hl'
    have key := hbound l hl hl'
    change eLpNorm (fun ω => realLIE (f ω (u ω + l ω)) - realLIE (f ω (u ω)) -
      realLIE (f' ω (u ω) (l ω))) ↱(1 : ℝ) μ ≤ ↱ε * eLpNorm l ↱p μ at key
    simp only [← map_sub, eLpNorm_realLIE, ENNReal.ofReal_one] at key
    apply (norm_integral_le_eLpNorm_one_toReal _).trans
    convert! ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hl.eLpNorm_ne_top) key using 1
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hε.le]
end IsCaratheodory
end NemytskiiLebesgue
