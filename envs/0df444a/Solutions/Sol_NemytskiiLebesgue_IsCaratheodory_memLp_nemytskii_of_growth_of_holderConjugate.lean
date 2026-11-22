-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.memLp_nemytskii_of_growth_of_holderConjugate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:38:38.96192+00:00
-- url     : https://prove2.me/submissions/67765231-2511-43e3-832e-87ff3e9fa3e7

module
public import Mathlib.MeasureTheory.Function.UnifTight
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_memLp_nemytskii_of_growth
public import Theorems.Thm_NemytskiiLebesgue_ofReal_div_ofReal_toReal


set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped NNReal ENNReal Topology
namespace NemytskiiLebesgue
namespace IsCaratheodory
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D]
    {f : Ω → D → D} (hf : IsCaratheodory f μ)
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {a : Ω → ℝ} (haq : MemLp a ↱q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω : Ω ∂μ, ∀ ξ : D, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ (p / q))
    {u : Ω → D} (hup : MemLp u ↱p μ) :
    MemLp (fun ω : Ω => f ω (u ω)) ↱q μ := by
  have hp : 1 ≤ p := by
    rw [Real.holderConjugate_iff] at hpq
    exact hpq.left.le
  have hq : 1 ≤ q := by
    rw [Real.holderConjugate_comm, Real.holderConjugate_iff] at hpq
    exact hpq.left.le
  exact
    hf.memLp_nemytskii_of_growth
      (by rwa [ENNReal.one_le_ofReal]) ENNReal.ofReal_ne_top
      (by rwa [ENNReal.one_le_ofReal]) ENNReal.ofReal_ne_top
      haq hC (ofReal_div_ofReal_toReal (zero_le_one.trans hp) (zero_le_one.trans hq) ▸ hfaCpq)
      hup
end IsCaratheodory
end NemytskiiLebesgue
