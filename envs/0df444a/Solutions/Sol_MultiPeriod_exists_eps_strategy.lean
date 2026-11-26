-- Prove2me | solution 1 for MultiPeriod.exists_eps_strategy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:14:11.114813+00:00
-- url     : https://prove2.me/submissions/af06df50-7865-4d6e-9f84-199831e0c22a

import Definitions.Def_BicausalOT_Defs
import Definitions.Def_BicausalOT_UpperBound
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_BicausalOT_MultiPeriod
import Theorems.Thm_eps_optimal_element


set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section
open MultiPeriod
variable (X Y : ℕ → Type*)
variable {X Y}
variable [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]
variable (κμ : (t : ℕ) → XHist X t → Measure (X (t + 1)))
variable (κν : (t : ℕ) → YHist Y t → Measure (Y (t + 1)))
variable (c : (t : ℕ) → PairHist X Y t → ℝ≥0∞)
variable {κμ κν}
variable (κμ κν)
namespace MultiPeriod
theorem _root_.solution (T : ℕ)
    (hne : ∀ t (h : PairHist X Y t), (Feas κμ κν t h).Nonempty)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ γε : Strat X Y,
      (∀ t h, γε t h ∈ Feas κμ κν t h) ∧
      ∀ t (h : PairHist X Y t),
        ∫⁻ z, VGo c κμ κν (T - t - 1) (t + 1) (h, z) ∂(γε t h)
          ≤ (⨅ (γm : Measure (X (t + 1) × Y (t + 1)))
              (_ : γm ∈ Feas κμ κν t h),
              ∫⁻ z, VGo c κμ κν (T - t - 1) (t + 1) (h, z) ∂γm) + ε := by
  have key : ∀ t (h : PairHist X Y t),
      ∃ γm ∈ Feas κμ κν t h,
        ∫⁻ z, VGo c κμ κν (T - t - 1) (t + 1) (h, z) ∂γm
          ≤ (⨅ (γm' : Measure (X (t + 1) × Y (t + 1)))
              (_ : γm' ∈ Feas κμ κν t h),
              ∫⁻ z, VGo c κμ κν (T - t - 1) (t + 1) (h, z) ∂γm') + ε :=
    fun t h => eps_optimal_element (Feas κμ κν t h) (hne t h)
      (fun γm => ∫⁻ z, VGo c κμ κν (T - t - 1) (t + 1) (h, z) ∂γm) ε hε
  choose γε hmem hopt using key
  exact ⟨γε, hmem, hopt⟩
end MultiPeriod
