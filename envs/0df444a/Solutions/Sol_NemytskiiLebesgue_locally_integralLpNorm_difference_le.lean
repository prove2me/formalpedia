-- Prove2me | solution 1 for NemytskiiLebesgue.locally_integralLpNorm_difference_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:38:07.187011+00:00
-- url     : https://prove2.me/submissions/858216aa-4ca8-4686-8bf9-0038758bea21

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Lipschitz
public import Theorems.Thm_NemytskiiLebesgue_ennreal_holderTriple_of_lt_of_lt
public import Theorems.Thm_NemytskiiLebesgue_eLpNorm_one_ofReal_eq_measure_univ_rpow_inv
public import Theorems.Thm_NemytskiiLebesgue_eLpNorm_norm_rpow_div_eq
public import Theorems.Thm_NemytskiiLebesgue_integralLpNorm_le_eLpNorm_of_ae_le
public import Theorems.Thm_NemytskiiLebesgue_rpow_le_ofReal_rpow_of_le_ofReal

section
public section
namespace NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory
open scoped NNReal ENNReal
private lemma aestronglyMeas_mul_one_add_norm_rpow_add_norm_rpow
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D]
    {u : Ω → D} (hu : AEStronglyMeasurable u μ)
    {v : Ω → D} (hv : AEStronglyMeasurable v μ)
    (C α : ℝ) :
    AEStronglyMeasurable (fun ω : Ω => C * (1 + ‖u ω‖ ^ α + ‖v ω‖ ^ α)) μ :=
  AEStronglyMeasurable.const_mul
    (AEStronglyMeasurable.add
      (AEStronglyMeasurable.add aestronglyMeasurable_const
        (hu.norm.aemeasurable.pow_const α).aestronglyMeasurable)
        (hv.norm.aemeasurable.pow_const α).aestronglyMeasurable)
    _
private lemma eLpNorm_one_add_norm_rpow_add_norm_rpow_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {p α : ℝ} (h1p : 1 ≤ p) (hα : 0 < α) (hpα : α ≤ p)
    {D : Type*} [NormedAddCommGroup D]
    {u : Ω → D} (hu : AEStronglyMeasurable u μ)
    {v : Ω → D} (hv : AEStronglyMeasurable v μ)
    {R : ℝ} (hR : 0 < R)
    (huR : eLpNorm u ↱p μ ≤ ↱R)
    (hvR : eLpNorm v ↱p μ ≤ ↱R) :
    eLpNorm (fun ω : Ω => (1 : ℝ) + ‖u ω‖ ^ α + ‖v ω‖ ^ α) ↱(p / α) μ ≤ ↱((μ ⊤).toReal ^ (α / p) +
      2 * R ^ α) := by
  have triangle :
      eLpNorm (fun ω : Ω => 1 + ‖u ω‖ ^ α + ‖v ω‖ ^ α) ↱(p / α) μ ≤
      eLpNorm ↓(1 : ℝ) ↱(p / α) μ +
      eLpNorm (‖u ·‖ ^ α) ↱(p / α) μ +
      eLpNorm (‖v ·‖ ^ α) ↱(p / α) μ := by
    have hpower : 1 ≤ ↱(p / α) :=
      ENNReal.ofReal_one ▸ ENNReal.ofReal_le_ofReal ((le_div_iff₀ hα).2 (by simpa))
    have hα_nonneg : 0 ≤ α := hα.le
    exact (eLpNorm_add_le (by fun_prop) (by fun_prop) hpower).trans
      (add_le_add (eLpNorm_add_le (by fun_prop) (by fun_prop) hpower) le_rfl)
  rw [two_mul]
  convert triangle.trans _ using 1
  have h0p : 0 < p := zero_lt_one.trans_le h1p
  convert
    add_le_add_three
      (eLpNorm_one_ofReal_eq_measure_univ_rpow_inv μ h0p hα).le
      (rpow_le_ofReal_rpow_of_le_ofReal hα.le hR huR)
      (rpow_le_ofReal_rpow_of_le_ofReal hα.le hR hvR)
      using 1
  · rw [eLpNorm_norm_rpow_div_eq u hu hα h0p,
        eLpNorm_norm_rpow_div_eq v hv hα h0p]
  · change ↱((μ ⊤).toReal ^ (α / p) + (R ^ α + R ^ α)) = μ ⊤ ^ (α / p) + ↱(R ^ α) + ↱(R ^ α)
    rw [ENNReal.ofReal_add,
        ENNReal.ofReal_add,
        ←ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (measure_ne_top _ _)]
    · ring
    all_goals positivity
end NemytskiiLebesgue
end
end

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory
open scoped NNReal ENNReal
namespace NemytskiiLebesgue
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {D : Type*} [NormedAddCommGroup D]
    {F : Type*} [NormedAddCommGroup F]
    {f : Ω → D → F}
    {p : ℝ} (h1p : 1 ≤ p)
    {q : ℝ} (h1q : 1 ≤ q)
    {α : ℝ} (hα : 0 ≤ α)
    (hqpα : q = p / (α + 1))
    {C : ℝ} (hC : 0 < C)
    (hfC : ∀ᵐ ω : Ω ∂μ, ∀ ξ η : D, ‖f ω ξ - f ω η‖ ≤ C * (1 + ‖ξ‖ ^ α + ‖η‖ ^ α) * ‖ξ - η‖)
    {R : ℝ} (hR : 0 < R) :
    ∃ L : ℝ, 0 < L ∧
      ∀ u v : Ω → D,
        MemLp u ↱p μ →
        MemLp v ↱p μ →
        eLpNorm u ↱p μ ≤ ↱R →
        eLpNorm v ↱p μ ≤ ↱R →
        integralLpNorm (fun ω : Ω => f ω (u ω) - f ω (v ω)) ↱q μ ≤ ↱L * eLpNorm (u - v) ↱p μ := by
  by_cases α_pos : 0 < α
  · refine
      ⟨C * ((μ ⊤).toReal ^ (α / p) + 2 * R ^ α),
       mul_pos hC
        (add_pos_of_nonneg_of_pos
          (Real.rpow_nonneg ENNReal.toReal_nonneg _)
          (mul_pos zero_lt_two (Real.rpow_pos_of_pos hR α))),
       fun u v hu hv huR hvR => ?_⟩
    have holder : eLpNorm (fun ω : Ω => C * (1 + ‖u ω‖ ^ α + ‖v ω‖ ^ α) * ‖u ω - v ω‖) ↱q μ ≤
                  eLpNorm (fun ω : Ω => C * (1 + ‖u ω‖ ^ α + ‖v ω‖ ^ α)) ↱(p / α) μ * eLpNorm (fun
                    ω : Ω => ‖u ω - v ω‖) ↱p μ := by
      have holde :
        ∀ g l : Ω → ℝ,
          AEStronglyMeasurable g μ → AEStronglyMeasurable l μ →
            eLpNorm (fun ω : Ω => g ω * l ω) ↱q μ ≤ eLpNorm g ↱(p / α) μ * eLpNorm l ↱p μ := by
        intros g l hg hl
        convert! eLpNorm_smul_le_mul_eLpNorm hl hg using 1
        convert ennreal_holderTriple_of_lt_of_lt (by positivity) α_pos using 1
        rw [hqpα]
      apply holde
      · exact aestronglyMeas_mul_one_add_norm_rpow_add_norm_rpow
          hu.aestronglyMeasurable hv.aestronglyMeasurable C α
      · exact (hu.aestronglyMeasurable.sub hv.aestronglyMeasurable).norm
    refine le_trans (integralLpNorm_le_eLpNorm_of_ae_le
      ((aestronglyMeas_mul_one_add_norm_rpow_add_norm_rpow
        hu.aestronglyMeasurable hv.aestronglyMeasurable C α).mul
        (hu.aestronglyMeasurable.sub hv.aestronglyMeasurable).norm) ?_) (holder.trans ?_)
    · filter_upwards [hfC] with ω hω using le_trans (hω _ _) (le_abs_self _)
    · gcongr
      · convert!
          mul_le_mul_right
            (eLpNorm_one_add_norm_rpow_add_norm_rpow_le h1p α_pos
              (show α ≤ p by
                rw [hqpα] at h1q
                rw [le_div_iff₀] at h1q <;> nlinarith
              ) hu.aestronglyMeasurable hv.aestronglyMeasurable hR huR hvR
            ) ↱C using 1
        · simpa only [Pi.smul_def, smul_eq_mul, Real.enorm_of_nonneg hC.le] using
            eLpNorm_const_smul C (fun ω => 1 + ‖u ω‖ ^ α + ‖v ω‖ ^ α) ↱(p / α) μ
        · rw [ENNReal.ofReal_mul hC.le]
      · exact (eLpNorm_norm (u - v)).le
  · refine ⟨3 * C, by positivity, ?_⟩
    intro u v hu hv huR hvR
    have hα0 : α = 0 := eq_of_le_of_ge (Std.not_lt.→ α_pos) hα
    have h3C : ∀ᵐ ω : Ω ∂μ, ‖f ω (u ω) - f ω (v ω)‖ ≤ 3 * C * ‖u ω - v ω‖ := by
      filter_upwards [hfC] with ω hω using le_trans (hω (u ω) (v ω)) (by
        norm_num [hα0]
        nlinarith [norm_nonneg (u ω - v ω)])
    have hqp : q = p
    · rw [hqpα, hα0]
      norm_num
    rw [hqp]
    have hmeas := (hu.aestronglyMeasurable.sub hv.aestronglyMeasurable).norm.const_mul (3 * C)
    refine (integralLpNorm_le_eLpNorm_of_ae_le hmeas ?_).trans_eq ?_
    · exact h3C.mono fun ω hω => hω.trans (le_abs_self _)
    · rw [show (fun ω => 3 * C * ‖(u - v) ω‖) =
          (3 * C) • (fun ω => ‖(u - v) ω‖) from rfl,
        eLpNorm_const_smul, Real.enorm_of_nonneg (by positivity),
        eLpNorm_norm (u - v)]
end NemytskiiLebesgue
