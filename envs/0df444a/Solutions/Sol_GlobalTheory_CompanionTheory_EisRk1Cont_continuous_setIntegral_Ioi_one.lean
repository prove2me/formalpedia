-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EisRk1Cont.continuous_setIntegral_Ioi_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:26:21.319004+00:00
-- url     : https://prove2.me/submissions/9cf0acab-d044-4210-ad34-1301f7fbd493

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousSetIntegralIoiOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisRk1Cont
namespace GlobalTheory.CompanionTheory.EisRk1Cont
theorem _root_.solution {Z : Type*} [TopologicalSpace Z] (F : Z → ℝ → ℂ)
    (hF : ∀ z y, 1 ≤ y → ContinuousAt (fun w : Z × ℝ ↦ F w.1 w.2) (z, y))
    (hb : ∀ z₀, ∃ V ∈ 𝓝 z₀, ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ V, ∀ x : ℝ, 1 ≤ x → ‖F z x‖ ≤ M * x ^ (-3 : ℝ)) :
    Continuous fun z ↦ ∫ x in Ioi (1 : ℝ), F z x := by
  have e2 : ∀ x : ℝ, 0 < x → x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := fun x hx => by
    rw [Real.rpow_neg hx.le]; congr 1; exact_mod_cast Real.rpow_natCast x 2
  have e3 : ∀ x : ℝ, 0 < x → x ^ (-3 : ℝ) = (x ^ 3)⁻¹ := fun x hx => by
    rw [Real.rpow_neg hx.le]; congr 1; exact_mod_cast Real.rpow_natCast x 3
  have hcont : ∀ z, ContinuousOn (F z) (Ioi 1) := fun z y hy =>
    (ContinuousAt.comp_of_eq (hF z y (le_of_lt hy))
      (by fun_prop : Continuous fun t : ℝ => (z, t)).continuousAt rfl).continuousWithinAt
  have hint : ∀ z, IntegrableOn (F z) (Ioi 1) := by
    intro z
    obtain ⟨V, hV, M, -, hM⟩ := hb z
    refine Integrable.mono'
      ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) one_pos).const_mul M)
      ((hcont z).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => ?_)
    exact hM z (mem_of_mem_nhds hV) x (le_of_lt hx)
  rw [continuous_iff_continuousAt]
  intro z₀
  rw [Metric.continuousAt_iff']
  intro ε hε
  obtain ⟨V, hV, M, hM0, hM⟩ := hb z₀
  obtain ⟨R, hR1, hRM⟩ : ∃ R : ℝ, 1 ≤ R ∧ 4 * M / ε ≤ R :=
    ⟨max 1 (4 * M / ε), le_max_left _ _, le_max_right _ _⟩
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
  have hδ0 : 0 < ε / 2 * (R ^ 2)⁻¹ := mul_pos (half_pos hε) (inv_pos.mpr (pow_pos hR0 2))
  have hunif : ∀ᶠ z in 𝓝 z₀, ∀ y ∈ Icc (1 : ℝ) R,
      dist (F z y) (F z₀ y) < ε / 2 * (R ^ 2)⁻¹ := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually fun y hy => ?_
    have h1 := Metric.tendsto_nhds.mp (hF z₀ y hy.1).tendsto _ (half_pos hδ0)
    have h2 := Metric.tendsto_nhds.mp
      (ContinuousAt.comp_of_eq (hF z₀ y hy.1)
        ((by fun_prop : Continuous fun p : Z × ℝ => (z₀, p.2)).continuousAt (x := (z₀, y))) rfl).tendsto
      _ (half_pos hδ0)
    filter_upwards [h1, h2] with p hp1 hp2
    calc dist (F p.1 p.2) (F z₀ p.2)
        ≤ dist (F p.1 p.2) (F z₀ y) + dist (F z₀ p.2) (F z₀ y) := dist_triangle_right _ _ _
      _ < ε / 2 * (R ^ 2)⁻¹ / 2 + ε / 2 * (R ^ 2)⁻¹ / 2 := add_lt_add hp1 hp2
      _ = ε / 2 * (R ^ 2)⁻¹ := add_halves _
  have hg : IntegrableOn (fun x : ℝ => ε / 2 * x ^ (-2 : ℝ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos).const_mul _
  have hgi : ∫ x in Ioi (1 : ℝ), ε / 2 * x ^ (-2 : ℝ) = ε / 2 := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos]
    norm_num
  filter_upwards [hV, hunif] with z hzV hz
  have key : ‖∫ x in Ioi (1 : ℝ), F z x - F z₀ x‖ ≤ ∫ x in Ioi (1 : ℝ), ε / 2 * x ^ (-2 : ℝ) := by
    refine norm_integral_le_of_norm_le hg ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => ?_)
    have hx1 : (1 : ℝ) < x := hx
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx1
    show ‖F z x - F z₀ x‖ ≤ ε / 2 * x ^ (-2 : ℝ)
    rw [e2 x hx0]
    rcases le_or_gt x R with hxR | hxR
    · rw [← dist_eq_norm]
      refine le_trans (hz x ⟨le_of_lt hx1, hxR⟩).le ?_
      have hsq : x ^ 2 ≤ R ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left (inv_anti₀ (pow_pos hx0 2) hsq) (half_pos hε).le
    · have h4 : 4 * M < ε * x := by
        have h' : 4 * M / ε < x := lt_of_le_of_lt hRM hxR
        rw [div_lt_iff₀ hε] at h'
        linarith
      calc ‖F z x - F z₀ x‖ ≤ ‖F z x‖ + ‖F z₀ x‖ := norm_sub_le _ _
        _ ≤ M * x ^ (-3 : ℝ) + M * x ^ (-3 : ℝ) :=
            add_le_add (hM z hzV x hx1.le) (hM z₀ (mem_of_mem_nhds hV) x hx1.le)
        _ = 2 * M * x⁻¹ * (x ^ 2)⁻¹ := by rw [e3 x hx0]; ring
        _ ≤ ε / 2 * (x ^ 2)⁻¹ := by
            refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (pow_nonneg hx0.le 2))
            rw [← div_eq_mul_inv, div_le_iff₀ hx0]
            linarith
  rw [hgi] at key
  rw [dist_eq_norm, ← integral_sub (hint z) (hint z₀)]
  linarith
end GlobalTheory.CompanionTheory.EisRk1Cont
