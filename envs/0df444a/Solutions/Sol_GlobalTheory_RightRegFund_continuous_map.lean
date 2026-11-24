-- Prove2me | solution 1 for GlobalTheory.RightRegFund.continuous_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:44:26.628638+00:00
-- url     : https://prove2.me/submissions/86298a08-f6ea-42ca-90c8-0dd0d8bb32a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AestronglyMeasurableCompRep
import Theorems.Thm_GlobalTheory_RightRegFund_norm_map
import Theorems.Thm_GlobalTheory_RightRegFund_edist_indicator_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal symmDiff Topology Pointwise
open GlobalTheory GlobalTheory.RightRegFund
variable {G : Type} [Group G]
variable {Γ : Subgroup G} {D : Set G} {r : G → G}
variable [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsMulLeftInvariant] [Countable Γ]
variable [μ.IsMulRightInvariant]
variable {R : G → (Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D))}
namespace GlobalTheory.RightRegFund
theorem _root_.solution [LocallyCompactSpace G] [SecondCountableTopology G]
    [IsFiniteMeasureOnCompacts μ]
    (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D)
    (hR : ∀ g F, (R g F : G → ℂ) =ᵐ[μ.restrict D] fun x => F (r (x * g)))
    (F : Lp ℂ 2 (μ.restrict D)) : Continuous fun g => R g F := by
  refine Lp.induction (p := 2) ENNReal.ofNat_ne_top (fun F => Continuous fun g => R g F)
    ?_ ?_ ?_ F
  · intro c s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst]
    refine continuous_iff_continuousAt.2 fun g₀ => tendsto_iff_edist_tendsto_0.2 ?_
    let m : C(G, C(G, G)) := ContinuousMap.curry ⟨fun p : G × G => p.2 * p.1, by fun_prop⟩
    have ht : Tendsto (fun g => μ (((fun x => x * g) ⁻¹' (s ∩ D)) ∆
        ((fun x => x * g₀) ⁻¹' (s ∩ D)))) (𝓝 g₀) (𝓝 0) :=
      tendsto_measure_symmDiff_preimage_nhds_zero (μ := μ) (ν := μ) (f := m) (g := m g₀)
        (m.continuous.tendsto g₀) (Eventually.of_forall fun g => measurePreserving_mul_right μ g)
        (measurePreserving_mul_right μ g₀) (hs.inter hDm).nullMeasurableSet
        (by rw [← Measure.restrict_apply hs]; exact hμs.ne)
    have ht2 := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ≥0∞).toReal)).tendsto 0).comp ht
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at ht2
    have ht3 := ENNReal.Tendsto.const_mul (a := ‖c‖ₑ) ht2 (Or.inr enorm_ne_top)
    rw [mul_zero] at ht3
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht3 (fun _ => zero_le)
      fun g => edist_indicator_le hD hDm hr hR c hs hμs.ne g g₀
  · intro f g hf hg _ h1 h2
    simp only [map_add]
    exact h1.add h2
  · refine isClosed_of_closure_subset fun F hF => ?_
    refine TendstoUniformly.continuous (F := fun F' g => R g F') (p := 𝓝 F) ?_
      (mem_closure_iff_frequently.1 hF)
    refine Metric.tendstoUniformly_iff.2 fun ε hε => ?_
    filter_upwards [Metric.ball_mem_nhds F hε] with F' h g
    rw [dist_eq_norm, ← map_sub, norm_map hD hDm hr hR, ← dist_eq_norm, dist_comm]
    exact h
end GlobalTheory.RightRegFund
