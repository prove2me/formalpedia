-- Prove2me | solution 1 for GlobalTheory.InjHol.eventually_zero_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:47:45.807142+00:00
-- url     : https://prove2.me/submissions/b3ac775e-5868-43fe-9e1f-8ca6b0baaa88

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AnalyticAtEntry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NotInjOnOfFderivEqZero
import Theorems.Thm_GlobalTheory_InjHol_exists_zero_of_norm_lt
import Theorems.Thm_GlobalTheory_InjHol_exists_apply_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Metric Topology
open scoped ContDiff
open GlobalTheory GlobalTheory.InjHol
namespace GlobalTheory.InjHol
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {g h : E → ℂ} {b : E} (hg : AnalyticAt ℂ g b) (hh : AnalyticAt ℂ h b)
    (h0 : fderiv ℂ g b ≠ 0) (hb : h b = 0) (hsub : ∀ᶠ z in 𝓝 b, h z = 0 → g z = 0) :
    ∀ᶠ z in 𝓝 b, g z = 0 → h z = 0 := by
  obtain ⟨v, hv⟩ := exists_apply_eq_one h0
  have hgb : g b = 0 := hsub.self_of_nhds hb
  have hT : Tendsto (fun q : E × ℂ => q.1 + q.2 • v) (𝓝 (b, 0)) (𝓝 b) := by
    have : ContinuousAt (fun q : E × ℂ => q.1 + q.2 • v) (b, 0) := by fun_prop
    simpa using this.tendsto
  have hT1 : Tendsto (fun q : E × ℂ => q.1) (𝓝 (b, 0)) (𝓝 b) := continuous_fst.tendsto _
  have hc : 0 < (2 * (‖v‖ + 1))⁻¹ := by positivity
  have hst := (hg.hasStrictFDerivAt.isLittleO.def hc)
  rw [nhds_prod_eq] at hst
  have hQ : ∀ᶠ q : E × ℂ in 𝓝 (b, 0), AnalyticAt ℂ h (q.1 + q.2 • v) ∧
      (g q.1 = 0 → h (q.1 + q.2 • v) = 0 → q.2 = 0) := by
    filter_upwards [hT.eventually hh.eventually_analyticAt, hT.eventually hsub,
      (hT.prodMk hT1).eventually hst] with q h1 h2 h3
    refine ⟨h1, fun h4 h5 => ?_⟩
    simp only [h2 h5, h4, add_sub_cancel_left, map_smul, hv, smul_eq_mul, mul_one, sub_self,
      zero_sub, norm_neg, norm_smul] at h3
    have h6 : (2 * (‖v‖ + 1))⁻¹ * ‖v‖ ≤ 1 / 2 := by
      rw [inv_mul_le_iff₀ (by positivity)]
      linarith
    have h7 : ‖q.2‖ ≤ 0 := by nlinarith [norm_nonneg q.2]
    exact norm_le_zero_iff.mp h7
  have hc0 : ContinuousAt (fun t : ℂ => (b, t)) 0 := by fun_prop
  obtain ⟨r, hr, hball⟩ :=
    nhds_basis_closedBall.eventually_iff.mp (hc0.eventually hQ.eventually_nhds)
  have h1 := (isCompact_closedBall (0 : ℂ) r).eventually_forall_of_forall_eventually
    (x₀ := b) (P := fun z t => AnalyticAt ℂ h (z + t • v) ∧ (g z = 0 → h (z + t • v) = 0 → t = 0))
    fun t ht => hball ht
  have h2 : ∀ᶠ z in 𝓝 b, ∀ t ∈ sphere (0 : ℂ) r, ‖h z‖ < ‖h (z + t • v)‖ := by
    refine (isCompact_sphere (0 : ℂ) r).eventually_forall_of_forall_eventually fun t ht => ?_
    have ht' := (hball (sphere_subset_closedBall ht)).self_of_nhds
    have c1 : ContinuousAt (fun q : E × ℂ => ‖h q.1‖) (b, t) :=
      (ContinuousAt.comp (f := Prod.fst) (x := (b, t)) hh.continuousAt continuousAt_fst).norm
    have c2 : ContinuousAt (fun q : E × ℂ => ‖h (q.1 + q.2 • v)‖) (b, t) :=
      (ContinuousAt.comp (f := fun q : E × ℂ => q.1 + q.2 • v) (x := (b, t))
        ht'.1.continuousAt (by fun_prop)).norm
    refine c1.eventually_lt c2 ?_
    simp only [hb, norm_zero, norm_pos_iff]
    exact fun h5 => ne_of_mem_sphere ht hr.ne' (ht'.2 hgb h5)
  filter_upwards [h1, h2] with z hz1 hz2 hgz
  obtain ⟨t, ht, ht0⟩ := exists_zero_of_norm_lt (φ := fun t => h (z + t • v)) hr
    (fun t ht => (DifferentiableAt.comp t (f := fun t : ℂ => z + t • v)
      (hz1 t ht).1.differentiableAt (by fun_prop)).differentiableWithinAt)
    (by simpa using hz2)
  have := (hz1 t ht).2 hgz ht0
  simpa [this] using ht0
end GlobalTheory.InjHol
