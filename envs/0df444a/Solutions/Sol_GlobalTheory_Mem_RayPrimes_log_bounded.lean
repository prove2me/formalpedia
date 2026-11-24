-- Prove2me | solution 1 for GlobalTheory.Mem.RayPrimes.log_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:57:13.948804+00:00
-- url     : https://prove2.me/submissions/2107faa7-6962-4e62-8df3-4c6e6b8f5db8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassPartialZetaContinuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProduct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLNonvanishingAtOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
open Filter Topology Asymptotics Set
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.RayPrimes
namespace GlobalTheory.Mem.RayPrimes
theorem _root_.solution (g : ℝ → ℂ) (L : ℂ → ℂ) (hL : Continuous L) (h1 : L 1 ≠ 0)
    (hg : ContinuousOn g (Ioi 1)) (he : ∀ s : ℝ, 1 < s → cexp (g s) = L s) :
    g =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
  have hc : Continuous (fun s : ℝ => L s / L 1 - 1) := by fun_prop (disch := exact h1)
  have ht : ∀ᶠ s : ℝ in 𝓝 1, ‖L s / L 1 - 1‖ < 1 / 2 := by
    have := (hc.norm.tendsto 1)
    simp only [ofReal_one, div_self h1, sub_self, norm_zero] at this
    exact this.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.1 ht
  have hb' : ∀ s ∈ Ioo (1 : ℝ) (1 + δ), ‖L s / L 1 - 1‖ < 1 / 2 := fun s hs => hb (by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1, hs.2])
  have hslit : ∀ s ∈ Ioo (1 : ℝ) (1 + δ), 1 + (L s / L 1 - 1) ∈ slitPlane := fun s hs =>
    mem_slitPlane_of_norm_lt_one (by linarith [hb' s hs])
  set k : ℝ → ℂ := fun s => g s - log (1 + (L s / L 1 - 1)) with hk
  have hkc : ContinuousOn k (Ioo 1 (1 + δ)) :=
    (hg.mono Ioo_subset_Ioi_self).sub
      (ContinuousOn.clog (continuous_const.add hc).continuousOn hslit)
  have hke : ∀ s ∈ Ioo (1 : ℝ) (1 + δ), cexp (k s) = L 1 := fun s hs => by
    have hne : L s ≠ 0 := by rw [← he s hs.1]; exact exp_ne_zero _
    simp only [hk]
    rw [exp_sub, exp_log (slitPlane_ne_zero (hslit s hs)), he s hs.1, add_sub_cancel]
    field_simp
  have hconst : ∀ s ∈ Ioo (1 : ℝ) (1 + δ), k s = k (1 + δ / 2) := fun s hs =>
    Complex.isCoveringMap_exp.constOn_of_comp isPreconnected_Ioo hkc
      (fun a ha b hb => Subtype.ext (by simp only; rw [hke a ha, hke b hb])) hs
      ⟨by linarith, by linarith⟩
  refine IsBigO.of_bound (‖k (1 + δ / 2)‖ + 1) ?_
  filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 1 + δ by linarith)] with s hs
  have h2 : g s = k (1 + δ / 2) + log (1 + (L s / L 1 - 1)) := by
    rw [← hconst s hs]; simp [hk]
  have h3 := norm_log_one_add_half_le_self (hb' s hs).le
  rw [h2, norm_one, mul_one]
  refine (norm_add_le _ _).trans ?_
  linarith [hb' s hs]
end GlobalTheory.Mem.RayPrimes
