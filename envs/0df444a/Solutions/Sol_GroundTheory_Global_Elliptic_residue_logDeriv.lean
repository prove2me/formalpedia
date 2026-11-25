-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.residue_logDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:35:55.122896+00:00
-- url     : https://prove2.me/submissions/99d44ff8-cfd2-4900-8a5a-ac197de48dd9

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Theorems.Thm_GroundTheory_Global_Elliptic_residue_eq_of_eventuallyEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p) {n : ℤ}
    (hn : meromorphicOrderAt f p = n) : residue (logDeriv f) p = n := by
  obtain ⟨g, hg, hgp, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hn
  simp only [smul_eq_mul] at hfg
  have hu : AnalyticAt ℂ (fun z ↦ deriv g z / g z) p := hg.deriv.div hg hgp
  apply residue_eq_of_eventuallyEq hu
  have h2 : ∀ᶠ z in 𝓝[≠] p, f =ᶠ[𝓝 z] fun w ↦ (w - p) ^ n * g w := by
    have := eventually_eventually_nhdsWithin.2 hfg
    filter_upwards [this, self_mem_nhdsWithin] with z hz hzp
    rwa [nhdsWithin_eq_nhds.2 (isOpen_compl_singleton.mem_nhds hzp)] at hz
  have h3 : ∀ᶠ z in 𝓝[≠] p, g z ≠ 0 :=
    nhdsWithin_le_nhds (hg.continuousAt.eventually_ne hgp)
  have h4 : ∀ᶠ z in 𝓝[≠] p, AnalyticAt ℂ g z := nhdsWithin_le_nhds hg.eventually_analyticAt
  filter_upwards [h2, h3, h4, self_mem_nhdsWithin] with z hz hgz hga hzp
  have hzp' : z - p ≠ 0 := sub_ne_zero.2 hzp
  have h1 : HasDerivAt (fun w ↦ (w - p) ^ n) ((n : ℂ) * (z - p) ^ (n - 1) * 1) z := by
    have := (hasDerivAt_zpow n (z - p) (Or.inl hzp')).comp z ((hasDerivAt_id z).sub_const p)
    exact this
  have hd : HasDerivAt (fun w ↦ (w - p) ^ n * g w)
      ((n : ℂ) * (z - p) ^ (n - 1) * 1 * g z + (z - p) ^ n * deriv g z) z :=
    h1.mul hga.differentiableAt.hasDerivAt
  rw [logDeriv_apply, hz.deriv_eq, hz.eq_of_nhds, hd.deriv, zpow_sub_one₀ hzp']
  have hzn : (z - p) ^ n ≠ 0 := zpow_ne_zero n hzp'
  field_simp
end GroundTheory.Global.Elliptic
