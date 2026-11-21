-- Prove2me | solution 1 for MasulloRH.zero_free_right
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-11-20T20:51:07.322284+00:00
-- url     : https://prove2.me/submissions/8961e060-528f-4f21-8755-0a7279e33ce5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_logDeriv_analytic_right
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Analysis.Meromorphic.Order

set_option autoImplicit false

open Filter
open scoped Topology

/-- A zero would give the logarithmic derivative meromorphic order `-1`,
contradicting the imported analyticity assertion. -/
theorem solution (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs_one : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  intro hz
  have ha : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs_one
  have hpos : 0 < meromorphicOrderAt riemannZeta s := by
    apply (tendsto_zero_iff_meromorphicOrderAt_pos ha.meromorphicAt).mp
    simpa only [hz] using ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hnear : ∀ᶠ z in 𝓝[≠] s, riemannZeta z ≠ 0 := by
    have hd := (isClosed_and_discrete_iff.mp
      ⟨isClosed_riemannZetaZeros, isDiscrete_riemannZetaZeros⟩) s
    change riemannZetaZerosᶜ ∈ 𝓝[≠] s
    exact Filter.disjoint_principal_right.mp hd
  have hfinite : meromorphicOrderAt riemannZeta s ≠ ⊤ := by
    intro htop
    obtain ⟨z, hne, heq⟩ := (hnear.and (meromorphicOrderAt_eq_top_iff.mp htop)).exists
    exact hne heq
  have hpole := meromorphicOrderAt_logDeriv_eq_neg_one ha.meromorphicAt
    (ne_of_gt hpos) hfinite
  have hnonneg := (MasulloRH.logDeriv_analytic_right s hs hs_one).meromorphicOrderAt_nonneg
  change 0 ≤ meromorphicOrderAt (logDeriv riemannZeta) s at hnonneg
  rw [hpole] at hnonneg
  change ((0 : ℤ) : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ) at hnonneg
  have hbad : (0 : ℤ) ≤ -1 := WithTop.coe_le_coe.mp hnonneg
  norm_num at hbad
