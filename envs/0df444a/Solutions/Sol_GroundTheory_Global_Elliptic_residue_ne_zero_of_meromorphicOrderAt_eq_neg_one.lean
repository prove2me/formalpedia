-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.residue_ne_zero_of_meromorphicOrderAt_eq_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:35:56.880088+00:00
-- url     : https://prove2.me/submissions/c2a2454c-bab1-4b78-b8ea-d8923074d6be

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
theorem _root_.solution {f : ℂ → ℂ} {p : ℂ}
    (hf : MeromorphicAt f p) (h : meromorphicOrderAt f p = ((-1 : ℤ) : WithTop ℤ)) :
    residue f p ≠ 0 := by
  obtain ⟨g, hg, hgp, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).1 h
  simp only [smul_eq_mul] at hfg
  obtain ⟨q, hq⟩ := hg
  have hu : AnalyticAt ℂ (dslope g p) p := hq.has_fpower_series_dslope_fslope.analyticAt
  rw [residue_eq_of_eventuallyEq (c := g p) hu ?_]
  · exact hgp
  filter_upwards [hfg, self_mem_nhdsWithin] with z hz hzp
  have hzp' : z - p ≠ 0 := sub_ne_zero.2 hzp
  have e := sub_smul_dslope g p z
  simp only [smul_eq_mul] at e
  rw [hz, zpow_neg_one]
  field_simp
  linear_combination -e
end GroundTheory.Global.Elliptic
