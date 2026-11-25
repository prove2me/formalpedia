-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.residue_eq_zero_of_meromorphicOrderAt_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:45:37.089693+00:00
-- url     : https://prove2.me/submissions/1ba8fb18-2d07-48ad-9157-3e413fb18396

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_RectangleIntegral
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ResidueTheorem
import Theorems.Thm_GroundTheory_Global_Elliptic_residue_congr
import Theorems.Thm_GroundTheory_Global_Elliptic_residue_eq_zero_of_analyticAt


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
open scoped Interval Real
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p)
    (h : 0 ≤ meromorphicOrderAt f p) : residue f p = 0 := by
  by_cases htop : meromorphicOrderAt f p = ⊤
  · rw [meromorphicOrderAt_eq_top_iff] at htop
    rw [residue_congr hf htop]
    exact residue_eq_zero_of_analyticAt analyticAt_const
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 htop
    have hn0 : 0 ≤ n := by rw [← hn] at h; exact_mod_cast h
    obtain ⟨g, hg, -, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hn.symm
    simp only [smul_eq_mul] at hfg
    lift n to ℕ using hn0
    rw [residue_congr hf hfg]
    apply residue_eq_zero_of_analyticAt
    simp only [zpow_natCast]
    fun_prop
end GroundTheory.Global.Elliptic
