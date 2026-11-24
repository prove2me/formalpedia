-- Prove2me | solution 1 for GlobalTheory.eigDim_ker_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:44:42.666133+00:00
-- url     : https://prove2.me/submissions/0a51fd3f-daed-4c63-83b1-297cc743c291

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankKerAevalEqNatDegreeMulFinrankEigenspaceAl
import Theorems.Thm_GlobalTheory_eigDim_rank_map
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial
namespace GlobalTheory
private lemma finrank_ker_toLin'_add_rank_eq_card {L : Type} [Field L] {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n L) :
    Module.finrank L (LinearMap.ker (Matrix.toLin' A)) + A.rank = Fintype.card n := by
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' A)
  rw [Matrix.toLin'_apply'] at h ⊢
  rw [Module.finrank_pi] at h
  unfold Matrix.rank
  omega
end GlobalTheory
end

set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K L : Type} [Field K] [Field L] (φ : K →+* L) {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) :
    Module.finrank L (LinearMap.ker (Matrix.toLin' (M.map φ))) =
      Module.finrank K (LinearMap.ker (Matrix.toLin' M)) := by
  have h1 := finrank_ker_toLin'_add_rank_eq_card (M.map φ)
  have h2 := finrank_ker_toLin'_add_rank_eq_card M
  rw [eigDim_rank_map] at h1
  omega
end GlobalTheory
