-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ProfiniteInteger.dvd_of_intCast_eq_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:44.325796+00:00
-- url     : https://prove2.me/submissions/6833e5db-3588-404f-ae89-4e1d1871f1fd

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open GroundTheory.LocalField.Abstract.ProfiniteInteger
namespace GroundTheory.LocalField.Abstract.ProfiniteInteger
theorem _root_.solution {n : ℕ} (hn : 0 < n) {m : ℤ} {w : ℤ̂} (h : (m : ℤ̂) = n • w) :
    (n : ℤ) ∣ m := by
  obtain ⟨N, rfl⟩ : ∃ N : ℕ+, (N : ℕ) = n := ⟨⟨n, hn⟩, rfl⟩
  have h' := congrArg (proj N) h
  rw [map_intCast, map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul] at h'
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd m N).1 h'
end GroundTheory.LocalField.Abstract.ProfiniteInteger
