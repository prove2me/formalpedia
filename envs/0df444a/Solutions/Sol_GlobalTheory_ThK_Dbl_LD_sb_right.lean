-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.sb_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:50.354248+00:00
-- url     : https://prove2.me/submissions/3e5e9487-f6ae-4c08-a9dd-b5d6074baa6e

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistA
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistC
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_sb_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology GlobalTheory.WeilM Matrix
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.LD
variable {k : Type} [Field k] {n d : ℕ}
variable [TopologicalSpace k] [IsTopologicalRing k] [ContinuousInv₀ k] [T2Space k]
namespace GlobalTheory.ThK.Dbl.LD
theorem _root_.solution {m : Type} {φ : Matrix m (Fin d) k → ℂ} (hφ : φ ∈ SB _) {h : Matrix (Fin d) (Fin d) k} (hh : h.det ≠ 0) :
    (fun y => φ (y * h)) ∈ SB (Matrix m (Fin d) k) :=
  sb_comp (· * h) (· * h⁻¹) (by fun_prop) (by fun_prop) (fun x => mul_nonsing_inv_cancel_right h x hh.isUnit) hφ
end GlobalTheory.ThK.Dbl.LD
