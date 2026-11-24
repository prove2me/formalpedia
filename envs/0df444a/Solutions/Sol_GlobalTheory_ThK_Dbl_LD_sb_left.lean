-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.sb_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:28:44.407786+00:00
-- url     : https://prove2.me/submissions/e5faae2c-7ee6-4238-9cae-8354168cc8e2

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistB
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistD
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistE
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
variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [ContinuousInv₀ k] [T2Space k] {d : ℕ}
variable [NonarchimedeanAddGroup k] [LocallyCompactSpace k]
namespace GlobalTheory.ThK.Dbl.LD
theorem _root_.solution {φ : Matrix (Fin d) (Fin d) k → ℂ} (hφ : φ ∈ SB _) (g : GL (Fin d) k) :
    (fun y => φ (g.1 * y)) ∈ SB (Matrix (Fin d) (Fin d) k) :=
  sb_comp (g.1 * ·) ((g⁻¹).1 * ·) (by fun_prop) (by fun_prop) (fun x => g.inv_mul_cancel_left x) hφ
end GlobalTheory.ThK.Dbl.LD
