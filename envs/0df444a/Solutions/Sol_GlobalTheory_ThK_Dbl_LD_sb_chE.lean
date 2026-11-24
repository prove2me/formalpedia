-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.sb_chE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:28:42.56174+00:00
-- url     : https://prove2.me/submissions/c13a9e63-a0c9-4928-97a2-8313a06d65dd

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistA
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistC
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_chR_chE
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_cont_chE
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_cont_chR
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_sb_chart


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
theorem _root_.solution {F : ((Fin (n + 1) → k) × (Fin d → k)) × Matrix (Fin n) (Fin d) k → ℂ} (hF : F ∈ SB _)
    (h0 : ∀ y, y.1.1 0 = 0 → F y = 0) : (fun X => F (chE X)) ∈ SB (Matrix (Fin (n + 1)) (Fin (d + 1)) k) :=
  sb_chart (U := {X : Matrix (Fin (n + 1)) (Fin (d + 1)) k | X 0 0 ≠ 0})
    (T := {y : ((Fin (n + 1) → k) × (Fin d → k)) × Matrix (Fin n) (Fin d) k | y.1.1 0 ≠ 0}) (isOpen_ne_fun (by fun_prop) continuous_const) cont_chE
    cont_chR.continuousOn chR_chE (fun y hy => by simpa [chR] using hy) hF (fun y hy => h0 y (not_not.1 hy))
    (fun _ _ => rfl) fun X hX => h0 _ (not_not.1 hX)
end GlobalTheory.ThK.Dbl.LD
