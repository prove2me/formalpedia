-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.sb_chR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:42:23.514293+00:00
-- url     : https://prove2.me/submissions/cd430bdb-9c33-4c38-96aa-d9706515fa92

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistA
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistC
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_chE_chR
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
theorem _root_.solution {φ : Matrix (Fin (n + 1)) (Fin (d + 1)) k → ℂ} (hφ : φ ∈ SB _) (h0 : ∀ X, X 0 0 = 0 → φ X = 0) :
    (fun y => φ (chR y)) ∈ SB (((Fin (n + 1) → k) × (Fin d → k)) × Matrix (Fin n) (Fin d) k) :=
  sb_chart (T := {X : Matrix (Fin (n + 1)) (Fin (d + 1)) k | X 0 0 ≠ 0})
    (U := {y : ((Fin (n + 1) → k) × (Fin d → k)) × Matrix (Fin n) (Fin d) k | y.1.1 0 ≠ 0}) (isOpen_ne_fun (by fun_prop) continuous_const)
    cont_chR.continuousOn cont_chE chE_chR (fun _ hy => hy) hφ (fun y hy => h0 y (not_not.1 hy))
    (fun _ _ => rfl) fun y hy => h0 _ (by simpa [chR] using hy)
end GlobalTheory.ThK.Dbl.LD
