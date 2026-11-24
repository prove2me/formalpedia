-- Prove2me | solution 1 for GlobalTheory.OppRad.S_U
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:07.902149+00:00
-- url     : https://prove2.me/submissions/77c030ce-be3c-49de-a80c-06dede132bef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixRegular
import Theorems.Thm_GlobalTheory_OppRad_conj_mem
import Theorems.Thm_GlobalTheory_OppRad_inv_rel
import Theorems.Thm_GlobalTheory_OppRad_S_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OppRad
open scoped Classical
variable {R V : Type} [Ring R] [Finite R] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ Rˣ V}
namespace GlobalTheory.OppRad
theorem _root_.solution {p q p' q' : R} {w : Rˣ} (hp : w.val * p' = p * w.val) (hq : w.val * q' = q * w.val) (v : V) :
    π w (S π (U p' q') v) = S π (U p q) (π w v) :=
  S_conj (fun _ => conj_mem hp hq) (fun _ => conj_mem (inv_rel hp) (inv_rel hq)) v
end GlobalTheory.OppRad
