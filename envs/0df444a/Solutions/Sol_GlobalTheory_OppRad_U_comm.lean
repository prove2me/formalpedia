-- Prove2me | solution 1 for GlobalTheory.OppRad.U_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:21:23.078962+00:00
-- url     : https://prove2.me/submissions/60845145-937c-4ab0-90c4-a2b44d2e98fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixRegular
import Theorems.Thm_GlobalTheory_OppRad_un_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.OppRad.un_val

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OppRad
open scoped Classical
variable {R : Type} [Ring R]
namespace GlobalTheory.OppRad
theorem _root_.solution {p q : R} (h : q * p = 0) {u v : Rˣ} (hu : u ∈ U p q) (hv : v ∈ U p q) : u * v = v * u := by
  have k : ∀ {u v : Rˣ}, u ∈ U p q → v ∈ U p q → (u * v).val = u.val + v.val - 1 := fun {u v} hu hv => by
    have : (u.val - 1) * (v.val - 1) = 0 := by rw [← hu.2, ← hv.1, mul_assoc, ← mul_assoc q, h]; simp
    rw [Units.val_mul, ← sub_zero (u.val * v.val), ← this]; noncomm_ring
  exact Units.ext (by rw [k hu hv, k hv hu, add_comm])
end GlobalTheory.OppRad
