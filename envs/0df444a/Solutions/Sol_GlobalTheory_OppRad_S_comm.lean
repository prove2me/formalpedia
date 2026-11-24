-- Prove2me | solution 1 for GlobalTheory.OppRad.S_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:21:22.161815+00:00
-- url     : https://prove2.me/submissions/a12382e3-c033-48ec-89c7-461560deb778

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixRegular
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
variable {G V : Type} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
variable {π}
namespace GlobalTheory.OppRad
theorem _root_.solution {H : Subgroup G} {h : G} (hh : ∀ u ∈ H, h * u = u * h) (v : V) :
    π h (S π H v) = S π H (π h v) :=
  S_conj (fun u hu => by rwa [hh u hu, mul_inv_cancel_right])
    (fun u hu => by rwa [inv_inv, mul_assoc, ← hh u hu, inv_mul_cancel_left]) v
end GlobalTheory.OppRad
