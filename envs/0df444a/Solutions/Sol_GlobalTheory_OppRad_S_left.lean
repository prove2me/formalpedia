-- Prove2me | solution 1 for GlobalTheory.OppRad.S_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:27.945929+00:00
-- url     : https://prove2.me/submissions/d6be0e15-238f-40f9-be7c-0958942e3b1a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixRegular
import Theorems.Thm_GlobalTheory_OppRad_S_conj
import Theorems.Thm_GlobalTheory_OppRad_S_right

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
theorem _root_.solution {H : Subgroup G} {h : G} (hh : h ∈ H) (v : V) : π h (S π H v) = S π H v := by
  rw [S_conj (K := H) (fun u hu => mul_mem (mul_mem hh hu) (inv_mem hh))
    (fun u hu => mul_mem (mul_mem (inv_mem hh) hu) (inv_mem (inv_mem hh))), S_right hh]
end GlobalTheory.OppRad
