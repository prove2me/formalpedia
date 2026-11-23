-- Prove2me | solution 1 for GlobalTheory.OppRad.S_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:12:28.380871+00:00
-- url     : https://prove2.me/submissions/38ce5000-674b-4bca-81c8-6dea5cca9ef5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixRegular
import Theorems.Thm_GlobalTheory_OppRad_un_val
import Theorems.Thm_GlobalTheory_OppRad_S_apply
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
variable {G V : Type} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
variable {π}
namespace GlobalTheory.OppRad
theorem _root_.solution {H : Subgroup G} {h : G} (hh : h ∈ H) (v : V) : S π H (π h v) = S π H v := by
  haveI := Fintype.ofFinite H
  rw [S_apply, S_apply]
  refine Fintype.sum_equiv (Equiv.mulRight (⟨h, hh⟩ : H)) _ _ fun u => ?_
  simp
end GlobalTheory.OppRad
