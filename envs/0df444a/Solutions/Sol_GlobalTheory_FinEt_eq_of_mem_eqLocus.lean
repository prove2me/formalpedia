-- Prove2me | solution 1 for GlobalTheory.FinEt.eq_of_mem_eqLocus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:42:42.560888+00:00
-- url     : https://prove2.me/submissions/745c99c8-a12c-43fc-ae2a-932f24dd1009

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Theorems.Thm_GlobalTheory_FinEt_eq_iff_eqLocus_eq_univ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry
universe u
noncomputable section
open GlobalTheory GlobalTheory.FinEt
attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc
variable {S : Scheme.{u}} {X Y : Over S}
namespace GlobalTheory.FinEt
theorem _root_.solution [PreconnectedSpace S] (f g : X ⟶ Y)
    [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] {s : S} (hs : s ∈ eqLocus f g) :
    f = g :=
  (eq_iff_eqLocus_eq_univ f g).mpr ((isClopen_eqLocus f g).eq_univ ⟨s, hs⟩)
end GlobalTheory.FinEt
