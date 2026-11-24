-- Prove2me | solution 1 for GlobalTheory.FinEt.isIso_iff_isoLocus_eq_univ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:04:52.736279+00:00
-- url     : https://prove2.me/submissions/3042dfe7-8c2c-4496-9a5e-920da8516513

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed

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
theorem _root_.solution (f : X ⟶ Y)
    [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] :
    IsIso f ↔ isoLocus f = Set.univ := by
  have := isFinite_left f
  have := etale_left f
  rw [isIso_iff_isIso_left, Scheme.Hom.isIso_iff_finrank_eq, Set.eq_univ_iff_forall]
  constructor
  · intro h s
    rw [mem_isoLocus_iff]
    intro y _
    rw [h, Pi.one_apply]
  · intro h
    funext y
    exact (mem_isoLocus_iff f _).mp (h _) y rfl
end GlobalTheory.FinEt
