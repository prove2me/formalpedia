-- Prove2me | solution 1 for GlobalTheory.FinEt.eq_iff_eqLocus_eq_univ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:04:46.013216+00:00
-- url     : https://prove2.me/submissions/8854b841-5e0f-4028-8999-52bfae43c4d0

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
theorem _root_.solution (f g : X ⟶ Y)
    [LocallyOfFiniteType Y.hom] [FormallyUnramified Y.hom] :
    f = g ↔ eqLocus f g = Set.univ := by
  constructor
  · rintro rfl
    exact Set.eq_univ_of_forall fun _ ↦ rfl
  · intro h
    have h1 := compl_eqLocus f g
    rw [h, Set.compl_univ, eq_comm, Set.image_eq_empty, Set.compl_empty_iff] at h1
    have := (comp_eq_comp_iff_range f g (𝟙 _)).mpr (by simp [h1])
    ext1
    simpa using this
end GlobalTheory.FinEt
