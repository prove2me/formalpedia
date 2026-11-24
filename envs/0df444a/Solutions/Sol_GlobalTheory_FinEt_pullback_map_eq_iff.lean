-- Prove2me | solution 1 for GlobalTheory.FinEt.pullback_map_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:04:56.004208+00:00
-- url     : https://prove2.me/submissions/09c4f210-f6b5-4f38-a27b-7b6185729212

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
theorem _root_.solution {T : Scheme.{u}} (t : T ⟶ S) (f g : X ⟶ Y)
    [LocallyOfFiniteType Y.hom] [FormallyUnramified Y.hom] :
    (Over.pullback t).map f = (Over.pullback t).map g ↔ Set.range t ⊆ eqLocus f g := by
  rw [pullback_map_eq_iff_preimage, ← Set.compl_subset_compl (s := eqLocus f g), compl_eqLocus,
    Set.image_subset_iff, Set.preimage_compl, Set.compl_subset_compl]
end GlobalTheory.FinEt
