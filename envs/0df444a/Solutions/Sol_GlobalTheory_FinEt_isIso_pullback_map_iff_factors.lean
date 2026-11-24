-- Prove2me | solution 1 for GlobalTheory.FinEt.isIso_pullback_map_iff_factors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:27:05.632697+00:00
-- url     : https://prove2.me/submissions/5483e88b-2e60-4188-ae7e-574950e7dbad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Theorems.Thm_GlobalTheory_FinEt_isIso_pullback_map_iff
import Theorems.Thm_GlobalTheory_FinEt_range_subset_iff_factors

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
theorem _root_.solution {T : Scheme.{u}} (t : T ⟶ S) (f : X ⟶ Y)
    [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] :
    IsIso ((Over.pullback t).map f) ↔ ∃ t' : T ⟶ isoLocusOpen f, t' ≫ (isoLocusOpen f).ι = t :=
  (isIso_pullback_map_iff t f).trans (range_subset_iff_factors t (isoLocusOpen f))
end GlobalTheory.FinEt
