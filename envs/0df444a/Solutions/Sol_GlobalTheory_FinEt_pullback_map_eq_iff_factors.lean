-- Prove2me | solution 1 for GlobalTheory.FinEt.pullback_map_eq_iff_factors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:27:06.308213+00:00
-- url     : https://prove2.me/submissions/c2c686f5-22d4-47c4-9c9d-b0386531d503

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Theorems.Thm_GlobalTheory_FinEt_pullback_map_eq_iff
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
theorem _root_.solution {T : Scheme.{u}} (t : T ⟶ S) (f g : X ⟶ Y)
    [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] :
    (Over.pullback t).map f = (Over.pullback t).map g ↔
      ∃ t' : T ⟶ eqLocusOpen f g, t' ≫ (eqLocusOpen f g).ι = t :=
  (pullback_map_eq_iff t f g).trans (range_subset_iff_factors t (eqLocusOpen f g))
end GlobalTheory.FinEt
