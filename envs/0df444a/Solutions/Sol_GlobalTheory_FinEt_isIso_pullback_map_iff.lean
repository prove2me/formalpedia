-- Prove2me | solution 1 for GlobalTheory.FinEt.isIso_pullback_map_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:04:54.700168+00:00
-- url     : https://prove2.me/submissions/91e23ff5-b338-4583-b655-05780d236115

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
theorem _root_.solution {T : Scheme.{u}} (t : T ⟶ S) (f : X ⟶ Y)
    [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] :
    IsIso ((Over.pullback t).map f) ↔ Set.range t ⊆ isoLocus f := by
  have := isFinite_left f
  have := etale_left f
  rw [isIso_pullback_map_iff_finrank]
  constructor
  · intro h s hs
    rw [mem_isoLocus_iff]
    rintro y rfl
    exact h y hs
  · intro h y hy
    exact (mem_isoLocus_iff f _).mp (h hy) y rfl
end GlobalTheory.FinEt
