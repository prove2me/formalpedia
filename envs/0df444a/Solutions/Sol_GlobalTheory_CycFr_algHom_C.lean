-- Prove2me | solution 1 for GlobalTheory.CycFr.algHom_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:05:06.761401+00:00
-- url     : https://prove2.me/submissions/661eb16d-8fa8-4115-b8a6-1ca32011cd2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddXMulDerivativeBin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open GlobalTheory GlobalTheory.CycFr
open PowerSeries
namespace GlobalTheory.CycFr
namespace _root_.GlobalTheory.CycFr
theorem _root_.solution {O B : Type} [CommRing O] [CommRing B] [Algebra O B] (f : O⟦X⟧ →ₐ[O] B) (c : O) :
    f (C c) = algebraMap O B c := by
  have hc : (C c : O⟦X⟧) = algebraMap O O⟦X⟧ c := by simp
  rw [hc, f.commutes]
end _root_.GlobalTheory.CycFr
end GlobalTheory.CycFr
