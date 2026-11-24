-- Prove2me | solution 1 for GlobalTheory.RegSS.isUnit_det_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:55:15.320055+00:00
-- url     : https://prove2.me/submissions/a195eef8-cd5a-47b0-8060-a7ec94caec82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct
open GlobalTheory GlobalTheory.RegSS
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
open Matrix NumberField
open scoped TensorProduct
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.RegSS
namespace _root_.GlobalTheory.RegSS
theorem _root_.solution {B : Type} [CommRing B] (f : A →+* B)
    {J : Matrix n n A} (hJ : IsUnit J.det) : IsUnit (J.map f).det := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact hJ.map f
end _root_.GlobalTheory.RegSS
end GlobalTheory.RegSS
