-- Prove2me | solution 1 for GlobalTheory.UnitVectorStabiliser.hf_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:05:14.374835+00:00
-- url     : https://prove2.me/submissions/2f6d313e-9869-47f7-9752-e8da492b06c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RestrHomSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal
open GlobalTheory GlobalTheory.UnitVectorStabiliser
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
  (s : A →+* A) (J : Matrix n n A)
namespace GlobalTheory.UnitVectorStabiliser
theorem _root_.solution (x y z : n → A) : hform s J (x + y) z = hform s J x z + hform s J y z := by
  simp only [hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
end GlobalTheory.UnitVectorStabiliser
