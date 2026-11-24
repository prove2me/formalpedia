-- Prove2me | solution 1 for GlobalTheory.UnitVectorStabiliser.hf_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:05:15.031747+00:00
-- url     : https://prove2.me/submissions/b00a40d3-ba42-4f06-9f60-475374a40512

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
theorem _root_.solution (hs : ∀ a, s (s a) = a) (hJ : ∀ i j, s (J j i) = J i j) (x y : n → A) :
    s (hform s J x y) = hform s J y x := by
  simp only [hform, map_sum, map_mul, hs]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]
  ring
end GlobalTheory.UnitVectorStabiliser
