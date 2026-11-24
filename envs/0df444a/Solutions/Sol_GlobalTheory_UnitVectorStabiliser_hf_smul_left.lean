-- Prove2me | solution 1 for GlobalTheory.UnitVectorStabiliser.hf_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:05:16.709739+00:00
-- url     : https://prove2.me/submissions/2c68ce9d-bf38-4d4a-9c59-02a20dbb3fe1

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
theorem _root_.solution (c : A) (x y : n → A) : hform s J (c • x) y = s c * hform s J x y := by
  simp only [hform, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
end GlobalTheory.UnitVectorStabiliser
