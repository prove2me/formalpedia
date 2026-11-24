-- Prove2me | solution 1 for GlobalTheory.UnitVectorStabiliser.hf_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:05:15.867567+00:00
-- url     : https://prove2.me/submissions/48b1de72-2c70-44b0-8e4a-bb03c056509e

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
theorem _root_.solution (i j : n) : hform s J (Pi.single i 1) (Pi.single j 1) = J i j := by
  simp [hform, Pi.single_apply, apply_ite]
end GlobalTheory.UnitVectorStabiliser
