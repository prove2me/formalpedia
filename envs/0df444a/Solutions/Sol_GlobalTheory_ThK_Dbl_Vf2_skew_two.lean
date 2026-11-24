-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.Vf2.skew_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:28:49.811797+00:00
-- url     : https://prove2.me/submissions/cc0f57bb-8de7-413e-b492-2e9306b6453d

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_ExistsPowIdem
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_SkewTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Vf2
open Matrix GlobalTheory.WeilM PositivityTheory.ThKG.Loc.Cone.Vf
variable {A K β : Type} [CommRing A] [Field K] [Fintype β] [DecidableEq β]
variable {c : A →+* A} {r : A →+* K} {G G' M m P Q : Matrix β β A}
omit [DecidableEq β]
namespace GlobalTheory.ThK.Dbl.Vf2
theorem _root_.solution (hc : ∀ z, c (c z) = z) (hG : ∀ i j, c (G j i) = G i j) (u w : β → A) :
    (vecMulVec u (G *ᵥ c ∘ w) - vecMulVec w (G *ᵥ c ∘ u))ᵀ * G +
      G * (vecMulVec u (G *ᵥ c ∘ w) - vecMulVec w (G *ᵥ c ∘ u)).map c = 0 := by
  have k : ∀ u w : β → A, (vecMulVec u (G *ᵥ c ∘ w))ᵀ * G = G * (vecMulVec w (G *ᵥ c ∘ u)).map c := fun u w => by
    ext i j
    simp only [mul_apply, transpose_apply, vecMulVec_apply, map_apply, map_mul, mulVec, dotProduct, map_sum, hc, hG,
      Function.comp_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [transpose_sub, Matrix.sub_mul, Matrix.map_sub _ (map_sub c), Matrix.mul_sub, k, k]
  abel
end GlobalTheory.ThK.Dbl.Vf2
