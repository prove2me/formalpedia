-- Prove2me | solution 1 for GlobalTheory.CubeLift.um_tri_del
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:41:39.370008+00:00
-- url     : https://prove2.me/submissions/e8b52652-d984-4c8f-a1f1-e14c653fe3c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Theorems.Thm_GlobalTheory_CubeLift_um_del
import Theorems.Thm_P2M_GlobalTheory_CubeLift_tri_p__6bdbd9e69cdf
import Theorems.Thm_P2M_GlobalTheory_CubeLift_tri_p__a6636054534f
import Theorems.Thm_P2M_GlobalTheory_CubeLift_tri_p__1bb88d54b808

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AddMonoidAlgebra
open GlobalTheory GlobalTheory.CubeLift
variable {A : Type} [CommRing A] {X Y W : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup W]
namespace GlobalTheory.CubeLift
theorem _root_.solution (g : (A[X])ˣ) (a b c : X →+ Y) : um (tri a b c) (del g p₁ p₂ p₃) = del g a b c := by
  rw [um_del, tri_p₁, tri_p₂, tri_p₃]
end GlobalTheory.CubeLift
