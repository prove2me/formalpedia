-- Prove2me | solution 1 for GlobalTheory.CubeLift.Cub.div_del
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:55:44.400947+00:00
-- url     : https://prove2.me/submissions/d50359c9-8f78-405c-adcb-d5cac1934237

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Theorems.Thm_GlobalTheory_CubeLift_um_tri_del

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
namespace Cub
theorem _root_.solution {e : (A[X × X × X])ˣ} (he : Cub e) (g : (A[X])ˣ) : Cub (e / del g p₁ p₂ p₃) := by
  refine ⟨fun Y _ a b c => ?_, fun Y _ a b c => ?_, fun Y _ a b c d => ?_⟩
  · rw [map_div, map_div, um_tri_del, um_tri_del, he.s₁, del, del, add_comm b a]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div]
    abel
  · rw [map_div, map_div, um_tri_del, um_tri_del, he.s₂, del, del, add_comm c b, add_right_comm a c b]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div]
    abel
  · have := congrArg Additive.ofMul (he.co Y a b c d)
    simp only [map_div, um_tri_del]
    simp only [del, ← add_assoc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div] at this ⊢
    linear_combination (norm := abel) this
end Cub
end GlobalTheory.CubeLift
