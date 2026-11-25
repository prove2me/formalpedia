-- Prove2me | solution 1 for GroundTheory.Brauer.center_tensorProduct_eq_map_includeLeft
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:05:10.980373+00:00
-- url     : https://prove2.me/submissions/7b343c42-9105-4b13-a0ff-da100cbc1035

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open TensorProduct Algebra.TensorProduct
variable {K A B : Type*} [Field K] [Ring A] [Ring B] [Algebra K A] [Algebra K B]
variable (K A B)
namespace GroundTheory.Brauer
theorem _root_.solution [Algebra.IsCentral K A] :
    Subalgebra.center K (B ⊗[K] A) = (Subalgebra.center K B).map includeLeft := by
  refine le_antisymm ?_ (Algebra.TensorProduct.includeLeft_map_center_le K B A)
  intro x hx
  let e := Algebra.TensorProduct.comm K A B
  have hx' : e.symm x ∈ Subalgebra.center K (A ⊗[K] B) := by
    rw [Subalgebra.mem_center_iff] at hx ⊢
    intro w
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply, hx]
  rw [center_tensorProduct_eq_map_includeRight] at hx'
  obtain ⟨b, hb, hbx⟩ := hx'
  refine ⟨b, hb, ?_⟩
  rw [← e.apply_symm_apply x, ← hbx]
  simp [e]
end GroundTheory.Brauer
