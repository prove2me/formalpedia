-- Prove2me | solution 1 for GroundTheory.LocalField.apply_mem_adjoin_of_mem_spanA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:42:30.225815+00:00
-- url     : https://prove2.me/submissions/2f7dd2a7-3c4f-42a5-bdc0-a8358475a290

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal
import Theorems.Thm_GroundTheory_LocalField_apply_mem_adjoin_of_mem_spanZ
import Theorems.Thm_GroundTheory_LocalField_IsCharacter_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
open scoped Classical
universe u
variable {G : Type u} [Group G] [Fintype G]
variable {E : Subgroup G → Prop} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Nat.card G))
include hζ
namespace GroundTheory.LocalField
theorem _root_.solution {f : G → ℂ} (hf : f ∈ spanA E ζ) (g : G) :
    f g ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, g', hg', rfl⟩ := hx
    rw [Pi.smul_apply, smul_eq_mul]
    exact Subalgebra.mul_mem _ ha (apply_mem_adjoin_of_mem_spanZ hζ hg' g)
  | zero => exact Subalgebra.zero_mem _
  | add x y _ _ hx hy => exact Subalgebra.add_mem _ hx hy
  | smul n x _ hx =>
    rw [Pi.smul_apply, zsmul_eq_mul]
    exact Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ n) hx
end GroundTheory.LocalField
