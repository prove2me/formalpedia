-- Prove2me | solution 1 for GroundTheory.LocalField.smul_mem_spanA_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:06:40.283873+00:00
-- url     : https://prove2.me/submissions/4a9a3241-aa65-4024-b94c-f21ca69ce043

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionIntegral
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionElementary
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan
import Theorems.Thm_GroundTheory_LocalField_smul_mem_spanA
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
variable {G : Type*} [Group G] [Fintype G]
variable (E : Subgroup G → Prop)
variable {E}
namespace GroundTheory.LocalField
theorem _root_.solution {ζ : ℂ} {a : ℂ} (ha : a ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ)) {f : G → ℂ}
    (hf : f ∈ spanA E ζ) : a • f ∈ spanA E ζ := by
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, g, hg, rfl⟩ := hy
    rw [smul_smul]
    exact smul_mem_spanA (Subalgebra.mul_mem _ ha hb) hg
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul n x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ n hx
end GroundTheory.LocalField
