-- Prove2me | solution 1 for GroundTheory.LocalField.congrData_of_mem_spanZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:23:52.064818+00:00
-- url     : https://prove2.me/submissions/891b223b-60f4-4373-a443-a7ec3e958af7

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal
import Theorems.Thm_GroundTheory_LocalField_congrData_zero
import Theorems.Thm_GroundTheory_LocalField_CongrData_add
import Theorems.Thm_GroundTheory_LocalField_CongrData_smul
import Theorems.Thm_GroundTheory_LocalField_CongrData_zsmul
import Theorems.Thm_GroundTheory_LocalField_IsCharacter_congrData
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
variable {ζ : ℂ} {N : ℕ} {s : G} {a : ℤ}
variable {E : Subgroup G → Prop}
namespace GroundTheory.LocalField
theorem _root_.solution (hζ : IsPrimitiveRoot ζ (Nat.card G)) {b : ℤ} (hab : s ^ a * s ^ b = s)
    (hb : (s ^ b) ^ N = 1) {f : G → ℂ} (hf : f ∈ spanZ E) : CongrData ζ N s a f := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, -, l, rfl⟩ := hx
    exact (IsCharacter.indLin K l).congrData hζ hab hb
  | zero => exact congrData_zero
  | add x y _ _ hx hy => exact hx.add hy
  | smul n x _ hx => exact hx.zsmul n
end GroundTheory.LocalField
