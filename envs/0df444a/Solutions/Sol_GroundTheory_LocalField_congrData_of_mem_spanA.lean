-- Prove2me | solution 1 for GroundTheory.LocalField.congrData_of_mem_spanA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:54:41.52988+00:00
-- url     : https://prove2.me/submissions/7c914713-bcb3-4b49-bfef-6411f86fbbca

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal
import Theorems.Thm_GroundTheory_LocalField_congrData_zero
import Theorems.Thm_GroundTheory_LocalField_CongrData_add
import Theorems.Thm_GroundTheory_LocalField_CongrData_smul
import Theorems.Thm_GroundTheory_LocalField_CongrData_zsmul
import Theorems.Thm_GroundTheory_LocalField_congrData_of_mem_spanZ
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
    (hb : (s ^ b) ^ N = 1) {f : G → ℂ} (hf : f ∈ spanA E ζ) : CongrData ζ N s a f := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x', hx', g, hg, rfl⟩ := hx
    exact (congrData_of_mem_spanZ hζ hab hb hg).smul ⟨x', hx'⟩
  | zero => exact congrData_zero
  | add x y _ _ hx hy => exact hx.add hy
  | smul n x _ hx => exact hx.zsmul n
end GroundTheory.LocalField
