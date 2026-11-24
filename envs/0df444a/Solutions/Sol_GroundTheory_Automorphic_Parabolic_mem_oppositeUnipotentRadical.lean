-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.mem_oppositeUnipotentRadical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:12:14.07365+00:00
-- url     : https://prove2.me/submissions/af914f11-09a0-443b-a1c2-d9873bb74296

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_unipotentRadical
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_mem_blockUpper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa
variable (F : Type*) [Field F] (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
variable (F n β)
variable {F n β}
variable (F n β)
variable {F n β}
variable (F n β)
variable {F n β}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {g : GL (Fin n) F} :
    g ∈ oppositeUnipotentRadical F n β ↔ (∀ i j, β i < β j → g i j = 0) ∧
      ∀ i j, β i = β j → g i j = (1 : Matrix (Fin n) (Fin n) F) i j := by
  rw [oppositeUnipotentRadical, mem_unipotentRadical, mem_blockUpper]
  exact ⟨fun ⟨h1, h2⟩ => ⟨fun i j hij => h1 (show OrderDual.toDual (β j) < OrderDual.toDual (β i)
      from hij), fun i j hij => h2 i j (by simpa using hij)⟩,
    fun ⟨h1, h2⟩ => ⟨fun i j hij => h1 i j hij, fun i j hij => h2 i j (by simpa using hij)⟩⟩
end GroundTheory.Automorphic.Parabolic
