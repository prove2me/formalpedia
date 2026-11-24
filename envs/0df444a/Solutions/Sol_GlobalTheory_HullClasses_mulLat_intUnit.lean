-- Prove2me | solution 1 for GlobalTheory.HullClasses.mulLat_intUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:37:25.746388+00:00
-- url     : https://prove2.me/submissions/5a7e955c-7fbb-4201-bf11-19b0011158e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntUnitOfMulLat
import Theorems.Thm_GlobalTheory_HullClasses_mem_mulLat
import Theorems.Thm_GlobalTheory_HullClasses_mem_Lam_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
noncomputable section
open GlobalTheory GlobalTheory.HullClasses
variable {K : UQ} (B : InvAlg K)
namespace GlobalTheory.HullClasses
theorem _root_.solution (u : B.Aˣ) (hu : u ∈ intUnits K.O B.A) : mulLat K.O (u : B.A) (abelian₂ B) = abelian₂ B := by
  apply le_antisymm
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := (mem_mulLat _ _ _).1 hy
    rw [mem_Lam_iff] at hz ⊢
    exact hu.1.mul hz
  · intro y hy
    refine (mem_mulLat _ _ _).2 ⟨((u⁻¹ : B.Aˣ) : B.A) * y, ?_, ?_⟩
    · rw [mem_Lam_iff] at hy ⊢
      exact hu.2.mul hy
    · rw [← mul_assoc, Units.mul_inv, one_mul]
end GlobalTheory.HullClasses
