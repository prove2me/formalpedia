-- Prove2me | solution 1 for GlobalTheory.TopForm.map_dForm_mul_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:17:20.462836+00:00
-- url     : https://prove2.me/submissions/2a49e6ff-52f1-4e49-91c7-06c205542b4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange
import Theorems.Thm_GlobalTheory_dWedge_mul_sub_mem


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
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.TopForm
variable {k A B C : Type*} [CommRing k] [CommRing A] [CommRing B] [CommRing C]
variable {D : ℕ}
variable {α : k →+* A} {β : k →+* B} {γ : k →+* C}
namespace GlobalTheory.TopForm
theorem _root_.solution (c : Forms α D →ₗ[A] A) (I : Ideal A) (h : A) (g : Fin D → A)
    (hg : ∀ i, g i ∈ I) : c (dForm α fun i => h * g i) - h ^ D * c (dForm α g) ∈ I := by
  letI := α.toAlgebra
  have := Submodule.mem_map_of_mem (f := c) (dWedge_mul_sub_mem k I h g hg)
  rw [Submodule.map_smul'', map_sub, map_smul] at this
  exact (Submodule.smul_mono le_rfl le_top).trans
    (by rw [smul_eq_mul, Ideal.mul_top]) this
end GlobalTheory.TopForm
