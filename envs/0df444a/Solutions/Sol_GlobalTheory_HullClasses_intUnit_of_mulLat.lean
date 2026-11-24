-- Prove2me | solution 1 for GlobalTheory.HullClasses.intUnit_of_mulLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:54:01.190565+00:00
-- url     : https://prove2.me/submissions/b593a96d-6677-4805-ab56-57012f3bd618

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntUnitOfMulLat
import Theorems.Thm_GlobalTheory_HullClasses_mem_mulLat
import Theorems.Thm_GlobalTheory_HullClasses_one_mem_Lam
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
theorem _root_.solution (v : B.Aˣ) (h : mulLat K.O (v : B.A) (abelian₂ B) = abelian₂ B) : v ∈ intUnits K.O B.A := by
  have h1 : (v : B.A) ∈ abelian₂ B := by
    rw [← h]; exact (mem_mulLat _ _ _).2 ⟨1, one_mem_Lam B, mul_one _⟩
  have h2 : (1 : B.A) ∈ mulLat K.O (v : B.A) (abelian₂ B) := by rw [h]; exact one_mem_Lam B
  obtain ⟨z, hz, hvz⟩ := (mem_mulLat _ _ _).1 h2
  have hz' : ((v⁻¹ : B.Aˣ) : B.A) = z := by
    calc ((v⁻¹ : B.Aˣ) : B.A) = ((v⁻¹ : B.Aˣ) : B.A) * ((v : B.A) * z) := by rw [hvz, mul_one]
      _ = z := by rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [mem_Lam_iff] at h1 hz
  exact ⟨h1, hz' ▸ hz⟩
end GlobalTheory.HullClasses
