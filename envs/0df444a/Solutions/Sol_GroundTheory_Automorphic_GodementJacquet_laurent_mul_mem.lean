-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementJacquet.laurent_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:01:20.967371+00:00
-- url     : https://prove2.me/submissions/663e7ccb-8b5e-4ea3-9b88-50d2b03ce2c5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJLaurentIdeal
import Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_mem_laurentSubalgebra_iff
import Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_X_inv_pow_mul_mem
import Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_algebraMap_mul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Polynomial
variable {I : Submodule ℂ (RatFunc ℂ)}
namespace GroundTheory.Automorphic.GodementJacquet
theorem _root_.solution (hX : ∀ R ∈ I, RatFunc.X * R ∈ I)
    (hXinv : ∀ R ∈ I, RatFunc.X⁻¹ * R ∈ I) {L : RatFunc ℂ} (hL : L ∈ laurentSubalgebra)
    {R : RatFunc ℂ} (hR : R ∈ I) : L * R ∈ I := by
  obtain ⟨P, k, rfl⟩ := mem_laurentSubalgebra_iff.1 hL
  rw [div_eq_mul_inv, ← inv_pow, mul_assoc]
  exact algebraMap_mul_mem hX P (X_inv_pow_mul_mem hXinv k hR)
end GroundTheory.Automorphic.GodementJacquet
