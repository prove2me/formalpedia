-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.exists_ellQ_mul_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:00:29.614167+00:00
-- url     : https://prove2.me/submissions/8cf5d3ec-f5de-44c6-98d5-8c555574b9b7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_exists_lcoeffMod_mul_ne_zero
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_ellQ_mk
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_mk_mul_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose
open Polynomial
variable {F : Type*} [Field F]
variable {q : F[X]} (hq : q ≠ 0)
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution {a : F[X] ⧸ F[X] ∙ q} (ha : a ≠ 0) :
    ∃ b, ellQ q hq (b * a) ≠ 0 := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  have hf : ¬ q ∣ f := by
    rintro ⟨c, rfl⟩
    apply ha
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton]
    exact ⟨c, by rw [smul_eq_mul, mul_comm]⟩
  obtain ⟨g, hg⟩ := exists_lcoeffMod_mul_ne_zero hq hf
  exact ⟨Submodule.Quotient.mk g, by rwa [mk_mul_mk, ellQ_mk, mul_comm]⟩
end GroundTheory.Automorphic.ContragredientTranspose
