-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.smul_eq_mk_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:48:46.19319+00:00
-- url     : https://prove2.me/submissions/6ccaa096-187f-4e80-93b0-62badd37a605

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
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
omit hq
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution (r : F[X]) (a : F[X] ⧸ F[X] ∙ q) :
    r • a = Submodule.Quotient.mk r * a := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mk_mul_mk]
end GroundTheory.Automorphic.ContragredientTranspose
