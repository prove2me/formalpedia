-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.ellQ_C_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:54:28.949488+00:00
-- url     : https://prove2.me/submissions/ae415973-e6a1-4789-a352-b057aa1af94e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_lcoeffMod_C_mul
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_ellQ_mk

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
theorem _root_.solution (c : F) (a : F[X] ⧸ F[X] ∙ q) : ellQ q hq (C c • a) = c * ellQ q hq a := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  rw [← Submodule.Quotient.mk_smul, smul_eq_mul, ellQ_mk, ellQ_mk, lcoeffMod_C_mul]
end GroundTheory.Automorphic.ContragredientTranspose
