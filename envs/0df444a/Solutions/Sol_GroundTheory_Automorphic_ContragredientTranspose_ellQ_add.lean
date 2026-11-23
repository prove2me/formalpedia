-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.ellQ_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:13.176636+00:00
-- url     : https://prove2.me/submissions/4f470c1e-b590-4a56-9824-dfedd295246a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
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
theorem _root_.solution (a b : F[X] ⧸ F[X] ∙ q) : ellQ q hq (a + b) = ellQ q hq a + ellQ q hq b := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [← Submodule.Quotient.mk_add, ellQ_mk, ellQ_mk, ellQ_mk, lcoeffMod_add]
end GroundTheory.Automorphic.ContragredientTranspose
