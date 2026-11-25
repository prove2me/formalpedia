-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.ContCoeff.zsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:48:02.500398+00:00
-- url     : https://prove2.me/submissions/8de025cc-2495-4d07-92f8-acd381ddb3ba

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_ContCoeff_mul

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
variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
variable {α : Type*} [TopologicalSpace α]
namespace GroundTheory.Automorphic.ContragredientTranspose
namespace ContCoeff
theorem _root_.solution {P : α → F[X]} (hP : ContCoeff P) (z : ℤ) :
    ContCoeff fun a => z • P a := fun k => by
  have e : ∀ a, (z • P a).coeff k = (z : F) * (P a).coeff k := fun a => by
    rw [zsmul_eq_mul, ← C_eq_intCast, coeff_C_mul]
  simp only [e]
  exact continuous_const.mul (hP k)
end ContCoeff
end GroundTheory.Automorphic.ContragredientTranspose
