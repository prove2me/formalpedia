-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.continuous_charpoly_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:00:28.83605+00:00
-- url     : https://prove2.me/submissions/07b7ef87-45d8-46e2-90a7-a835815b44c7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_continuous_charpoly_coeff_of_fintype

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
variable {m : Type*} [Fintype m] [DecidableEq m]
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution {n : ℕ} (k : ℕ) :
    Continuous fun A : Matrix (Fin n) (Fin n) F => A.charpoly.coeff k :=
  continuous_charpoly_coeff_of_fintype k
end GroundTheory.Automorphic.ContragredientTranspose
