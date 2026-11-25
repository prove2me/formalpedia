-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.continuous_charpoly_coeff_of_fintype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:54:29.126281+00:00
-- url     : https://prove2.me/submissions/e9f366df-aa5d-4c88-8827-60046527bb01

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_ContCoeff_add
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_ContCoeff_const
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_ContCoeff_zsmul
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_ContCoeff_sum
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_ContCoeff_prod

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
theorem _root_.solution (k : ℕ) :
    Continuous fun A : Matrix m m F => A.charpoly.coeff k := by
  have hentry : ∀ i j : m, ContCoeff fun A : Matrix m m F => A.charmatrix i j := by
    intro i j
    simp only [Matrix.charmatrix_apply]
    refine (ContCoeff.const _).add ?_
    have hc : Continuous fun A : Matrix m m F => A i j := continuous_id.matrix_elem i j
    have := ContCoeff.C (α := Matrix m m F) (f := fun A => -A i j) hc.neg
    simpa [sub_eq_add_neg] using this
  have : ContCoeff fun A : Matrix m m F => A.charpoly := by
    simp only [Matrix.charpoly, Matrix.det_apply]
    refine ContCoeff.sum _ fun σ _ => ?_
    have hp := ContCoeff.prod Finset.univ fun i _ => hentry (σ i) i
    have := hp.zsmul (Equiv.Perm.sign σ : ℤ)
    simpa only [Units.smul_def] using this
  exact this k
end GroundTheory.Automorphic.ContragredientTranspose
