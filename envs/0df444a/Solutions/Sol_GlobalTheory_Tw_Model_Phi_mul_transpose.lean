-- Prove2me | solution 1 for GlobalTheory.Tw.Model.Phi_mul_transpose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:15:43.609847+00:00
-- url     : https://prove2.me/submissions/97e26e72-60e7-403c-8ba9-21cad4991773

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Theorems.Thm_P2M_GlobalTheory_Tw_Model_Phi_apply__7c1f3a1c520a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.Tw GlobalTheory.Tw.Model
variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]
omit [StarRing R]
namespace GlobalTheory.Tw.Model
theorem _root_.solution : Phi n R * (Phi n R)ᵀ = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Phi_apply', ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.rev_inj, Matrix.one_apply]
  split_ifs with h
  · subst h
    rw [← pow_add, ← two_mul, pow_mul]; simp
  · simp
end GlobalTheory.Tw.Model
