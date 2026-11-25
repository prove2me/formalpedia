-- Prove2me | solution 1 for GroundTheory.BlockD.FourierDecayAlt.GaugeExists.prod_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:36:41.798644+00:00
-- url     : https://prove2.me/submissions/f3838a7b-35f2-42f5-b8e1-4fe39e9462a7

import Mathlib
import Definitions.Def_GroundTheory_IdeleRoots_ConstantFrames_GaugeExistence_RotationOfDiagonalGenerator
import Definitions.Def_GroundTheory_IdeleRoots_ConstantFrames_GaugeExistence_QdetSub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPolyS_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_Ent_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_Rep_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Polynomial Formalism.REAL
open GroundTheory GroundTheory.BlockD GroundTheory.BlockD.FourierDecayAlt GroundTheory.BlockD.FourierDecayAlt.GaugeExists
noncomputable section
variable {A : Type} [Ring A] [Algebra ℂ A]
omit [Algebra ℂ A]
namespace GroundTheory.BlockD.FourierDecayAlt.GaugeExists
theorem _root_.solution (m : ℕ) (c : Fin m → A) :
    (List.ofFn fun k : Fin m => X + C (c k)).prod.natDegree ≤ m ∧
      (List.ofFn fun k : Fin m => X + C (c k)).prod.coeff m = 1 ∧
      ∀ j, j + 1 = m → (List.ofFn fun k : Fin m => X + C (c k)).prod.coeff j = ∑ k, c k := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih (fun k => c k.castSucc)
    rw [List.ofFn_succ', List.prod_concat]
    set P := (List.ofFn fun k : Fin m => X + C (c k.castSucc)).prod
    refine ⟨?_, ?_, ?_⟩
    · refine (natDegree_mul_le).trans ?_
      have : (X + C (c (Fin.last m))).natDegree ≤ 1 :=
        (natDegree_add_le _ _).trans (max_le natDegree_X_le (by simp))
      omega
    · rw [mul_add, coeff_add, coeff_mul_X, coeff_mul_C, h2,
        coeff_eq_zero_of_natDegree_lt (show P.natDegree < m + 1 by omega)]
      simp
    · intro j hj
      have hj' : j = m := by omega
      subst hj'
      rw [Fin.sum_univ_castSucc, mul_add, coeff_add, coeff_mul_C, h2, one_mul]
      congr 1
      cases j with
      | zero => simp [P]
      | succ i => rw [coeff_mul_X, h3 i rfl]
end GroundTheory.BlockD.FourierDecayAlt.GaugeExists
