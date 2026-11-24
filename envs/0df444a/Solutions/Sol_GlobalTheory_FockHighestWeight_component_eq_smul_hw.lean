-- Prove2me | solution 1 for GlobalTheory.FockHighestWeight.component_eq_smul_hw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:07:09.783097+00:00
-- url     : https://prove2.me/submissions/62714e9e-6f5e-440d-91e5-93969cf35ac8

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LowerTriOfInterlaced
import Theorems.Thm_GlobalTheory_FockHighestWeight_weight_rowW_diagExp
import Theorems.Thm_GlobalTheory_FockHighestWeight_lowerTri_of_interlaced
import Theorems.Thm_GlobalTheory_FockHighestWeight_eq_diagExp_of_lowerTri
import Theorems.Thm_GlobalTheory_FockHighestWeight_eval_idFrame_eq_coeff
import Theorems.Thm_GlobalTheory_FockHighestWeight_eval_idFrame_hw
import Theorems.Thm_Formalism_GradedWeylDivisibility_colSums
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylRowGraded
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwMem
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwRowWeight
import Theorems.Thm_Formalism_GradedWeylDivisibility_leadInterlaced
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.FockHighestWeight
variable {r n : ℕ}
namespace GlobalTheory.FockHighestWeight
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] (hn : n ≤ r) {ν : Fin n → ℕ} (hν : Antitone ν)
    {F : MvPolynomial (Fin r × Fin n) R} (hF : F ∈ dualWeyl R r n ν) :
    weightedHomogeneousComponent (rowW r n) (rowNu (r := r) ν) F = eval (idFrame R r n) F • hw R hn ν := by
  classical
  rw [← sub_eq_zero]
  by_contra hG
  set G := weightedHomogeneousComponent (rowW r n) (rowNu (r := r) ν) F - eval (idFrame R r n) F • hw R hn ν with hGdef
  have hH := hwMem R r n hn ν hν
  have hGm : G ∈ dualWeyl R r n ν :=
    Submodule.sub_mem _ (dualWeylRowGraded R r n ν _ F hF) (Submodule.smul_mem _ _ hH)
  have hGw : G ∈ weightedHomogeneousSubmodule R (rowW r n) (rowNu (r := r) ν) :=
    Submodule.sub_mem _ (weightedHomogeneousComponent_mem _ _ _)
      (Submodule.smul_mem _ _ (hwRowWeight R r n hn ν hν))
  have hd : (colLex r n).degree G ∈ G.support := (MonomialOrder.degree_mem_support_iff G).mpr hG
  have he := eq_diagExp_of_lowerTri hn (lowerTri_of_interlaced (leadInterlaced R r n ν G hGm hG))
    (colSums R r n ν G hGm _ hd) (hGw (mem_support_iff.mp hd))
  rw [he, mem_support_iff] at hd
  apply hd
  rw [hGdef, coeff_sub, coeff_weightedHomogeneousComponent, if_pos (weight_rowW_diagExp ν), coeff_smul,
    ← eval_idFrame_eq_coeff (colSums R r n ν F hF), ← eval_idFrame_eq_coeff (colSums R r n ν _ hH),
    eval_idFrame_hw]
  simp
end GlobalTheory.FockHighestWeight
