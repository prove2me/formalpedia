-- Prove2me | solution 1 for GlobalTheory.AdmLoc.exData_T1_T2_T3_fortyOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:05:46.826841+00:00
-- url     : https://prove2.me/submissions/9306f1b8-4e98-43e6-a8d4-d981b8c7a9b8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_StatementTor
import Definitions.Def_ReciprocityTheory_BasicDefinitions_AdRep
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle
import Theorems.Thm_GlobalTheory_AdmLoc_exData_sg
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AdmLoc
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions TensorProduct
open Formalism.MainNotions.N (twistRep coefRep)
open Formalism.GaloisCohomology (scalRep)
open ReciprocityTheory.Def (Z1 B1 H1 d0 d1 C1)
open scoped Pointwise
namespace GlobalTheory.AdmLoc
theorem _root_.solution : exData.T1 41 ∧ exData.T2 41 ∧ exData.T3 41 := by
  refine ⟨fun i => ?_, fun i u hu β hβ => ?_, fun i u hu y h1 h2 h3 => ?_⟩
  · rw [exData_sg]; simp [exData]
  · rw [exData_sg]
    simp only [exData, TopData.B] at hu hβ
    split_ifs at hu hβ <;> simp [mem_block] at hu hβ <;> rw [lt_abs] <;> push_cast <;> omega
  · rw [exData_sg] at h1 h2
    simp only [exData, TopData.cloudRes] at hu h2 h3
    split_ifs at hu h3 <;> simp at hu <;> simp only [Int.ModEq] at h3 <;> push_cast at h1 h2 h3 <;> omega
end GlobalTheory.AdmLoc
