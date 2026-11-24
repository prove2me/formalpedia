-- Prove2me | solution 1 for GlobalTheory.FunObj.idxRatio_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:17:03.323991+00:00
-- url     : https://prove2.me/submissions/e771b42f-b11b-4c53-908d-be0c0d83d981

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InverseUnipotentVolumeConjDiagonalUnitsGLMul
import Theorems.Thm_GlobalTheory_FunObj_idxRatio_eq_of_le
import Theorems.Thm_GlobalTheory_FunObj_relIndex_inf_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open Matrix
variable {G : Type*} [Group G]
variable [TopologicalSpace G] [IsTopologicalGroup G]
namespace GlobalTheory.FunObj
theorem _root_.solution (N : Subgroup G) {U V W : Subgroup G} (hUo : IsOpen (U : Set G))
    (hUc : IsCompact (U : Set G)) (hVo : IsOpen (V : Set G)) (hVc : IsCompact (V : Set G))
    (hWo : IsOpen (W : Set G)) (hWc : IsCompact (W : Set G)) :
    idxRatio (N ⊓ U) (N ⊓ V) * idxRatio (N ⊓ V) (N ⊓ W) = idxRatio (N ⊓ U) (N ⊓ W) := by
  have hO : IsOpen ((U ⊓ V ⊓ W : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf, Subgroup.coe_inf]; exact (hUo.inter hVo).inter hWo
  have l1 : N ⊓ (U ⊓ V ⊓ W) ≤ (N ⊓ U) ⊓ (N ⊓ V) := by
    intro x hx; simp only [Subgroup.mem_inf] at hx ⊢; tauto
  have l2 : N ⊓ (U ⊓ V ⊓ W) ≤ (N ⊓ V) ⊓ (N ⊓ W) := by
    intro x hx; simp only [Subgroup.mem_inf] at hx ⊢; tauto
  have l3 : N ⊓ (U ⊓ V ⊓ W) ≤ (N ⊓ U) ⊓ (N ⊓ W) := by
    intro x hx; simp only [Subgroup.mem_inf] at hx ⊢; tauto
  have nV : (N ⊓ (U ⊓ V ⊓ W)).relIndex (N ⊓ V) ≠ 0 := relIndex_inf_ne_zero hO hVc inf_le_left inf_le_right
  have nW : (N ⊓ (U ⊓ V ⊓ W)).relIndex (N ⊓ W) ≠ 0 := relIndex_inf_ne_zero hO hWc inf_le_left inf_le_right
  rw [idxRatio_eq_of_le l1 (relIndex_inf_ne_zero hO hUc (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_right)),
    idxRatio_eq_of_le l2 (relIndex_inf_ne_zero hO hVc (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_right)),
    idxRatio_eq_of_le l3 (relIndex_inf_ne_zero hO hUc (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_right))]
  have nV' : ((N ⊓ (U ⊓ V ⊓ W)).relIndex (N ⊓ V) : ℚ) ≠ 0 := by exact_mod_cast nV
  have nW' : ((N ⊓ (U ⊓ V ⊓ W)).relIndex (N ⊓ W) : ℚ) ≠ 0 := by exact_mod_cast nW
  field_simp
end GlobalTheory.FunObj
