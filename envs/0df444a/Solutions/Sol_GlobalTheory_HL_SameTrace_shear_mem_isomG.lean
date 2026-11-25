-- Prove2me | solution 1 for GlobalTheory.HL.SameTrace.shear_mem_isomG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:22:03.385427+00:00
-- url     : https://prove2.me/submissions/bd9abb53-3455-49f3-99c7-ff3dd70775b7

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DualInterSelfDualHermitianLatticeSubspaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AlgebraMapMemO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryOfSameTrace
import Theorems.Thm_GlobalTheory_HL_SameTrace_hf_sum_r
import Theorems.Thm_GlobalTheory_HL_SameTrace_shear_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_add_r
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_cj
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_smul_r
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.SameTrace
open GlobalTheory.HL.Eichler GlobalTheory.UnramOrder
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
namespace GlobalTheory.HL.SameTrace
theorem _root_.solution {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm) {m : ℕ}
    (b c d : Fin m → Fin n → E) (hdb : ∀ i j, hf L Hm (d i) (b j) = 0)
    (hdd : ∀ i j, hf L Hm (d i) (d j) = 0)
    (hv : ∀ v k, hf L Hm v (d k) = ∑ j, hf L Hm v (b j) * hf L Hm (c j) (d k))
    (hcd : ∀ j k, hf L Hm (c j) (d k) + hf L Hm (d j) (c k) = 0) :
    shear L Hm b d hdb ∈ isomG L Hm := by
  intro v w
  have hw : ∀ k, hf L Hm (d k) w = ∑ j, L.cj (hf L Hm w (b j)) * hf L Hm (d k) (c j) := by
    intro k
    rw [← hf_cj L h, hv, map_sum]
    simp only [map_mul, hf_cj L h]
  simp only [shear_apply, hf_add_l, hf_add_r, hf_sum_l, hf_sum_r, hf_smul_l, hf_smul_r, hdd,
    mul_zero, Finset.sum_const_zero, add_zero]
  simp only [hw]
  simp only [hv v, Finset.mul_sum]
  have key : ∑ k, ∑ j, L.cj (hf L Hm w (b k)) * (hf L Hm v (b j) * hf L Hm (c j) (d k))
      + ∑ j, ∑ k, hf L Hm v (b j) * (L.cj (hf L Hm w (b k)) * hf L Hm (d j) (c k)) = 0 := by
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    linear_combination L.cj (hf L Hm w (b k)) * hf L Hm v (b j) * hcd j k
  linear_combination key
end GlobalTheory.HL.SameTrace
