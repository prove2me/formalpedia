-- Prove2me | solution 1 for GlobalTheory.HL.StdLat.mem_iff_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:45:39.153542+00:00
-- url     : https://prove2.me/submissions/37d55594-46ee-4bd3-9531-9c8f6bd05e53

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Theorems.Thm_GlobalTheory_HL_StdLat_mem_perp_span
import Theorems.Thm_GlobalTheory_HL_StdLat_pr_e
import Theorems.Thm_GlobalTheory_HL_StdLat_pr_es
import Theorems.Thm_GlobalTheory_HL_StdLat_mem_lat
import Theorems.Thm_GlobalTheory_HL_StdLat_pr_mem
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.StdLat
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
variable {L Hm} {r : ℕ} {e es : Fin r → Fin n → E} (hH : IsHerm L Hm)
  (hee : ∀ i j, hf L Hm (e i) (e j) = 0) (hss : ∀ i j, hf L Hm (es i) (es j) = 0)
  (hes : ∀ i j, hf L Hm (e i) (es j) = if i = j then 1 else 0)
include hH hes
variable {A : Submodule L.O (Fin n → E)}
variable (hXA : ∀ x ∈ Submodule.span E (Set.range e), x ∈ A)
  (hAp : ∀ x ∈ A, ∀ j, hf L Hm x (e j) = 0)
  (hd : ∀ y, (∀ j, hf L Hm y (e j) = 0) → ((∀ x ∈ A, hf L Hm x y ∈ L.O) ↔ y ∈ A))
include hee hss hXA hAp
namespace GlobalTheory.HL.StdLat
theorem _root_.solution (x : Fin n → E) : x ∈ A ↔ ∃ y ∈ lat L Hm e es A,
    y ∈ perp L Hm (Submodule.span E (Set.range e)) ∧ y - x ∈ Submodule.span E (Set.range e) := by
  constructor
  · intro hx
    refine ⟨pr L Hm e es x, Submodule.mem_sup_left (Submodule.mem_sup_right ⟨pr_mem hXA hAp hx,
      (mem_perp_span L Hm es _).2 (pr_es hss hes x)⟩),
      (mem_perp_span L Hm e _).2 (pr_e hH hee hes x), ?_⟩
    simp only [pr, hAp x hx, zero_smul, Finset.sum_const_zero, sub_zero, sub_sub_cancel_left]
    exact Submodule.neg_mem _ (Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  · rintro ⟨y, hy, hy', hyx⟩
    have h1 := ((mem_lat hH hee hss hes hAp y).1 hy).2.2
    rw [mem_perp_span] at hy'
    simp only [pr, hy', zero_smul, Finset.sum_const_zero, sub_zero] at h1
    have h2 : y ∈ A := by
      simpa using A.add_mem h1 (hXA (∑ j, hf L Hm y (es j) • e j) (Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)))
    simpa using A.sub_mem h2 (hXA _ hyx)
end GlobalTheory.HL.StdLat
