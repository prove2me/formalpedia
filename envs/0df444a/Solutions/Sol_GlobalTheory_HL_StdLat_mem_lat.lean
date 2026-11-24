-- Prove2me | solution 1 for GlobalTheory.HL.StdLat.mem_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:29:12.557574+00:00
-- url     : https://prove2.me/submissions/100b647e-9643-4409-aa29-110218e4a1f6

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Theorems.Thm_GlobalTheory_HL_StdLat_hf_zero_l
import Theorems.Thm_GlobalTheory_HL_StdLat_mem_perp_span
import Theorems.Thm_GlobalTheory_HL_StdLat_hse
import Theorems.Thm_GlobalTheory_HL_StdLat_pr_es
import Theorems.Thm_GlobalTheory_HL_StdLat_pr_add
import Theorems.Thm_GlobalTheory_HL_StdLat_pr_smul
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
include hee hss
namespace GlobalTheory.HL.StdLat
theorem _root_.solution (hAp : ∀ x ∈ A, ∀ j, hf L Hm x (e j) = 0) (x : Fin n → E) :
    x ∈ lat L Hm e es A ↔
      (∀ j, hf L Hm x (es j) ∈ L.O) ∧ (∀ j, hf L Hm x (e j) ∈ L.O) ∧ pr L Hm e es x ∈ A := by
  have hite : ∀ (p : Prop) [Decidable p], (if p then (1 : E) else 0) ∈ L.O := fun p _ => by
    split_ifs
    exacts [L.O.one_mem, L.O.zero_mem]
  constructor
  · let P : Submodule L.O (Fin n → E) :=
      { carrier := {x | (∀ j, hf L Hm x (es j) ∈ L.O) ∧ (∀ j, hf L Hm x (e j) ∈ L.O) ∧
          pr L Hm e es x ∈ A}
        zero_mem' := by
          refine ⟨fun j => ?_, fun j => ?_, ?_⟩
          · rw [hf_zero_l]; exact L.O.zero_mem
          · rw [hf_zero_l]; exact L.O.zero_mem
          · simp [pr, hf_zero_l]
        add_mem' := by
          rintro a b ⟨h1, h2, h3⟩ ⟨k1, k2, k3⟩
          refine ⟨fun j => ?_, fun j => ?_, ?_⟩
          · rw [hf_add_l]; exact L.O.add_mem (h1 j) (k1 j)
          · rw [hf_add_l]; exact L.O.add_mem (h2 j) (k2 j)
          · rw [pr_add]; exact A.add_mem h3 k3
        smul_mem' := by
          rintro c a ⟨h1, h2, h3⟩
          have hc : c • a = (c : E) • a := rfl
          refine ⟨fun j => ?_, fun j => ?_, ?_⟩
          · rw [hc, hf_smul_l]; exact L.O.mul_mem c.2 (h1 j)
          · rw [hc, hf_smul_l]; exact L.O.mul_mem c.2 (h2 j)
          · rw [hc, pr_smul]; exact A.smul_mem c h3 }
    have : lat L Hm e es A ≤ P := by
      refine sup_le (sup_le ?_ ?_) ?_
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        refine ⟨fun j => ?_, fun j => ?_, ?_⟩
        · rw [hes]; exact hite _
        · rw [hee]; exact L.O.zero_mem
        · simp [pr, hes, hee]
      · rintro x ⟨hx, hx'⟩
        have hx2 := (mem_perp_span L Hm es x).1 hx'
        refine ⟨fun j => ?_, fun j => ?_, ?_⟩
        · rw [hx2]; exact L.O.zero_mem
        · rw [hAp x hx]; exact L.O.zero_mem
        · simpa [pr, hx2, hAp x hx] using hx
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        refine ⟨fun j => ?_, fun j => ?_, ?_⟩
        · rw [hss]; exact L.O.zero_mem
        · rw [hse hH hes]; exact hite _
        · simp [pr, hss, hse hH hes]
    exact fun h => this h
  · rintro ⟨h1, h2, h3⟩
    have hx : x = ∑ j, hf L Hm x (es j) • e j + pr L Hm e es x + ∑ j, hf L Hm x (e j) • es j := by
      simp only [pr]; abel
    rw [hx]
    refine Submodule.add_mem_sup (Submodule.add_mem_sup ?_ ⟨h3, ?_⟩) ?_
    · exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ (⟨_, h1 j⟩ : L.O) (Submodule.subset_span ⟨j, rfl⟩)
    · exact (mem_perp_span L Hm es _).2 (pr_es hss hes x)
    · exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ (⟨_, h2 j⟩ : L.O) (Submodule.subset_span ⟨j, rfl⟩)
end GlobalTheory.HL.StdLat
