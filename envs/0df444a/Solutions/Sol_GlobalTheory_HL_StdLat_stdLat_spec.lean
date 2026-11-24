-- Prove2me | solution 1 for GlobalTheory.HL.StdLat.stdLat_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:54:31.751691+00:00
-- url     : https://prove2.me/submissions/903e3ff6-d597-43c9-86b4-d2054aa365ec

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Theorems.Thm_GlobalTheory_HL_StdLat_hf_sum_l
import Theorems.Thm_GlobalTheory_HL_StdLat_mem_perp_span
import Theorems.Thm_GlobalTheory_HL_StdLat_mem_lat
import Theorems.Thm_GlobalTheory_HL_StdLat_lat_isSD
import Theorems.Thm_GlobalTheory_HL_StdLat_mem_iff_lat
import Theorems.Thm_GlobalTheory_HL_StdLat_exists_coef
import Theorems.Thm_GlobalTheory_HL_StdLat_image_lt
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
namespace GlobalTheory.HL.StdLat
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (g : Fin (r + 1) → S.V) (gs : Fin r → S.V), (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es') → ∀ A, S.IsInner g gs A → IsSD L S.Hm (S.stdLat g gs A) ∧ (∀ j ≤ r + 1, ∀ x, (x ∈ S.stdLat g gs A ∧ x ∈ S.spanTo g j) ↔ x ∈ Submodule.span L.O (g '' {i | (i : ℕ) < j})) ∧ ∀ x, x ∈ A ↔ ∃ y ∈ S.stdLat g gs A, y ∈ perp L S.Hm (S.spanTo g r) ∧ y - x ∈ S.spanTo g r := by
  intro F _ _ _ _ _ E _ _ _ L r k S g gs hg A hA
  have hH := S.herm.1
  have key : (∀ a (j : Fin r), hf L S.Hm (g a) (g j.castSucc) = 0) ∧
      (∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0) ∧
      ∀ i j, hf L S.Hm (gs i) (gs j) = 0 := by
    rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨fun a j => by simp [S.gram, Fin.castSucc_ne_last], S.dual, S.iso⟩
    · exact ⟨fun a j => by simp [S.gram', Fin.castSucc_ne_last], S.dual', S.iso'⟩
  obtain ⟨hge, hgs, hss⟩ := key
  set e : Fin r → S.V := fun j => g j.castSucc with he
  have hX : S.spanTo g r = Submodule.span E (Set.range e) := by
    rw [Frames.spanTo, image_lt]
  have hl : S.stdLat g gs A = lat L S.Hm e gs A := rfl
  obtain ⟨hXA, hAp, hfg, hd, hz, z', hz', hzz⟩ := hA
  rw [hX] at hXA hAp hd
  simp only [mem_perp_span] at hAp hd
  have hee : ∀ i j, hf L S.Hm (e i) (e j) = 0 := fun i j => hge _ j
  have hes : ∀ i j, hf L S.Hm (e i) (gs j) = if i = j then 1 else 0 := fun i j => by
    simp [he, hgs]
  rw [hX, hl]
  refine ⟨lat_isSD hH hee hss hes hXA hAp hd hfg, fun j _ x => ⟨?_, fun hx => ⟨?_, ?_⟩⟩,
    mem_iff_lat hH hee hss hes hXA hAp⟩
  · rintro ⟨hx, hx'⟩
    obtain ⟨c, hc, rfl⟩ := exists_coef g _ hx'
    obtain ⟨h1, -, h3⟩ := (mem_lat hH hee hss hes hAp _).1 hx
    have h4 : ∀ j, hf L S.Hm (∑ i, c i • g i) (gs j) = c j.castSucc := fun j => by
      simp [hf_sum_l, hf_smul_l, hgs]
    have h5 : ∀ j, hf L S.Hm (∑ i, c i • g i) (e j) = 0 := fun j => by
      simp [hf_sum_l, hf_smul_l, he, hge]
    have h6 : pr L S.Hm e gs (∑ i, c i • g i) = c (Fin.last r) • g (Fin.last r) := by
      simp only [pr, h4, h5, zero_smul, Finset.sum_const_zero, sub_zero]
      rw [Fin.sum_univ_castSucc]
      simp [he]
    have h7 : ∀ i, c i ∈ L.O := fun i => by
      refine Fin.lastCases ?_ (fun i => h4 i ▸ h1 i) i
      have := (hd z' (hAp z' hz')).2 hz' _ h3
      rw [h6, Frames.h, hf_smul_l] at this
      rw [Frames.h] at hzz
      rwa [hzz, mul_one] at this
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : (i : ℕ) < j
    · exact Submodule.smul_mem _ (⟨_, h7 i⟩ : L.O) (Submodule.subset_span ⟨i, hi, rfl⟩)
    · rw [hc i hi, zero_smul]; exact Submodule.zero_mem _
  · refine (Submodule.span_le.2 ?_ : _ ≤ lat L S.Hm e gs A) hx
    rintro _ ⟨i, -, rfl⟩
    refine Fin.lastCases ?_ (fun i => ?_) i
    · refine Submodule.mem_sup_left (Submodule.mem_sup_right ⟨hz, (mem_perp_span L _ gs _).2 fun j => ?_⟩)
      simp [hgs, (Fin.castSucc_ne_last j).symm]
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩))
  · exact Submodule.span_subset_span L.O E _ hx
end GlobalTheory.HL.StdLat
