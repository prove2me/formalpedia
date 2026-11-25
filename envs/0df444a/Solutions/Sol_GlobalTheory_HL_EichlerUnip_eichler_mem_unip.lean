-- Prove2me | solution 1 for GlobalTheory.HL.EichlerUnip.eichler_mem_unip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:18:12.104103+00:00
-- url     : https://prove2.me/submissions/2edcece3-cc82-4f8f-810c-47b53b292560

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerMapMemUnipotentCharacter
import Theorems.Thm_GlobalTheory_HL_EichlerUnip_spanTo_mono
import Theorems.Thm_GlobalTheory_HL_EichlerUnip_mem_spanTo
import Theorems.Thm_GlobalTheory_HL_EichlerUnip_hf_spanTo
import Theorems.Thm_GlobalTheory_HL_EichlerUnip_hf_symm0
import Theorems.Thm_GlobalTheory_HL_EichlerUnip_mem_unipOn
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_Eichler_eichler_isometry
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_sub_l
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.EichlerUnip
open GlobalTheory.HL.Eichler
namespace GlobalTheory.HL.EichlerUnip
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (g : Fin (r + 1) → S.V) (gs : Fin r → S.V), (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es') → ∀ (j : Fin r) (x u : S.V) (s : E), x ∈ S.spanTo g (j + 1) → u ∈ perp L S.Hm (S.spanTo g (j + 1)) → s + L.cj s = S.h u u → ∃ n ∈ S.Nof g, (∀ v, n v = eich L S.Hm x u s v) ∧ (∀ v, n⁻¹ v = eich L S.Hm x (-u) (L.cj s) v) ∧ (∀ v ∈ S.spanTo g (j + 1), n v = v) ∧ ∀ m ∈ S.Nof g, S.psiOf g gs n = L.psi0 (algebraMap F E S.th⁻¹ * (S.h x (gs j) * S.h (m (g j.succ)) u)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S g gs hg j x u s hx hu hs
  have hgram : ∀ a b : Fin (r + 1), (b : ℕ) < r → hf L S.Hm (g a) (g b) = 0 := by
    intro a b hb
    have hb' : b ≠ Fin.last r := fun h => by simp [h] at hb
    rcases hg with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · rw [S.gram]; simp [hb']
    · rw [S.gram']; simp [hb']
  have hdual : ∀ a i, hf L S.Hm (g a) (gs i) = if a = i.castSucc then 1 else 0 := by
    intro a i
    rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact S.dual a i
    · exact S.dual' a i
  have hjr : (j : ℕ) + 1 ≤ r := j.2
  have hgX : ∀ a, ∀ y ∈ S.spanTo g r, hf L S.Hm (g a) y = 0 := fun a y hy =>
    hf_symm0 S (hf_spanTo S g _ (fun i hi => hf_symm0 S (hgram a i hi)) hy)
  have hXX : ∀ {c : ℕ}, ∀ v ∈ S.spanTo g c, v ∈ perp L S.Hm (S.spanTo g r) := fun v hv y hy =>
    hf_spanTo S g y (fun i _ => hgX i y hy) hv
  have hxr : x ∈ S.spanTo g r := spanTo_mono S g hjr hx
  have hE : ∀ (u : S.V) (s : E), ∀ v ∈ perp L S.Hm (S.spanTo g r),
      eich L S.Hm x u s v - v = hf L S.Hm v u • x := by
    intro u s v hv
    simp only [eich, hv x hxr]
    module
  have hfl : ∀ u ∈ perp L S.Hm (S.spanTo g (j + 1)), ∀ (s : E) (i : ℕ), ∀ v ∈ S.spanTo g (i + 1),
      eich L S.Hm x u s v - v ∈ S.spanTo g i := by
    intro u hu s i v hv
    rw [hE u s v (hXX v hv)]
    rcases le_or_gt i j with h | h
    · rw [hf_symm0 S (hu v (spanTo_mono S g (by omega) hv)), zero_smul]
      exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (spanTo_mono S g h hx)
  obtain ⟨n, hn, h1, h2⟩ := eichler_isometry L S.Hm S.herm x u s (hXX x hx x hxr) (hu x hx) hs
  refine ⟨n, ⟨⟨hn, ?_⟩, ?_⟩, h1, h2, ?_, ?_⟩
  · refine Subgroup.mem_iInf.2 fun i => ?_
    refine mem_unipOn (spanTo_mono S g (by omega)) n (fun v hv => ?_) (fun v hv => ?_)
    · rw [h1]; exact hfl u hu s i v hv
    · rw [h2]; exact hfl _ (Submodule.neg_mem _ hu) _ i v hv
  · refine mem_unipOn (fun v hv => hXX v hv) n (fun v hv => ?_) (fun v hv => ?_)
    · rw [h1, hE _ _ v hv]; exact Submodule.smul_mem _ _ hxr
    · rw [h2, hE _ _ v hv]; exact Submodule.smul_mem _ _ hxr
  · intro v hv
    have := hE u s v (hXX v hv)
    rw [hf_symm0 S (hu v hv), zero_smul, sub_eq_zero] at this
    rw [h1, this]
  · rintro m ⟨⟨-, hm1⟩, hm2⟩
    replace hm1 := Subgroup.mem_iInf.1 hm1
    have hm : m (g j.succ) - g j.succ ∈ S.spanTo g (j + 1) := by
      rcases hjr.lt_or_eq with h | h
      · exact (hm1 ⟨j + 1, h⟩).2 _ (mem_spanTo S g _ (by simp))
      · have := hm2.2 (g j.succ) (hgX _)
        exact spanTo_mono S g h.ge this
    have hmu : hf L S.Hm (m (g j.succ)) u = hf L S.Hm (g j.succ) u := by
      have := hf_symm0 S (hu _ hm)
      rwa [hf_sub_l, sub_eq_zero] at this
    have hc : ∀ i : Fin r, S.coef g gs n i = hf L S.Hm x (gs i) * hf L S.Hm (g i.succ) u := by
      intro i
      have h3 := hE u s (g i.succ) (hgX _)
      rw [sub_eq_iff_eq_add, ← h1] at h3
      have h4 : i.succ ≠ i.castSucc := (Fin.castSucc_lt_succ).ne'
      simp only [Frames.coef, Frames.h]
      rw [h3, hf_add_l, hf_smul_l, hdual, if_neg h4]
      ring
    have hsum : ∑ i, S.coef g gs n i = S.h x (gs j) * S.h (m (g j.succ)) u := by
      simp only [Frames.h]
      rw [Finset.sum_eq_single j, hc, hmu]
      · intro i _ hij
        rw [hc]
        rcases lt_or_gt_of_ne hij with h | h
        · have h' : (i : ℕ) < j := h
          rw [hf_symm0 S (hu _ (mem_spanTo S g i.succ (by simp; omega))), mul_zero]
        · have h' : (j : ℕ) < i := h
          rw [hf_spanTo S g (gs i) (fun a ha => ?_) hx, zero_mul]
          rw [hdual, if_neg]
          rintro rfl
          simp at ha
          omega
      · simp
    simp only [Frames.psiOf, hsum]
end GlobalTheory.HL.EichlerUnip
