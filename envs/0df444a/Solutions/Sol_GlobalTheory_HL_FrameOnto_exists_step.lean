-- Prove2me | solution 1 for GlobalTheory.HL.FrameOnto.exists_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:47:51.543864+00:00
-- url     : https://prove2.me/submissions/fa5090fa-3de4-49aa-a1ba-3f215a70aa05

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Theorems.Thm_GlobalTheory_HL_FrameOnto_mem_unipOn
import Theorems.Thm_GlobalTheory_HL_FrameOnto_spanTo_mono
import Theorems.Thm_GlobalTheory_HL_FrameOnto_hf_spanTo
import Theorems.Thm_GlobalTheory_HL_FrameOnto_mem_perp
import Theorems.Thm_GlobalTheory_HL_FrameOnto_spanTo_le_perp
import Theorems.Thm_GlobalTheory_HL_FrameOnto_exists_dual
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_Eichler_eichler_isometry
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_cj
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_neg_r
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameOnto
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
variable (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (T : Fˣ)
  (gram : ∀ a b, hf L S.Hm (g a) (g b) =
    if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E T else 0)
  (dual : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
include gram dual
namespace GlobalTheory.HL.FrameOnto
theorem _root_.solution [IsNonarchimedeanLocalField F] [CharZero F] (j : Fin (r + 1)) (x : S.V)
    (hx : x ∈ S.spanTo g j) :
    ∃ n ∈ S.Nof g, n (g j) = g j + x ∧ (∀ i, i ≠ j → n (g i) = g i) ∧
      ∀ v ∈ S.spanTo g j, n v = v := by
  obtain ⟨u, hu⟩ := exists_dual S g gs T gram dual j
  have hjr : (j : ℕ) ≤ r := Nat.lt_succ_iff.1 j.2
  have hxX : x ∈ S.spanTo g r := spanTo_mono S g hjr hx
  have hlow : ∀ v ∈ S.spanTo g j, hf L S.Hm v u = 0 := fun v hv =>
    hf_spanTo S g hv fun i hi => by
      rw [hu, if_neg]
      rintro rfl
      omega
  have hux : hf L S.Hm u x = 0 := by rw [← hf_cj L S.herm.1, hlow x hx, map_zero]
  have hs : algebraMap F E 2⁻¹ * hf L S.Hm u u + L.cj (algebraMap F E 2⁻¹ * hf L S.Hm u u) =
      hf L S.Hm u u := by
    rw [map_mul, AlgEquiv.commutes, hf_cj L S.herm.1, ← add_mul, ← map_add]
    norm_num
  obtain ⟨n, hn, h1, h2⟩ := eichler_isometry L S.Hm S.herm x u _
    (spanTo_le_perp S g T gram hxX x hxX) hux hs
  have e1 : ∀ v ∈ perp L S.Hm (S.spanTo g r), n v - v = hf L S.Hm v u • x := fun v hv => by
    rw [h1, eich, hv x hxX]; simp
  have e2 : ∀ v ∈ perp L S.Hm (S.spanTo g r), n⁻¹ v - v = -(hf L S.Hm v u • x) := fun v hv => by
    rw [h2, eich, hv x hxX, hf_neg_r]; simp
  have e3 : ∀ l : Fin r, ∀ v ∈ S.spanTo g (l + 1), hf L S.Hm v u • x ∈ S.spanTo g l := by
    intro l v hv
    by_cases h : (j : ℕ) ≤ l
    · exact Submodule.smul_mem _ _ (spanTo_mono S g h hx)
    · rw [hlow v (spanTo_mono S g (by omega) hv)]; simp
  refine ⟨n, ⟨⟨hn, Subgroup.mem_iInf.2 fun l => ?_⟩, ?_⟩, ?_, fun i hi => ?_, fun v hv => ?_⟩
  · have hl : S.spanTo g (l + 1) ≤ perp L S.Hm (S.spanTo g r) :=
      (spanTo_mono S g l.2).trans (spanTo_le_perp S g T gram)
    refine mem_unipOn (spanTo_mono S g (Nat.le_succ _)) n (fun v hv => ?_) (fun v hv => ?_)
    · rw [e1 v (hl hv)]; exact e3 l v hv
    · rw [e2 v (hl hv)]; exact Submodule.neg_mem _ (e3 l v hv)
  · refine mem_unipOn (spanTo_le_perp S g T gram) n (fun v hv => ?_) (fun v hv => ?_)
    · rw [e1 v hv]; exact Submodule.smul_mem _ _ hxX
    · rw [e2 v hv]; exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hxX)
  · have := e1 _ (mem_perp S g T gram j)
    rw [hu, if_pos rfl, one_smul] at this
    rw [← this]; abel
  · have := e1 _ (mem_perp S g T gram i)
    rw [hu, if_neg hi, zero_smul] at this
    exact sub_eq_zero.1 this
  · have := e1 _ (spanTo_le_perp S g T gram (spanTo_mono S g hjr hv))
    rw [hlow v hv, zero_smul] at this
    exact sub_eq_zero.1 this
end GlobalTheory.HL.FrameOnto
