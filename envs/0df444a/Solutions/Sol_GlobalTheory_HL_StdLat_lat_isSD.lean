-- Prove2me | solution 1 for GlobalTheory.HL.StdLat.lat_isSD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:38:41.88716+00:00
-- url     : https://prove2.me/submissions/97f9770f-7cdb-4865-9b6f-3e68dfee9469

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Theorems.Thm_GlobalTheory_HL_StdLat_hf_zero_l
import Theorems.Thm_GlobalTheory_HL_StdLat_mem_perp_span
import Theorems.Thm_GlobalTheory_HL_StdLat_exists_mul_mem
import Theorems.Thm_GlobalTheory_HL_StdLat_pr_e
import Theorems.Thm_GlobalTheory_HL_StdLat_pr_es
import Theorems.Thm_GlobalTheory_HL_StdLat_pr_smul
import Theorems.Thm_GlobalTheory_HL_StdLat_hf_decomp
import Theorems.Thm_GlobalTheory_HL_StdLat_mem_lat
import Theorems.Thm_GlobalTheory_HL_StdLat_pr_mem_of
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_cj
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_smul_r
import Theorems.Thm_GlobalTheory_UnramOrder_cj_mem
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
include hee hss hXA hAp hd
namespace GlobalTheory.HL.StdLat
theorem _root_.solution
    (hfg : (A ⊓ (perp L Hm (Submodule.span E (Set.range es))).restrictScalars L.O).FG) :
    IsSD L Hm (lat L Hm e es A) := by
  have hm := mem_lat hH hee hss hes hAp
  have hcj : ∀ x : E, L.cj x ∈ L.O → x ∈ L.O := fun x hx => by
    simpa [L.cj_cj] using UnramOrder.cj_mem L hx
  have he : ∀ j, e j ∈ lat L Hm e es A := fun j =>
    Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨j, rfl⟩))
  have hs : ∀ j, es j ∈ lat L Hm e es A := fun j =>
    Submodule.mem_sup_right (Submodule.subset_span ⟨j, rfl⟩)
  have h0 : ∀ x ∈ A, (∀ j, hf L Hm x (es j) = 0) → x ∈ lat L Hm e es A := fun x hx hx' =>
    Submodule.mem_sup_left (Submodule.mem_sup_right ⟨hx, (mem_perp_span L Hm es x).2 hx'⟩)
  refine ⟨⟨((Submodule.fg_span (Set.finite_range e)).sup hfg).sup
    (Submodule.fg_span (Set.finite_range es)), ?_⟩, fun y => ⟨fun h => ?_, fun hy x hx => ?_⟩⟩
  · rw [eq_top_iff]
    rintro y -
    obtain ⟨s, hs'⟩ := hfg
    obtain ⟨c, hc, -, hcs⟩ := exists_mul_mem L (s.image fun x => hf L Hm x y)
    have h1 : pr L Hm e es (algebraMap F E c • y) ∈ A := by
      refine pr_mem_of hH hee hss hes hXA hAp hd _ fun x hx hx' => ?_
      have hx2 : x ∈ Submodule.span L.O (s : Set (Fin n → E)) := by
        rw [hs']; exact ⟨hx, (mem_perp_span L Hm es x).2 hx'⟩
      clear hx hx'
      induction hx2 using Submodule.span_induction with
      | mem x hx =>
        rw [hf_smul_r, AlgEquiv.commutes]
        exact hcs _ (Finset.mem_image_of_mem _ hx)
      | zero => rw [hf_zero_l]; exact L.O.zero_mem
      | add a b _ _ ha hb => rw [hf_add_l]; exact L.O.add_mem ha hb
      | smul d a _ ha =>
        have hc : d • a = (d : E) • a := rfl
        rw [hc, hf_smul_l]; exact L.O.mul_mem d.2 ha
    have h2 := h0 _ h1 (pr_es hss hes _)
    have hy : y = ∑ j, hf L Hm y (es j) • e j +
        algebraMap F E c⁻¹ • pr L Hm e es (algebraMap F E c • y) + ∑ j, hf L Hm y (e j) • es j := by
      rw [pr_smul, smul_smul, ← map_mul, inv_mul_cancel₀ hc, map_one, one_smul]
      simp only [pr]; abel
    rw [hy]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (he j))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span h2)
    · exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (hs j))
  · rw [hm]
    refine ⟨fun j => hcj _ ?_, fun j => hcj _ ?_,
      pr_mem_of hH hee hss hes hXA hAp hd _ fun x hx hx' => h x (h0 x hx hx')⟩
    · rw [hf_cj L hH]; exact h _ (hs j)
    · rw [hf_cj L hH]; exact h _ (he j)
  · rw [hm] at hx hy
    rw [hf_decomp hH hee hss hes]
    refine L.O.add_mem (L.O.add_mem ?_ ?_) ((hd _ (pr_e hH hee hes y)).2 hy.2.2 _ hx.2.2)
    · exact L.O.sum_mem fun j _ => L.O.mul_mem (hx.1 j) (UnramOrder.cj_mem L (hy.2.1 j))
    · exact L.O.sum_mem fun j _ => L.O.mul_mem (hx.2.1 j) (UnramOrder.cj_mem L (hy.1 j))
end GlobalTheory.HL.StdLat
