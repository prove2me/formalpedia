-- Prove2me | solution 1 for GlobalTheory.HL.FrameLift.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:51:52.988608+00:00
-- url     : https://prove2.me/submissions/80330127-5428-4137-8343-c02a61973033

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DualInterSelfDualHermitianLatticeSubspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfDualLatticeUnipotentTranslateStandard
import Theorems.Thm_GlobalTheory_HL_FrameLift_hf_sum_l
import Theorems.Thm_GlobalTheory_HL_FrameLift_hf_sum_r
import Theorems.Thm_GlobalTheory_HL_FrameLift_mem_perp_iff
import Theorems.Thm_GlobalTheory_HL_FrameLift_mem_perp_range
import Theorems.Thm_GlobalTheory_HL_FrameLift_sum_mem_O
import Theorems.Thm_GlobalTheory_HL_FrameLift_expand
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_add_r
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_cj
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_smul_r
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_sub_l
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_sub_r
import Theorems.Thm_GlobalTheory_HL_FrameOnto_mem_perp
import Theorems.Thm_GlobalTheory_HL_FrameOnto_mem_spanTo
import Theorems.Thm_GlobalTheory_HL_FrameOnto_spanTo_le_perp
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameLift
open GlobalTheory.HL.Eichler GlobalTheory.HL.FrameOnto
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
variable (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (T : Fˣ)
  (gram : ∀ a b, hf L S.Hm (g a) (g b) =
    if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E T else 0)
  (dual : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
  (iso : ∀ i j, hf L S.Hm (gs i) (gs j) = 0)
include gram dual iso
namespace GlobalTheory.HL.FrameLift
theorem _root_.solution [IsNoetherianRing L.O] (Λ : Submodule L.O S.V) (hfg : Λ.FG)
    (hsd : ∀ y, (∀ x ∈ Λ, hf L S.Hm x y ∈ L.O) ↔ y ∈ Λ) (hg : ∀ b, g b ∈ Λ) (hgs : ∀ j, gs j ∈ Λ)
    (c : S.V) (hc : c ∈ Λ) (hc' : ∀ b, hf L S.Hm (g b) c = if b = Fin.last r then 1 else 0) :
    ∃ A, S.IsInner g gs A ∧ Λ = S.stdLat g gs A := by
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, hf L S.Hm x y ∈ L.O := fun x hx y hy => (hsd y).2 hy x hx
  have hXp := spanTo_le_perp S g T gram
  set A : Submodule L.O S.V := (Λ ⊔ (S.spanTo g r).restrictScalars L.O) ⊓
    (perp L S.Hm (S.spanTo g r)).restrictScalars L.O with hA
  have memA : ∀ x, x ∈ A ↔ (∃ a ∈ Λ, ∃ z ∈ S.spanTo g r, a + z = x) ∧
      x ∈ perp L S.Hm (S.spanTo g r) := fun x => by
    simp [hA, Submodule.mem_sup]
  have inA : ∀ x ∈ Λ, x ∈ perp L S.Hm (S.spanTo g r) → x ∈ A := fun x hx hx' =>
    (memA x).2 ⟨⟨x, hx, 0, zero_mem _, add_zero x⟩, hx'⟩
  have dual' : ∀ i j : Fin r, hf L S.Hm (gs i) (g j.castSucc) = if j = i then 1 else 0 := fun i j => by
    rw [← hf_cj L S.herm.1, dual]
    by_cases h : j = i <;> simp [h]
  have gram0 : ∀ i j : Fin r, hf L S.Hm (g i.castSucc) (g j.castSucc) = 0 := fun i j => by
    rw [gram, if_neg]; simp
  have hle : A ⊓ (perp L S.Hm (Submodule.span E (Set.range gs))).restrictScalars L.O ≤ Λ := by
    rintro x ⟨hx, hx'⟩
    obtain ⟨⟨a, ha, z, hz, rfl⟩, -⟩ := (memA x).1 hx
    refine add_mem ha ?_
    rw [expand S g gs dual hz]
    refine sum_mem_O S _ _ (fun i => ?_) fun i => hg _
    have h0 := (mem_perp_range S gs _).1 hx' i
    rw [hf_add_l] at h0
    rw [eq_neg_of_add_eq_zero_right h0]
    exact neg_mem (hint _ ha _ (hgs i))
  have hproj : ∀ v ∈ Λ, v - ∑ i : Fin r, hf L S.Hm v (g i.castSucc) • gs i ∈ Λ ∧
      v - ∑ i : Fin r, hf L S.Hm v (g i.castSucc) • gs i ∈ perp L S.Hm (S.spanTo g r) := by
    intro v hv
    refine ⟨sub_mem hv (sum_mem_O S _ _ (fun i => hint _ hv _ (hg _)) hgs),
      (mem_perp_iff S g _).2 fun j => ?_⟩
    simp [hf_sub_l, hf_sum_l, hf_smul_l, dual']
  refine ⟨A, ⟨fun x hx => (memA x).2 ⟨⟨0, zero_mem _, x, hx, zero_add x⟩, hXp hx⟩,
    fun x hx => ((memA x).1 hx).2, hfg.of_le hle,
    fun y hy => ⟨fun h => ?_, fun h x hx => ?_⟩, inA _ (hg _) (mem_perp S g T gram _),
    c, inA c hc ((mem_perp_iff S g _).2 fun j => ?_), ?_⟩, le_antisymm (fun v hv => ?_) ?_⟩
  · refine (memA y).2 ⟨⟨y - ∑ i : Fin r, hf L S.Hm y (gs i) • g i.castSucc, (hsd _).1 fun v hv => ?_, _,
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (mem_spanTo S g (by simp)),
      sub_add_cancel _ _⟩, hy⟩
    have := h _ (inA _ (hproj v hv).1 (hproj v hv).2)
    convert this using 1
    simp only [Frames.h, hf_sub_l, hf_sub_r, hf_sum_l, hf_sum_r, hf_smul_l, hf_smul_r,
      hf_cj L S.herm.1, mul_comm]
  · obtain ⟨⟨a, ha, z, hz, rfl⟩, hx'⟩ := (memA x).1 hx
    obtain ⟨⟨b, hb, w, hw, rfl⟩, -⟩ := (memA y).1 h
    have hb' : b ∈ perp L S.Hm (S.spanTo g r) := by simpa using sub_mem hy (hXp hw)
    have k : hf L S.Hm z b = 0 := by rw [← hf_cj L S.herm.1, hb' z hz, map_zero]
    unfold Frames.h
    rw [hf_add_r, hx' w hw, add_zero, hf_add_l, k, add_zero]
    exact hint _ ha _ hb
  · rw [← hf_cj L S.herm.1, hc', if_neg (Fin.castSucc_ne_last j), map_zero]
  · unfold Frames.h
    rw [hc', if_pos rfl]
  · obtain ⟨h1, h2⟩ := hproj v hv
    set x := v - ∑ i : Fin r, hf L S.Hm v (g i.castSucc) • gs i with hx
    have hxO : ∀ i, hf L S.Hm x (gs i) ∈ L.O := fun i => hint _ h1 _ (hgs i)
    have e : v = (∑ i : Fin r, hf L S.Hm x (gs i) • g i.castSucc +
        (x - ∑ i : Fin r, hf L S.Hm x (gs i) • g i.castSucc)) +
        ∑ i : Fin r, hf L S.Hm v (g i.castSucc) • gs i := by rw [hx]; abel
    rw [e]
    refine Submodule.add_mem_sup (Submodule.add_mem_sup
      (sum_mem_O S _ _ hxO fun i => Submodule.subset_span ⟨i, rfl⟩) ⟨inA _ ?_ ?_, ?_⟩) ?_
    · exact sub_mem h1 (sum_mem_O S _ _ hxO fun i => hg _)
    · exact sub_mem h2 (Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (mem_perp S g T gram _))
    · refine (mem_perp_range S gs _).2 fun j => ?_
      simp [hf_sub_l, hf_sum_l, hf_smul_l, dual]
    · exact sum_mem_O S _ _ (fun i => hint _ hv _ (hg _)) fun i => Submodule.subset_span ⟨i, rfl⟩
  · refine sup_le (sup_le (Submodule.span_le.2 ?_) hle) (Submodule.span_le.2 ?_)
    · rintro _ ⟨i, rfl⟩; exact hg _
    · rintro _ ⟨i, rfl⟩; exact hgs _
end GlobalTheory.HL.FrameLift
