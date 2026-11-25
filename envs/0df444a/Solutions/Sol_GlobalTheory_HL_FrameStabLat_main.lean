-- Prove2me | solution 1 for GlobalTheory.HL.FrameStabLat.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:18:03.93697+00:00
-- url     : https://prove2.me/submissions/cf074838-6004-4e1a-aa88-f41ebc2b0430

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsLatticeStabilizerNormalisingSubgroup
import Theorems.Thm_GlobalTheory_HL_FrameStabLat_mem_stab_iff
import Theorems.Thm_GlobalTheory_HL_FrameStabLat_mem_stab_set_iff
import Theorems.Thm_GlobalTheory_HL_FrameStabLat_span_le
import Theorems.Thm_GlobalTheory_HL_FrameStabLat_map_span
import Theorems.Thm_GlobalTheory_HL_FrameStabLat_map_spanE
import Theorems.Thm_GlobalTheory_HL_FrameStabLat_map_mem_of_mem_sup_three_submodules
import Theorems.Thm_GlobalTheory_HL_FrameStabLat_inter
import Theorems.Thm_GlobalTheory_HL_FrameStabLat_cong_coef
import Theorems.Thm_GlobalTheory_HL_FrameStabLat_frame_facts
import Theorems.Thm_GlobalTheory_HL_FrameStabLat_spanTo_top
import Theorems.Thm_GlobalTheory_HL_FrameStabLat_move_perp
import Theorems.Thm_GlobalTheory_HL_FrameStabLat_cls_map
import Theorems.Thm_GlobalTheory_HL_FrameStabLat_self_mem_cls
import Theorems.Thm_GlobalTheory_HL_FrameStabLat_mem_of_cls
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_HL_FrameOnto_unipotent_onto
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameStabLat
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E} {r k : ℕ}
namespace GlobalTheory.HL.FrameStabLat
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ n ∈ S.N, ∀ n' ∈ S.N', ∃ Λ : Submodule L.O S.V, IsLat L Λ ∧ S.St ⊓ stabL L Λ = S.St ⊓ stabL L (Submodule.span L.O (Set.range fun b => n (S.f b))) ⊓ stabL L (Submodule.span L.O (Set.range fun b => n' (S.f' b))) ∧ S.St ⊓ MulAction.stabilizer S.GLV (S.frameCls (fun b => n (S.f b)) fun b => n' (S.f' b)) ≤ S.St ⊓ stabL L Λ ∧ ∀ h ∈ S.St ⊓ stabL L Λ, CongId L S.ϖ Λ 1 h → h ∈ MulAction.stabilizer S.GLV (S.frameCls (fun b => n (S.f b)) fun b => n' (S.f' b)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S n hn n' hn'
  obtain ⟨hli, hcompl, -, -, -, -, -, b, -, hb⟩ := GlobalTheory.FrameBasic.main L r k S
  obtain ⟨hN, hN', -⟩ := GlobalTheory.HL.FrameOnto.unipotent_onto L r k S
  obtain ⟨hf, hf', hdis⟩ := linearIndependent_sum.1 hli
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at hf hf' hdis
  obtain ⟨hg, hP, hs⟩ := frame_facts S.f hf S.N hN n hn
  obtain ⟨hg', hP', hs'⟩ := frame_facts S.f' hf' S.N' hN' n' hn'
  set g : Fin (r + 1) → S.V := fun b => n (S.f b) with hgdef
  set g' : Fin (r + 1) → S.V := fun b => n' (S.f' b) with hgdef'
  have hME : S.ME = Submodule.span E (Set.range S.f) ⊔ Submodule.span E (Set.range S.f') := by
    unfold Frames.ME
    rw [spanTo_top, spanTo_top]
  have hfix : ∀ h ∈ S.St, ∀ w ∈ S.W0, h w = w := by
    intro h hh w hw
    have h1 := move_perp S S.f h hh.1 w hw (hME ▸ le_sup_left)
    have h2 := move_perp S S.f' h hh.2 w hw (hME ▸ le_sup_right)
    exact sub_eq_zero.1 (Submodule.disjoint_def.1 hdis _ h1 h2)
  rw [← hP, ← hP'] at hME hdis
  set P := Submodule.span E (Set.range g) with hPdef
  set P' := Submodule.span E (Set.range g') with hPdef'
  set A := Submodule.span L.O (Set.range g) with hAdef
  set A' := Submodule.span L.O (Set.range g') with hAdef'
  set B := Submodule.span L.O (Set.range b) with hBdef
  have hA : ∀ x ∈ A, x ∈ P := fun x hx => span_le L.O g hx
  have hA' : ∀ x ∈ A', x ∈ P' := fun x hx => span_le L.O g' hx
  have hB : ∀ x ∈ B, x ∈ S.W0 := fun x hx => hb ▸ span_le L.O b hx
  have hind : ∀ a ∈ P, ∀ a' ∈ P', ∀ w ∈ S.W0, a + a' + w = 0 → a = 0 ∧ a' = 0 := by
    intro a ha a' ha' w hw e
    have h1 : a + a' ∈ S.ME := hME ▸ Submodule.add_mem_sup ha ha'
    have h2 : a + a' ∈ S.W0 := by
      rw [eq_neg_of_add_eq_zero_left e]; exact S.W0.neg_mem hw
    have h3 := Submodule.disjoint_def.1 hcompl.disjoint _ h1 h2
    have h4 : a = 0 := Submodule.disjoint_def.1 hdis a ha (by
      rw [eq_neg_of_add_eq_zero_left h3]; exact P'.neg_mem ha')
    exact ⟨h4, by simpa [h4] using h3⟩
  have hint := fun x (hx : x ∈ A ⊔ A' ⊔ B) => inter L.O A A' B P P' S.W0 hA hA' hB hind hx
  have lA : ∀ x ∈ A, x ∈ A ⊔ A' ⊔ B := fun x hx =>
    Submodule.mem_sup_left (Submodule.mem_sup_left hx)
  have lA' : ∀ x ∈ A', x ∈ A ⊔ A' ⊔ B := fun x hx =>
    Submodule.mem_sup_left (Submodule.mem_sup_right hx)
  have lB : ∀ x ∈ B, x ∈ A ⊔ A' ⊔ B := fun x hx => Submodule.mem_sup_right hx
  have presP : ∀ h ∈ S.St, (∀ x ∈ P, h x ∈ P) ∧ ∀ x ∈ P', h x ∈ P' := by
    intro h hh
    obtain ⟨s, -, e⟩ := hs h hh.1
    obtain ⟨s', -, e'⟩ := hs' h hh.2
    refine ⟨fun x hx => map_spanE g h P (fun j => ?_) hx, fun x hx => map_spanE g' h P' (fun j => ?_) hx⟩
    · rw [show h (g j) = ∑ i, s i j • g i from e j]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    · rw [show h (g' j) = ∑ i, s' i j • g' i from e' j]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  have down : ∀ h ∈ S.St, (∀ x ∈ A ⊔ A' ⊔ B, h x ∈ A ⊔ A' ⊔ B) →
      (∀ x ∈ A, h x ∈ A) ∧ ∀ x ∈ A', h x ∈ A' := fun h hh H =>
    ⟨fun x hx => (hint _ (H x (lA x hx))).1 ((presP h hh).1 x (hA x hx)),
      fun x hx => (hint _ (H x (lA' x hx))).2 ((presP h hh).2 x (hA' x hx))⟩
  have up : ∀ h ∈ S.St, (∀ x ∈ A, h x ∈ A) → (∀ x ∈ A', h x ∈ A') →
      ∀ x ∈ A ⊔ A' ⊔ B, h x ∈ A ⊔ A' ⊔ B := fun h hh H H' =>
    map_mem_of_mem_sup_three_submodules L.O A A' B _ h (fun x hx => lA _ (H x hx)) (fun x hx => lA' _ (H' x hx))
      fun x hx => by rw [hfix h hh x (hB x hx)]; exact lB x hx
  refine ⟨A ⊔ A' ⊔ B, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · exact ((Submodule.fg_span (Set.finite_range _)).sup (Submodule.fg_span (Set.finite_range _))).sup
      (Submodule.fg_span (Set.finite_range _))
  · rw [eq_top_iff, ← hcompl.sup_eq_top, hME, hb]
    refine sup_le (sup_le ?_ ?_) ?_
    · exact Submodule.span_mono fun x hx => lA x (Submodule.subset_span hx)
    · exact Submodule.span_mono fun x hx => lA' x (Submodule.subset_span hx)
    · exact Submodule.span_mono fun x hx => lB x (Submodule.subset_span hx)
  · ext h
    simp only [Subgroup.mem_inf, mem_stab_iff]
    constructor
    · rintro ⟨hh, H1, H2⟩
      have d1 := down h hh H1
      have d2 := down h⁻¹ (S.St.inv_mem hh) H2
      exact ⟨⟨hh, d1.1, d2.1⟩, d1.2, d2.2⟩
    · rintro ⟨⟨hh, a1, a2⟩, a3, a4⟩
      exact ⟨hh, up h hh a1 a3, up h⁻¹ (S.St.inv_mem hh) a2 a4⟩
  · rintro h ⟨hh, H⟩
    obtain ⟨H1, H2⟩ := (mem_stab_set_iff _ h).1 H
    have m1 := mem_of_cls S g g' _ (H1 _ (self_mem_cls S g g'))
    have m2 := mem_of_cls S g g' _ (H2 _ (self_mem_cls S g g'))
    refine ⟨hh, (mem_stab_iff L.O _ h).2 ⟨?_, ?_⟩⟩
    · exact up h hh (fun x hx => map_span L.O g h A m1.1 hx) fun x hx => map_span L.O g' h A' m1.2 hx
    · exact up h⁻¹ (S.St.inv_mem hh) (fun x hx => map_span L.O g h⁻¹ A m2.1 hx)
        fun x hx => map_span L.O g' h⁻¹ A' m2.2 hx
  · have hϖ : ((S.ϖ : F) ^ 1) ≠ 0 := by
      rw [pow_one]
      exact fun h => S.ϖ_irr.ne_zero (Subtype.ext h)
    have hu : IsUnit (algebraMap F E ((S.ϖ : F) ^ 1)) := (IsUnit.mk0 _ hϖ).map _
    have hO : algebraMap F E ((S.ϖ : F) ^ 1) ∈ L.O := by
      rw [L.O_def, pow_one]
      exact isIntegral_algebraMap (R := 𝒪[F]) (A := E) (x := S.ϖ)
    have hth : ∃ d ∈ L.O, algebraMap F E ((S.ϖ : F) ^ 1) = algebraMap F E S.th * d := by
      unfold Frames.th
      split_ifs
      · exact ⟨1, L.O.one_mem, by simp⟩
      · exact ⟨_, hO, by simp⟩
    have step : ∀ h ∈ S.St, CongId L S.ϖ (A ⊔ A' ⊔ B) 1 h →
        ∀ p ∈ S.frameCls g g', h • p ∈ S.frameCls g g' := by
      intro h hh hc
      obtain ⟨s, us, e⟩ := hs h hh.1
      obtain ⟨s', us', e'⟩ := hs' h hh.2
      exact cls_map S g g' h s s' us us' e e' _ hO hth
        (cong_coef L.O g hg h s e _ hu _ (fun x hx => (hint x hx).1)
          fun j => hc _ (lA _ (Submodule.subset_span ⟨j, rfl⟩)))
        (cong_coef L.O g' hg' h s' e' _ hu _ (fun x hx => (hint x hx).2)
          fun j => hc _ (lA' _ (Submodule.subset_span ⟨j, rfl⟩)))
    rintro h ⟨hh, H⟩ hc
    obtain ⟨-, H2⟩ := (mem_stab_iff L.O _ h).1 H
    refine (mem_stab_set_iff _ h).2 ⟨step h hh hc, step h⁻¹ (S.St.inv_mem hh) fun v hv => ?_⟩
    obtain ⟨w, hw, e⟩ := hc _ (H2 v hv)
    refine ⟨-w, Submodule.neg_mem _ hw, ?_⟩
    rw [smul_neg, ← e, show h (h⁻¹ v) = v from h.apply_symm_apply v, neg_sub]
end GlobalTheory.HL.FrameStabLat
