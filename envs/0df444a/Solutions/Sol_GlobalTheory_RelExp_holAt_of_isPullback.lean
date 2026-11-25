-- Prove2me | solution 1 for GlobalTheory.RelExp.holAt_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:36:19.758815+00:00
-- url     : https://prove2.me/submissions/6f250b9a-d434-47fe-ae8e-b863306cc21f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EventuallyEqOfAdditiveOfHasFDerivAt
import Theorems.Thm_GlobalTheory_RelExp_isHolTo_mono
import Theorems.Thm_GlobalTheory_RelExp_HolAt_congr
import Theorems.Thm_GlobalTheory_holFamily_of_affine
import Theorems.Thm_GlobalTheory_top_le_preimage_iff_mem
import Theorems.Thm_P2M_GlobalTheory_valAt__add_b0728a15060b
import Theorems.Thm_P2M_GlobalTheory_valAt__appLE_1af07a5a9e22
import Theorems.Thm_P2M_GlobalTheory_valAt__mul_dca2439ccec2
import Theorems.Thm_P2M_GlobalTheory_valAt__neg_6a42563cad15
import Theorems.Thm_P2M_GlobalTheory_valAt__one_9935cf2928d8
import Theorems.Thm_P2M_GlobalTheory_valAt__rules_bb0546efa0f1
import Theorems.Thm_P2M_GlobalTheory_valAt__zero_f075fc9dd23d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.RelExp
variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {Z Y : Scheme.{0}}
namespace GlobalTheory.RelExp
theorem _root_.solution {S X : Scheme.{0}} {p : Z ⟶ X} {q : Z ⟶ Y} {s : X ⟶ S} {t : Y ⟶ S}
    (H : IsPullback p q s t) {c : E → (Sp ℂ ⟶ Z)} {w₀ : E} (ha : HolAt (fun w => c w ≫ p) w₀)
    (hb : HolAt (fun w => c w ≫ q) w₀) : HolAt c w₀ := by
  obtain ⟨W₁, hW₁, hw₁, ha⟩ := ha
  obtain ⟨W₂, hW₂, hw₂, hb⟩ := hb
  have hW := hW₁.inter hW₂
  replace ha := isHolTo_mono ha hW Set.inter_subset_left
  replace hb := isHolTo_mono hb hW Set.inter_subset_right
  refine ⟨W₁ ∩ W₂, hW, ⟨hw₁, hw₂⟩, fun U f => ?_⟩
  generalize W₁ ∩ W₂ = W at ha hb
  refine holFamily_of_affine valAt'_rules W Z c (fun w₀ hw₀ => ?_) U f
  obtain ⟨S₀, hS₀, hx₀, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤)
    (x := (c w₀ ≫ p ≫ s) (default : PrimeSpectrum ℂ)) trivial
  obtain ⟨U₁, hU₁, hx₁, h₁⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := s ⁻¹ᵁ S₀)
    (x := (c w₀ ≫ p) (default : PrimeSpectrum ℂ)) hx₀
  obtain ⟨U₂, hU₂, hx₂, h₂⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (U := t ⁻¹ᵁ S₀)
    (x := (c w₀ ≫ q) (default : PrimeSpectrum ℂ)) (by rw [H.w] at hx₀; exact hx₀)
  have h₁' : U₁ ≤ s ⁻¹ᵁ S₀ := h₁
  have h₂' : U₂ ≤ t ⁻¹ᵁ S₀ := h₂
  set V : Z.Opens := p ⁻¹ᵁ U₁ ⊓ q ⁻¹ᵁ U₂ with hVdef
  have hiff : ∀ w, ⊤ ≤ c w ⁻¹ᵁ V ↔ ⊤ ≤ (c w ≫ p) ⁻¹ᵁ U₁ ∧ ⊤ ≤ (c w ≫ q) ⁻¹ᵁ U₂ := fun w => by
    rw [hVdef, Scheme.Hom.preimage_inf, le_inf_iff, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
  have hV : IsAffineOpen V := by
    have : IsAffine _ := hS₀
    have : IsAffine _ := hU₁
    have : IsAffine _ := hU₂
    exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := S₀) (UT := U₂) (UX := U₁) h₂' h₁'
      hVdef).isoPullback.hom
  have po := (isIso_pushoutSection_iff H (US := S₀) (UT := U₂) (UX := U₁) h₂' h₁' hVdef).mp
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ hS₀ hU₂ hU₁)
  have hgen := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
  refine ⟨V, hV, (hiff w₀).2 ⟨(top_le_preimage_iff_mem _ _).2 hx₁, (top_le_preimage_iff_mem _ _).2 hx₂⟩, ?_,
    fun g => ?_⟩
  · convert (ha U₁ 0).1.inter (hb U₂ 0).1 using 1
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, hiff]
    tauto
  · have hg : g ∈ Subring.closure _ := hgen.ge (Subring.mem_top g)
    induction hg using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · exact ((ha U₁ y).2.mono fun w hw => ⟨hw.1, ((hiff w).1 hw.2).1⟩).congr fun w hw =>
          valAt'_appLE _ _ _ _ _ _ hw.2
      · exact ((hb U₂ y).2.mono fun w hw => ⟨hw.1, ((hiff w).1 hw.2).2⟩).congr fun w hw =>
          valAt'_appLE _ _ _ _ _ _ hw.2
    | zero => simp only [valAt'_zero]; exact differentiableOn_const _
    | one => exact (differentiableOn_const (1 : ℂ)).congr fun w hw => valAt'_one _ hw.2
    | add x y _ _ hx hy => simp only [valAt'_add]; exact hx.add hy
    | neg x _ hx => simp only [valAt'_neg]; exact hx.neg
    | mul x y _ _ hx hy => simp only [valAt'_mul]; exact hx.mul hy
end GlobalTheory.RelExp
