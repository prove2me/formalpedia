-- Prove2me | solution 1 for GlobalTheory.HolFibre.isHolTo_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:41:45.696312+00:00
-- url     : https://prove2.me/submissions/36d47225-4abc-448e-8e08-dabe48f088ef

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsHolToFibPtAndCompFibre
import Theorems.Thm_GlobalTheory_holFamily_of_affine
import Theorems.Thm_GlobalTheory_top_le_preimage_comp
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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HolFibre
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.HolFibre
theorem _root_.solution {W : Set E} {S X Y Z : Scheme.{0}}
    {p : Z ⟶ X} {q : Z ⟶ Y} {s : X ⟶ S} {t : Y ⟶ S} (H : IsPullback p q s t) {c : E → (Sp ℂ ⟶ Z)}
    (ha : IsHolTo W (fun w => c w ≫ p)) (hb : IsHolTo W (fun w => c w ≫ q)) : IsHolTo W c := by
  intro U f
  refine holFamily_of_affine valAt'_rules W Z c (fun w₀ hw₀ => ?_) U f
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hx₀, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((c w₀ ≫ p ≫ s) (default : PrimeSpectrum ℂ))) isOpen_univ
  have hm₁ : (c w₀ ≫ p) (default : PrimeSpectrum ℂ) ∈ s ⁻¹ᵁ U₀ := by
    rw [← top_le_preimage_iff_mem, ← top_le_preimage_comp, Category.assoc, top_le_preimage_iff_mem]
    exact hx₀
  have hm₂ : (c w₀ ≫ q) (default : PrimeSpectrum ℂ) ∈ t ⁻¹ᵁ U₀ := by
    rw [← top_le_preimage_iff_mem, ← top_le_preimage_comp, Category.assoc, ← H.w, top_le_preimage_iff_mem]
    exact hx₀
  obtain ⟨_, ⟨U₁, hU₁, rfl⟩, hx₁, hl₁⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    hm₁ (s ⁻¹ᵁ U₀).isOpen
  obtain ⟨_, ⟨U₂, hU₂, rfl⟩, hx₂, hl₂⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    hm₂ (t ⁻¹ᵁ U₀).isOpen
  have hU₀ : IsAffineOpen U₀ := hU₀
  have hU₁ : IsAffineOpen U₁ := hU₁
  have hU₂ : IsAffineOpen U₂ := hU₂
  have hl₁ : U₁ ≤ s ⁻¹ᵁ U₀ := hl₁
  have hl₂ : U₂ ≤ t ⁻¹ᵁ U₀ := hl₂
  set V : Z.Opens := p ⁻¹ᵁ U₁ ⊓ q ⁻¹ᵁ U₂ with hVdef
  have hiff : ∀ w, ⊤ ≤ c w ⁻¹ᵁ V ↔ ⊤ ≤ (c w ≫ p) ⁻¹ᵁ U₁ ∧ ⊤ ≤ (c w ≫ q) ⁻¹ᵁ U₂ := fun w => by
    rw [hVdef, Scheme.Hom.preimage_inf, le_inf_iff, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
  have hV : IsAffineOpen V := by
    have : IsAffine _ := hU₀
    have : IsAffine _ := hU₁
    have : IsAffine _ := hU₂
    exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := U₀) (UT := U₂) (UX := U₁) hl₂ hl₁
      hVdef).isoPullback.hom
  have po := (isIso_pushoutSection_iff H (US := U₀) (UT := U₂) (UX := U₁) hl₂ hl₁ hVdef).mp
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ hU₀ hU₂ hU₁)
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
          valAt'_appLE (c w) p U₁ V _ y hw.2
      · exact ((hb U₂ y).2.mono fun w hw => ⟨hw.1, ((hiff w).1 hw.2).2⟩).congr fun w hw =>
          valAt'_appLE (c w) q U₂ V _ y hw.2
    | zero => exact (differentiableOn_const (0 : ℂ)).congr fun w _ => valAt'_zero _ _
    | one => exact (differentiableOn_const (1 : ℂ)).congr fun w hw => valAt'_one _ hw.2
    | add x y _ _ hx hy => exact (hx.add hy).congr fun w _ => valAt'_add _ _ _ _
    | neg x _ hx => exact hx.neg.congr fun w _ => valAt'_neg _ _ _
    | mul x y _ _ hx hy => exact (hx.mul hy).congr fun w _ => valAt'_mul _ _ _ _
end GlobalTheory.HolFibre
