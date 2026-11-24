-- Prove2me | solution 1 for GlobalTheory.HolHom.holAt_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:08:39.227011+00:00
-- url     : https://prove2.me/submissions/9735750b-8ba4-438a-af84-9f46dacf2256

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Theorems.Thm_GlobalTheory_HolHom_valR_appLE
import Theorems.Thm_GlobalTheory_HolHom_exists_affine
import Theorems.Thm_GlobalTheory_HolHom_holAt_of_affine

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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HolHom
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}
namespace GlobalTheory.HolHom
theorem _root_.solution {Y S Z : Scheme.{0}} {f : Y ⟶ S} {g : Z ⟶ X} {iX : X ⟶ S} {iY : Z ⟶ Y}
    (H : IsPullback g iY iX f) {c : V → (Sp ℂ ⟶ Z)} {z : V}
    (h₁ : HolAt (fun t => c t ≫ g) z) (h₂ : HolAt (fun t => c t ≫ iY) z) : HolAt c z := by
  obtain ⟨T, hT, hpT, -⟩ := exists_affine (c z ≫ g ≫ iX) (U := ⊤) le_top
  obtain ⟨U, hU, hpU, hUT⟩ := exists_affine (c z ≫ g) (U := iX ⁻¹ᵁ T) hpT
  obtain ⟨W, hW, hpW, hWT⟩ := exists_affine (c z ≫ iY) (U := f ⁻¹ᵁ T) (by rw [H.w] at hpT; exact hpT)
  have hmem : ∀ t, ⊤ ≤ c t ⁻¹ᵁ (g ⁻¹ᵁ U ⊓ iY ⁻¹ᵁ W) ↔ ⊤ ≤ (c t ≫ g) ⁻¹ᵁ U ∧ ⊤ ≤ (c t ≫ iY) ⁻¹ᵁ W := by
    intro t
    rw [Scheme.Hom.preimage_inf, le_inf_iff]
    rfl
  have hP : IsAffineOpen (g ⁻¹ᵁ U ⊓ iY ⁻¹ᵁ W) := by
    have : IsAffine _ := hU
    have : IsAffine _ := hW
    have : IsAffine _ := hT
    exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := T) (UT := W) (UX := U) hWT hUT rfl).isoPullback.hom
  have po := (isIso_pushoutSection_iff H (US := T) (UT := W) (UX := U) hWT hUT rfl).1
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ hT hW hU)
  have hev : ∀ᶠ t in 𝓝 z, ⊤ ≤ c t ⁻¹ᵁ (g ⁻¹ᵁ U ⊓ iY ⁻¹ᵁ W) := by
    filter_upwards [(h₁ U hpU).1, (h₂ W hpW).1] with t h1 h2 using (hmem t).2 ⟨h1, h2⟩
  refine holAt_of_affine hP ((hmem z).2 ⟨hpU, hpW⟩) hev fun r => ?_
  have hr := (CommRingCat.closure_range_union_range_eq_top_of_isPushout po).ge (Subring.mem_top r)
  induction hr using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · exact ((h₁ U hpU).2 a).congr_of_eventuallyEq (hev.mono fun t ht => valR_appLE _ _ _ _ _ _ ht)
    · exact ((h₂ W hpW).2 b).congr_of_eventuallyEq (hev.mono fun t ht => valR_appLE _ _ _ _ _ _ ht)
  | zero =>
    refine (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq (hev.mono fun t ht => ?_)
    simp only [valAt'_eq_valR, valR_eq _ _ ht, map_zero]
  | one =>
    refine (differentiableAt_const (1 : ℂ)).congr_of_eventuallyEq (hev.mono fun t ht => ?_)
    simp only [valAt'_eq_valR, valR_eq _ _ ht, map_one]
  | add x y _ _ hx hy =>
    refine (hx.add hy).congr_of_eventuallyEq (hev.mono fun t ht => ?_)
    simp only [valAt'_eq_valR, valR_eq _ _ ht, map_add, Pi.add_apply]
  | neg x _ hx =>
    refine hx.neg.congr_of_eventuallyEq (hev.mono fun t ht => ?_)
    simp only [valAt'_eq_valR, valR_eq _ _ ht, map_neg, Pi.neg_apply]
  | mul x y _ _ hx hy =>
    refine (hx.mul hy).congr_of_eventuallyEq (hev.mono fun t ht => ?_)
    simp only [valAt'_eq_valR, valR_eq _ _ ht, map_mul, Pi.mul_apply]
end GlobalTheory.HolHom
