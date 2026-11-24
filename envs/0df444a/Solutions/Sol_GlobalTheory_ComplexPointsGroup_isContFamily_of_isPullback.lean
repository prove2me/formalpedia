-- Prove2me | solution 1 for GlobalTheory.ComplexPointsGroup.isContFamily_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:18:06.119897+00:00
-- url     : https://prove2.me/submissions/2dabdd88-0d9e-4553-a914-d944fa3d14e1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsTopologicalGroupComplexPoints
import Theorems.Thm_GlobalTheory_ComplexPointsGroup_IsContFamily_isOpen_mem
import Theorems.Thm_GlobalTheory_ComplexPointsGroup_IsContFamily_continuousOn
import Theorems.Thm_GlobalTheory_ComplexPointsGroup_isContFamily_of_affine
import Theorems.Thm_P2M_GlobalTheory_ComplexPointsGroup_valAt__appLE_86929644a546

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ComplexPointsGroup
variable {T : Type} [TopologicalSpace T]
variable (hv : ∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a))
include hv
namespace GlobalTheory.ComplexPointsGroup
theorem _root_.solution {X Y S Z : Scheme.{0}} [IsAffine S] {f : Y ⟶ S} {g : Z ⟶ X} {iX : X ⟶ S}
    {iY : Z ⟶ Y} (H : IsPullback g iY iX f) {e : T → (Sp ℂ ⟶ Z)}
    (h₁ : IsContFamily (fun t => e t ≫ g)) (h₂ : IsContFamily (fun t => e t ≫ iY)) : IsContFamily e := by
  refine isContFamily_of_affine hv fun t₀ => ?_
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤)
    (x := (e t₀ ≫ g) (default : PrimeSpectrum ℂ)) trivial
  obtain ⟨V, hV, hpV, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (U := ⊤)
    (x := (e t₀ ≫ iY) (default : PrimeSpectrum ℂ)) trivial
  have hmem : ∀ t, ⊤ ≤ e t ⁻¹ᵁ (g ⁻¹ᵁ U ⊓ iY ⁻¹ᵁ V) ↔ ⊤ ≤ (e t ≫ g) ⁻¹ᵁ U ∧ ⊤ ≤ (e t ≫ iY) ⁻¹ᵁ V := by
    intro t
    rw [Scheme.Hom.preimage_inf, le_inf_iff]
    rfl
  have hP : IsAffineOpen (g ⁻¹ᵁ U ⊓ iY ⁻¹ᵁ V) := by
    have : IsAffine _ := hU
    have : IsAffine _ := hV
    have : IsAffine _ := isAffineOpen_top S
    exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := V) (UX := U) le_top le_top rfl).isoPullback.hom
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := V) (UX := U) le_top le_top rfl).1
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) hV hU)
  refine ⟨_, hP, (hmem t₀).2 ⟨((hv _ _).1 _).2 hpU, ((hv _ _).1 _).2 hpV⟩, ?_, fun r => ?_⟩
  · simp only [hmem]
    exact (h₁.isOpen_mem U).inter (h₂.isOpen_mem V)
  have hr := (CommRingCat.closure_range_union_range_eq_top_of_isPushout po).ge (Subring.mem_top r)
  induction hr using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · exact ((h₁.continuousOn U a).mono fun t ht => ((hmem t).1 ht).1).congr
        fun t ht => valAt'_appLE hv _ _ _ _ _ _ ht
    · exact ((h₂.continuousOn V b).mono fun t ht => ((hmem t).1 ht).2).congr
        fun t ht => valAt'_appLE hv _ _ _ _ _ _ ht
  | zero =>
    refine (continuousOn_const (c := (0 : ℂ))).congr fun t ht => ?_
    obtain ⟨ev, hev⟩ := (hv Z (e t)).2.1 _ ht
    simp only [hev, map_zero]
  | one =>
    refine (continuousOn_const (c := (1 : ℂ))).congr fun t ht => ?_
    obtain ⟨ev, hev⟩ := (hv Z (e t)).2.1 _ ht
    simp only [hev, map_one]
  | add x y _ _ hx hy =>
    refine (hx.add hy).congr fun t ht => ?_
    obtain ⟨ev, hev⟩ := (hv Z (e t)).2.1 _ ht
    simp only [hev, map_add, Pi.add_apply]
  | neg x _ hx =>
    refine hx.neg.congr fun t ht => ?_
    obtain ⟨ev, hev⟩ := (hv Z (e t)).2.1 _ ht
    simp only [hev, map_neg, Pi.neg_apply]
  | mul x y _ _ hx hy =>
    refine (hx.mul hy).congr fun t ht => ?_
    obtain ⟨ev, hev⟩ := (hv Z (e t)).2.1 _ ht
    simp only [hev, map_mul, Pi.mul_apply]
end GlobalTheory.ComplexPointsGroup
