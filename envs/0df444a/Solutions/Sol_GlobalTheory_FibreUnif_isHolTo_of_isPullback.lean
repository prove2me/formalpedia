-- Prove2me | solution 1 for GlobalTheory.FibreUnif.isHolTo_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:52.748584+00:00
-- url     : https://prove2.me/submissions/498e9b77-7aea-4334-8c1e-7fdd2fef90b1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_FamilyUniformisationFibreTheta
import Theorems.Thm_GlobalTheory_coe_modNEquivTorsion_mk
import Theorems.Thm_GlobalTheory_top_le_preimage_basicOpen_iff
import Theorems.Thm_GlobalTheory_top_le_preimage_comp
import Theorems.Thm_GlobalTheory_top_le_preimage_iff_mem
import Theorems.Thm_GlobalTheory_top_le_preimage_mono
import Theorems.Thm_P2M_GlobalTheory_valAt__add_b0728a15060b
import Theorems.Thm_P2M_GlobalTheory_valAt__appLE_1af07a5a9e22
import Theorems.Thm_P2M_GlobalTheory_valAt__mul_dca2439ccec2
import Theorems.Thm_P2M_GlobalTheory_valAt__neg_6a42563cad15
import Theorems.Thm_P2M_GlobalTheory_valAt__one_9935cf2928d8
import Theorems.Thm_P2M_GlobalTheory_valAt__pow_e372e8ea15a8
import Theorems.Thm_P2M_GlobalTheory_valAt__res_db2aea6d876c
import Theorems.Thm_P2M_GlobalTheory_valAt__zero_f075fc9dd23d
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_modNEquivTorsion_mk



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
open GlobalTheory
open GlobalTheory.FibreUnif
namespace GlobalTheory.FibreUnif
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X Y Z : Scheme.{0}} {φ : Y ⟶ Z}
    {s : Y ⟶ Sp ℂ} {p : Z ⟶ X} {y : Sp ℂ ⟶ X} (H : IsPullback φ s p y) {e : V → (Sp ℂ ⟶ Y)}
    (hs : ∀ z, e z ≫ s = 𝟙 _) (hol : IsHolTo Set.univ (fun z => e z ≫ φ)) : IsHolTo Set.univ e := by
  suffices key : ∀ (W : Y.Opens) (f : Γ(Y, W)) (z₀ : V), ⊤ ≤ e z₀ ⁻¹ᵁ W →
      (∀ᶠ z in 𝓝 z₀, ⊤ ≤ e z ⁻¹ᵁ W) ∧ DifferentiableAt ℂ (fun z => valAt' (e z) W f) z₀ by
    intro W f
    refine ⟨isOpen_iff_mem_nhds.2 fun z hz => ?_, fun z hz => (key W f z hz.2).2.differentiableWithinAt⟩
    filter_upwards [(key W f z hz.2).1] with z' hz' using ⟨trivial, hz'⟩
  intro W f z₀ hW
  obtain ⟨S, hS, hyS, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤)
    (x := y (default : PrimeSpectrum ℂ)) trivial
  have hyS' : ⊤ ≤ y ⁻¹ᵁ S := (top_le_preimage_iff_mem y S).2 hyS
  have hey : (e z₀ ≫ φ) ≫ p = y := by rw [Category.assoc, H.w, ← Category.assoc, hs, Category.id_comp]
  obtain ⟨U, hU, hxU, hUS⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (U := p ⁻¹ᵁ S)
    (x := (e z₀ ≫ φ) (default : PrimeSpectrum ℂ))
    ((top_le_preimage_iff_mem _ _).1 ((top_le_preimage_comp _ p S).1 (hey.symm ▸ hyS')))
  have hUS' : U ≤ p ⁻¹ᵁ S := hUS
  have hVdef : φ ⁻¹ᵁ U = φ ⁻¹ᵁ U ⊓ s ⁻¹ᵁ ⊤ := by simp
  have hV : IsAffineOpen (φ ⁻¹ᵁ U) := by
    have : IsAffine _ := isAffineOpen_top (Sp ℂ)
    have : IsAffine _ := hU
    have : IsAffine _ := hS
    exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := S) (UT := ⊤) (UX := U) hyS' hUS' hVdef).isoPullback.hom
  have po := (isIso_pushoutSection_iff H (US := S) (UT := ⊤) (UX := U) hyS' hUS' hVdef).mp
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ hS (isAffineOpen_top _) hU)
  have hgen := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
  have hU₀ : ⊤ ≤ (e z₀ ≫ φ) ⁻¹ᵁ U := (top_le_preimage_iff_mem _ _).2 hxU
  have hV₀ : ⊤ ≤ e z₀ ⁻¹ᵁ (φ ⁻¹ᵁ U) := (top_le_preimage_comp _ φ U).1 hU₀
  have hN := (hol U 0).1.mem_nhds (x := z₀) ⟨trivial, hU₀⟩
  have hev : ∀ᶠ z in 𝓝 z₀, ⊤ ≤ e z ⁻¹ᵁ (φ ⁻¹ᵁ U) := by
    filter_upwards [hN] with z hz using (top_le_preimage_comp _ φ U).1 hz.2
  have hconst : ∀ (a : Γ(Y, φ ⁻¹ᵁ U)) (c : ℂ), (∀ z, ⊤ ≤ e z ⁻¹ᵁ (φ ⁻¹ᵁ U) → valAt' (e z) _ a = c) →
      DifferentiableAt ℂ (fun z => valAt' (e z) _ a) z₀ := fun a c h1 =>
    (differentiableAt_const c).congr_of_eventuallyEq (hev.mono h1)
  have D : ∀ a : Γ(Y, φ ⁻¹ᵁ U), DifferentiableAt ℂ (fun z => valAt' (e z) _ a) z₀ := by
    intro a
    have ha : a ∈ Subring.closure _ := hgen.ge (Subring.mem_top a)
    induction ha using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨b, rfl⟩ | ⟨b, rfl⟩
      · have h3 : (fun z => valAt' (e z) _ ((φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom b)) =ᶠ[𝓝 z₀]
            fun z => valAt' (e z ≫ φ) U b := hev.mono fun z hz => valAt'_appLE _ _ _ _ _ _ hz
        exact ((hol U b).2.differentiableAt hN).congr_of_eventuallyEq h3
      · refine hconst _ (valAt' (𝟙 _) ⊤ b) (fun z hz => ?_)
        rw [valAt'_appLE _ _ _ _ _ _ hz, hs]
    | zero => exact hconst _ 0 (fun z _ => valAt'_zero _ _)
    | one => exact hconst _ 1 (fun z hz => valAt'_one _ hz)
    | add x y _ _ hx hy =>
      simp only [valAt'_add]
      exact hx.add hy
    | neg x _ hx =>
      simp only [valAt'_neg]
      exact hx.neg
    | mul x y _ _ hx hy =>
      simp only [valAt'_mul]
      exact hx.mul hy
  obtain ⟨h, hhU, hh₀⟩ := hV.exists_basicOpen_le (V := W)
    ⟨_, (top_le_preimage_iff_mem _ W).1 hW⟩ ((top_le_preimage_iff_mem _ _).1 hV₀)
  have hD₀ : ⊤ ≤ e z₀ ⁻¹ᵁ Y.basicOpen h := (top_le_preimage_iff_mem _ _).2 hh₀
  have hn₀ : valAt' (e z₀) _ h ≠ 0 := (top_le_preimage_basicOpen_iff _ _ h).1 hD₀
  have hev' : ∀ᶠ z in 𝓝 z₀, ⊤ ≤ e z ⁻¹ᵁ Y.basicOpen h := by
    filter_upwards [(D h).continuousAt.eventually_ne hn₀] with z hz
    exact (top_le_preimage_basicOpen_iff _ _ h).2 hz
  refine ⟨hev'.mono fun z hz => top_le_preimage_mono _ hhU hz, ?_⟩
  have hloc := hV.isLocalization_basicOpen h
  obtain ⟨⟨a, _, n, rfl⟩, ha⟩ := IsLocalization.surj (Submonoid.powers h) (resG Y hhU f)
  have ha' : resG Y hhU f * resG Y (Y.basicOpen_le h) (h ^ n) = resG Y (Y.basicOpen_le h) a := ha
  have hb₀ : valAt' (e z₀) _ (h ^ n) ≠ 0 := by
    rw [valAt'_pow _ hV₀]
    exact pow_ne_zero n hn₀
  have hmul : (fun z => valAt' (e z) W f * valAt' (e z) _ (h ^ n)) =ᶠ[𝓝 z₀] fun z => valAt' (e z) _ a := by
    filter_upwards [hev'] with z hz
    rw [← valAt'_res _ hhU f hz, ← valAt'_res _ (Y.basicOpen_le h) (h ^ n) hz, ← valAt'_mul, ha', valAt'_res _ _ _ hz]
  refine ((D a).mul ((D (h ^ n)).inv hb₀)).congr_of_eventuallyEq ?_
  filter_upwards [hmul, (D (h ^ n)).continuousAt.eventually_ne hb₀] with z h1 h2
  simp only [Pi.mul_apply, Pi.inv_apply]
  rw [eq_mul_inv_iff_mul_eq₀ h2]
  exact h1
end GlobalTheory.FibreUnif
