-- Prove2me | solution 1 for GlobalTheory.FibreDeriv.isDerivAt0_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:06:40.633876+00:00
-- url     : https://prove2.me/submissions/a50b31fb-0dea-460c-bdec-19cb829cbe09

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsDerivAt0OfIsPullback
import Theorems.Thm_GlobalTheory_FibreDeriv_jet_congr
import Theorems.Thm_GlobalTheory_FibreDeriv_jet_const
import Theorems.Thm_GlobalTheory_FibreDeriv_jet_add
import Theorems.Thm_GlobalTheory_FibreDeriv_jet_neg
import Theorems.Thm_GlobalTheory_FibreDeriv_jet_mul
import Theorems.Thm_GlobalTheory_FibreDeriv_evEps_appLE
import Theorems.Thm_GlobalTheory_FibreDeriv_evEps_spMap
import Theorems.Thm_GlobalTheory_FibreDeriv_top_le_preimage_eps
import Theorems.Thm_GlobalTheory_FibreDeriv_isDerivAt0_iff
import Theorems.Thm_GlobalTheory_FibreDeriv_isDerivAt0_of_affine
import Theorems.Thm_GlobalTheory_top_le_preimage_comp
import Theorems.Thm_GlobalTheory_top_le_preimage_iff_mem
import Theorems.Thm_P2M_GlobalTheory_valAt__add_b0728a15060b
import Theorems.Thm_P2M_GlobalTheory_valAt__appLE_1af07a5a9e22
import Theorems.Thm_P2M_GlobalTheory_valAt__id_top_2b98de8ae8d0
import Theorems.Thm_P2M_GlobalTheory_valAt__mul_dca2439ccec2
import Theorems.Thm_P2M_GlobalTheory_valAt__neg_6a42563cad15
import Theorems.Thm_P2M_GlobalTheory_valAt__one_9935cf2928d8
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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology
open GlobalTheory
open GlobalTheory.FibreDeriv
variable {g : ℕ} {X Y : Scheme.{0}}
namespace GlobalTheory.FibreDeriv
theorem _root_.solution {Z : Scheme.{0}} {φ : Y ⟶ Z} {s : Y ⟶ Sp ℂ} {p : Z ⟶ X} {y : Sp ℂ ⟶ X}
    (H : IsPullback φ s p y) {e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)} (hs : ∀ z, e z ≫ s = 𝟙 _)
    (hol : IsHolTo Set.univ (fun z => e z ≫ φ)) {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Y}
    (hv : v ≫ s = spMap (algebraMap ℂ (DualNumber ℂ))) (hd : IsDerivAt0 (fun z => e z ≫ φ) w (v ≫ φ)) :
    IsDerivAt0 e w v := by
  rw [isDerivAt0_iff] at hd
  have h0 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 := by
    refine H.hom_ext (by rw [Category.assoc, hd.1]) ?_
    rw [Category.assoc, hv, hs, ← Spec.map_comp, ← Spec.map_id]
    congr 1
  obtain ⟨S, hS, hyS, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤)
    (x := y (default : PrimeSpectrum ℂ)) trivial
  have hyS' : ⊤ ≤ y ⁻¹ᵁ S := (top_le_preimage_iff_mem y S).2 hyS
  have hey : (e 0 ≫ φ) ≫ p = y := by rw [Category.assoc, H.w, ← Category.assoc, hs, Category.id_comp]
  obtain ⟨U, hU, hxU, hUS⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (U := p ⁻¹ᵁ S)
    (x := (e 0 ≫ φ) (default : PrimeSpectrum ℂ))
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
  have hU₀ : ⊤ ≤ (e 0 ≫ φ) ⁻¹ᵁ U := (top_le_preimage_iff_mem _ _).2 hxU
  have hV₀ : ⊤ ≤ e 0 ⁻¹ᵁ (φ ⁻¹ᵁ U) := (top_le_preimage_comp _ φ U).1 hU₀
  have hVv : ⊤ ≤ v ⁻¹ᵁ (φ ⁻¹ᵁ U) := (top_le_preimage_eps v _ h0 _).2 hV₀
  have hUv : ⊤ ≤ (v ≫ φ) ⁻¹ᵁ U := by rwa [Scheme.Hom.comp_preimage]
  have hN := (hol U 0).1.mem_nhds (x := 0) ⟨trivial, hU₀⟩
  have hev : ∀ᶠ z in 𝓝 0, ⊤ ≤ e z ⁻¹ᵁ (φ ⁻¹ᵁ U) := by
    filter_upwards [hN] with z hz using (top_le_preimage_comp _ φ U).1 hz.2
  have hconst : ∀ (a : Γ(Y, φ ⁻¹ᵁ U)) (c : ℂ), (∀ z, ⊤ ≤ e z ⁻¹ᵁ (φ ⁻¹ᵁ U) → valAt' (e z) _ a = c) →
      evEps v _ hVv a = algebraMap ℂ _ c → DifferentiableAt ℂ (fun z => valAt' (e z) _ a) 0 ∧
      evEps v _ hVv a = jet w (fun z => valAt' (e z) _ a) := fun a c h1 h2 => by
    have h3 : (fun z => valAt' (e z) _ a) =ᶠ[𝓝 0] fun _ => c := hev.mono h1
    exact ⟨(differentiableAt_const c).congr_of_eventuallyEq h3, by rw [jet_congr w h3, jet_const, h2]⟩
  refine isDerivAt0_of_affine h0 hV hVv fun a => ?_
  have ha : a ∈ Subring.closure _ := hgen.ge (Subring.mem_top a)
  induction ha using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · have h3 : (fun z => valAt' (e z) _ ((φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom b)) =ᶠ[𝓝 0]
          fun z => valAt' (e z ≫ φ) U b := hev.mono fun z hz => valAt'_appLE _ _ _ _ _ _ hz
      exact ⟨((hol U b).2.differentiableAt hN).congr_of_eventuallyEq h3,
        by rw [jet_congr w h3, ← hd.2 U hUv b, evEps_appLE]⟩
    · refine hconst _ ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom b) (fun z hz => ?_) ?_
      · rw [valAt'_appLE _ _ _ _ _ _ hz, hs]
        have := valAt'_id_top ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom b)
        simpa using this
      · rw [evEps_appLE v s ⊤ _ _ b hVv le_top]
        have := evEps_spMap b le_top
        rw [← this]
        congr 1
        congr 1
  | zero => exact hconst _ 0 (fun z _ => valAt'_zero _ _) (by simp)
  | one => exact hconst _ 1 (fun z hz => valAt'_one _ hz) (by simp)
  | add x y _ _ hx hy =>
    simp only [valAt'_add]
    exact ⟨hx.1.add hy.1, by rw [jet_add w hx.1 hy.1, map_add, hx.2, hy.2]⟩
  | neg x _ hx =>
    simp only [valAt'_neg]
    exact ⟨hx.1.neg, by rw [jet_neg w, map_neg, hx.2]⟩
  | mul x y _ _ hx hy =>
    simp only [valAt'_mul]
    exact ⟨hx.1.mul hy.1, by rw [jet_mul w hx.1 hy.1, map_mul, hx.2, hy.2]⟩
end GlobalTheory.FibreDeriv
