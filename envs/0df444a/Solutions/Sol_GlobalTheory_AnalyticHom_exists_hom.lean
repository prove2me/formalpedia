-- Prove2me | solution 1 for GlobalTheory.AnalyticHom.exists_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:11.07169+00:00
-- url     : https://prove2.me/submissions/b20a5c7f-3fcf-430b-8ea5-4ffc6eff1627

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_DenseClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsHomOfLinearScalingHermForm
import Theorems.Thm_GlobalTheory_AnalyticHom_val_mul
import Theorems.Thm_GlobalTheory_AnalyticHom_val_add
import Theorems.Thm_GlobalTheory_AnalyticHom_val_resG
import Theorems.Thm_GlobalTheory_AnalyticHom_val_appLE
import Theorems.Thm_GlobalTheory_AnalyticHom_le_preimage_mono
import Theorems.Thm_GlobalTheory_AnalyticHom_le_preimage_nonzeroLocus
import Theorems.Thm_GlobalTheory_AnalyticHom_exists_hom_of_values
import Theorems.Thm_GlobalTheory_AnalyticHom_chart_le
import Theorems.Thm_GlobalTheory_AnalyticHom_exists_sec_pow
import Theorems.Thm_GlobalTheory_AnalyticHom_isThetaFn_comp
import Theorems.Thm_GlobalTheory_AnalyticHom_le_preimage_lbPow
import Theorems.Thm_GlobalTheory_AnalyticHom_exists_quot
import Theorems.Thm_GlobalTheory_CubeValues_le_preimage_inf
import Theorems.Thm_GlobalTheory_SymmetricSemicharacter_exists_chart
import Theorems.Thm_GlobalTheory_SymmetricSemicharacter_valueRules
import Theorems.Thm_GlobalTheory_isReduced_of_smooth_complex


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open GlobalTheory.AnalyticHom
open CubeValues SymmetricSemicharacter ComplexPoints AffinePointValues
variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g g' : ℕ}
  (u : HolUnif A L g) (u' : HolUnif A' L' g')
namespace GlobalTheory.AnalyticHom
theorem _root_.solution [Smooth A.hom] [Smooth A'.hom] [IsSeparated A'.hom] (hL : L.IsLB) (hL' : L'.IsLB)
    (ha : Out.RelAmple A' L')
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    {Hm' : Matrix (Fin g') (Fin g') ℂ} {χ' : u'.Λ → ℂ} (hχ : ∀ l, χ l ^ 2 = 1)
    (hχ' : ∀ l, χ' l ^ 2 = 1)
    (hs : ∀ (k : ℕ) θ, u.IsThetaFn Hm χ k θ → ∃! s, u.IsFnPow k s θ)
    (hθ : ∀ (k : ℕ) s, ∃! θ, u'.IsThetaFn Hm' χ' k θ ∧ u'.IsFnPow k s θ)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (n : ℕ) (hΛ : ∀ l ∈ u.Λ, F l ∈ u'.Λ)
    (hH : ∀ z w, hermForm Hm' (F z) (F w) = (n : ℂ) * hermForm Hm z w) :
    ∃ f : A.left ⟶ A'.left, ∀ z, (u.ex z).left ≫ f = (u'.ex (F z)).left := by
  haveI := isReduced_of_smooth_complex _ A.hom inferInstance
  haveI := isReduced_of_smooth_complex _ A'.hom inferInstance
  obtain ⟨N, -, M, s, hcov, hD⟩ := ha ⊤ (isAffineOpen_top _)
  have hr : Set.range (𝟙 A'.left : A'.left ⟶ A'.left) ⊆ Set.range (A'.hom ⁻¹ᵁ ⊤).ι := by
    intro x _
    rw [Scheme.Opens.range_ι]
    trivial
  obtain ⟨σ, hσ⟩ : ∃ σ : A'.left ⟶ (A'.hom ⁻¹ᵁ ⊤).toScheme, σ ≫ (A'.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  choose s' hs' using fun i => exists_sec_pow L' _ σ hσ N A'.hom (s i)
  choose θ hθ₁ hθ₂ using fun i => (hθ N (s' i)).exists
  choose t ht using fun i j =>
    (hs _ _ (isThetaFn_comp u u' hχ hχ' F n hΛ hH (hθ₁ i) (hθ₁ j))).exists
  choose ch hch using exists_chart u valueRules hL
  choose ch' hch' using exists_chart u' valueRules hL'
  have hU : ∀ z, ⊤ ≤ ((u'.ex z).left ≫ σ) ⁻¹ᵁ (Out.powOver A' L' ⊤ N).U (fun _ => ch' z) := fun z =>
    le_preimage_mono (u'.ex z).left (chart_le L' _ σ hσ N fun _ => ch' z)
      ((le_preimage_lbPow _ L' N fun _ => ch' z).2 (hch' z))
  have hval : ∀ i z, valAt' ((u'.ex z).left ≫ σ) ((Out.powOver A' L' ⊤ N).U fun _ => ch' z)
      ((s i).f fun _ => ch' z) = θ i z * u'.fr (ch' z) z ^ N := fun i z =>
    have k := (le_preimage_lbPow _ L' N fun _ => ch' z).2 (hch' z)
    (hs' i _ _ k).symm.trans (hθ₂ i _ z k)
  have hfr : ∀ z, u'.fr (ch' z) z ^ N ≠ 0 := fun z => pow_ne_zero _ (u'.fr_ne _ _ (hch' z))
  have hmem : ∀ i z, ⊤ ≤ ((u'.ex z).left ≫ σ) ⁻¹ᵁ Out.nonzeroLocus (s i) ↔ θ i z ≠ 0 := fun i z => by
    rw [le_preimage_nonzeroLocus _ (s i) _ (hU z), hval, mul_ne_zero_iff_right (hfr z)]
  have hon : ∀ x : Sp ℂ ⟶ A.left, x ≫ A.hom = 𝟙 _ → ∃ z, (u.ex z).left = x := fun x hx => by
    obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk x hx)
    exact ⟨z, by rw [hz]; rfl⟩
  refine (exists_hom_of_values A.hom (fun z => (u.ex z).left)
    (fun z => (u'.ex (F z)).left ≫ σ) hon ((A'.hom ⁻¹ᵁ ⊤).ι ≫ A'.hom) (fun z => ?_)).elim
    fun G hG => ⟨G ≫ (A'.hom ⁻¹ᵁ ⊤).ι, fun z => by
      rw [← Category.assoc, hG, Category.assoc, hσ, Category.comp_id]⟩
  have hz : ((u'.ex (F z)).left ≫ σ) (default : PrimeSpectrum ℂ) ∈ ⨆ i, Out.nonzeroLocus (s i) := by
    rw [hcov]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  replace hi := (hmem i _).1 (((valueRules _ _).1 _).2 hi)
  obtain ⟨hDi, r, hr, hsurj⟩ := hD i
  have hne : ∀ w, ⊤ ≤ (u.ex w).left ⁻¹ᵁ A.left.basicOpen ((t i i).f fun _ => ch z) →
      θ i (F w) ≠ 0 := fun w hw => by
    have k := ((valueRules _ _).2.2.2.2.1 _ _).1 hw
    rw [ht i i _ w (le_preimage_mono _ (A.left.basicOpen_le _) hw)] at k
    exact left_ne_zero_of_mul (left_ne_zero_of_mul k)
  have hzU := (le_preimage_lbPow _ L (2 * (n * N)) fun _ => ch z).2 (hch z)
  refine ⟨A.left.basicOpen ((t i i).f fun _ => ch z), _, hDi, ?_,
    fun w hw => (hmem i _).2 (hne w hw), fun f => ?_⟩
  · refine ((valueRules _ _).2.2.2.2.1 _ _).2 ?_
    rw [ht i i _ z hzU]
    exact mul_ne_zero (mul_ne_zero hi hi) (pow_ne_zero _ (u.fr_ne _ _ (hch z)))
  obtain ⟨Q, rfl⟩ := hsurj f
  induction Q using MvPolynomial.induction_on with
  | C a =>
    have hc : ∀ w, ((u'.ex w).left ≫ σ) ≫ (A'.hom ∣_ ⊤) = ((u'.ex 0).left ≫ σ) ≫ (A'.hom ∣_ ⊤) := by
      intro w
      rw [← cancel_mono (⊤ : (Sp ℂ).Opens).ι]
      simp only [Category.assoc, morphismRestrict_ι, reassoc_of% hσ, Over.w]
    refine ⟨constFn A.hom _ (valAt' (((u'.ex 0).left ≫ σ) ≫ (A'.hom ∣_ ⊤)) ⊤ a), fun w hw => ?_⟩
    rw [(valueRules _ _).2.2.2.2.2 A.hom (Over.w (u.ex w)) _ _ hw, MvPolynomial.eval₂Hom_C,
      ← hc (F w)]
    exact (val_appLE _ (A'.hom ∣_ ⊤) ⊤ _ _ a ((hmem i _).2 (hne w hw))).symm
  | add Q Q' h h' =>
    obtain ⟨a, ha⟩ := h
    obtain ⟨a', ha'⟩ := h'
    refine ⟨a + a', fun w hw => ?_⟩
    rw [map_add, val_add _ hw, val_add _ ((hmem i _).2 (hne w hw)), ha w hw, ha' w hw]
  | mul_X Q j h =>
    obtain ⟨a, ha⟩ := h
    obtain ⟨b, hb⟩ := exists_quot u (ht i j) (ht i i) fun _ => ch z
    refine ⟨a * b, fun w hw => ?_⟩
    have hw' := (hmem i _).2 (hne w hw)
    rw [map_mul, val_mul _ hw, val_mul _ hw', ha w hw, MvPolynomial.eval₂Hom_X']
    congr 1
    have k := (le_preimage_inf _ _ _).2 ⟨hw', hU (F w)⟩
    have k₁ := congrArg (valAt' ((u'.ex (F w)).left ≫ σ) _) (hr j fun _ => ch' (F w))
    rw [val_mul _ k, val_resG _ _ k, val_resG _ _ k, val_resG _ _ k, hval, hval, ← _root_.mul_assoc] at k₁
    have k₂ := mul_right_cancel₀ (hfr _) k₁
    have k₃ := hb w hw
    refine mul_right_cancel₀ (mul_ne_zero (hne w hw) (hne w hw)) (k₃.trans ?_)
    linear_combination θ i (F w) * k₂
end GlobalTheory.AnalyticHom
