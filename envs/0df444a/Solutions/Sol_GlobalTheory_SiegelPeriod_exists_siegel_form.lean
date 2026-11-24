-- Prove2me | solution 1 for GlobalTheory.SiegelPeriod.exists_siegel_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:48:04.461204+00:00
-- url     : https://prove2.me/submissions/be0e0354-9172-4ee8-8c7d-2b6899f984ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSiegelForm
import Theorems.Thm_GlobalTheory_SiegelNormalForm_form_conj
import Theorems.Thm_GlobalTheory_SiegelNormalForm_form_pull
import Theorems.Thm_GlobalTheory_SiegelNormalForm_form_single
import Theorems.Thm_GlobalTheory_SiegelNormalForm_isUnit_of_lagrangian
import Theorems.Thm_GlobalTheory_SiegelNormalForm_siegel_of_relations
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.SiegelPeriod
open GlobalTheory.SiegelNormalForm Matrix
namespace GlobalTheory.SiegelPeriod
theorem _root_.solution : ∀ (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), (∀ a b, EF (bas a) (bas b) = omegaStd a b) → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → ∃ h τ : Matrix (Fin g) (Fin g) ℂ, IsUnit h ∧ h⁻¹ = (Matrix.of fun i j => Q (bas (Pi.single (.inr j) 1)) i) ∧ τ = h * (Matrix.of fun i j => Q (bas (Pi.single (.inl j) 1)) i) ∧ τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ (∀ z w, hermForm Hm z w = hermForm (((τ.map Complex.im)⁻¹).map Complex.ofReal) (h.mulVec z) (h.mulVec w)) ∧ ∀ a, h.mulVec (Q (bas a)) = τ.mulVec (fun i => (a (.inl i) : ℂ)) + fun i => (a (.inr i) : ℂ) := by
  intro La _ EF g bas Q Hm hbas ⟨_, _, _, hH, hpos, hE⟩
  unfold hermForm at hpos hE ⊢
  set e : Fin g → Fin g → ℂ := fun i => Q (bas (Pi.single (.inr i) 1)) with he
  set f : Fin g → Fin g → ℂ := fun i => Q (bas (Pi.single (.inl i) 1)) with hf
  have hee : ∀ i j, (e i ⬝ᵥ Hm *ᵥ star (e j)).im = 0 := fun i j => by
    simp only [he]
    rw [hE, hbas]; simp [omegaStd]
  have hff : ∀ i j, (f i ⬝ᵥ Hm *ᵥ star (f j)).im = 0 := fun i j => by
    simp only [hf]
    rw [hE, hbas]; simp [omegaStd]
  have hef : ∀ i j, (e i ⬝ᵥ Hm *ᵥ star (f j)).im = if i = j then -1 else 0 := fun i j => by
    simp only [he, hf]
    rw [hE, hbas]
    by_cases hij : i = j
    · subst hij; simp [omegaStd, Pi.single_apply]
    · simp [omegaStd, Pi.single_apply, hij, Ne.symm hij]
  let P : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun k i => e i k
  let F : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun k i => f i k
  have hP : ∀ i, P *ᵥ Pi.single i 1 = e i := fun i => by
    ext k; simp [P]
  have hF : ∀ i, F *ᵥ Pi.single i 1 = f i := fun i => by
    ext k; simp [F]
  let Y : Matrix (Fin g) (Fin g) ℝ := (Pᵀ * Hm * P.map star).map Complex.re
  have hYe : ∀ i j, (Pᵀ * Hm * P.map star) i j = e i ⬝ᵥ Hm *ᵥ star (e j) := fun i j => by
    rw [← form_single (Pᵀ * Hm * P.map star), ← form_pull, hP, hP]
  have hY : Pᵀ * Hm * P.map star = Y.map (↑) := by
    ext i j
    apply Complex.ext
    · simp [Y]
    · rw [hYe, hee]; simp
  have hPu : IsUnit P := isUnit_of_lagrangian P Hm f hpos Y hY
    (fun i j => by rw [hP, hef])
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hPu
  have hPi : Function.Injective P.mulVec := Matrix.mulVec_injective_iff_isUnit.2 hPu
  have hPP : ∀ z, P *ᵥ (P⁻¹ *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P hPd, Matrix.one_mulVec]
  let τ : Matrix (Fin g) (Fin g) ℂ := P⁻¹ * F
  have hPτ : ∀ z, P *ᵥ (τ *ᵥ z) = F *ᵥ z := fun z => by
    rw [← Matrix.mulVec_mulVec, hPP]
  have hτ : ∀ j, P *ᵥ (τ *ᵥ Pi.single j 1) = f j := fun j => by
    rw [hPτ, hF]
  have hform : ∀ z w, (P *ᵥ z) ⬝ᵥ Hm *ᵥ star (P *ᵥ w) = z ⬝ᵥ Y.map (↑) *ᵥ star w :=
    fun z w => by rw [form_pull, hY]
  have hYs : Yᵀ = Y := by
    ext i j
    have := congrArg Complex.re (form_conj hH (e i) (e j))
    simp only [Complex.star_def, Complex.conj_re] at this
    simp only [Y, Matrix.transpose_apply, Matrix.map_apply, hYe, this]
  have hYp : Y.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (by simpa [Matrix.IsHermitian] using hYs) ?_
    intro a ha
    have hne : P *ᵥ (fun i => (a i : ℂ)) ≠ 0 := by
      intro h0
      have := hPi (h0.trans (Matrix.mulVec_zero P).symm)
      exact ha (funext fun i => by simpa using congrFun this i)
    have := hpos _ hne
    rw [hform] at this
    simpa [Matrix.mulVec, dotProduct] using this
  obtain ⟨hτs, hτp, hYτ⟩ := siegel_of_relations Y hYp τ
    (fun i j => by rw [← hform, hP, hτ, hef]) (fun i j => by rw [← hform, hτ, hτ, hff])
  have hYi : (τ.map Complex.im)⁻¹ = Y := Matrix.inv_eq_left_inv hYτ
  refine ⟨P⁻¹, τ, Matrix.isUnit_nonsing_inv_iff.2 hPu, Matrix.nonsing_inv_nonsing_inv P hPd, rfl,
    hτs, hτp, fun z w => ?_, fun a => hPi ?_⟩
  · rw [hYi, ← hform, hPP, hPP]
  · have h1 : ∀ m : Fin g → ℤ, (fun i => (m i : ℂ)) = ∑ i, m i • (Pi.single i 1 : Fin g → ℂ) := by
      intro m; ext k; simp [Finset.sum_apply, Pi.single_apply]
    have h2 : a = ∑ i, a (.inl i) • Pi.single (.inl i) 1 + ∑ i, a (.inr i) • Pi.single (.inr i) 1 := by
      ext k; rcases k with k | k <;> simp [Finset.sum_apply, Pi.single_apply]
    rw [hPP, h1 (fun i => a (.inl i)), h1 (fun i => a (.inr i))]
    simp only [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, hP, hτ]
    conv_lhs => rw [h2]
    simp only [map_add, map_sum, map_zsmul, he, hf]
end GlobalTheory.SiegelPeriod
