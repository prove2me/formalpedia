-- Prove2me | solution 1 for GlobalTheory.SW.gauss_form_dictionary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:57:18.206751+00:00
-- url     : https://prove2.me/submissions/9d797898-df5c-4ab0-ab6e-4e9fcfcaef95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_GaussianQuadFormRationalCoordsHermitian
import Theorems.Thm_GlobalTheory_SW_GaussDict_exists_coords
import Theorems.Thm_GlobalTheory_SW_GaussDict_im_tauOf
import Theorems.Thm_GlobalTheory_SW_GaussDict_tauOf_mulVec
import Theorems.Thm_GlobalTheory_SW_GaussDict_zetaOf_dot
import Theorems.Thm_GlobalTheory_SW_Dict_zetaOf_surj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Complex NumberField GlobalTheory.SW
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
namespace GlobalTheory.SW.GaussDict
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
end GlobalTheory.SW.GaussDict
private theorem exists_tauOf_mulVec_eq_zetaOf {E : Type} [Field E] [NumberField E] {Ψ : Finset (E →+* ℂ)}
    (hΨ : IsType Ψ) {m N : ℕ} (Y : CM Ψ N N) (hY : ∀ τ, IsUnit (Y τ)) (z z' : CM Ψ m N)
    (k : Fin m) :
    ∃ u : QI E N → ℂ, tauOf Ψ Y *ᵥ u = zetaOf Ψ z z' k ∧
      zetaOf Ψ z z' k ⬝ᵥ u = 2 * ∑ τ : Ψ, z' τ k ⬝ᵥ (Y τ)⁻¹ *ᵥ z τ k := by
  obtain ⟨u, hu⟩ := GlobalTheory.SW.GaussDict.exists_coords hΨ (fun τ => ((Y τ)ᵀ)⁻¹ *ᵥ z' τ k)
    (fun τ => (Y τ)⁻¹ *ᵥ z τ k)
  have h1 : ∀ τ : Ψ, (fun c => ∑ j, τ.1 (Module.finBasis ℚ E j) * u (c, j)) =
      ((Y τ)ᵀ)⁻¹ *ᵥ z' τ k := fun τ => funext fun a => (hu τ a).1
  have h2 : ∀ τ : Ψ, (fun c => ∑ j, conj (τ.1 (Module.finBasis ℚ E j)) * u (c, j)) =
      (Y τ)⁻¹ *ᵥ z τ k := fun τ => funext fun a => (hu τ a).2
  have hY1 : ∀ τ, Y τ * (Y τ)⁻¹ = 1 := fun τ =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (hY τ))
  have hY2 : ∀ τ, (Y τ)ᵀ * ((Y τ)ᵀ)⁻¹ = 1 := fun τ => Matrix.mul_nonsing_inv _ (by
    rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det _).mp (hY τ))
  refine ⟨u, funext fun p => ?_, ?_⟩
  · rw [GlobalTheory.SW.GaussDict.tauOf_mulVec]
    simp only [h1, h2, Matrix.mulVec_mulVec, hY1, hY2, Matrix.one_mulVec, zetaOf]
    exact Finset.sum_congr rfl fun τ _ => by ring
  · rw [GlobalTheory.SW.GaussDict.zetaOf_dot]
    simp only [h1, h2]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← Matrix.transpose_nonsing_inv, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
      dotProduct_comm]
    ring
end

set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
namespace GlobalTheory.SW
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), ∀ Z ∈ Hn Ψ N, ∀ (z z' : CM Ψ n N) (k : Fin n), zetaOf Ψ z z' k ⬝ᵥ ((tauOf Ψ Z).map fun t => (t.im : ℂ))⁻¹ *ᵥ zetaOf Ψ z z' k = 2 * ∑ τ : Ψ, z' τ k ⬝ᵥ (imH (Z τ))⁻¹ *ᵥ z τ k := by
  intro E _ _ _ Ψ hΨ n N Z hZ z z' k
  rw [GlobalTheory.SW.GaussDict.im_tauOf]
  have hY : ∀ τ : Ψ, IsUnit (imH (Z τ)) := fun τ =>
    ((show ∀ τ : Ψ, (imH (Z τ)).PosDef from hZ) τ).isUnit
  have hsurj : Function.Surjective (tauOf Ψ fun τ => imH (Z τ)).mulVec := fun ξ => by
    obtain ⟨w, w', hw⟩ := GlobalTheory.SW.Dict.zetaOf_surj (n := 1) hΨ (fun _ => ξ)
    obtain ⟨u, hu, -⟩ := exists_tauOf_mulVec_eq_zetaOf hΨ (fun τ => imH (Z τ)) hY w w' 0
    exact ⟨u, by rw [hu, hw]⟩
  have hU := Matrix.mulVec_surjective_iff_isUnit.mp hsurj
  obtain ⟨u, hu, hdot⟩ := exists_tauOf_mulVec_eq_zetaOf hΨ (fun τ => imH (Z τ)) hY z z' k
  have hinv : (tauOf Ψ fun τ => imH (Z τ))⁻¹ *ᵥ zetaOf Ψ z z' k = u := by
    rw [← hu, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hU), Matrix.one_mulVec]
  rw [hinv, hdot]
end GlobalTheory.SW
