-- Prove2me | solution 1 for GlobalTheory.PeriodCoord.exists_period_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:08:10.961329+00:00
-- url     : https://prove2.me/submissions/a4eedbc0-e597-4733-a9b4-f590b5c95c7d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsPreconnectedBlockUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFinsetOfMemNhds
import Theorems.Thm_GlobalTheory_PeriodCoord_realMap_apply
import Theorems.Thm_GlobalTheory_PeriodCoord_realMap_inj
import Theorems.Thm_GlobalTheory_PeriodCoord_det_ne_zero_of_pos
import Theorems.Thm_GlobalTheory_PeriodCoord_exists_finset_of_mem_nhds
import Theorems.Thm_GlobalTheory_PeriodCoord_ext_period
import Theorems.Thm_GlobalTheory_PeriodCoord_exists_colMat
import Theorems.Thm_GlobalTheory_PeriodCoord_comm_of_realMap
import Theorems.Thm_GlobalTheory_PeriodCoord_symm_and_support
import Theorems.Thm_GlobalTheory_PeriodCoord_conjugate_mem_iff
import Theorems.Thm_GlobalTheory_PeriodCoord_exists_index
import Theorems.Thm_GlobalTheory_RiemannRel_differentiableOn_left_inverse


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodCoord
noncomputable section
variable {g : ℕ}
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {ty : Fin g → (E →+* ℂ)}
namespace GlobalTheory.PeriodCoord
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P₀ : D.La →+ (Fin g → ℂ)), IsTypeFn H D.p D.q ty → IsPeriod D ty P₀ → ∃ (Z : (D.La →+ (Fin g → ℂ)) → (Fin D.dim → ℂ)) (s : Finset D.La) (ε : ℝ), 0 < ε ∧ (∀ (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D.La →+ (Fin g → ℂ))), IsOpen B → IsHolPeriods D ty B P → (∀ b ∈ B, ∀ x ∈ s, ‖P b x - P₀ x‖ < ε) → DifferentiableOn ℂ (fun b => Z (P b)) B) ∧ ∀ P P' : D.La →+ (Fin g → ℂ), IsPeriod D ty P → IsPeriod D ty P' → (∀ x ∈ s, ‖P x - P₀ x‖ < ε) → (∀ x ∈ s, ‖P' x - P₀ x‖ < ε) → Z P = Z P' → ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), (∀ a, P' a = h (P a)) ∧ ∀ (a : 𝓞 E) z, h (fun k => ty k (a : E) * z k) = fun k => ty k (a : E) * h z k := by
  intro E _ _ _ H D g ty P₀ hty hP₀
  obtain ⟨α, β, hαβ⟩ := exists_colMat hP₀
  obtain ⟨e, he⟩ := exists_index hty
  obtain ⟨M₀, -, hpos₀, hM₀⟩ := hP₀.2.2.2.2
  have hA₀ : colMat α P₀ = 1 := by
    refine (realMap_inj (B := colMat β P₀) (B' := 0) (ext_period hP₀ fun x => ?_)).1
    rw [← hαβ P₀ hP₀]
    simp [realMap_apply]
  have hcont : Continuous fun f : D.La → Fin g → ℂ => (colMat α f).det := by
    refine Continuous.matrix_det (continuous_matrix fun i j => ?_)
    simp only [colMat, of_apply]
    fun_prop
  obtain ⟨s, ε, hε, hs⟩ := exists_finset_of_mem_nhds
    ((hcont.continuousAt (x := ⇑P₀)).eventually_ne (show (colMat α P₀).det ≠ 0 by simp [hA₀]))
  refine ⟨fun P k => (((colMat α P)⁻¹ * colMat β P)ᵀ * M₀) (e k).1 (e k).2, s, ε, hε, ?_, ?_⟩
  · intro m B P _ hP hnear
    have hc : ∀ (γ : Fin g → (D.La →₀ ℂ)) i j, DifferentiableOn ℂ (fun b => colMat γ (P b) i j) B :=
      fun γ i j => by
        simp only [colMat, of_apply]
        exact DifferentiableOn.fun_sum fun x _ => (differentiableOn_pi.1 (hP.2 x) i).const_mul _
    have hinv := RiemannRel.differentiableOn_left_inverse (fun b => colMat α (P b)) (fun b => (colMat α (P b))⁻¹)
      (hc α) (fun b hb => nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (hs _ (hnear b hb))))
    refine differentiableOn_pi.2 fun k => ?_
    simp only [mul_apply, transpose_apply]
    exact DifferentiableOn.fun_sum fun l _ =>
      (DifferentiableOn.fun_sum fun n _ => (hinv _ _).mul (hc β _ _)).mul_const _
  · intro P P' hP hP' hn hn' hZ
    have hA : (colMat α P).det ≠ 0 := hs _ hn
    have hA' : (colMat α P').det ≠ 0 := hs _ hn'
    have h1 := hαβ P hP
    have h1' := hαβ P' hP'
    have h2 := symm_and_support hP₀ hP hM₀ h1 hA
    have h2' := symm_and_support hP₀ hP' hM₀ h1' hA'
    beta_reduce at hZ
    clear hs hαβ
    generalize colMat α P = A, colMat β P = B, colMat α P' = A', colMat β P' = B' at *
    have hu := isUnit_iff_ne_zero.2 hA
    have hu' := isUnit_iff_ne_zero.2 hA'
    have h3 : ∀ i j, ty i (H.rt : E) = H.rt0 → ((A⁻¹ * B)ᵀ * M₀) i j = ((A'⁻¹ * B')ᵀ * M₀) i j := by
      intro i j hi
      by_cases hj : ty j = ComplexEmbedding.conjugate (ty i)
      · obtain ⟨k, hk⟩ := he i j hi hj
        simpa only [hk] using congrFun hZ k
      · rw [(h2 i j).2 hj, (h2' i j).2 hj]
    have h4 : (A⁻¹ * B)ᵀ * M₀ = (A'⁻¹ * B')ᵀ * M₀ := by
      ext i j
      by_cases hi : ty i (H.rt : E) = H.rt0
      · exact h3 i j hi
      by_cases hj : ty j = ComplexEmbedding.conjugate (ty i)
      · rw [(h2 i j).1, (h2' i j).1]
        exact h3 j i (by rw [hj, conjugate_mem_iff]; exact hi)
      · rw [(h2 i j).2 hj, (h2' i j).2 hj]
    have h5 : A⁻¹ * B = A'⁻¹ * B' := by
      have hM := isUnit_iff_ne_zero.2 (det_ne_zero_of_pos hpos₀)
      have := congrArg (· * M₀⁻¹) h4
      simp only [mul_nonsing_inv_cancel_right _ _ hM] at this
      exact transpose_injective this
    have hN : IsUnit (A' * A⁻¹).det := by
      rw [det_mul]; exact hu'.mul (isUnit_nonsing_inv_det _ hu)
    have h6 : ∀ x, P' x = (A' * A⁻¹) *ᵥ P x := fun x => by
      rw [h1, h1', realMap_apply, realMap_apply, mulVec_add, mulVec_mulVec, mulVec_mulVec,
        nonsing_inv_mul_cancel_right _ _ hu, Matrix.mul_assoc, h5, mul_nonsing_inv_cancel_left _ _ hu']
    refine ⟨Matrix.toLinearEquiv' _ (invertibleOfIsUnitDet _ hN), h6, fun a z => ?_⟩
    have h7 := (comm_of_realMap hP hP' (A := A' * A⁻¹) (B := 0) (fun x => by simp [realMap_apply, h6]) a).1
    have h8 : ∀ z : Fin g → ℂ, (fun k => ty k (a : E) * z k) = actMat ty a *ᵥ z := fun z => by
      funext k; rw [actMat, mulVec_diagonal]
    rw [h8, h8]
    change (A' * A⁻¹) *ᵥ _ = _ *ᵥ ((A' * A⁻¹) *ᵥ z)
    rw [mulVec_mulVec, mulVec_mulVec, h7]
end GlobalTheory.PeriodCoord
