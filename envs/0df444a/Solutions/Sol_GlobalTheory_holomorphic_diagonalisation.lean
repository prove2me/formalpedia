-- Prove2me | solution 1 for GlobalTheory.holomorphic_diagonalisation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:00:05.768134+00:00
-- url     : https://prove2.me/submissions/5badc4a2-63af-4fab-8c32-005060b7a4e1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DifferentiableOnComplexExtend
import Theorems.Thm_GlobalTheory_complexExtend_tmul
import Theorems.Thm_GlobalTheory_exists_eigen_element
import Theorems.Thm_GlobalTheory_complexExtend_diagonal
import Theorems.Thm_GlobalTheory_differentiableOn_complexExtend

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (O : Type) [CommRing O] (g m : ℕ) (B : Set (Fin m → ℂ)) (b₀ : Fin m → ℂ) (F : (Fin m → ℂ) → (O →+* Matrix (Fin g) (Fin g) ℂ)) (ty : Fin g → (O →+* ℂ)), Module.Finite ℤ O → IsReduced (ℂ ⊗[ℤ] O) → IsOpen B → b₀ ∈ B → (∀ a i j, DifferentiableOn ℂ (fun b => F b a i j) B) → (∀ a, F b₀ a = Matrix.diagonal (fun i => ty i a)) → ∃ (B' : Set (Fin m → ℂ)) (h : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ h b₀ = 1 ∧ (∀ i j, DifferentiableOn ℂ (fun b => h b i j) B') ∧ ∀ b ∈ B', IsUnit (h b) ∧ ∀ a, F b a * h b = h b * Matrix.diagonal (fun i => ty i a) := by
  intro O _ g m B b₀ F ty hfin hred hB hb₀ hF hF₀
  choose e he1 he using fun τ => exists_eigen_element O τ
  let h : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ :=
    fun b => Matrix.of fun i j => complexExtend (F b) (e (ty j)) i j
  have hd : ∀ i j, DifferentiableOn ℂ (fun b => h b i j) B := fun i j =>
    differentiableOn_complexExtend F hF _ i j
  have h0 : h b₀ = 1 := by
    ext i j
    simp only [h, Matrix.of_apply, complexExtend_diagonal _ ty hF₀]
    by_cases hij : i = j
    · subst hij; simp [he1]
    · simp [hij]
  have hc : ContinuousOn h B :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hd i j).continuousOn
  have hdet : ContinuousOn (fun b => (h b).det) B :=
    (Continuous.matrix_det continuous_id).comp_continuousOn hc
  refine ⟨B ∩ (fun b => (h b).det) ⁻¹' {0}ᶜ, h,
    hdet.isOpen_inter_preimage hB isOpen_compl_singleton, ⟨hb₀, by simp [h0]⟩,
    Set.inter_subset_left, h0, fun i j => (hd i j).mono Set.inter_subset_left, ?_⟩
  rintro b ⟨-, hb⟩
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hb), fun a => ?_⟩
  ext i j
  have key := congrArg (fun x => complexExtend (F b) x i j) (he (ty j) a)
  simp only [map_mul, map_smul, complexExtend_tmul, one_smul, Matrix.smul_apply,
    smul_eq_mul] at key
  rw [Matrix.mul_diagonal, mul_comm]
  exact key
end GlobalTheory
