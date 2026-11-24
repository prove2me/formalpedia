-- Prove2me | solution 1 for GlobalTheory.LocalQuad.isotropic_four
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:45:11.419071+00:00
-- url     : https://prove2.me/submissions/b27466db-57a7-4445-996e-6ce6dad4085c

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsQuaternaryOfCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitValuedTernaryLtOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroFiveOfValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsForallAbvSubLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRingHomAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroCoordNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometricCm
import Theorems.Thm_GlobalTheory_LocalQuad_exists_norm_over_extension
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_LocalQuad_exists_quaternary_of_coordinates
import Theorems.Thm_GlobalTheory_LocalQuad_isotropic_four_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk
attribute [local simp] GlobalTheory.Inertia.negIndex_neg
attribute [local simp] GlobalTheory.Inertia.posIndex_neg



set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad
namespace GlobalTheory.LocalQuad
theorem _root_.solution (H : GlobalTheory.Published.HasseNormSt) (F : Type) [Field F] [NumberField F]
    (a : Fin 4 → F) (ha : ∀ i, a i ≠ 0)
    (hr : ∀ σ : F →+* ℝ, ∃ x : Fin 4 → ℝ, x ≠ 0 ∧ ∑ i, σ (a i) * x i ^ 2 = 0)
    (hf : ∀ v : HeightOneSpectrum (𝓞 F), ∃ x : Fin 4 → v.adicCompletion F, x ≠ 0 ∧
      ∑ i, algebraMap F (v.adicCompletion F) (a i) * x i ^ 2 = 0) :
    ∃ x : Fin 4 → F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  rw [isotropic_four_iff (ha 0)]
  have hα : -(a 0 * a 1) ≠ 0 := by simp [ha]
  have hβ : -(a 0 * a 2) ≠ 0 := by simp [ha]
  have hγ : a 0 * a 3 ≠ 0 := by simp [ha]
  have hr' := fun σ : F →+* ℝ =>
    (isotropic_four_iff (a := fun i => σ (a i)) (by simpa using ha 0)).1 (hr σ)
  have hf' := fun v : HeightOneSpectrum (𝓞 F) =>
    (isotropic_four_iff (a := fun i => algebraMap F (v.adicCompletion F) (a i))
      (by simpa using ha 0)).1 (hf v)
  simp only [← map_mul, ← map_neg] at hr' hf'
  generalize -(a 0 * a 1) = α at *
  generalize -(a 0 * a 2) = β at *
  generalize a 0 * a 3 = γ at *
  by_cases hs : IsSquare (α * β * γ)
  · obtain ⟨s, hs⟩ := hs
    obtain ⟨X, Y, h⟩ := exists_norm_over_extension H F F hα hβ hγ (s := s)
      (by rw [hs, sq]; rfl) hr' hf'
    refine ⟨X, Y, 1, 0, by simp, ?_⟩
    change β = X ^ 2 - α * Y ^ 2 at h
    linear_combination -h
  · have : Fact (∀ r : F, r ^ 2 ≠ α * β * γ + 0 * r) :=
      ⟨fun r h => hs ⟨r, by linear_combination -h⟩⟩
    let L := QuadraticAlgebra F (α * β * γ) 0
    have : NumberField L := NumberField.of_module_finite F L
    obtain ⟨X, Y, h⟩ := exists_norm_over_extension H F L hα hβ hγ (s := ⟨0, 1⟩)
      (by ext <;> simp [sq, L]) hr' hf'
    have h1 := congrArg QuadraticAlgebra.re h
    have h2 := congrArg QuadraticAlgebra.im h
    simp [sq, L] at h1 h2
    refine exists_quaternary_of_coordinates hα hβ (X₀ := X.re) (X₁ := X.im) (Y₀ := Y.re)
      (Y₁ := Y.im) (by linear_combination h1) ?_
    linear_combination (-1 / 2 : F) * h2
end GlobalTheory.LocalQuad
