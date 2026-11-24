-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SelfDualReal.exists_selfDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:56:18.444613+00:00
-- url     : https://prove2.me/submissions/98b542a1-b53b-417e-bb35-f4f80f7dd513

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_BijectiveLinearCombinationOfRankAtStalk
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualReal_selfDual_transport
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualReal_selfDual_euclid

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
open scoped FourierTransform RealInnerProductSpace
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SelfDualReal
namespace GlobalTheory.CompanionTheory.SelfDualReal
theorem _root_.solution : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
    [BorelSpace V] (N : ℕ) (e : V ≃+ (Fin N → ℝ)) (A : Matrix (Fin N) (Fin N) ℝ) (χ : V → V → ℂ),
    Continuous e → Continuous e.symm → A.IsSymm → A.det ≠ 0 →
    (∀ x y, χ x y = Complex.exp (((dotProduct (e x) (A.mulVec (e y)) : ℝ) : ℂ) * Complex.I)) →
    ∃ μ : Measure V, SelfDual μ χ := by
  intro V _ _ _ _ N e A χ he he' hA hd hχ
  let p : EuclideanSpace ℝ (Fin N) ≃L[ℝ] (Fin N → ℝ) := EuclideanSpace.equiv (Fin N) ℝ
  let B : Matrix (Fin N) (Fin N) ℝ := (-2 * Real.pi)⁻¹ • A
  have hpi : (-2 * Real.pi) ≠ 0 := by have := Real.pi_pos; intro h; linarith
  have hB : B.det ≠ 0 := by
    simp only [B, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hpi)) hd
  have hBs : B.IsSymm := hA.smul _
  let S : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N) :=
    (p.symm.toLinearEquiv : (Fin N → ℝ) →ₗ[ℝ] _) ∘ₗ Matrix.toLin' B ∘ₗ
      (p.symm.toLinearEquiv.symm : _ →ₗ[ℝ] (Fin N → ℝ))
  have hin : ∀ x y : EuclideanSpace ℝ (Fin N), ⟪x, y⟫ = dotProduct (p x) (p y) := by
    intro x y
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    rfl
  have hSa : ∀ y, p (S y) = B.mulVec (p y) := fun y => rfl
  have hS : ∀ x y, ⟪S x, y⟫ = ⟪x, S y⟫ := by
    intro x y
    rw [hin, hin, hSa, hSa, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hBs.eq]
  have hdS : LinearMap.det S ≠ 0 := by
    simp only [S]
    rw [LinearMap.det_conj, LinearMap.det_toLin']
    exact hB
  obtain ⟨ν, hν⟩ := selfDual_euclid S hS hdS
  let f : V ≃+ EuclideanSpace ℝ (Fin N) := e.trans p.symm.toLinearEquiv.toAddEquiv
  have := selfDual_transport f (p.symm.continuous.comp he) (he'.comp p.continuous) ν _ hν
  refine ⟨ν.map f.symm, ?_⟩
  convert this using 3 with x y
  have hpf : ∀ x, p (f x) = e x := fun x => rfl
  rw [hχ, hin, hSa, hpf, hpf]
  simp only [B, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [mul_inv_cancel_left₀ hpi]
end GlobalTheory.CompanionTheory.SelfDualReal
