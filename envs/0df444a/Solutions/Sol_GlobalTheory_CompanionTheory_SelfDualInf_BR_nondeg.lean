-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SelfDualInf.BR_nondeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:39:39.239691+00:00
-- url     : https://prove2.me/submissions/07e8cc6f-df4a-4896-ae3e-36f043417906

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_BijectiveLinearCombinationOfRankAtStalk
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_HasCoordOfFiniteDimensional
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_trace_nondeg_of
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SelfDualInf
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
namespace GlobalTheory.CompanionTheory.SelfDualInf
theorem _root_.solution [Algebra.IsSeparable F E] (L : R →+ ℝ)
    (hL : ∀ t, (∀ r, L (r * t) = 0) → t = 0) (hσ : ∀ x, σ (σ x) = x) {M n : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hdet : J.det ≠ 0) (X : Fin n → Fin M → R ⊗[F] E)
    (h : ∀ Y, L (BR R σ J X Y) = 0) : X = 0 := by
  classical
  funext a
  let v : Fin M → R ⊗[F] E := fun i => sigR R σ (X a i)
  have hv : ∀ j, ∑ i, v i * JR R J i j = 0 := by
    intro j
    refine trace_nondeg_of R L hL _ fun u => ?_
    have e : BR R σ J X (Pi.single a (Pi.single j u)) =
        Algebra.trace R (R ⊗[F] E) ((∑ i, v i * JR R J i j) * u) := by
      unfold BR
      rw [Finset.sum_eq_single a]
      · congr 1
        simp [hR, hform, v, Pi.single_apply, Finset.sum_mul]
      · intro c _ hc
        simp [hR, hform, Pi.single_apply, hc]
      · simp
    rw [← e]
    exact h _
  have hinv : JR (F := F) R J * JR (F := F) R J⁻¹ = 1 := by
    unfold JR
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv J (isUnit_iff_ne_zero.2 hdet),
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hv0 : Matrix.vecMul v (JR R J) = 0 := funext fun j => by
    simpa [Matrix.vecMul, dotProduct] using hv j
  have hz : v = 0 := by
    calc v = Matrix.vecMul v (JR (F := F) R J * JR (F := F) R J⁻¹) := by rw [hinv, Matrix.vecMul_one]
      _ = Matrix.vecMul (Matrix.vecMul v (JR (F := F) R J)) (JR (F := F) R J⁻¹) := (Matrix.vecMul_vecMul _ _ _).symm
      _ = 0 := by rw [hv0, Matrix.zero_vecMul]
  funext i
  have := congrArg (sigR R σ) (congrFun hz i)
  simpa [v, sigR_invol R σ hσ] using this
end GlobalTheory.CompanionTheory.SelfDualInf
