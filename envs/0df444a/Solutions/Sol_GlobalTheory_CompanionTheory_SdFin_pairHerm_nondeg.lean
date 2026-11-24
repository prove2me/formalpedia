-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SdFin.pairHerm_nondeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:41:08.302087+00:00
-- url     : https://prove2.me/submissions/103b9dd9-8d8f-4f58-a4a3-8f63ede8fe8f

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_IndicatorInSchrodingerSpanStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_AdelicCharacterLocalNontrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmallDualLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_AdditiveCharConductorExists
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Tjcosets
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_ExistsSdWSdHerm
import Theorems.Thm_GlobalTheory_CompanionTheory_SdFin_sigR_sigR
import Theorems.Thm_GlobalTheory_CompanionTheory_SdFin_trace_nondeg
import Theorems.Thm_GlobalTheory_CompanionTheory_SdFin_trace_sigR
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
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU Topology
open scoped TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SdFin
variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
variable {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
namespace GlobalTheory.CompanionTheory.SdFin
theorem _root_.solution [FiniteDimensional F E] [Algebra.IsSeparable F E] [CharZero F]
    (hσ : ∀ x, σ (σ x) = x) (n : ℕ) (S : HermR R σ n) (h : ∀ T, pairHerm R σ n S T = 0) : S = 0 := by
  classical
  apply Subtype.ext
  ext a b
  refine trace_nondeg R _ fun w => ?_
  have hT : (Matrix.single b a w + Matrix.single a b (sigR R σ w)) ∈ HermR R σ n := by
    intro i j
    simp only [Matrix.add_apply, Matrix.single_apply, map_add, apply_ite (sigR R σ), map_zero,
      sigR_sigR R σ hσ]
    rw [add_comm]
    simp only [and_comm]
  have h1 := h ⟨_, hT⟩
  have h2 : ∑ i, ∑ j, (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j *
      (Matrix.single b a w + Matrix.single a b (sigR R σ w) : Matrix _ _ _) j i =
      S.1 a b * w + sigR R σ (S.1 a b * w) := by
    rw [map_mul, S.2 b a]
    simp [Matrix.single_apply, mul_add, Finset.sum_add_distrib, ite_and]
  simp only [pairHerm] at h1
  rw [h2, map_add, trace_sigR, ← two_mul, ← mul_assoc] at h1
  have h3 : algebraMap F R (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap F R) 2, ← map_mul]; simp
  rwa [h3, one_mul] at h1
end GlobalTheory.CompanionTheory.SdFin
