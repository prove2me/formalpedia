-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SdFin.BR_nondeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:41:07.002025+00:00
-- url     : https://prove2.me/submissions/552429c7-4a02-47e0-b952-a37f3155f658

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
theorem _root_.solution [FiniteDimensional F E] [Algebra.IsSeparable F E] (hσ : ∀ x, σ (σ x) = x)
    (hJ : IsHermND σ J) {n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) (h : ∀ Y, BR R σ J X Y = 0) : X = 0 := by
  classical
  funext a
  have h1 : Matrix.vecMul (fun i => sigR R σ (X a i)) (JR R J) = 0 := by
    funext j
    refine trace_nondeg R _ fun w => ?_
    have h2 := h (Pi.single a (Pi.single j w))
    rw [BR, Finset.sum_eq_single a (fun b _ hb => by
      simp [Pi.single_eq_of_ne hb, hR, hform]) (by simp)] at h2
    simpa [hR, hform, Pi.single_apply, Matrix.vecMul, dotProduct, Finset.sum_mul] using h2
  have hu : IsUnit (JR R J : Matrix (Fin M) (Fin M) (R ⊗[F] E)).det := by
    have : (JR R J : Matrix (Fin M) (Fin M) (R ⊗[F] E)).det = inclR R J.det :=
      ((inclR R).map_det J).symm
    rw [this]
    exact (Ne.isUnit hJ.2).map _
  have h2 := congrArg (fun v => Matrix.vecMul v (JR R J)⁻¹) h1
  simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one,
    Matrix.zero_vecMul] at h2
  funext i
  rw [← sigR_sigR R σ hσ (X a i), congrFun h2 i]
  simp
end GlobalTheory.CompanionTheory.SdFin
