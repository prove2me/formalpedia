-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SdFin.hR_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:39:49.577855+00:00
-- url     : https://prove2.me/submissions/83a874d6-cef7-4276-a727-ba081bbf1e15

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
theorem _root_.solution [FiniteDimensional F E] (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J)
    (x y : Fin M → R ⊗[F] E) :
    Algebra.trace R (R ⊗[F] E) (hR R σ J x y) = Algebra.trace R (R ⊗[F] E) (hR R σ J y x) := by
  rw [← trace_sigR R σ]
  congr 1
  simp only [hR, hform, map_sum, map_mul, sigR_sigR R σ hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : sigR R σ (JR R J j i) = JR R J i j := by
    show (1 : R) ⊗ₜ[F] σ (J j i) = (1 : R) ⊗ₜ[F] J i j
    rw [hJ.1]
  rw [this]; ring
end GlobalTheory.CompanionTheory.SdFin
