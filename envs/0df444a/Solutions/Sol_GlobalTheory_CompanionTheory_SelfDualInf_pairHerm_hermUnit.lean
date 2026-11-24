-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SelfDualInf.pairHerm_hermUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:20:39.668801+00:00
-- url     : https://prove2.me/submissions/c7de3167-dc9e-49ec-9144-82ae79b4b37c

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_BijectiveLinearCombinationOfRankAtStalk
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_HasCoordOfFiniteDimensional
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_trace_sigR
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
theorem _root_.solution [CharZero F] (hσ : ∀ x, σ (σ x) = x) (n : ℕ) (S : HermR R σ n)
    (a b : Fin n) (u : R ⊗[F] E) :
    pairHerm R σ n S (hermUnit R σ hσ n a b u) = Algebra.trace R (R ⊗[F] E)
      ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) a b * u) := by
  set w := (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) a b * u with hw
  have hs : sigR R σ w = (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) b a * sigR R σ u := by
    rw [hw, map_mul, S.2 b a]
  have hsum : (∑ c, ∑ d, (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) c d *
      (hermUnit R σ hσ n a b u : Matrix (Fin n) (Fin n) (R ⊗[F] E)) d c) = w + sigR R σ w := by
    rw [hs, hw]
    simp [hermUnit, mul_add, Finset.sum_add_distrib, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']
  have h2 : algebraMap F R (1 / 2) * 2 = 1 := by
    rw [show (2 : R) = algebraMap F R 2 from (map_ofNat _ 2).symm, ← map_mul,
      one_div_mul_cancel (two_ne_zero), map_one]
  unfold pairHerm
  rw [hsum, map_add, trace_sigR R σ hσ, ← two_mul, ← mul_assoc, h2, one_mul]
end GlobalTheory.CompanionTheory.SelfDualInf
