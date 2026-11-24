-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SelfDualInf.BR_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:20:59.372067+00:00
-- url     : https://prove2.me/submissions/da84983f-837b-4baa-9675-501c878a3c0d

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_BijectiveLinearCombinationOfRankAtStalk
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_HasCoordOfFiniteDimensional
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_trace_sigR
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_sigR_hR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SelfDualInf
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
namespace GlobalTheory.CompanionTheory.SelfDualInf
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (X Y : Fin n → Fin M → R ⊗[F] E) :
    BR R σ J X Y = BR R σ J Y X :=
  Finset.sum_congr rfl fun a _ => by rw [← sigR_hR R σ hσ hJ (Y a) (X a), trace_sigR R σ hσ]
end GlobalTheory.CompanionTheory.SelfDualInf
