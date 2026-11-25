-- Prove2me | solution 1 for GlobalTheory.RegSS.etale_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:08:44.320143+00:00
-- url     : https://prove2.me/submissions/70267a2a-3ed0-4c3c-8439-95983a651904

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct
open GlobalTheory GlobalTheory.RegSS
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {σ : E →ₐ[F] E}
open Matrix NumberField
open scoped TensorProduct
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {σ : E →ₐ[F] E}
namespace GlobalTheory.RegSS
namespace _root_.GlobalTheory.RegSS
theorem _root_.solution [CharZero F] (B : Type) [CommRing B]
    [Algebra F B] [Module.Finite F B] [IsReduced B] : Algebra.Etale F B := by
  have : IsArtinianRing B := IsArtinianRing.of_finite F B
  rw [Algebra.Etale.iff_exists_algEquiv_prod]
  letI : ∀ I : MaximalSpectrum B, Field (B ⧸ I.asIdeal) := fun I =>
    Ideal.Quotient.field I.asIdeal
  exact ⟨MaximalSpectrum B, inferInstance, fun I => B ⧸ I.asIdeal, inferInstance, inferInstance,
    (IsArtinianRing.equivPi B).restrictScalars F, fun I => ⟨inferInstance, inferInstance⟩⟩
end _root_.GlobalTheory.RegSS
end GlobalTheory.RegSS
