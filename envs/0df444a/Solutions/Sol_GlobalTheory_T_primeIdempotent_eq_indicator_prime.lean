-- Prove2me | solution 1 for GlobalTheory.T.primeIdempotent_eq_indicator_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:10:50.52484+00:00
-- url     : https://prove2.me/submissions/d73c0eae-8a50-46e8-87aa-fce8c92ad531

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PrimeIdempotentEqIndicatorPrime
import Definitions.Def_Formalism_UnipotentAdelicQuotients_ThmBInHecke
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PrimeIdempotentEqIndicatorPrimeStatement
import Theorems.Thm_GlobalTheory_isPrimeIdem_eq_indicator


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ Φ : AE F E ≃+* (mixedSpace E × FiniteAdeleRing (𝓞 E) E), (∀ x : E, Φ (incA F E x) = (mixedEmbedding E x, algebraMap E _ x)) → (∀ y, finPart F E y ∈ intAE F E ↔ ∀ P, Valued.v ((Φ y).2 P) ≤ 1) → (∀ v ε, IsPlaceIdem F v ε → (Φ (algebraMap (AF F) (AE F E) ε)).1 = 0 ∧ ∀ P : HeightOneSpectrum (𝓞 E), (Φ (algebraMap (AF F) (AE F E) ε)).2 P = if P.under (𝓞 F) = v then 1 else 0) → ∀ P e f, IsPrimeIdem σ P e f → ((Φ e).1 = 0 ∧ (Φ e).2 P = 1 ∧ ∀ Q, Q ≠ P → (Φ e).2 Q = 0) := by
  first | exact @GlobalTheory.isPrimeIdem_eq_indicator | exact GlobalTheory.isPrimeIdem_eq_indicator | (intros; apply GlobalTheory.isPrimeIdem_eq_indicator <;> assumption)
end _root_.GlobalTheory.T
