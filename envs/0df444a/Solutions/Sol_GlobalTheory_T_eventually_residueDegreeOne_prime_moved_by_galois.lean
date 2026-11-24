-- Prove2me | solution 1 for GlobalTheory.T.eventually_residueDegreeOne_prime_moved_by_galois
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:06:39.612944+00:00
-- url     : https://prove2.me/submissions/69e2fbe2-13f1-435e-bdf8-e0d992b0fe92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EventuallyResidueDegreeOnePrimeMovedByGalois
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_DegOneIffSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EventuallyResidueDegreeOnePrimeMovedByGaloisStatement
import Theorems.Thm_GlobalTheory_HeckeSplit_eventually_degOne_moved


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E] (c : E ≃ₐ[F] E), c ≠ 1 → ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, DegOne F w → ∃ x : 𝓞 E, x ∈ w.asIdeal ∧ ∀ y : 𝓞 E, (y : E) = c (x : E) → y ∉ w.asIdeal := by
  first | exact @GlobalTheory.HeckeSplit.eventually_degOne_moved | exact GlobalTheory.HeckeSplit.eventually_degOne_moved | (intros; apply GlobalTheory.HeckeSplit.eventually_degOne_moved <;> assumption)
end _root_.GlobalTheory.T
