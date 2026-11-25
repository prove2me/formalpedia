-- Prove2me | solution 1 for GlobalTheory.T.norm_div_localEmbedding_close_to_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:22:12.105798+00:00
-- url     : https://prove2.me/submissions/19d06a5b-181d-466b-a12e-e6aaf1ab5265

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormDivLocalEmbeddingCloseToOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormCloseToOneOfCloseAbovePlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormDivLocalEmbeddingCloseToOneStatement
import Theorems.Thm_GlobalTheory_NormCompat_RatioClose_norm_div_close_to_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E'] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E')) (σ : E' →+* w.adicCompletion E), (∀ x : E, σ (algebraMap E E' x) = algebraMap E _ x) → (∀ x : E', Valued.v (σ x) = w'.valuation E' x) → ∀ M : ℕ, ∃ M' : ℕ, ∀ z : E', z ≠ 0 → (∀ w'' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E'), w''.asIdeal.comap (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers E')) = w.asIdeal → w'' ≠ w' → w''.valuation E' (z - 1) ≤ WithZero.exp (-(M' : ℤ))) → Valued.v (algebraMap E (w.adicCompletion E) (Algebra.norm E z) / σ z - 1) ≤ WithZero.exp (-(M : ℤ)) := by
  first | exact @GlobalTheory.NormCompat.RatioClose.norm_div_close_to_one | exact GlobalTheory.NormCompat.RatioClose.norm_div_close_to_one | (intros; apply GlobalTheory.NormCompat.RatioClose.norm_div_close_to_one <;> assumption)
end _root_.GlobalTheory.T
