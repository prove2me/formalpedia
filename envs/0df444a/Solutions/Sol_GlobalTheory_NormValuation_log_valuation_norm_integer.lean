-- Prove2me | solution 1 for GlobalTheory.NormValuation.log_valuation_norm_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:03:16.165475+00:00
-- url     : https://prove2.me/submissions/94ad12d5-bae1-4669-9319-bba3517a32ae

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IntValuationNormEqSumResidueDegreeMul
import Theorems.Thm_GlobalTheory_NormValuation_log_valuation_of_integer
import Theorems.Thm_GlobalTheory_NormValuation_exponent_relNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
noncomputable section
open GlobalTheory GlobalTheory.NormValuation
variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
namespace GlobalTheory.NormValuation
theorem _root_.solution (v : HeightOneSpectrum (𝓞 E)) (s : Finset (HeightOneSpectrum (𝓞 K)))
    (hs : ∀ w, w ∈ s ↔ w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal)
    (x : 𝓞 K) (hx : x ≠ 0) :
    WithZero.log (v.valuation E (Algebra.norm E (algebraMap (𝓞 K) K x))) =
      ∑ w ∈ s, (w.asIdeal.inertiaDeg (𝓞 E) : ℤ) * WithZero.log (w.valuation K (algebraMap (𝓞 K) K x)) := by
  have h1 : algebraMap (𝓞 E) E (Algebra.intNorm (𝓞 E) (𝓞 K) x) = Algebra.norm E (algebraMap (𝓞 K) K x) :=
    Algebra.algebraMap_intNorm (A := 𝓞 E) (K := E) (L := K) (B := 𝓞 K) x
  have h2 : Algebra.intNorm (𝓞 E) (𝓞 K) x ≠ 0 := by
    intro h0
    have : Algebra.norm E (algebraMap (𝓞 K) K x) = 0 := by rw [← h1, h0, map_zero]
    rw [Algebra.norm_eq_zero_iff] at this
    exact hx ((FaithfulSMul.algebraMap_eq_zero_iff (𝓞 K) K).1 this)
  have hI : Ideal.span {x} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  rw [← h1, log_valuation_of_integer v E _ h2, ← Ideal.relNorm_singleton,
    exponent_relNorm v s hs _ hI, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [log_valuation_of_integer w K x hx, mul_neg]
end GlobalTheory.NormValuation
