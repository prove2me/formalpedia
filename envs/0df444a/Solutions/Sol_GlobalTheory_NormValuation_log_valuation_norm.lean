-- Prove2me | solution 1 for GlobalTheory.NormValuation.log_valuation_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:19:05.81783+00:00
-- url     : https://prove2.me/submissions/4c3d01b4-27b8-45b4-9abe-fb33f7434d8b

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IntValuationNormEqSumResidueDegreeMul
import Theorems.Thm_GlobalTheory_NormValuation_log_valuation_norm_integer

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 E)) (a : Kˣ) (s : Finset (HeightOneSpectrum (𝓞 K)))
    (hs : ∀ w, w ∈ s ↔ w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal) :
    WithZero.log (v.valuation E (Algebra.norm E (a : K))) =
      ∑ w ∈ s, (w.asIdeal.inertiaDeg (𝓞 E) : ℤ) * WithZero.log (w.valuation K (a : K)) := by
  obtain ⟨b, c, hc, h⟩ := IsFractionRing.div_surjective (A := 𝓞 K) (a : K)
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hb0 : b ≠ 0 := by
    rintro rfl
    apply a.ne_zero
    rw [← h, map_zero, zero_div]
  have hK : ∀ y : 𝓞 K, y ≠ 0 → algebraMap (𝓞 K) K y ≠ 0 := fun y hy =>
    (FaithfulSMul.algebraMap_eq_zero_iff (𝓞 K) K).not.2 hy
  have hN : ∀ y : 𝓞 K, y ≠ 0 → Algebra.norm E (algebraMap (𝓞 K) K y) ≠ 0 := fun y hy =>
    Algebra.norm_ne_zero_iff.2 (hK y hy)
  have hdiv : Algebra.norm E (algebraMap (𝓞 K) K b / algebraMap (𝓞 K) K c) =
      Algebra.norm E (algebraMap (𝓞 K) K b) / Algebra.norm E (algebraMap (𝓞 K) K c) := by
    rw [eq_div_iff (hN c hc0), ← map_mul, div_mul_cancel₀ _ (hK c hc0)]
  rw [← h, hdiv, map_div₀, WithZero.log_div ((Valuation.ne_zero_iff _).2 (hN b hb0))
    ((Valuation.ne_zero_iff _).2 (hN c hc0)), log_valuation_norm_integer v s hs b hb0,
    log_valuation_norm_integer v s hs c hc0, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_div₀, WithZero.log_div ((Valuation.ne_zero_iff _).2 (hK b hb0))
    ((Valuation.ne_zero_iff _).2 (hK c hc0)), mul_sub]
end GlobalTheory.NormValuation
