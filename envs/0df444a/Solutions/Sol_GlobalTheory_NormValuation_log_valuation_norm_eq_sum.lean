-- Prove2me | solution 1 for GlobalTheory.NormValuation.log_valuation_norm_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:34:08.273026+00:00
-- url     : https://prove2.me/submissions/8a330c05-d3b4-47ab-bc6d-79eb544075a2

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IntValuationNormEqSumResidueDegreeMul
import Theorems.Thm_GlobalTheory_NormValuation_log_valuation_norm

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
namespace GlobalTheory.NormValuation
theorem _root_.solution : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (v : HeightOneSpectrum (𝓞 E)) (a : Kˣ) (s : Finset (HeightOneSpectrum (𝓞 K))), (∀ w, w ∈ s ↔ w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal) → WithZero.log (v.valuation E (Algebra.norm E (a : K))) = ∑ w ∈ s, (w.asIdeal.inertiaDeg (𝓞 E) : ℤ) * WithZero.log (w.valuation K (a : K)) :=
  fun _ _ _ _ _ _ _ v a s hs => GlobalTheory.NormValuation.log_valuation_norm v a s hs
end GlobalTheory.NormValuation
