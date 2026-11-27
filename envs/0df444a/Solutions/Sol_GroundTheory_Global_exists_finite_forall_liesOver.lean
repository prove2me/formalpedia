-- Prove2me | solution 1 for GroundTheory.Global.exists_finite_forall_liesOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:46:25.666573+00:00
-- url     : https://prove2.me/submissions/7b30b08e-5cca-4dae-9631-05d616f722fc

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_GoodReductionAlmostAll
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_FunctionFieldIntegral
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOneDensity
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_BadPrimesFinite
import Theorems.Thm_GroundTheory_Global_under_eq_of_liesOver

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain IsLocalRing WeierstrassCurve.Affine
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
namespace GroundTheory.Global
theorem _root_.solution {p : HeightOneSpectrum (𝓞 L) → Prop}
    (hp : ∀ᶠ w in Filter.cofinite, p w) :
    ∃ T : Set (HeightOneSpectrum (𝓞 K)), T.Finite ∧ ∀ v ∉ T, ∀ w : HeightOneSpectrum (𝓞 L),
      w.asIdeal.LiesOver v.asIdeal → p w := by
  refine ⟨(fun w => w.under (𝓞 K)) '' {w | ¬ p w}, (Filter.eventually_cofinite.mp hp).image _,
    fun v hv w hw => by_contra fun hn => hv ⟨w, hn, under_eq_of_liesOver hw⟩⟩
end GroundTheory.Global
