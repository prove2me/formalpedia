-- Prove2me | solution 1 for GlobalTheory.PlaceOver.comap_eq_of_continuous_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:08:42.949333+00:00
-- url     : https://prove2.me/submissions/8728d75e-f9cb-4f0a-8bbf-893891548f59

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComapEqOfContinuousAdicCompletionIso
import Theorems.Thm_GlobalTheory_PlaceOver_valuation_lt_one_of_continuous
import Theorems.Thm_GlobalTheory_PlaceOver_valued_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open GlobalTheory GlobalTheory.PlaceOver
namespace GlobalTheory.PlaceOver
theorem _root_.solution : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (w' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E'))
    (i : w.adicCompletion E ≃+* w'.adicCompletion E'), Continuous i →
    (∀ x : E, i (algebraMap E _ x) = algebraMap E' _ (algebraMap E E' x)) →
    w'.asIdeal.comap (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers E')) = w.asIdeal := by
  intro E E' _ _ _ _ _ w w' i hi hc
  have hle : w.asIdeal ≤ w'.asIdeal.comap (algebraMap (𝓞 E) (𝓞 E')) := by
    intro e he
    rw [Ideal.mem_comap, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E')]
    have h1 : Valued.v (algebraMap E (w.adicCompletion E) (e : E)) < 1 := by
      rw [valued_algebraMap]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w e).2 he
    have h2 := valuation_lt_one_of_continuous (i : w.adicCompletion E →+* w'.adicCompletion E') hi h1
    have h3 : (i : w.adicCompletion E →+* w'.adicCompletion E') (algebraMap E (w.adicCompletion E) (e : E)) =
        algebraMap E' (w'.adicCompletion E') (algebraMap E E' (e : E)) := hc _
    rw [h3, valued_algebraMap] at h2
    exact h2
  exact (w.isMaximal.eq_of_le (Ideal.comap_ne_top _ w'.isPrime.ne_top) hle).symm
end GlobalTheory.PlaceOver
