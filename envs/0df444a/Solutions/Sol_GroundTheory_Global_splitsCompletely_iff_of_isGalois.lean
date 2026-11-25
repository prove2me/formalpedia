-- Prove2me | solution 1 for GroundTheory.Global.splitsCompletely_iff_of_isGalois
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:49:19.845159+00:00
-- url     : https://prove2.me/submissions/9c5c3598-af3c-4cc7-a577-8e7687733f24

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOneDensity

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
open NumberField IsDedekindDomain Filter Topology Set Ideal
noncomputable section
variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
namespace GroundTheory.Global
theorem _root_.solution [IsGalois K L] (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [hw : w.asIdeal.LiesOver v.asIdeal] :
    SplitsCompletely L v ↔
      w.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ w.asIdeal.inertiaDeg (𝓞 K) = 1 := by
  have : IsGaloisGroup Gal(L/K) (𝓞 K) (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ K L
  constructor
  · intro h
    exact h w hw
  · rintro ⟨he, hf⟩ w' hw'
    rw [Ideal.ramificationIdx_eq_of_isGaloisGroup v.asIdeal w'.asIdeal w.asIdeal Gal(L/K),
      Ideal.inertiaDeg_eq_of_isGaloisGroup v.asIdeal w'.asIdeal w.asIdeal Gal(L/K)]
    exact ⟨he, hf⟩
end GroundTheory.Global
