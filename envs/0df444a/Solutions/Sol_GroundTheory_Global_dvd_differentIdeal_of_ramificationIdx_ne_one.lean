-- Prove2me | solution 1 for GroundTheory.Global.dvd_differentIdeal_of_ramificationIdx_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:21:52.970278+00:00
-- url     : https://prove2.me/submissions/ad6d4e1c-bce4-47f6-b6be-d0c34851496d

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
variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L]
namespace GroundTheory.Global
theorem _root_.solution {w : HeightOneSpectrum (𝓞 L)}
    (h : w.asIdeal.ramificationIdx (𝓞 K) ≠ 1) :
    w.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 L) := by
  have h2 : 2 ≤ w.asIdeal.ramificationIdx (𝓞 K) := by
    have := Ideal.ramificationIdx_pos w.asIdeal (𝓞 K)
    omega
  set v := w.asIdeal.under (𝓞 K)
  have hv0 : v ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot w.ne_bot
  have : v.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hv0
  have hmap : v.map (algebraMap (𝓞 K) (𝓞 L)) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective
      (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))).not.mpr hv0
  have he := Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity v w.asIdeal hmap
  have hdvd : w.asIdeal ^ w.asIdeal.ramificationIdx (𝓞 K) ∣
      v.map (algebraMap (𝓞 K) (𝓞 L)) := by
    rw [he]
    exact pow_multiplicity_dvd _ _
  have := pow_sub_one_dvd_differentIdeal_aux (𝓞 K) K L w.asIdeal (by omega) hv0 hdvd
  exact (dvd_pow_self _ (by omega)).trans this
end GroundTheory.Global
