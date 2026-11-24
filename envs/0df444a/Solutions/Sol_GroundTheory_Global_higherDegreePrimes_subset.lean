-- Prove2me | solution 1 for GroundTheory.Global.higherDegreePrimes_subset
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T03:55:59.129861+00:00
-- url     : https://prove2.me/submissions/0183213e-eaee-4dd8-a501-611372c7a5e6

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
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
open NumberField IsDedekindDomain Filter Topology Set
noncomputable section
variable {K L : Type*} [Field L] [NumberField L]
variable (K L) [Field K] [NumberField K] [Algebra K L]
variable {K L}


theorem solution :
    higherDegreePrimes K L ⊆ {w : HeightOneSpectrum (𝓞 L) | ¬ (Ideal.absNorm w.asIdeal).Prime} := by
  intro w hw; change 2 ≤ w.asIdeal.inertiaDeg (𝓞 K) at hw
  change ¬ (Ideal.absNorm w.asIdeal).Prime
  rw [← Ideal.absNorm_pow_inertiaDeg (w.asIdeal.under (𝓞 K)) w.asIdeal]
  exact Nat.Prime.not_prime_pow hw
