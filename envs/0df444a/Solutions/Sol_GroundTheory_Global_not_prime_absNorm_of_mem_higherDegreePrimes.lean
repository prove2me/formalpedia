-- Prove2me | solution 1 for GroundTheory.Global.not_prime_absNorm_of_mem_higherDegreePrimes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:09:55.992295+00:00
-- url     : https://prove2.me/submissions/e66986fd-ec3f-4eea-b287-147c1cc36784

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
namespace GroundTheory.Global
theorem _root_.solution {w : HeightOneSpectrum (𝓞 L)}
    (hw : w ∈ higherDegreePrimes K L) : ¬ (Ideal.absNorm w.asIdeal).Prime := by
  rw [← Ideal.absNorm_pow_inertiaDeg (w.asIdeal.under (𝓞 K)) w.asIdeal]
  have : 2 ≤ w.asIdeal.inertiaDeg (𝓞 K) := hw
  exact Nat.Prime.not_prime_pow' (by omega)
end GroundTheory.Global
