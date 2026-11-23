-- Prove2me | solution 1 for GroundTheory.Global.rationalPrimeUnder_le_absNorm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:53.815658+00:00
-- url     : https://prove2.me/submissions/e05bef10-d74d-46a5-b5e5-12cde513d84e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Theorems.Thm_GroundTheory_Global_absNorm_eq_rationalPrimeUnder_pow

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
namespace GroundTheory.Global
theorem _root_.solution (w : HeightOneSpectrum (𝓞 L)) :
    rationalPrimeUnder w ≤ Ideal.absNorm w.asIdeal := by
  rw [absNorm_eq_rationalPrimeUnder_pow]
  exact Nat.le_self_pow (Ideal.inertiaDeg_pos w.asIdeal ℤ).ne' _
end GroundTheory.Global
