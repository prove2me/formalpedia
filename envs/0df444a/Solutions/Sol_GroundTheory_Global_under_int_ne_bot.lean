-- Prove2me | solution 1 for GroundTheory.Global.under_int_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:36.286333+00:00
-- url     : https://prove2.me/submissions/af35c925-4791-40f0-a788-a0ddf5a5f764

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
omit [NumberField L]
namespace GroundTheory.Global
theorem _root_.solution (w : HeightOneSpectrum (𝓞 L)) : w.asIdeal.under ℤ ≠ ⊥ :=
  mt Ideal.eq_bot_of_comap_eq_bot w.ne_bot
end GroundTheory.Global
