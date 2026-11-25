-- Prove2me | solution 1 for GroundTheory.Global.compl_degreeOnePrimes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:07:59.308325+00:00
-- url     : https://prove2.me/submissions/d1ba0628-e412-4c75-aa24-15a5bd6827a5

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
namespace GroundTheory.Global
theorem _root_.solution : (degreeOnePrimes K L)ᶜ = higherDegreePrimes K L := by
  ext w
  have := Ideal.inertiaDeg_pos w.asIdeal (𝓞 K)
  simp only [degreeOnePrimes, higherDegreePrimes, mem_compl_iff, mem_ofPred_eq]
  omega
end GroundTheory.Global
