-- Prove2me | solution 1 for GroundTheory.Global.isBoundedUnder_primeIdealZetaSum_higherDegreePrimes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:34:07.692821+00:00
-- url     : https://prove2.me/submissions/ddcfb854-524d-4845-8810-1dacb768ec2d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Theorems.Thm_GroundTheory_Global_primeIdealZetaSum_higherDegreePrimes_le

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
variable (K L)
namespace GroundTheory.Global
theorem _root_.solution :
    IsBoundedUnder (· ≤ ·) (𝓝[>] 1) fun s => (higherDegreePrimes K L).primeIdealZetaSum s := by
  obtain ⟨C, hC⟩ := primeIdealZetaSum_higherDegreePrimes_le K L
  exact isBoundedUnder_of_eventually_le (a := C)
    (eventually_nhdsWithin_of_forall fun s hs => hC s (le_of_lt hs))
end GroundTheory.Global
