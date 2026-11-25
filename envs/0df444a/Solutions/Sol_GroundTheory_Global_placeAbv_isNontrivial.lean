-- Prove2me | solution 1 for GroundTheory.Global.placeAbv_isNontrivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:15:26.616769+00:00
-- url     : https://prove2.me/submissions/03554aaf-e9b6-43bb-8f68-3106906a6f34

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_WeakApprox
import Theorems.Thm_GroundTheory_Global_adicAbv_isNontrivial

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
open IsDedekindDomain NumberField
variable {K : Type*} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K))
namespace GroundTheory.Global
theorem _root_.solution : ∀ i, (placeAbv S T i).IsNontrivial
  | .inl v => adicAbv_isNontrivial v.1
  | .inr w => w.1.isNontrivial
end GroundTheory.Global
