-- Prove2me | solution 1 for GroundTheory.Global.placeAbv_pairwise_not_isEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:16:19.226639+00:00
-- url     : https://prove2.me/submissions/ac58919d-aa25-4f9d-b2c2-d940682dc327

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_WeakApprox
import Theorems.Thm_GroundTheory_Global_not_isEquiv_adicAbv
import Theorems.Thm_GroundTheory_Global_not_isEquiv_adicAbv_infinitePlace

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
theorem _root_.solution :
    Pairwise fun i j ↦ ¬ (placeAbv S T i).IsEquiv (placeAbv S T j) := by
  rintro (⟨v, hv⟩ | ⟨w, hw⟩) (⟨v', hv'⟩ | ⟨w', hw'⟩) hij he
  · exact not_isEquiv_adicAbv (fun h ↦ hij (by subst h; rfl)) he
  · exact not_isEquiv_adicAbv_infinitePlace v w' he
  · exact not_isEquiv_adicAbv_infinitePlace v' w he.symm
  · exact hij (by
      have : w = w' := InfinitePlace.eq_iff_isEquiv.2 he
      subst this; rfl)
end GroundTheory.Global
