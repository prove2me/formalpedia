-- Prove2me | solution 1 for GlobalTheory.FullFlag.ofBasis_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:50:15.549878+00:00
-- url     : https://prove2.me/submissions/2e22e736-9acd-4ca3-9562-ead13767f0d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsAdaptedOfIsLocalRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TensorProduct
open GlobalTheory
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
open GlobalTheory.FullFlag
variable {n : ℕ}
namespace GlobalTheory.FullFlag
theorem _root_.solution (b : Basis (Fin n) R M) (S : Type*) [CommRing S] [Algebra R S] :
    ofBasis (b.baseChange S) = (ofBasis b).baseChange S := by
  ext1
  funext k
  simp only [ofBasis_sub, baseChange_sub, Basis.flag, Submodule.baseChange_span, Set.image_image]
  simp
end GlobalTheory.FullFlag
