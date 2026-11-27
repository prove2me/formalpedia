-- Prove2me | solution 1 for KStar.TotallyRealRoots.nuGal_eq_nu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:49:33.757652+00:00
-- url     : https://prove2.me/submissions/024b8dea-0f88-40e7-9d14-d8c95567829f

import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_TotallyRealRoots_LeNuIffPowMemPrinc
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_TotallyRealRoots_GalDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open KStar KStar.TotallyRealRoots
namespace KStar.TotallyRealRoots
theorem _root_.solution (l : ℕ) [Fact l.Prime] (E : Type*) [Field E] (tr : ℕ) :
    nuGal l E tr = nu l (galImage l E) tr := by
  unfold nuGal nu nuStar galImage
  rw [iInf, Set.image_image]
  congr 1
  ext x
  simp [MonoidHom.coe_range]
end KStar.TotallyRealRoots
