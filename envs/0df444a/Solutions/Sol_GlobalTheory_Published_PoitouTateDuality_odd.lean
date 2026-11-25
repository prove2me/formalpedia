-- Prove2me | solution 1 for GlobalTheory.Published.PoitouTateDuality.odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:10:35.198815+00:00
-- url     : https://prove2.me/submissions/3b03ea7d-a566-4d06-ae34-2ce5fb5a1d4e

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__CohDimTwoLocalOfLocalFiniteness_b2c2e165733ad400
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ExistsPrimitiveRootPow_85cddf4c39d1fc1a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory GlobalTheory.Published
open PoitouTate
namespace GlobalTheory.Published
namespace PoitouTateDuality
theorem _root_.solution (h : PoitouTateDuality) : PoitouTateOdd :=
  fun F Ω _ _ _ _ _ l _ r hl => h F Ω l r (Or.inl hl)
end PoitouTateDuality
end GlobalTheory.Published
