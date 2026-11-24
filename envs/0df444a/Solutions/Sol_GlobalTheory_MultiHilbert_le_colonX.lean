-- Prove2me | solution 1 for GlobalTheory.MultiHilbert.le_colonX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:00:39.800526+00:00
-- url     : https://prove2.me/submissions/245a1748-6619-47d7-8f60-3a1bb7dc283c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsMultigradedHilbertPoly
import Theorems.Thm_GlobalTheory_MultiHilbert_mem_colonX

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MultiHilbert
open MvPolynomial
variable {K σ M : Type} [Field K] [AddCancelCommMonoid M] (w : σ → M)
namespace GlobalTheory.MultiHilbert
theorem _root_.solution (I : Ideal (MvPolynomial σ K)) (i : σ) : I ≤ colonX I i :=
  fun _ h => mem_colonX.2 (I.mul_mem_left _ h)
end GlobalTheory.MultiHilbert
