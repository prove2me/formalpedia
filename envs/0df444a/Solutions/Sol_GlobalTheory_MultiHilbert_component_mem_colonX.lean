-- Prove2me | solution 1 for GlobalTheory.MultiHilbert.component_mem_colonX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:00:44.070898+00:00
-- url     : https://prove2.me/submissions/99364adb-057f-43c9-810d-787e21f56a1b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsMultigradedHilbertPoly
import Theorems.Thm_GlobalTheory_MultiHilbert_component_X_mul
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
theorem _root_.solution {I : Ideal (MvPolynomial σ K)}
    (hI : ∀ F ∈ I, ∀ n, weightedHomogeneousComponent w n F ∈ I) (i : σ) :
    ∀ F ∈ colonX I i, ∀ n, weightedHomogeneousComponent w n F ∈ colonX I i := by
  intro F hF n
  rw [mem_colonX, ← component_X_mul]
  exact hI _ hF _
end GlobalTheory.MultiHilbert
