-- Prove2me | solution 1 for GlobalTheory.PrimeSection.eq_of_germ_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:34:07.227974+00:00
-- url     : https://prove2.me/submissions/80c9499d-b0e4-4522-a4cf-ee363428dc50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.PrimeSection
variable {X : Scheme.{u}} [IsIntegral X]
namespace GlobalTheory.PrimeSection
theorem _root_.solution {W : X.Opens} {s s' : Γ(X, W)}
    (h : ∀ hW : genericPoint X ∈ W, X.presheaf.germ W _ hW s = X.presheaf.germ W _ hW s') :
    s = s' := by
  by_cases hW : genericPoint X ∈ W
  · exact germ_injective_of_isIntegral X (genericPoint X) hW (h hW)
  · refine TopCat.Presheaf.section_ext X.sheaf W s s' fun x hx => ?_
    exact (hW (genericPoint_mem hx)).elim
end GlobalTheory.PrimeSection
