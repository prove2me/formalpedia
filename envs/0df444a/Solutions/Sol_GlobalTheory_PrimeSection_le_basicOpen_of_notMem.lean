-- Prove2me | solution 1 for GlobalTheory.PrimeSection.le_basicOpen_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:08:33.345289+00:00
-- url     : https://prove2.me/submissions/b2597e99-2d6b-45bf-854d-20d0a6f0ef57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
import Theorems.Thm_GlobalTheory_PrimeSection_mem_of_notMem_basicOpen

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
variable {X : Scheme.{u}} {t : Γ(X, ⊤)} {η : X}
  (hη : ∀ x : X, x ∉ X.basicOpen t ↔ η ⤳ x)
  (hp : ∀ U : X.Opens, IsAffineOpen U → η ∈ U →
    Prime (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))
include hη
namespace GlobalTheory.PrimeSection
theorem _root_.solution {W : X.Opens} (hW : η ∉ W) : W ≤ X.basicOpen t := by
  intro x hx
  by_contra hxt
  exact hW (mem_of_notMem_basicOpen hη hx hxt)
end GlobalTheory.PrimeSection
