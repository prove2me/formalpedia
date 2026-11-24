-- Prove2me | solution 1 for GlobalTheory.PrimeSection.mem_primeIdealOf_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:32:47.663505+00:00
-- url     : https://prove2.me/submissions/e9ea5c13-37c3-4311-839c-921ef93b8def

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
variable {X : Scheme.{u}} {t : Γ(X, ⊤)} {η : X}
  (hη : ∀ x : X, x ∉ X.basicOpen t ↔ η ⤳ x)
  (hp : ∀ U : X.Opens, IsAffineOpen U → η ∈ U →
    Prime (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))
namespace GlobalTheory.PrimeSection
theorem _root_.solution {U : X.Opens} (hU : IsAffineOpen U) (x : U) (s : Γ(X, U)) :
    s ∈ (hU.primeIdealOf x).asIdeal ↔ x.1 ∉ X.basicOpen s := by
  rw [hU.primeIdealOf_eq_map_closedPoint x, X.mem_basicOpen s x.1 x.2]
  change X.presheaf.germ U x.1 x.2 s ∈ IsLocalRing.maximalIdeal _ ↔ _
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
end GlobalTheory.PrimeSection
