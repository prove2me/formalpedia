-- Prove2me | solution 1 for GlobalTheory.PrimeSection.dvd_iff_notMem_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:08:29.805186+00:00
-- url     : https://prove2.me/submissions/18c9e469-d2a5-4115-8189-94a2668a3c85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
import Theorems.Thm_GlobalTheory_PrimeSection_mem_primeIdealOf_iff
import Theorems.Thm_GlobalTheory_PrimeSection_primeIdealOf_eq_span

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
include hη hp
namespace GlobalTheory.PrimeSection
theorem _root_.solution {U : X.Opens} (hU : IsAffineOpen U) (h : η ∈ U) (s : Γ(X, U)) :
    X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t ∣ s ↔ η ∉ X.basicOpen s := by
  rw [← Ideal.mem_span_singleton, ← primeIdealOf_eq_span hη hp hU h]
  exact mem_primeIdealOf_iff hU ⟨η, h⟩ s
end GlobalTheory.PrimeSection
