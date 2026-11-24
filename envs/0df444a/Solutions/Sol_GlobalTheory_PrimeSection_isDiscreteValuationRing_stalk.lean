-- Prove2me | solution 1 for GlobalTheory.PrimeSection.isDiscreteValuationRing_stalk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:21:54.834133+00:00
-- url     : https://prove2.me/submissions/4a1b51c4-2eaf-41a3-adea-3c18cbeba293

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
import Theorems.Thm_GlobalTheory_PrimeSection_germ_res
import Theorems.Thm_GlobalTheory_PrimeSection_primeIdealOf_eq_span
import Theorems.Thm_GlobalTheory_PrimeElement_irreducible_algebraMap
import Theorems.Thm_GlobalTheory_PrimeElement_isDiscreteValuationRing
import Theorems.Thm_GlobalTheory_PrimeElement_isPrime_span


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
variable [IsIntegral X]
include hη hp
namespace GlobalTheory.PrimeSection
theorem _root_.solution [IsLocallyNoetherian X] :
    IsDiscreteValuationRing (X.presheaf.stalk η) ∧
      Irreducible (X.presheaf.germ ⊤ η trivial t) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ η) isOpen_univ
  have hπ := hp U hU hηU
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : Nonempty U := ⟨⟨η, hηU⟩⟩
  have := GlobalTheory.PrimeElement.isPrime_span hπ
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨η, hηU⟩ : U)
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk η) (Ideal.span {X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t}) := by
    have h0 := hU.isLocalization_stalk ⟨η, hηU⟩
    unfold IsLocalization.AtPrime at h0 ⊢
    convert h0 using 3
    exact (primeIdealOf_eq_span hη hp hU hηU).symm
  refine ⟨GlobalTheory.PrimeElement.isDiscreteValuationRing (X.presheaf.stalk η) hπ.ne_zero, ?_⟩
  have hirr := GlobalTheory.PrimeElement.irreducible_algebraMap (X.presheaf.stalk η) hπ.ne_zero
  convert hirr using 1
  exact (germ_res le_top hηU t).symm
end GlobalTheory.PrimeSection
