-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems.IsPadicCompleteSetting.exists_isPrimitiveRoot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:51:16.144069+00:00
-- url     : https://prove2.me/submissions/8847eedc-5dd9-4cff-9d1a-b7cad4d4ba0a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_HodgeTateCharacterSystems

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open IsLocalRing ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems
noncomputable section
variable {C : Type u} [Field C]
namespace GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems
namespace IsPadicCompleteSetting
theorem _root_.solution {O : ValuationSubring C} {p : ℕ}
    (h : IsPadicCompleteSetting O p) : ∃ ζ : O, IsPrimitiveRoot ζ p := by
  obtain ⟨hp, hac, hcz, -, -⟩ := h
  haveI := hac
  haveI := hcz
  haveI : NeZero (p : C) := ⟨by exact_mod_cast hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C p
  have hmem : ζ ∈ O := by
    apply O.mem_of_valuation_le_one
    have h1 : O.valuation ζ ^ p = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    by_contra hlt
    push_neg at hlt
    have h2 := one_lt_pow' hlt hp.ne_zero
    rw [h1] at h2
    exact lt_irrefl _ h2
  exact ⟨⟨ζ, hmem⟩, IsPrimitiveRoot.of_map_of_injective (f := O.subtype) (by exact hζ) Subtype.coe_injective⟩
end IsPadicCompleteSetting
end GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems
