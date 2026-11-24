-- Prove2me | solution 1 for GlobalTheory.HeckeCompare.card_eq_tors_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:14:25.634614+00:00
-- url     : https://prove2.me/submissions/ab576b0b-297c-40b9-97f7-050c131ecc0a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NatCastMemConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HeckeCompare
namespace GlobalTheory.HeckeCompare
theorem _root_.solution {Q : Type} [CommGroup Q] (C : Subgroup Q) (p : ℕ) :
    Nat.card C = Nat.card {x : Q // x ∈ C ∧ x ^ p = 1} * Nat.card (C.map (powMonoidHom p)) := by
  rw [← ((powMonoidHom p).comp C.subtype).ker.card_mul_index, Subgroup.index_ker, MonoidHom.range_comp,
    Subgroup.range_subtype]
  congr 1
  exact Nat.card_congr ⟨fun x => ⟨x.1.1, x.1.2, x.2⟩, fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩, fun _ => rfl, fun _ => rfl⟩
end GlobalTheory.HeckeCompare
