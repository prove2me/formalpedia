-- Prove2me | solution 1 for GlobalTheory.HeckeCompare.card_orth_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:14:26.846476+00:00
-- url     : https://prove2.me/submissions/5733d438-42f5-4674-884f-0ae95f088033

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
theorem _root_.solution {G k : Type} [CommGroup G] [Finite G] [Field k] [IsAlgClosed k] [CharZero k]
    (B : G →* G →* kˣ) (hB : Function.Injective B) (S : Subgroup G) :
    Nat.card {x : G // ∀ c ∈ S, B x c = 1} * Nat.card S = Nat.card G := by
  have : NeZero ((Monoid.exponent G : ℕ) : k) := ⟨Nat.cast_ne_zero.2 Monoid.exponent_ne_zero_of_finite⟩
  have : NeZero ((Monoid.exponent S : ℕ) : k) := ⟨Nat.cast_ne_zero.2 Monoid.exponent_ne_zero_of_finite⟩
  have hc := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G k
  have : Finite (G →* kˣ) := Nat.finite_of_card_ne_zero (by rw [hc]; exact Nat.card_pos.ne')
  have hb := hB.bijective_of_nat_card_le hc.le
  have hs : Function.Surjective ((MonoidHom.domRestrictHom S kˣ).comp B) :=
    (MonoidHom.domRestrict_surjective k S).comp hb.2
  rw [← ((MonoidHom.domRestrictHom S kˣ).comp B).ker.card_mul_index, Subgroup.index_ker,
    MonoidHom.range_eq_top.2 hs, Subgroup.card_top, CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  rw [MonoidHom.mem_ker, MonoidHom.ext_iff]
  exact ⟨fun h c => h c.1 c.2, fun h c hc => h ⟨c, hc⟩⟩
end GlobalTheory.HeckeCompare
