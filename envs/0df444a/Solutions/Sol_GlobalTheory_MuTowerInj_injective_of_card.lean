-- Prove2me | solution 1 for GlobalTheory.MuTowerInj.injective_of_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:00:40.830803+00:00
-- url     : https://prove2.me/submissions/d1781991-9bb6-4241-9fbc-0786f34bfb82

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MuCocycleCoboundaryLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GlobalTheory GlobalTheory.MuTowerInj
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {R₁ R₂ R₃ M₁ M₂ M₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃]
  [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [Module R₁ M₁] [Module R₂ M₂] [Module R₃ M₃]
  [TopologicalSpace M₁] [TopologicalSpace M₂] [TopologicalSpace M₃]
  [DiscreteTopology M₁] [DiscreteTopology M₂] [DiscreteTopology M₃]
namespace GlobalTheory.MuTowerInj
theorem _root_.solution {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Finite A] [Finite B] [Finite C] (f : A →+ B) (g : B →+ C) (h : g.ker ≤ f.range)
    (hc : Nat.card B = Nat.card A * Nat.card C) : Function.Injective f := by
  have eA : Nat.card f.ker * Nat.card f.range = Nat.card A := by
    rw [← AddSubgroup.index_ker]
    exact AddSubgroup.card_mul_index _
  have eB : Nat.card g.ker * Nat.card g.range = Nat.card B := by
    rw [← AddSubgroup.index_ker]
    exact AddSubgroup.card_mul_index _
  have h1 : Nat.card g.ker ≤ Nat.card f.range := AddSubgroup.card_le_of_le h
  have h2 : Nat.card g.range ≤ Nat.card C :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hpos : 0 < Nat.card f.range * Nat.card C := Nat.mul_pos Nat.card_pos Nat.card_pos

  have hk : Nat.card f.ker ≤ 1 := by
    by_contra hne
    rw [not_le] at hne
    have hlt : Nat.card f.range * Nat.card C < Nat.card f.range * Nat.card C :=
      calc Nat.card f.range * Nat.card C
          < Nat.card f.ker * (Nat.card f.range * Nat.card C) := lt_mul_of_one_lt_left hpos hne
        _ = Nat.card A * Nat.card C := by rw [← eA, mul_assoc]
        _ = Nat.card B := hc.symm
        _ = Nat.card g.ker * Nat.card g.range := eB.symm
        _ ≤ Nat.card f.range * Nat.card C := Nat.mul_le_mul h1 h2
    exact lt_irrefl _ hlt
  rw [AddSubgroup.card_le_one_iff_eq_bot] at hk
  exact (AddMonoidHom.ker_eq_bot_iff f).1 hk
end GlobalTheory.MuTowerInj
