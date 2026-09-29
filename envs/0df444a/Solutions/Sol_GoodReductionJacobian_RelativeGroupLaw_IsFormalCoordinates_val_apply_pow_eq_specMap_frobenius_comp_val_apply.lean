-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.IsFormalCoordinates.val_apply_pow_eq_specMap_frobenius_comp_val_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/6fc6614d-2bb1-54c8-a095-5b57c713a18c

import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_IsFormalCoordinates_val_apply_pow_eq_specMap_frobenius_comp_val_apply

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

def frobAlgHomTwist (k₀ : Type) [CommRing k₀] (r : ℕ) [Fact r.Prime] (C : Type) [CommRing C] [CharP C r]
    (c : k₀ →+* C) :
    @AlgHom k₀ C C _ _ _ c.toAlgebra ((frobenius C r).comp c).toAlgebra :=
  @AlgHom.mk k₀ C C _ _ _ c.toAlgebra ((frobenius C r).comp c).toAlgebra (frobenius C r) (fun _ => rfl)

theorem solution
    {k₀ : Type} [CommRing k₀] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of k₀)}
    {L : RelativeGroupLaw k₀ f} {g : ℕ} {F : MvFormalGroup g k₀} {θ : RelativeGroupLaw.FormalCoordinates f g}
    (hθ : L.IsFormalCoordinates F θ)
    (r : ℕ) [Fact r.Prime] (C : Type) [CommRing C] [CharP C r] (c : k₀ →+* C)
    (s : Fin g → C) (hs : ∀ i, IsNilpotent (s i)) :
    (@θ C _ ((frobenius C r).comp c).toAlgebra (fun i => s i ^ r)).1 =
      Spec.map (CommRingCat.ofHom (frobenius C r)) ≫ (@θ C _ c.toAlgebra s).1 := by
  obtain ⟨hnat, -⟩ := hθ
  have key := @hnat C _ c.toAlgebra C _ ((frobenius C r).comp c).toAlgebra (frobAlgHomTwist k₀ r C c) s hs
  have hφs : ((frobAlgHomTwist k₀ r C c) ∘ s : Fin g → C) = fun i => s i ^ r := by
    funext i
    show frobenius C r (s i) = s i ^ r
    rfl
  rw [hφs] at key
  rw [key]
  rfl

end S_GoodReductionJacobian_RelativeGroupLaw_IsFormalCoordinates_val_apply_pow_eq_specMap_frobenius_comp_val_apply
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_IsFormalCoordinates_val_apply_pow_eq_specMap_frobenius_comp_val_apply (solution)
