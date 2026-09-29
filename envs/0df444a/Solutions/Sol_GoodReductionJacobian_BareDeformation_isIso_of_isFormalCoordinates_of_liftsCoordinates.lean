-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.isIso_of_isFormalCoordinates_of_liftsCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/540965f8-c91d-58b3-bde8-3b6c50c05154

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_MvFormalGroup_Deformation
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hom_apply_eq_apply_nilEval_of_isFormalCoordinates
import Theorems.Thm_MvPowerSeries_existsUnique_apply_eq_adicEval_of_natural_of_isNilpotent
import Theorems.Thm_MvFormalGroup_nilEval_eq_adicEval_of_pow_succ_eq_bot
import Theorems.Thm_MvFormalGroup_nilEval_subst_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_isIso_of_isFormalCoordinates_of_liftsCoordinates

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld IsLocalRing
open scoped TensorProduct

theorem FUAux_nilEval_map {σ : Type} [Fintype σ] [DecidableEq σ] {B B₁ C : Type} [CommRing B] [CommRing B₁] [CommRing C]
    [Algebra B B₁] [Algebra B₁ C] [Algebra B C] [IsScalarTower B B₁ C] (n : ℕ) (φ : MvPowerSeries σ B) (s : σ → C) :
    MvFormalGroup.nilEval n (MvPowerSeries.map (algebraMap B B₁) φ) s = MvFormalGroup.nilEval n φ s := by
  unfold MvFormalGroup.nilEval
  rw [MvPowerSeries.trunc'_map, MvPolynomial.aeval_map_algebraMap]

theorem FUAux_exists_pow_succ_eq_bot {C : Type} [CommRing C] (J : Ideal C) (hJ : IsNilpotent J) :
    ∃ n : ℕ, J ^ (n + 1) = ⊥ := by
  obtain ⟨m, hm⟩ := hJ
  exact ⟨m, by rw [pow_succ, hm]; exact zero_mul _⟩

theorem solution
    (B B₁ : Type) [CommRing B] [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
    {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}
    (Ĝ₁ : MvFormalGroup 2 B₁) (θ₁ : RelativeGroupLaw.FormalCoordinates f₁ 2) (hθ₁ : L₁.IsFormalCoordinates Ĝ₁ θ₁)
    (D : BareDeformation f₁ L₁ B)
    (G G' : MvFormalGroup.Deformation Ĝ₁ B) (θ θ' : RelativeGroupLaw.FormalCoordinates D.f 2)
    (hθ : D.L.IsFormalCoordinates G.F θ) (hθ' : D.L.IsFormalCoordinates G'.F θ')
    (hl : D.LiftsCoordinates θ₁ θ) (hl' : D.LiftsCoordinates θ₁ θ') :
    ∃ φ : MvFormalGroup.Hom G.F G'.F,
      (∃ ψ : MvFormalGroup.Hom G'.F G.F, ψ.comp φ = MvFormalGroup.Hom.id G.F ∧ φ.comp ψ = MvFormalGroup.Hom.id G'.F) ∧
      (∀ i : Fin 2, MvPowerSeries.map (algebraMap B B₁) (φ.toPowerSeries i) = MvPowerSeries.X i) ∧
      ∀ (B'' : Type) [CommRing B''] [Algebra B B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
        ∀ s : Fin 2 → B'', (∀ i, s i ∈ J) →
          θ B'' s = θ' B'' (fun i => MvFormalGroup.nilEval n (φ.toPowerSeries i) s) := by
  classical
  obtain ⟨φ, hinv, htrans, -⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_hom_apply_eq_apply_nilEval_of_isFormalCoordinates D.L G.F G'.F θ θ' hθ hθ'
  refine ⟨φ, hinv, ?_, htrans⟩
  intro i

  have hu := MvPowerSeries.existsUnique_apply_eq_adicEval_of_natural_of_isNilpotent (R := B₁) (σ := Fin 2)
    (fun C _ _ J x => x i) (fun C C' _ _ _ _ J J' _ _ φ' _ x _ => rfl)
  refine hu.unique ?_ (fun C _ _ J hJ x hx => (MvFormalGroup.adicEval_X J x i).symm)
  intro C _ _ J hJ x hx
  obtain ⟨n, hn⟩ := FUAux_exists_pow_succ_eq_bot J hJ
  letI : Algebra B C := ((algebraMap B₁ C).comp (algebraMap B B₁)).toAlgebra
  haveI : IsScalarTower B B₁ C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  rw [← MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hn _ _ hx, FUAux_nilEval_map]

  have hxnil : ∀ j, IsNilpotent (x j) := fun j =>
    ⟨n + 1, by have h := Ideal.pow_mem_pow (hx j) (n + 1); rwa [hn, Ideal.mem_bot] at h⟩
  have heq : θ C x = θ' C x := Subtype.ext ((hl C x hxnil).symm.trans (hl' C x hxnil))
  have hmem : ∀ j, MvFormalGroup.nilEval n (φ.toPowerSeries j) x ∈ J := fun j =>
    (MvFormalGroup.nilEval_subst_of_mem J n hn x hx φ.toPowerSeries φ.constantCoeff_eq_zero 0).1 j
  have key : x = fun j => MvFormalGroup.nilEval n (φ.toPowerSeries j) x :=
    (hθ'.2 C J n hn).2.1 x _ hx hmem (heq.symm.trans (htrans C J n hn x hx))
  exact congrFun key i

end S_GoodReductionJacobian_BareDeformation_isIso_of_isFormalCoordinates_of_liftsCoordinates
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_isIso_of_isFormalCoordinates_of_liftsCoordinates (solution)
