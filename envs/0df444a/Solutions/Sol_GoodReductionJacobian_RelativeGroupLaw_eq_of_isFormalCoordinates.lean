-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.eq_of_isFormalCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/af7aa936-8ec9-5c90-a50b-90aa1fd84790

import Mathlib
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_CerednikDrinfeld_QMModuli
import Theorems.Thm_CerednikDrinfeld_QM_exists_injective_range_isTangentVector_of_isFormalCoordinates
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_isFormalCoordinates

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

theorem solution
    {B : Type} [CommRing B] [Nontrivial B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}
    (L : RelativeGroupLaw B f) {g g' : ℕ} (F : MvFormalGroup g B) (F' : MvFormalGroup g' B)
    (θ : RelativeGroupLaw.FormalCoordinates f g) (θ' : RelativeGroupLaw.FormalCoordinates f g')
    (hθ : L.IsFormalCoordinates F θ) (hθ' : L.IsFormalCoordinates F' θ') : g = g' := by
  classical

  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  let k : Type := B ⧸ m
  letI : Field k := Ideal.Quotient.field m

  obtain ⟨τ, -, hτinj, hτrange, hτadd, hτsmul⟩ :=
    CerednikDrinfeld.QM.exists_injective_range_isTangentVector_of_isFormalCoordinates L F θ hθ k
  obtain ⟨τ', -, hτ'inj, hτ'range, hτ'add, hτ'smul⟩ :=
    CerednikDrinfeld.QM.exists_injective_range_isTangentVector_of_isFormalCoordinates L F' θ' hθ' k

  have hex : ∀ v : Fin g → k, ∃ v' : Fin g' → k, τ' v' = τ v := fun v =>
    (hτ'range (τ v)).2 ((hτrange (τ v)).1 ⟨v, rfl⟩)
  choose e he using hex
  have hex' : ∀ v' : Fin g' → k, ∃ v : Fin g → k, τ v = τ' v' := fun v' =>
    (hτrange (τ' v')).2 ((hτ'range (τ' v')).1 ⟨v', rfl⟩)
  choose e' he' using hex'
  have hee' : ∀ v', e (e' v') = v' := fun v' => hτ'inj (by rw [he, he'])
  have he'e : ∀ v, e' (e v) = v := fun v => hτinj (by rw [he', he])
  have hadd : ∀ v w, e (v + w) = e v + e w := fun v w =>
    hτ'inj (by rw [he, hτadd, hτ'add, he, he])
  have hsmul : ∀ (c : k) (v : Fin g → k), e (c • v) = c • e v := fun c v =>
    hτ'inj (Subtype.ext (by rw [hτ'smul, he, he, hτsmul]))
  let E : (Fin g → k) ≃ₗ[k] (Fin g' → k) :=
    { toFun := e
      map_add' := hadd
      map_smul' := hsmul
      invFun := e'
      left_inv := he'e
      right_inv := hee' }
  have h := E.finrank_eq
  simpa using h

end S_GoodReductionJacobian_RelativeGroupLaw_eq_of_isFormalCoordinates
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_isFormalCoordinates (solution)
