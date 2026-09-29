-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.inv_comp_eq_inv_comp_of_charts
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/6706f279-768a-5c47-8186-c652a23b70a0

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_one_comp_eq_one_comp_of_charts
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_inv_comp_eq_inv_comp_of_charts

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    {S B₁ B₂ : Type u} [CommRing S] [CommRing B₁] [CommRing B₂] [Algebra S B₁] [Algebra S B₂]
    {Y A₁ A₂ : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of S))
    (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (ι₁ : A₁ ⟶ Y)
    (h₁ : ι₁ ≫ f = f₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap S B₁)))
    (f₂ : A₂ ⟶ Spec (CommRingCat.of B₂)) (ι₂ : A₂ ⟶ Y) [Mono ι₂]
    (h₂ : IsPullback ι₂ f₂ f (Spec.map (CommRingCat.ofHom (algebraMap S B₂))))
    (L₁ : RelativeGroupLaw B₁ f₁) (L₂ : RelativeGroupLaw B₂ f₂)
    (hagree : ∀ {T : Scheme.{u}} (t₁ : T ⟶ Spec (CommRingCat.of B₁)) (t₂ : T ⟶ Spec (CommRingCat.of B₂))
        (a b : SchemeHomOver t₁ f₁) (a' b' : SchemeHomOver t₂ f₂),
        a.1 ≫ ι₁ = a'.1 ≫ ι₂ → b.1 ≫ ι₁ = b'.1 ≫ ι₂ → (L₁.mul t₁ a b).1 ≫ ι₁ = (L₂.mul t₂ a' b').1 ≫ ι₂)
    {T : Scheme.{u}} (t₁ : T ⟶ Spec (CommRingCat.of B₁)) (t₂ : T ⟶ Spec (CommRingCat.of B₂))
    (ht : t₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap S B₁)) = t₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap S B₂)))
    (x : SchemeHomOver t₁ f₁) (x' : SchemeHomOver t₂ f₂) (hx : x.1 ≫ ι₁ = x'.1 ≫ ι₂) :
    (L₁.inv t₁ x).1 ≫ ι₁ = (L₂.inv t₂ x').1 ≫ ι₂ := by
  set y := L₁.inv t₁ x with hy_def
  have hcomp : (y.1 ≫ ι₁) ≫ f = t₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap S B₂)) := by
    rw [Category.assoc, h₁, ← Category.assoc, y.2, ht]
  let y' : SchemeHomOver t₂ f₂ := ⟨h₂.lift (y.1 ≫ ι₁) t₂ hcomp, h₂.lift_snd _ _ _⟩
  have hy' : y.1 ≫ ι₁ = y'.1 ≫ ι₂ := (h₂.lift_fst _ _ _).symm
  have hmul := hagree t₁ t₂ y x y' x' hy' hx
  rw [L₁.inv_mul_cancel,
    GoodReductionJacobian.RelativeGroupLaw.one_comp_eq_one_comp_of_charts f f₁ ι₁ h₁ f₂ ι₂ h₂ L₁ L₂ hagree t₁ t₂ ht] at hmul
  have hprod : L₂.mul t₂ y' x' = L₂.one t₂ := Subtype.ext ((cancel_mono ι₂).mp hmul.symm)
  have hinv : y' = L₂.inv t₂ x' := by
    letI := L₂.pointGroup t₂
    have : y' * x' = 1 := hprod
    exact eq_inv_of_mul_eq_one_left this
  rw [hy', hinv]

end S_GoodReductionJacobian_RelativeGroupLaw_inv_comp_eq_inv_comp_of_charts
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_inv_comp_eq_inv_comp_of_charts (solution)
