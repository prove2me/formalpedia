-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.nsmulPt_eq_one_of_mul_inv_one_pushPt_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/795dd137-c139-55dc-8332-3389dcb199f3

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_nsmulPt_eq_one_of_mul_inv_one_pushPt_comp

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal IsLocalRing

open scoped Quaternion TensorProduct NumberField

universe u

namespace E162LVd3

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem nsmulPt_eq_pow (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (P : SchemeHomOver t f) :
    letI := L.pointGroup t
    nsmulPt L t n P = P ^ n := by
  letI := L.pointGroup t
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih =>
    rw [pow_succ, ← ih]; rfl

theorem map_nsmulPt_of_map_mul {R' : Type u} [CommRing R'] {A' : Scheme.{u}}
    {f' : A' ⟶ Spec (CommRingCat.of R')}
    (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R' f')
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of R'))
    (σ : SchemeHomOver t f → SchemeHomOver t' f')
    (hσ : ∀ P Q, σ (L.mul t P Q) = L'.mul t' (σ P) (σ Q)) (n : ℕ) (P : SchemeHomOver t f) :
    σ (nsmulPt L t n P) = nsmulPt L' t' n (σ P) ∧ σ (L.one t) = L'.one t' := by
  letI := L.pointGroup t
  letI := L'.pointGroup t'
  let σ' : SchemeHomOver t f →* SchemeHomOver t' f' := MonoidHom.mk' σ hσ
  refine ⟨?_, ?_⟩
  · rw [nsmulPt_eq_pow, nsmulPt_eq_pow]
    exact map_pow σ' P n
  · exact map_one σ'

end E162LVd3

open E162LVd3 in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (B B₀ : Type) [CommRing B] [CommRing B₀] [Algebra B B₀]
    (E₀ : FakeEllipticCurve Λ N B₀) (D : BareDeformation E₀.f E₀.L B)
    {ι : Type} (φ : ι → (D.A ⟶ D.A)) (hφ : ∀ i, φ i ≫ D.f = D.f)
    (hφ_hom : ∀ (i : ι) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t D.f),
      pushPt (φ i) (hφ i) (D.L.mul t P Q) = D.L.mul t (pushPt (φ i) (hφ i) P) (pushPt (φ i) (hφ i) Q)) :
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t D.f),
        nsmulPt D.L t N P = D.L.one t → nsmulPt D.L t N Q = D.L.one t →
          nsmulPt D.L t N (D.L.mul t P Q) = D.L.one t ∧ nsmulPt D.L t N (D.L.inv t P) = D.L.one t) ∧
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)), nsmulPt D.L t N (D.L.one t) = D.L.one t) ∧
    (∀ (i : ι) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t D.f),
        nsmulPt D.L t N P = D.L.one t → nsmulPt D.L t N (pushPt (φ i) (hφ i) P) = D.L.one t) ∧
    (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B₀)) (P : SchemeHomOver t' E₀.f),
        FactorsThrough E₀.lev P →
          nsmulPt D.L (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀))) N
              ⟨P.1 ≫ D.g, by rw [Category.assoc, D.cart.w, ← Category.assoc, P.2]⟩
            = D.L.one (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀)))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro T t P Q hP hQ
    letI := D.L.pointGroup t
    rw [nsmulPt_eq_pow] at hP hQ
    change P ^ N = 1 at hP
    change Q ^ N = 1 at hQ
    have hc : Commute P Q := D.comm t P Q
    refine ⟨?_, ?_⟩
    · rw [nsmulPt_eq_pow]
      show (P * Q) ^ N = 1
      rw [hc.mul_pow, hP, hQ, one_mul]
    · rw [nsmulPt_eq_pow]
      show (P⁻¹) ^ N = 1
      rw [inv_pow, hP, inv_one]
  · intro T t
    letI := D.L.pointGroup t
    rw [nsmulPt_eq_pow]
    exact one_pow N
  · intro i T t P hP
    have h := (map_nsmulPt_of_map_mul D.L D.L t t (pushPt (φ i) (hφ i)) (hφ_hom i t) N P)
    rw [← h.1, hP, h.2]
  · intro T t' P hP
    have hσ := map_nsmulPt_of_map_mul E₀.L D.L t' (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀)))
      (fun P => ⟨P.1 ≫ D.g, by rw [Category.assoc, D.cart.w, ← Category.assoc, P.2]⟩)
      (fun P Q => Subtype.ext (D.hom t' P Q)) N P
    rw [← hσ.1, E₀.lev_torsion t' P hP, hσ.2]

end S_GoodReductionJacobian_BareDeformation_nsmulPt_eq_one_of_mul_inv_one_pushPt_comp
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_nsmulPt_eq_one_of_mul_inv_one_pushPt_comp (solution)
