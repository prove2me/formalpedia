-- Prove2me | solution 1 for Module.Finite.of_algHom_equiv_isIdempotentElem_tensorProduct_of_etale_of_rankAtStalk_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/5c120461-3687-5e91-b2d3-e7e7ecc1315a

import Mathlib
import Theorems.Thm_Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Finite_of_algHom_equiv_isIdempotentElem_tensorProduct_of_etale_of_rankAtStalk_eq

set_option autoImplicit false

open TensorProduct

universe u

namespace IdemFin

variable {R : Type u} [CommRing R] {Q : Type u} [CommRing Q] [Algebra R Q]
  {R₁ : Type u} [CommRing R₁] [Algebra R R₁] {r : ℕ}
  (φ : (R₁ ⊗[R] Q) ≃ₐ[R₁] (Fin r → R₁))

noncomputable def Ψ (A : Type u) [CommRing A] [Algebra R A] [Algebra R₁ A] [IsScalarTower R R₁ A] :
    (A ⊗[R] Q) ≃ₐ[R₁] (Fin r → A) :=
  ((Algebra.TensorProduct.cancelBaseChange R R₁ R₁ A Q).symm.trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[R₁] A) φ)).trans
    ((Algebra.TensorProduct.piRight R₁ R₁ A (fun _ : Fin r => R₁)).trans
      (AlgEquiv.piCongrRight fun _ => Algebra.TensorProduct.rid R₁ R₁ A))

lemma Ψ_tmul (A : Type u) [CommRing A] [Algebra R A] [Algebra R₁ A] [IsScalarTower R R₁ A]
    (a : A) (q : Q) (k : Fin r) :
    Ψ φ A (a ⊗ₜ q) k = φ (1 ⊗ₜ q) k • a := by
  simp [Ψ, Algebra.TensorProduct.cancelBaseChange_symm_tmul, Algebra.TensorProduct.piRight_tmul]

lemma Ψ_natural (A B : Type u) [CommRing A] [Algebra R A] [Algebra R₁ A] [IsScalarTower R R₁ A]
    [CommRing B] [Algebra R B] [Algebra R₁ B] [IsScalarTower R R₁ B] (i : A →ₐ[R₁] B) (x : A ⊗[R] Q) (k : Fin r) :
    Ψ φ B (Algebra.TensorProduct.map (i.restrictScalars R) (AlgHom.id R Q) x) k = i (Ψ φ A x k) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a q =>
    rw [Algebra.TensorProduct.map_tmul]
    simp only [AlgHom.coe_restrictScalars', AlgHom.id_apply, Ψ_tmul, map_smul]
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy]

end IdemFin

open IdemFin in

theorem solution
    (R : Type u) [CommRing R] (Q : Type u) [CommRing Q] [Algebra R Q] [Module.Finite R Q] [Algebra.Etale R Q]
    (r : ℕ) (hr : ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) Q p = r)
    (C : Type u) [CommRing C] [Algebra R C]
    (η : ∀ (S : Type u) [CommRing S] [Algebra R S], (C →ₐ[R] S) ≃ {e : S ⊗[R] Q // IsIdempotentElem e})
    (hη : ∀ (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] (g : S →ₐ[R] T) (c : C →ₐ[R] S),
        ((η T (g.comp c) : {e : T ⊗[R] Q // IsIdempotentElem e}) : T ⊗[R] Q) =
          Algebra.TensorProduct.map g (AlgHom.id R Q) ((η S c : {e : S ⊗[R] Q // IsIdempotentElem e}) : S ⊗[R] Q)) :
    Module.Finite R C := by
  classical

  obtain ⟨R₁, _, _, _, _, _, ⟨φ⟩⟩ :=
    Algebra.Etale.exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq R Q r hr

  let C₁ : Type u := R₁ ⊗[R] C
  let j : C →ₐ[R] C₁ := Algebra.TensorProduct.includeRight
  let u : C₁ ⊗[R] Q := (η C₁ j).1
  have hu : IsIdempotentElem u := (η C₁ j).2

  let e : Fin r → C₁ := Ψ φ C₁ u
  have he : ∀ k, IsIdempotentElem (e k) := by
    intro k
    have : IsIdempotentElem (Ψ φ C₁ u) := hu.map (Ψ φ C₁)
    exact congrFun this.eq k

  let D : Subalgebra R₁ C₁ := Algebra.adjoin R₁ (Set.range e)
  have hD_fg : (Subalgebra.toSubmodule D).FG := by
    apply fg_adjoin_of_finite (Set.finite_range e)
    rintro _ ⟨k, rfl⟩
    refine ⟨Polynomial.X * (Polynomial.X - Polynomial.C 1), Polynomial.monic_X.mul (Polynomial.monic_X_sub_C 1), ?_⟩
    simp [mul_sub, (he k).eq]
  have he_mem : ∀ k, e k ∈ D := fun k => Algebra.subset_adjoin ⟨k, rfl⟩

  let eD : Fin r → D := fun k => ⟨e k, he_mem k⟩
  have heD : IsIdempotentElem eD := by
    change eD * eD = eD
    funext k
    apply Subtype.ext
    exact (he k).eq
  let u' : ↥D ⊗[R] Q := (Ψ φ D).symm eD
  have hu' : IsIdempotentElem u' := heD.map (Ψ φ D).symm
  let i : ↥D →ₐ[R] C₁ := (D.val).restrictScalars R
  have hiu' : Algebra.TensorProduct.map i (AlgHom.id R Q) u' = u := by
    apply (Ψ φ C₁).injective
    funext k
    rw [Ψ_natural φ D C₁ D.val u' k]
    change D.val (Ψ φ (↥D) ((Ψ φ ↥D).symm eD) k) = e k
    rw [AlgEquiv.apply_symm_apply]
    rfl

  let s : C →ₐ[R] D := (η D).symm ⟨u', hu'⟩
  have his : i.comp s = j := by
    apply (η C₁).injective
    apply Subtype.ext
    rw [hη D C₁ i s]
    change Algebra.TensorProduct.map i (AlgHom.id R Q) ((η ↥D ((η ↥D).symm ⟨u', hu'⟩)) : ↥D ⊗[R] Q) = u
    rw [Equiv.apply_symm_apply]
    exact hiu'
  have hj_mem : ∀ c : C, j c ∈ D := by
    intro c
    have : i (s c) = j c := by rw [← his]; rfl
    rw [← this]
    exact (s c).2

  have hD_top : D = ⊤ := by
    rw [eq_top_iff]
    intro x _
    induction x using TensorProduct.induction_on with
    | zero => exact D.zero_mem
    | tmul a c =>
      have : a ⊗ₜ[R] c = a • j c := by
        change a ⊗ₜ[R] c = a • ((1 : R₁) ⊗ₜ[R] c)
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact D.smul_mem (hj_mem c) a
    | add x y hx hy => exact D.add_mem (hx trivial) (hy trivial)
  haveI : Module.Finite R₁ C₁ := by
    have h := hD_fg
    rw [hD_top, Algebra.top_toSubmodule] at h
    exact ⟨h⟩

  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat (R := R) (M := C) R₁

end S_Module_Finite_of_algHom_equiv_isIdempotentElem_tensorProduct_of_etale_of_rankAtStalk_eq
end P2MW
export P2MW.S_Module_Finite_of_algHom_equiv_isIdempotentElem_tensorProduct_of_etale_of_rankAtStalk_eq (solution)
