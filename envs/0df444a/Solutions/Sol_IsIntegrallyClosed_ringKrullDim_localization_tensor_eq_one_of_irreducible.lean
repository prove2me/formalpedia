-- Prove2me | solution 1 for IsIntegrallyClosed.ringKrullDim_localization_tensor_eq_one_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/65141c9d-fafc-59bf-bffa-8f66c52988f4

import Mathlib
import Theorems.Thm_Algebra_TensorProduct_nonempty_algEquiv_tensor_quotient_of_isScalarTower
import Theorems.Thm_ringKrullDim_localization_eq_one_of_isPrincipalIdealRing_of_flat
import Theorems.Thm_IsIntegrallyClosed_mem_span_singleton_of_mul_mem_of_isIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsIntegrallyClosed_ringKrullDim_localization_tensor_eq_one_of_irreducible

open scoped TensorProduct Polynomial

universe u v

noncomputable section

namespace DimOneFibreAux

open Polynomial TensorProduct

variable (Λ : Type u) [CommRing Λ] (p : Λ)

abbrev F₀ : Type u := Λ ⧸ Ideal.span {p}

abbrev Fib (A : Type u) [CommRing A] [Algebra Λ A] : Type u :=
  A ⧸ (Ideal.span {p}).map (algebraMap Λ A)

variable (A : Type u) [CommRing A] [Algebra Λ A] [Algebra Λ[X] A] [IsScalarTower Λ Λ[X] A]

noncomputable def xFib : Fib Λ p A := Ideal.Quotient.mk _ (algebraMap Λ[X] A X)

@[reducible] noncomputable def algPolyFib : Algebra (F₀ Λ p)[X] (Fib Λ p A) :=
  (Polynomial.aeval (R := F₀ Λ p) (xFib Λ p A)).toRingHom.toAlgebra

@[reducible] noncomputable def algPolyPoly : Algebra Λ[X] (F₀ Λ p)[X] :=
  (Polynomial.mapRingHom (algebraMap Λ (F₀ Λ p))).toAlgebra

attribute [local instance] algPolyFib algPolyPoly

theorem algebraMap_polyFib_apply (f : (F₀ Λ p)[X]) :
    algebraMap (F₀ Λ p)[X] (Fib Λ p A) f = Polynomial.aeval (xFib Λ p A) f := rfl

theorem algebraMap_polyPoly_apply (g : Λ[X]) :
    algebraMap Λ[X] (F₀ Λ p)[X] g = g.map (algebraMap Λ (F₀ Λ p)) := rfl

scoped instance isScalarTower_F₀_poly_fib : IsScalarTower (F₀ Λ p) (F₀ Λ p)[X] (Fib Λ p A) :=
  IsScalarTower.of_algebraMap_eq fun a => by
    rw [algebraMap_polyFib_apply, Polynomial.algebraMap_apply, Polynomial.aeval_C]
    rfl

theorem algebraMap_polyL_fib_apply (g : Λ[X]) :
    algebraMap Λ[X] (Fib Λ p A) g = Ideal.Quotient.mk _ (algebraMap Λ[X] A g) := rfl

scoped instance isScalarTower_poly_poly_fib : IsScalarTower Λ[X] (F₀ Λ p)[X] (Fib Λ p A) :=
  IsScalarTower.of_algebraMap_eq' (by
    apply Polynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply, algebraMap_polyPoly_apply, Polynomial.map_C, algebraMap_polyFib_apply,
        Polynomial.aeval_C, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.algebraMap_quotient_map_quotient,
        algebraMap_polyL_fib_apply, Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
    · rw [RingHom.comp_apply, algebraMap_polyPoly_apply, Polynomial.map_X, algebraMap_polyFib_apply,
        Polynomial.aeval_X]
      rfl)

scoped instance moduleFinite_fib [Module.Finite Λ[X] A] : Module.Finite (F₀ Λ p)[X] (Fib Λ p A) :=
  Module.Finite.of_restrictScalars_finite Λ[X] _ _

variable [IsDomain Λ] [IsPrincipalIdealRing Λ]
variable [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
variable [Module.Finite Λ[X] A] [FaithfulSMul Λ[X] A]

theorem smul_mk_eq_zero_imp (hp : Irreducible p) (r : (F₀ Λ p)[X]) (hr : r ≠ 0) (a : A)
    (h : r • (Ideal.Quotient.mk ((Ideal.span {p}).map (algebraMap Λ A)) a) = 0) :
    Ideal.Quotient.mk ((Ideal.span {p}).map (algebraMap Λ A)) a = 0 := by
  haveI : UniqueFactorizationMonoid Λ[X] := inferInstance
  haveI : IsIntegrallyClosed Λ[X] := inferInstance
  haveI hpm : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp

  obtain ⟨g, rfl⟩ := Polynomial.map_surjective (algebraMap Λ (F₀ Λ p)) Ideal.Quotient.mk_surjective r

  have hCp : (Ideal.span {(C p : Λ[X])}).IsPrime := by
    have := Ideal.isPrime_map_C_of_isPrime (P := Ideal.span {p})
    rwa [Ideal.map_span, Set.image_singleton] at this
  have hg : g ∉ Ideal.span {(C p : Λ[X])} := by
    intro hg
    apply hr
    have : g ∈ RingHom.ker (Polynomial.mapRingHom (algebraMap Λ (F₀ Λ p))) := by
      rw [Polynomial.ker_mapRingHom, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker, Ideal.map_span,
        Set.image_singleton]
      exact hg
    exact this

  rw [Algebra.smul_def, ← algebraMap_polyPoly_apply, ← IsScalarTower.algebraMap_apply,
    algebraMap_polyL_fib_apply, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.map_span,
    Set.image_singleton] at h
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.map_span, Set.image_singleton]
  have hp' : algebraMap Λ A p = algebraMap Λ[X] A (C p) := by
    rw [Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
  rw [hp'] at h ⊢
  exact IsIntegrallyClosed.mem_span_singleton_of_mul_mem_of_isIntegral hCp
    (Polynomial.C_ne_zero.mpr hp.ne_zero) hg h

theorem isTorsionFree_fib (hp : Irreducible p) : Module.IsTorsionFree (F₀ Λ p)[X] (Fib Λ p A) := by
  haveI hpm : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp
  letI : Field (F₀ Λ p) := Ideal.Quotient.field _
  refine ⟨fun r hr => ?_⟩
  have hr0 : r ≠ 0 := hr.ne_zero
  have key : ∀ z : Fib Λ p A, r • z = 0 → z = 0 := fun z hz => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact smul_mk_eq_zero_imp Λ p A hp r hr0 a hz
  have hinj : Function.Injective (DistribSMul.toAddMonoidHom (Fib Λ p A) r) :=
    (injective_iff_map_eq_zero _).mpr key
  exact hinj

theorem free_fib (hp : Irreducible p) : Module.Free (F₀ Λ p)[X] (Fib Λ p A) := by
  haveI hpm : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp
  letI : Field (F₀ Λ p) := Ideal.Quotient.field _
  haveI := isTorsionFree_fib Λ p A hp
  exact Module.free_of_finite_type_torsion_free'

theorem ringKrullDim_localization_eq_of_ringEquiv {C T : Type*} [CommRing C] [CommRing T]
    (e : C ≃+* T) (n : WithBot ℕ∞)
    (hT : ∀ (m' : Ideal T) [m'.IsMaximal], ringKrullDim (Localization.AtPrime m') = n)
    (m : Ideal C) [m.IsMaximal] : ringKrullDim (Localization.AtPrime m) = n := by
  haveI hm' : (m.comap e.symm.toRingHom).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ e.symm.surjective
  have eL : Localization.AtPrime m ≃+* Localization.AtPrime (m.comap e.symm.toRingHom) :=
    IsLocalization.ringEquivOfRingEquiv (M := m.primeCompl) (T := (m.comap e.symm.toRingHom).primeCompl)
      (Localization.AtPrime m) (Localization.AtPrime (m.comap e.symm.toRingHom)) e (by
        ext y
        simp only [Submonoid.mem_map]
        constructor
        · rintro ⟨x, hx, rfl⟩
          intro hy
          apply hx
          have hy' : e.symm.toRingHom (e x) ∈ m := hy
          simpa using hy'
        · intro hy
          refine ⟨e.symm y, ?_, by simp⟩
          intro hx
          apply hy
          show e.symm.toRingHom y ∈ m
          simpa using hx)
  rw [ringKrullDim_eq_of_ringEquiv eL]
  exact hT _

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3200000 in

theorem ringKrullDim_localization_tensor_eq_one (hp : Irreducible p)
    (k : Type v) [Field k] [Algebra Λ k] (hk : algebraMap Λ k p = 0)
    (m : Ideal (k ⊗[Λ] A)) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = 1 := by
  haveI hpm : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp
  letI : Field (F₀ Λ p) := Ideal.Quotient.field _
  letI : Algebra (F₀ Λ p) k :=
    (Ideal.Quotient.lift (Ideal.span {p}) (algebraMap Λ k) (fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul, hk, mul_zero])).toAlgebra
  haveI : IsScalarTower Λ (F₀ Λ p) k :=
    IsScalarTower.of_algebraMap_eq fun a => (Ideal.Quotient.lift_mk (Ideal.span {p}) (algebraMap Λ k) _).symm
  obtain ⟨e₁⟩ := Algebra.TensorProduct.nonempty_algEquiv_tensor_quotient_of_isScalarTower
    Λ (Ideal.span {p}) k A
  haveI : Module.Free (F₀ Λ p)[X] (Fib Λ p A) := free_fib Λ p A hp

  have eD : (F₀ Λ p)[X] ⊗[F₀ Λ p] k ≃+* k[X] :=
    ((Algebra.TensorProduct.comm (F₀ Λ p) (F₀ Λ p)[X] k).trans (polyEquivTensor (F₀ Λ p) k).symm).toRingEquiv
  haveI : IsDomain ((F₀ Λ p)[X] ⊗[F₀ Λ p] k) := MulEquiv.isDomain (k[X]) eD.toMulEquiv
  haveI : IsPrincipalIdealRing ((F₀ Λ p)[X] ⊗[F₀ Λ p] k) :=
    IsPrincipalIdealRing.of_surjective eD.symm eD.symm.surjective
  have hD : ¬ IsField ((F₀ Λ p)[X] ⊗[F₀ Λ p] k) := fun hF =>
    Polynomial.not_isField k (MulEquiv.isField hF eD.symm.toMulEquiv)
  haveI : Module.Flat ((F₀ Λ p)[X] ⊗[F₀ Λ p] k)
      (((F₀ Λ p)[X] ⊗[F₀ Λ p] k) ⊗[(F₀ Λ p)[X]] Fib Λ p A) := Module.Flat.of_free
  haveI : IsScalarTower (F₀ Λ p)[X] (F₀ Λ p)[X] (Fib Λ p A) := ⟨fun x y z => mul_smul x y z⟩

  letI : CommRing ((F₀ Λ p)[X] ⊗[F₀ Λ p] k) := inferInstance
  have eT : k ⊗[Λ] A ≃+* ((F₀ Λ p)[X] ⊗[F₀ Λ p] k) ⊗[(F₀ Λ p)[X]] Fib Λ p A :=
    e₁.toRingEquiv.trans <|
      (Algebra.TensorProduct.comm (F₀ Λ p) k (Fib Λ p A)).toRingEquiv.trans <|
        (Algebra.TensorProduct.cancelBaseChange (F₀ Λ p) (F₀ Λ p)[X] (F₀ Λ p)[X]
          (Fib Λ p A) k).symm.toRingEquiv.trans <|
          (Algebra.TensorProduct.comm (F₀ Λ p)[X] (Fib Λ p A) ((F₀ Λ p)[X] ⊗[F₀ Λ p] k)).toRingEquiv

  exact ringKrullDim_localization_eq_of_ringEquiv (C := k ⊗[Λ] A)
    (T := ((F₀ Λ p)[X] ⊗[F₀ Λ p] k) ⊗[(F₀ Λ p)[X]] Fib Λ p A) eT 1
    (fun m' _ => ringKrullDim_localization_eq_one_of_isPrincipalIdealRing_of_flat
      ((F₀ Λ p)[X] ⊗[F₀ Λ p] k) hD m') m

end DimOneFibreAux
p2m_reactivate "P2MW.S_IsIntegrallyClosed_ringKrullDim_localization_tensor_eq_one_of_irreducible.DimOneFibreAux"

end
p2m_reactivate "P2MW.S_IsIntegrallyClosed_ringKrullDim_localization_tensor_eq_one_of_irreducible.DimOneFibreAux"

open scoped TensorProduct Polynomial in
theorem solution
    {Λ A : Type u} [CommRing Λ] [IsDomain Λ] [IsPrincipalIdealRing Λ] {p : Λ} (hp : Irreducible p)
    [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra Λ A] [Algebra Λ[X] A] [IsScalarTower Λ Λ[X] A]
    [Module.Finite Λ[X] A] [FaithfulSMul Λ[X] A]
    (k : Type v) [Field k] [Algebra Λ k] (hk : algebraMap Λ k p = 0)
    (m : Ideal (k ⊗[Λ] A)) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = 1 :=
  DimOneFibreAux.ringKrullDim_localization_tensor_eq_one Λ p A hp k hk m

end S_IsIntegrallyClosed_ringKrullDim_localization_tensor_eq_one_of_irreducible
end P2MW
export P2MW.S_IsIntegrallyClosed_ringKrullDim_localization_tensor_eq_one_of_irreducible (solution)
