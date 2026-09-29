-- Prove2me | solution 1 for HopfAlgebra.exists_bialgHom_surjective_forall_comp_eq_of_natural_injective_of_range_eq_torsion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/7c880dfa-1387-5e19-bde4-d42c668dbf4d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_bialgHom_surjective_forall_comp_eq_of_natural_injective_of_range_eq_torsion

set_option autoImplicit false
set_option Elab.async false

universe u v

open scoped TensorProduct
open WithConv

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk antipode_one ofAlgHom mul_antipode_lTensor_comul_apply antipode_mul mul_antipode_rTensor_comul_apply"
namespace YonedaTorsion
p2m_open "HopfAlgebra"

theorem surjective_of_forall_injective_comp_of_range_eq_equalizer
    {R : Type u} [CommRing R] {H₁ H₂ : Type v} [CommRing H₁] [Algebra R H₁] [CommRing H₂] [Algebra R H₂]
    (r : H₂ →ₐ[R] H₁) (a b : H₂ →ₐ[R] H₂)
    (hinj : ∀ (T : Type v) [CommRing T] [Algebra R T], Function.Injective (fun φ : H₁ →ₐ[R] T => φ.comp r))
    (himg : ∀ (T : Type v) [CommRing T] [Algebra R T] (ψ : H₂ →ₐ[R] T),
      (∃ φ : H₁ →ₐ[R] T, φ.comp r = ψ) ↔ ψ.comp a = ψ.comp b) :
    Function.Surjective r := by
  classical
  let I : Ideal H₂ := Ideal.span (Set.range fun x => a x - b x)
  let mk : H₂ →ₐ[R] H₂ ⧸ I := Ideal.Quotient.mkₐ R I

  have hmk : mk.comp a = mk.comp b := by
    apply AlgHom.ext
    intro x
    change Ideal.Quotient.mk I (a x) = Ideal.Quotient.mk I (b x)
    rw [Ideal.Quotient.eq]
    exact Ideal.subset_span ⟨x, rfl⟩
  obtain ⟨φ₀, hφ₀⟩ := (himg _ mk).mpr hmk

  have hr : r.comp a = r.comp b := (himg H₁ r).mp ⟨AlgHom.id R H₁, AlgHom.id_comp r⟩

  have hI : ∀ x ∈ I, r x = 0 := by
    intro x hx
    have hle : I ≤ RingHom.ker (r : H₂ →+* H₁) := by
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨y, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, AlgHom.coe_toRingHom, map_sub, sub_eq_zero]
      exact congrArg (fun f : H₂ →ₐ[R] H₁ => f y) hr
    exact hle hx
  let rbar : H₂ ⧸ I →ₐ[R] H₁ := Ideal.Quotient.liftₐ I r hI
  have hrbar : rbar.comp mk = r := AlgHom.ext fun x => rfl

  have h1 : φ₀.comp rbar = AlgHom.id R _ := by
    apply Ideal.Quotient.algHom_ext
    change (φ₀.comp rbar).comp mk = (AlgHom.id R (H₂ ⧸ I)).comp mk
    rw [AlgHom.comp_assoc, hrbar, hφ₀, AlgHom.id_comp]
  have h2 : rbar.comp φ₀ = AlgHom.id R H₁ := by
    apply hinj H₁
    change (rbar.comp φ₀).comp r = (AlgHom.id R H₁).comp r
    rw [AlgHom.comp_assoc, hφ₀, hrbar, AlgHom.id_comp]

  intro y
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (I := I) (φ₀ y)
  refine ⟨x, ?_⟩
  calc r x = rbar (mk x) := rfl
    _ = rbar (φ₀ y) := by rw [← hx]; rfl
    _ = (rbar.comp φ₀) y := rfl
    _ = y := by rw [h2]; rfl

theorem isUnit_toConv {S A B : Type*} [CommRing S] [CommRing A] [HopfAlgebra S A]
    [CommRing B] [Algebra S B] (f : A →ₐ[S] B) : IsUnit (toConv f) := by
  let Salg : A →ₐ[S] A := AlgHom.ofLinearMap (HopfAlgebra.antipode S) HopfAlgebra.antipode_one
      (fun a b => by rw [HopfAlgebra.antipode_mul, mul_comm])
  have hSalg : ∀ a, Salg a = HopfAlgebra.antipode S a := fun a => rfl
  rw [isUnit_iff_exists]
  refine ⟨toConv (f.comp Salg), ?_, ?_⟩
  · refine WithConv.ext (AlgHom.ext fun c => ?_)
    show (toConv f * toConv (f.comp Salg)) c = (1 : WithConv (A →ₐ[S] B)) c
    rw [AlgHom.convMul_apply, AlgHom.convOne_apply]
    have key : (Algebra.TensorProduct.lift f (f.comp Salg) (fun _ _ => Commute.all _ _)).toLinearMap =
        f.toLinearMap ∘ₗ LinearMap.mul' S A ∘ₗ (HopfAlgebra.antipode S (A := A)).lTensor A := by
      refine TensorProduct.ext' fun x y => ?_
      simp [hSalg]
    have happ := congrArg (fun g : A ⊗[S] A →ₗ[S] B => g (Coalgebra.comul (R := S) c)) key
    simp only [AlgHom.toLinearMap_apply, LinearMap.comp_apply] at happ
    simp only [ofConv_toConv] at happ ⊢
    rw [happ, HopfAlgebra.mul_antipode_lTensor_comul_apply, AlgHom.commutes]
  · refine WithConv.ext (AlgHom.ext fun c => ?_)
    show (toConv (f.comp Salg) * toConv f) c = (1 : WithConv (A →ₐ[S] B)) c
    rw [AlgHom.convMul_apply, AlgHom.convOne_apply]
    have key : (Algebra.TensorProduct.lift (f.comp Salg) f (fun _ _ => Commute.all _ _)).toLinearMap =
        f.toLinearMap ∘ₗ LinearMap.mul' S A ∘ₗ (HopfAlgebra.antipode S (A := A)).rTensor A := by
      refine TensorProduct.ext' fun x y => ?_
      simp [hSalg]
    have happ := congrArg (fun g : A ⊗[S] A →ₗ[S] B => g (Coalgebra.comul (R := S) c)) key
    simp only [AlgHom.toLinearMap_apply, LinearMap.comp_apply] at happ
    simp only [ofConv_toConv] at happ ⊢
    rw [happ, HopfAlgebra.mul_antipode_rTensor_comul_apply, AlgHom.commutes]

theorem ofConv_includeLeft_mul_includeRight {R : Type u} [CommRing R] {H : Type v} [CommRing H] [Bialgebra R H] :
    (toConv (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H) *
      toConv (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H)).ofConv =
      Bialgebra.comulAlgHom R H := by
  rw [AlgHom.convMul_def, ofConv_toConv, ofConv_toConv, ofConv_toConv]
  have key : (Algebra.TensorProduct.lmul' R (S := H ⊗[R] H)).comp
      (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H)
        (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H)) = AlgHom.id R (H ⊗[R] H) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [← AlgHom.comp_assoc, key, AlgHom.id_comp]

theorem ofConv_toConv_comp_mul_toConv_comp {R : Type u} [CommRing R] {H : Type v} [CommRing H] [Bialgebra R H]
    {H' : Type v} [CommRing H'] [Bialgebra R H']
    {T : Type v} [CommRing T] [Algebra R T] (f g : H →ₐ[R] T) (r : H' →ₐ[R] H) :
    (toConv (f.comp r) * toConv (g.comp r)).ofConv =
      ((Algebra.TensorProduct.lmul' R (S := T)).comp (Algebra.TensorProduct.map f g)).comp
        ((Algebra.TensorProduct.map r r).comp (Bialgebra.comulAlgHom R H')) := by
  rw [AlgHom.convMul_def, ofConv_toConv, ofConv_toConv, ofConv_toConv, Algebra.TensorProduct.map_comp]
  simp only [AlgHom.comp_assoc]

noncomputable def powMap (R : Type u) [CommRing R] (H' : Type v) [CommRing H'] [Bialgebra R H'] (n : ℕ) :
    H' →ₐ[R] H' := (toConv (AlgHom.id R H') ^ n).ofConv

section tors
variable {R : Type u} [CommRing R] {H' : Type v} [CommRing H'] [Bialgebra R H']
  {T : Type v} [CommRing T] [Algebra R T]

theorem convOne_eq_toConv_comp (x : H' →ₐ[R] T) :
    (1 : WithConv (H' →ₐ[R] T)) = toConv (x.comp (1 : WithConv (H' →ₐ[R] H')).ofConv) := by
  rw [AlgHom.convOne_def, AlgHom.convOne_def, ofConv_toConv, ← AlgHom.comp_assoc]
  congr 2
  ext

theorem convPow_eq_toConv_comp (x : H' →ₐ[R] T) (n : ℕ) :
    toConv x ^ n = toConv (x.comp (toConv (AlgHom.id R H') ^ n).ofConv) := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact convOne_eq_toConv_comp x
  | succ n ih =>
    rw [pow_succ, pow_succ, AlgHom.comp_convMul_distrib, ofConv_toConv, AlgHom.comp_id, toConv_ofConv, ih]

theorem toConv_pow_eq_one_iff (n : ℕ) (x : H' →ₐ[R] T) :
    toConv x ^ n = 1 ↔ x.comp (powMap R H' n) = x.comp (1 : WithConv (H' →ₐ[R] H')).ofConv := by
  rw [powMap, convPow_eq_toConv_comp, convOne_eq_toConv_comp x]
  exact toConv_injective.eq_iff

end tors

end HopfAlgebra.YonedaTorsion

open HopfAlgebra.YonedaTorsion in
theorem solution
    {R : Type u} [CommRing R] (n : ℕ)
    (H : Type v) [CommRing H] [HopfAlgebra R H]
    (H' : Type v) [CommRing H'] [HopfAlgebra R H']
    (ι : ∀ (T : Type v) [CommRing T] [Algebra R T], (H →ₐ[R] T) → (H' →ₐ[R] T))
    (hnat : ∀ (T T' : Type v) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
      (g : T →ₐ[R] T') (ψ : H →ₐ[R] T), ι T' (g.comp ψ) = g.comp (ι T ψ))
    (hmul : ∀ (T : Type v) [CommRing T] [Algebra R T] (ψ₁ ψ₂ : H →ₐ[R] T),
      ι T (toConv ψ₁ * toConv ψ₂).ofConv = (toConv (ι T ψ₁) * toConv (ι T ψ₂)).ofConv)
    (hinj : ∀ (T : Type v) [CommRing T] [Algebra R T], Function.Injective (ι T))
    (htors : ∀ (T : Type v) [CommRing T] [Algebra R T] (x : H' →ₐ[R] T),
      x ∈ Set.range (ι T) ↔ toConv x ^ n = 1) :
    ∃ π : H' →ₐc[R] H, Function.Surjective π ∧
      ∀ (T : Type v) [CommRing T] [Algebra R T] (ψ : H →ₐ[R] T), ι T ψ = ψ.comp (π : H' →ₐ[R] H) := by
  classical

  let π₀ : H' →ₐ[R] H := ι H (AlgHom.id R H)
  have hchar : ∀ (T : Type v) [CommRing T] [Algebra R T] (ψ : H →ₐ[R] T), ι T ψ = ψ.comp π₀ := by
    intro T _ _ ψ
    have h := hnat H T ψ (AlgHom.id R H)
    rw [AlgHom.comp_id] at h
    exact h

  have hone : ∀ (T : Type v) [CommRing T] [Algebra R T],
      ι T (1 : WithConv (H →ₐ[R] T)).ofConv = (1 : WithConv (H' →ₐ[R] T)).ofConv := by
    intro T _ _
    have h := hmul T (1 : WithConv (H →ₐ[R] T)).ofConv (1 : WithConv (H →ₐ[R] T)).ofConv
    rw [toConv_ofConv, one_mul] at h
    have h' : toConv (ι T (1 : WithConv (H →ₐ[R] T)).ofConv)
        = toConv (ι T (1 : WithConv (H →ₐ[R] T)).ofConv) * toConv (ι T (1 : WithConv (H →ₐ[R] T)).ofConv) := by
      have h1 := congrArg toConv h
      rw [toConv_ofConv] at h1
      exact h1
    obtain ⟨w, hw⟩ := isUnit_toConv (ι T (1 : WithConv (H →ₐ[R] T)).ofConv)
    rw [← hw] at h'
    have h2 : (w : WithConv (H' →ₐ[R] T)) = 1 := by
      have h3 := congrArg (fun z => (↑w⁻¹ : WithConv (H' →ₐ[R] T)) * z) h'
      simp only [Units.inv_mul, ← mul_assoc, one_mul] at h3
      exact h3.symm
    have h4 : ι T (1 : WithConv (H →ₐ[R] T)).ofConv = (toConv (ι T (1 : WithConv (H →ₐ[R] T)).ofConv)).ofConv :=
      (ofConv_toConv _).symm
    rw [h4, ← hw, h2]

  have hcounit : (Bialgebra.counitAlgHom R H).comp π₀ = Bialgebra.counitAlgHom R H' := by
    have h := hone H
    rw [hchar, AlgHom.convOne_def, AlgHom.convOne_def, AlgHom.comp_assoc] at h
    apply AlgHom.ext
    intro x
    have hx := congrArg (fun f : H' →ₐ[R] H => Bialgebra.counitAlgHom R H (f x)) h
    simpa using hx

  have hcomul : (Algebra.TensorProduct.map π₀ π₀).comp (Bialgebra.comulAlgHom R H') =
      (Bialgebra.comulAlgHom R H).comp π₀ := by
    have h1 := hmul (H ⊗[R] H)
      (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H)
      (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H)
    rw [hchar, ofConv_includeLeft_mul_includeRight, hchar, hchar, ofConv_toConv_comp_mul_toConv_comp] at h1
    have key : (Algebra.TensorProduct.lmul' R (S := H ⊗[R] H)).comp
        (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H)
          (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H)) = AlgHom.id R (H ⊗[R] H) := by
      apply Algebra.TensorProduct.ext'
      intro a b
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [key, AlgHom.id_comp] at h1
    exact h1.symm
  let π : H' →ₐc[R] H := BialgHom.ofAlgHom π₀ hcounit hcomul
  have hπ : (π : H' →ₐ[R] H) = π₀ := rfl

  have hsurj : Function.Surjective π₀ := by
    refine surjective_of_forall_injective_comp_of_range_eq_equalizer π₀ (powMap R H' n)
      (1 : WithConv (H' →ₐ[R] H')).ofConv (fun T _ _ => ?_) (fun T _ _ ψ => ?_)
    · intro φ₁ φ₂ hφ
      apply hinj T
      rw [hchar, hchar]
      exact hφ
    · rw [← toConv_pow_eq_one_iff, ← htors T ψ, Set.mem_range]
      constructor
      · rintro ⟨φ, hφ⟩
        exact ⟨φ, by rw [hchar]; exact hφ⟩
      · rintro ⟨φ, hφ⟩
        exact ⟨φ, by rw [← hchar]; exact hφ⟩
  refine ⟨π, ?_, fun T _ _ ψ => ?_⟩
  · rw [show (⇑π) = ⇑π₀ from rfl]
    exact hsurj
  · rw [hπ]
    exact hchar T ψ

end S_HopfAlgebra_exists_bialgHom_surjective_forall_comp_eq_of_natural_injective_of_range_eq_torsion
end P2MW
export P2MW.S_HopfAlgebra_exists_bialgHom_surjective_forall_comp_eq_of_natural_injective_of_range_eq_torsion (solution)
