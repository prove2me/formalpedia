-- Prove2me | solution 1 for HopfAlgebra.isReduced_cartierDual_of_bijective_tensorProduct_isReduced_cartierDual_of_bijective_tensorProduct_comul_zmodp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/82b51c09-c10a-5544-9fee-99649307a886

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_HopfAlgebra_CartierDualMap
import Theorems.Thm_Deformation_DieudonneModule_exists_addEquiv_prod_apply_eq_map_of_tensorProduct
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_isReduced_cartierDual_of_bijective_tensorProduct_isReduced_cartierDual_of_bijective_tensorProduct_comul_zmodp

set_option autoImplicit false

open scoped TensorProduct

universe v

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

namespace OrdConn

theorem exists_mul_mul_eq_self {E : Type*} [CommRing E] [IsArtinianRing E] [IsReduced E] (x : E) :
    ∃ t : E, x * x * t = x := by
  classical
  let φ := IsArtinianRing.equivPi E

  have hF : ∀ I : MaximalSpectrum E, IsField (E ⧸ I.asIdeal) := fun I =>
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient I.asIdeal).mp I.isMaximal
  let s : ∀ I : MaximalSpectrum E, E ⧸ I.asIdeal := fun I =>
    if h : φ x I = 0 then 0 else Classical.choose ((hF I).mul_inv_cancel h)
  have hs : ∀ I, φ x I * φ x I * s I = φ x I := by
    intro I
    by_cases h : φ x I = 0
    · simp [s, h]
    · have := Classical.choose_spec ((hF I).mul_inv_cancel h)
      simp only [s, dif_neg h]
      rw [mul_assoc, this, mul_one]
  refine ⟨φ.symm s, φ.injective ?_⟩
  funext I
  rw [map_mul, map_mul, AlgEquiv.apply_symm_apply, Pi.mul_apply, Pi.mul_apply]
  exact hs I

theorem eq_zero_or_eq_one_of_isIdempotentElem {R : Type*} [CommRing R] [IsLocalRing R] {e : R}
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with hu | hu
  · right
    obtain ⟨u, rfl⟩ := hu
    have : (u : R) * u = u := he.eq
    calc (u : R) = (u : R) * u * ↑u⁻¹ := by rw [Units.mul_inv_cancel_right]
      _ = 1 := by rw [this, Units.mul_inv]
  · left
    have h1 : IsIdempotentElem (1 - e) := he.one_sub
    obtain ⟨u, hu⟩ := hu
    have : (1 - e) = 1 := by
      have h2 : (u : R) * u = u := by rw [hu]; exact h1.eq
      calc (1 - e) = (u : R) := hu.symm
        _ = (u : R) * u * ↑u⁻¹ := by rw [Units.mul_inv_cancel_right]
        _ = 1 := by rw [h2, Units.mul_inv]
    have := congrArg (fun y => 1 - y) this
    simpa using this

theorem algHom_apply_eq_algebraMap {k : Type*} [Field k] {E : Type*} [CommRing E] [Algebra k E]
    [Module.Finite k E] [IsReduced E] {C : Type*} [CommRing C] [Algebra k C] [Module.Finite k C]
    [IsLocalRing C] (χ : C →ₐ[k] k) (ψ : E →ₐ[k] C) (e : E) :
    ψ e = algebraMap k C (χ (ψ e)) := by
  classical
  haveI : IsArtinianRing E := IsArtinianRing.of_finite k E
  haveI : IsArtinianRing C := IsArtinianRing.of_finite k C
  set c : k := χ (ψ e) with hc
  set e' : E := e - algebraMap k E c with he'

  have hχsurj : Function.Surjective χ := fun a => ⟨algebraMap k C a, by simp⟩
  have hker : RingHom.ker (χ : C →+* k) = IsLocalRing.maximalIdeal C :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective (χ : C →+* k) hχsurj)
  have hz : ψ e' ∈ IsLocalRing.maximalIdeal C := by
    rw [← hker, RingHom.mem_ker]
    simp [he', hc]
  have hznil : IsNilpotent (ψ e') := by
    obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := C)
    have hmem : ψ e' ∈ (⊥ : Ideal C).jacobson := IsLocalRing.maximalIdeal_le_jacobson _ hz
    refine ⟨N, ?_⟩
    have : ψ e' ^ N ∈ (⊥ : Ideal C).jacobson ^ N := Ideal.pow_mem_pow hmem N
    rw [hN] at this
    simpa using this

  obtain ⟨t, ht⟩ := exists_mul_mul_eq_self e'
  have hf : IsIdempotentElem (e' * t) := by
    change e' * t * (e' * t) = e' * t
    calc e' * t * (e' * t) = (e' * e' * t) * t := by ring
      _ = e' * t := by rw [ht]
  have hef : e' * (e' * t) = e' := by rw [← mul_assoc, ht]

  rcases eq_zero_or_eq_one_of_isIdempotentElem (hf.map ψ) with h0 | h1
  · have : ψ e' = 0 := by rw [← hef, map_mul, h0, mul_zero]
    have : ψ e - algebraMap k C c = 0 := by simpa [he'] using this
    exact sub_eq_zero.1 this
  · exfalso
    have hunit : IsUnit (ψ e') := IsUnit.of_mul_eq_one (ψ t) (by rw [← map_mul, h1])
    obtain ⟨N, hN⟩ := hznil
    have := (hunit.pow N)
    rw [hN] at this
    exact not_isUnit_zero this

end OrdConn

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type v} [CommRing B] [HopfAlgebra (ZMod p) B]
    [Coalgebra.IsCocomm (ZMod p) B] [Module.Finite (ZMod p) B]
    {Bc : Type v} [CommRing Bc] [HopfAlgebra (ZMod p) Bc] [Module.Finite (ZMod p) Bc]
    {Be : Type v} [CommRing Be] [HopfAlgebra (ZMod p) Be] [Module.Finite (ZMod p) Be]
    (qc : B →ₐc[ZMod p] Bc) (πe : B →ₐc[ZMod p] Be) (σ : Be →ₐc[ZMod p] B)
    (Θ : B →ₐc[ZMod p] Bc ⊗[ZMod p] Be)
    (hqc : Function.Surjective qc) (hπe : Function.Surjective πe)
    (hker_πe : RingHom.ker (πe : B →ₐ[ZMod p] Be) = nilradical B)
    (hσ : πe.comp σ = BialgHom.id (ZMod p) Be)
    (hunr : Algebra.FormallyUnramified (ZMod p) Be)
    (hker_qc : RingHom.ker (qc : B →ₐ[ZMod p] Bc) =
      Ideal.map (σ : Be →ₐ[ZMod p] B) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) Be)))
    (hΘ : ∀ b : B, Θ b = Algebra.TensorProduct.map (qc : B →ₐ[ZMod p] Bc) (πe : B →ₐ[ZMod p] Be)
      (Coalgebra.comul (R := ZMod p) b))
    (hBc : IsLocalRing Bc)
    (hord : ∃ (M : Type v) (_ : CommRing M) (_ : HopfAlgebra (ZMod p) M) (_ : Module.Finite (ZMod p) M)
        (_ : Module.Free (ZMod p) M) (E : Type v) (_ : CommRing E) (_ : HopfAlgebra (ZMod p) E)
        (Θ : B →ₐc[ZMod p] M ⊗[ZMod p] E),
        Function.Bijective Θ ∧ IsReduced E ∧ IsReduced (CartierDual (ZMod p) M)) :
    IsReduced (CartierDual (ZMod p) Bc) := by

  classical
  obtain ⟨M, _, _, _, _, E, _, _, Θ', hΘ', hEred, hMred⟩ := hord
  haveI := hBc

  set Θe : B ≃ₐc[ZMod p] M ⊗[ZMod p] E := BialgEquiv.ofBijective Θ' hΘ' with hΘe
  obtain ⟨i₁, i₂, q₁, q₂, hi₁, hi₂, -, -, -⟩ :=
    Deformation.DieudonneModule.exists_addEquiv_prod_apply_eq_map_of_tensorProduct p M E

  set ι : M ⊗[ZMod p] E →ₐc[ZMod p] B := (Θe.symm : M ⊗[ZMod p] E →ₐc[ZMod p] B) with hι
  have hιsurj : Function.Surjective ι := fun b => ⟨Θe b, Θe.symm_apply_apply b⟩
  set φ : M →ₐc[ZMod p] Bc := (qc.comp ι).comp i₁ with hφ
  set ψ : E →ₐc[ZMod p] Bc := (qc.comp ι).comp i₂ with hψ

  haveI : Nontrivial M := by
    rcases subsingleton_or_nontrivial M with hM | hM
    ·
      exfalso
      haveI := hM
      have h1 : (1 : B) = 0 := by
        apply Θe.injective
        exact Subsingleton.elim _ _
      exact one_ne_zero (congrArg (Coalgebra.counit (R := ZMod p) (A := B)) h1 |>.trans (map_zero _) |>.symm.trans
        (by rw [Bialgebra.counit_one]) |>.symm)
    · exact hM
  haveI : Module.Finite (ZMod p) E := by
    have hinj : Function.Injective (Algebra.TensorProduct.includeRight : E →ₐ[ZMod p] M ⊗[ZMod p] E) :=
      Algebra.TensorProduct.includeRight_injective (RingHom.injective _)
    have hinj' : Function.Injective ((ι : M ⊗[ZMod p] E →ₐ[ZMod p] B).toLinearMap ∘ₗ
        (Algebra.TensorProduct.includeRight : E →ₐ[ZMod p] M ⊗[ZMod p] E).toLinearMap) :=
      Θe.symm.injective.comp hinj
    exact Module.Finite.of_injective _ hinj'

  have hψ : ∀ e : E, ψ e = algebraMap (ZMod p) Bc (Coalgebra.counit (R := ZMod p) e) := by
    intro e
    have := OrdConn.algHom_apply_eq_algebraMap (Bialgebra.counitAlgHom (ZMod p) Bc) (ψ : E →ₐ[ZMod p] Bc) e
    rw [Bialgebra.counitAlgHom_apply] at this
    rw [show (ψ : E →ₐ[ZMod p] Bc) e = ψ e from rfl, CoalgHomClass.counit_comp_apply] at this
    exact this

  have hφsurj : Function.Surjective φ := by
    intro x
    obtain ⟨b, rfl⟩ := hqc x
    obtain ⟨w, rfl⟩ := hιsurj b
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul m e =>
      refine ⟨Coalgebra.counit (R := ZMod p) e • m, ?_⟩
      have hme : m ⊗ₜ[ZMod p] e = (i₁ m) * (i₂ e) := by
        rw [show (i₁ m : M ⊗[ZMod p] E) = (i₁ : M →ₐ[ZMod p] M ⊗[ZMod p] E) m from rfl, hi₁,
          show (i₂ e : M ⊗[ZMod p] E) = (i₂ : E →ₐ[ZMod p] M ⊗[ZMod p] E) e from rfl, hi₂]
        simp [Algebra.TensorProduct.tmul_mul_tmul]
      rw [hme, map_mul, map_mul, map_smul, Algebra.smul_def, show qc (ι (i₂ e)) = ψ e from rfl, hψ e,
        mul_comm]
      rfl
    | add w₁ w₂ ih₁ ih₂ =>
      obtain ⟨m₁, h₁⟩ := ih₁
      obtain ⟨m₂, h₂⟩ := ih₂
      exact ⟨m₁ + m₂, by rw [map_add, h₁, h₂, map_add, map_add]⟩

  have hinj : Function.Injective (CartierDual.map φ) := by
    refine (injective_iff_map_eq_zero _).2 fun u hu => ?_
    apply DFunLike.ext
    intro x
    obtain ⟨m, rfl⟩ := hφsurj x
    have := congrArg (fun v : CartierDual (ZMod p) M => v m) hu
    simp [CartierDual.map_apply] at this
    exact this
  exact isReduced_of_injective (CartierDual.map φ) hinj

end S_HopfAlgebra_isReduced_cartierDual_of_bijective_tensorProduct_isReduced_cartierDual_of_bijective_tensorProduct_comul_zmodp
end P2MW
export P2MW.S_HopfAlgebra_isReduced_cartierDual_of_bijective_tensorProduct_isReduced_cartierDual_of_bijective_tensorProduct_comul_zmodp (solution)
