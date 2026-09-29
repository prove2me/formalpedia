-- Prove2me | solution 1 for MvPowerSeries.annihilator_ker_eq_span_det
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/0d4acf37-dea1-5b66-9716-1ec9f9de4b0b

import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Colon
import Theorems.Thm_Ideal_colon_span_eq_sup_span_det_of_isWeaklyRegular
import Theorems.Thm_MvPowerSeries_mem_pow_span_X_of_coeff_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_annihilator_ker_eq_span_det

universe u v w x

namespace FrobDictTATE

open Polynomial RingTheory.Sequence
open scoped TensorProduct Pointwise

section RegPoly

variable {S : Type u} [CommRing S]

theorem monic_aeval_X {A : Type v} [CommRing A] [Algebra S A] {p : S[X]} (hp : p.Monic) :
    (aeval (Polynomial.X : A[X]) p).Monic := by
  rw [aeval_X_left_eq_map]
  exact hp.map _

theorem isWeaklyRegular_quotSMulTop_C {A : Type v} [CommRing A] {q : A[X]} (hq : q.Monic)
    {bs : List A} (hbs : IsWeaklyRegular A bs) :
    IsWeaklyRegular (QuotSMulTop q A[X]) (bs.map (algebraMap A A[X])) := by

  haveI : Module.Free A (A[X] ⧸ Ideal.span {q}) := hq.free_adjoinRoot
  have h1 : IsWeaklyRegular ((A[X] ⧸ Ideal.span {q}) ⊗[A] A) bs := hbs.isWeaklyRegular_lTensor
  have h2 : IsWeaklyRegular (A[X] ⧸ Ideal.span {q}) bs :=
    ((TensorProduct.rid A (A[X] ⧸ Ideal.span {q})).isWeaklyRegular_congr bs).mp h1
  have h3 : IsWeaklyRegular (A[X] ⧸ Ideal.span {q}) (bs.map (algebraMap A A[X])) :=
    (isWeaklyRegular_map_algebraMap_iff A[X] _ bs).mpr h2
  have heq : (q • ⊤ : Submodule A[X] A[X]) = Ideal.span {q} := by
    rw [← Submodule.ideal_span_singleton_smul q ⊤, smul_eq_mul, Ideal.mul_top]
  exact ((Submodule.quotEquivOfEq _ _ heq).isWeaklyRegular_congr _).mpr h3

theorem isWeaklyRegular_mvPolynomial (n : ℕ) (p : Fin n → S[X]) (hp : ∀ i, (p i).Monic) :
    IsWeaklyRegular (MvPolynomial (Fin n) S)
      (List.ofFn fun i => aeval (MvPolynomial.X i : MvPolynomial (Fin n) S) (p i)) := by
  induction n with
  | zero => rw [List.ofFn_zero]; exact IsWeaklyRegular.nil _ _
  | succ n ih =>
    let e := MvPolynomial.finSuccEquiv S n

    have key : IsWeaklyRegular (MvPolynomial (Fin n) S)[X]
        ((List.ofFn fun i => aeval (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) S) (p i)).map e) := by
      rw [List.map_ofFn, List.ofFn_succ]
      simp only [Function.comp_apply]
      rw [← aeval_algHom_apply e, MvPolynomial.finSuccEquiv_X_zero]
      have htail : (List.ofFn fun i : Fin n =>
          e (aeval (MvPolynomial.X i.succ : MvPolynomial (Fin (n + 1)) S) (p i.succ))) =
          (List.ofFn fun i : Fin n => aeval (MvPolynomial.X i : MvPolynomial (Fin n) S) (p i.succ)).map
            (algebraMap (MvPolynomial (Fin n) S) (MvPolynomial (Fin n) S)[X]) := by
        rw [List.map_ofFn]
        congr 1
        funext i
        simp only [Function.comp_apply]
        rw [← aeval_algHom_apply e, MvPolynomial.finSuccEquiv_X_succ, Polynomial.C_eq_algebraMap]
        simpa using (aeval_algHom_apply (IsScalarTower.toAlgHom S (MvPolynomial (Fin n) S)
          (MvPolynomial (Fin n) S)[X]) (MvPolynomial.X i) (p i.succ))
      rw [htail, isWeaklyRegular_cons_iff]
      refine ⟨(monic_aeval_X (hp 0)).isRegular.left.isSMulRegular, ?_⟩
      exact isWeaklyRegular_quotSMulTop_C (monic_aeval_X (hp 0)) (ih (fun i => p i.succ) fun i => hp _)
    refine (e.toAddEquiv.isWeaklyRegular_congr ?_).mpr key
    exact List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun r _ x => map_mul e r x)

end RegPoly

end FrobDictTATE

namespace FrobDictTATE

open Polynomial RingTheory.Sequence MvPowerSeries
open scoped TensorProduct Pointwise

section RegPS

variable {𝒪 : Type u} [CommRing 𝒪] [IsNoetherianRing 𝒪]

scoped instance flat_mvPowerSeries (n : ℕ) :
    Module.Flat (MvPolynomial (Fin n) 𝒪) (MvPowerSeries (Fin n) 𝒪) :=
  Module.Flat.of_linearEquiv (MvPowerSeries.toAdicCompletionAlgEquiv (Fin n) 𝒪).toLinearEquiv

theorem isWeaklyRegular_mvPowerSeries (n : ℕ) (p : Fin n → 𝒪[X]) (hp : ∀ i, (p i).Monic) :
    IsWeaklyRegular (MvPowerSeries (Fin n) 𝒪)
      (List.ofFn fun i => aeval (MvPowerSeries.X i : MvPowerSeries (Fin n) 𝒪) (p i)) := by
  set Q := MvPolynomial (Fin n) 𝒪
  set P := MvPowerSeries (Fin n) 𝒪
  have h1 := isWeaklyRegular_mvPolynomial n p hp
  have h2 : IsWeaklyRegular (P ⊗[Q] Q) _ := h1.isWeaklyRegular_lTensor
  have h3 := ((TensorProduct.rid Q P).isWeaklyRegular_congr _).mp h2
  have h4 := (isWeaklyRegular_map_algebraMap_iff P _ _).mpr h3
  rw [List.map_ofFn] at h4
  convert h4 using 2
  funext i
  simp only [Function.comp_apply]
  have hX : algebraMap Q P (MvPolynomial.X i) = MvPowerSeries.X i := by
    rw [MvPowerSeries.algebraMap_apply', MvPolynomial.coe_X, Algebra.algebraMap_self, MvPowerSeries.map_id,
      RingHom.id_apply]
  rw [← hX]
  exact aeval_algHom_apply (IsScalarTower.toAlgHom 𝒪 Q P) (MvPolynomial.X i) (p i)

end RegPS

section CayleyHamilton

variable {𝒪 : Type u} [CommRing 𝒪] {n : ℕ}

theorem aeval_X_charpoly_mem (J : Ideal (MvPowerSeries (Fin n) 𝒪))
    [Module.Finite 𝒪 (MvPowerSeries (Fin n) 𝒪 ⧸ J)] [Module.Free 𝒪 (MvPowerSeries (Fin n) 𝒪 ⧸ J)]
    (i : Fin n) :
    aeval (MvPowerSeries.X i : MvPowerSeries (Fin n) 𝒪)
      (Algebra.lmul 𝒪 _ (Ideal.Quotient.mk J (MvPowerSeries.X i))).charpoly ∈ J := by
  set T := MvPowerSeries (Fin n) 𝒪 ⧸ J
  set L := Algebra.lmul 𝒪 T (Ideal.Quotient.mk J (MvPowerSeries.X i)) with hL
  have h0 : aeval L L.charpoly = 0 := L.aeval_self_charpoly
  rw [hL, aeval_algHom_apply (Algebra.lmul 𝒪 T), ← hL] at h0
  have h1 : aeval (Ideal.Quotient.mk J (MvPowerSeries.X i)) L.charpoly = 0 := by
    have := congr($h0 1)
    simpa using this
  rw [← Ideal.Quotient.mkₐ_eq_mk 𝒪, aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk] at h1
  exact Ideal.Quotient.eq_zero_iff_mem.mp h1

end CayleyHamilton

section Main

variable {𝒪 : Type u} [CommRing 𝒪] [IsNoetherianRing 𝒪]

local notation "P" n => MvPowerSeries (Fin n) 𝒪

omit [IsNoetherianRing 𝒪] in
theorem mem_span_X_iff {n : ℕ} (q : MvPowerSeries (Fin n) 𝒪) :
    q ∈ Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) 𝒪)) ↔
      MvPowerSeries.constantCoeff q = 0 := by
  constructor
  · intro hq
    have hle : Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) 𝒪)) ≤
        RingHom.ker MvPowerSeries.constantCoeff :=
      Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact MvPowerSeries.constantCoeff_X i)
    exact hle hq
  · intro hq
    have h := MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero 1 q (fun m hm => by
      have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).mp (by omega)
      subst hm0
      rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply])
    rwa [pow_one] at h

omit [IsNoetherianRing 𝒪] in

theorem annihilator_map_mk_eq {A : Type v} [CommRing A] (J I : Ideal A) :
    ((I.map (Ideal.Quotient.mk J)).annihilator : Ideal (A ⧸ J)) =
      (J.colon (I : Set A)).map (Ideal.Quotient.mk J) := by
  ext t
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective t
  rw [Submodule.mem_annihilator, Ideal.mem_quotient_iff_mem_sup,
    sup_eq_left.mpr (Ideal.le_colon (I := J) (S := (I : Set A))), Submodule.mem_colon]
  constructor
  · intro h r hr
    rw [smul_eq_mul, ← Ideal.Quotient.eq_zero_iff_mem, map_mul]
    exact h _ (Ideal.mem_map_of_mem _ hr)
  · intro h s hs
    obtain ⟨r, hr, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hs
    rw [smul_eq_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact h r hr

theorem main (n : ℕ) (g : Matrix (Fin n) (Fin n) (MvPowerSeries (Fin n) 𝒪))
    (f : Fin n → MvPowerSeries (Fin n) 𝒪) (hf : ∀ i, f i = ∑ j, g i j * MvPowerSeries.X j)
    [Module.Finite 𝒪 (MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f))]
    [Module.Free 𝒪 (MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f))]
    (π : (MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f)) →ₐ[𝒪] 𝒪)
    (hπ : (π : _ →+* 𝒪).comp (Ideal.Quotient.mk (Ideal.span (Set.range f))) =
      MvPowerSeries.constantCoeff) :
    (RingHom.ker π).annihilator =
        Ideal.span {Ideal.Quotient.mk (Ideal.span (Set.range f)) g.det} ∧
      (RingHom.ker π).annihilator.map π =
        Ideal.span {(g.map MvPowerSeries.constantCoeff).det} := by
  classical
  have hπ' : ∀ q, π (Ideal.Quotient.mk _ q) = MvPowerSeries.constantCoeff q := fun q => by
    have := RingHom.congr_fun hπ q
    simpa using this

  have hJI : Ideal.span (Set.range f) ≤
      Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) 𝒪)) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [hf i]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

  have hker : RingHom.ker π = (Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) 𝒪))).map
      (Ideal.Quotient.mk (Ideal.span (Set.range f))) := by
    ext t
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective t
    rw [RingHom.mem_ker, hπ', ← mem_span_X_iff, Ideal.mem_quotient_iff_mem_sup, sup_eq_left.mpr hJI]

  let p : Fin n → 𝒪[X] := fun i =>
    (Algebra.lmul 𝒪 _ (Ideal.Quotient.mk (Ideal.span (Set.range f)) (MvPowerSeries.X i))).charpoly
  have hy : ∃ y : Fin n → MvPowerSeries (Fin n) 𝒪, IsWeaklyRegular (MvPowerSeries (Fin n) 𝒪) (List.ofFn y) ∧
      ∀ i, y i ∈ Ideal.span (Set.range f) :=
    ⟨fun i => aeval (MvPowerSeries.X i) (p i), isWeaklyRegular_mvPowerSeries n p fun i =>
      LinearMap.charpoly_monic _, fun i => aeval_X_charpoly_mem _ i⟩

  obtain ⟨hcolon, -⟩ := Ideal.colon_span_eq_sup_span_det_of_isWeaklyRegular MvPowerSeries.X f g hf hy
  have hann : (RingHom.ker π).annihilator =
      Ideal.span {Ideal.Quotient.mk (Ideal.span (Set.range f)) g.det} := by
    rw [hker, annihilator_map_mk_eq, hcolon, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span,
      Set.image_singleton]
  refine ⟨hann, ?_⟩
  rw [hann, Ideal.map_span, Set.image_singleton, hπ', RingHom.map_det, RingHom.mapMatrix_apply]

end Main

end FrobDictTATE
p2m_reactivate "P2MW.S_MvPowerSeries_annihilator_ker_eq_span_det.FrobDictTATE"

open FrobDictTATE in
theorem solution
    {𝒪 : Type u} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (n : ℕ) (g : Matrix (Fin n) (Fin n) (MvPowerSeries (Fin n) 𝒪))
    (f : Fin n → MvPowerSeries (Fin n) 𝒪) (hf : ∀ i, f i = ∑ j, g i j * MvPowerSeries.X j)
    [Module.Finite 𝒪 (MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f))]
    [Module.Free 𝒪 (MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f))]
    (π : (MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f)) →ₐ[𝒪] 𝒪)
    (hπ : (π : _ →+* 𝒪).comp (Ideal.Quotient.mk (Ideal.span (Set.range f))) =
      MvPowerSeries.constantCoeff) :
    (RingHom.ker π).annihilator =
        Ideal.span {Ideal.Quotient.mk (Ideal.span (Set.range f)) g.det} ∧
      (RingHom.ker π).annihilator.map π =
        Ideal.span {(g.map MvPowerSeries.constantCoeff).det} :=
  main n g f hf π hπ

end S_MvPowerSeries_annihilator_ker_eq_span_det
end P2MW
export P2MW.S_MvPowerSeries_annihilator_ker_eq_span_det (solution)
