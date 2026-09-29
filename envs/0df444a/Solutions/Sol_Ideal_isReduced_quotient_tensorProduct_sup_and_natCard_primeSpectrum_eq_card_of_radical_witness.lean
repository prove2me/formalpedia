-- Prove2me | solution 1 for Ideal.isReduced_quotient_tensorProduct_sup_and_natCard_primeSpectrum_eq_card_of_radical_witness
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/3a3105e5-7dd5-5be0-b3a5-01f5ffc4184c

import Mathlib
import Theorems.Thm_IsIntegrallyClosed_height_eq_one_of_mem_associatedPrimes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_isReduced_quotient_tensorProduct_sup_and_natCard_primeSpectrum_eq_card_of_radical_witness

set_option autoImplicit false

open Polynomial TensorProduct

namespace CrossingCount

theorem radical_span_singleton_eq
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (𝔭inf 𝔭zero : Ideal A) [𝔭inf.IsPrime] [𝔭zero.IsPrime] (hinf : 𝔭inf ≠ ⊥)
    (u v : A) (hcover : ∀ 𝔮 : Ideal A, 𝔮.IsPrime → u * v ∈ 𝔮 → 𝔭inf ≤ 𝔮 ∨ 𝔭zero ≤ 𝔮)
    (huzero : u ∈ 𝔭zero) (huinf : u ∉ 𝔭inf) :
    (Ideal.span {u}).radical = 𝔭zero := by
  have hu : u ≠ 0 := by rintro rfl; exact huinf (zero_mem _)
  refine le_antisymm ((Ideal.IsPrime.radical_le_iff inferInstance).mpr
    ((Ideal.span_singleton_le_iff_mem _).mpr huzero)) ?_
  rw [← Ideal.sInf_minimalPrimes]
  refine le_sInf fun 𝔯 h𝔯 => ?_
  haveI h𝔯p : 𝔯.IsPrime := h𝔯.1.1
  have hu𝔯 : u ∈ 𝔯 := h𝔯.1.2 (Ideal.subset_span rfl)

  have hass : 𝔯 ∈ associatedPrimes A (A ⧸ Ideal.span {u}) := by
    apply Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
    rwa [Ideal.annihilator_quotient]
  have hht : 𝔯.height = 1 := IsIntegrallyClosed.height_eq_one_of_mem_associatedPrimes hu 𝔯 hass
  rcases hcover 𝔯 h𝔯p (Ideal.mul_mem_right _ _ hu𝔯) with h | h
  ·
    exfalso
    rcases h.lt_or_eq with hlt | heq
    · have h1 : (⊥ : Ideal A).height + 1 ≤ 𝔭inf.height :=
        Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hinf)
      have h2 : 𝔭inf.height + 1 ≤ 𝔯.height := Ideal.height_add_one_le_of_lt_of_isPrime hlt
      rw [Ideal.height_bot, zero_add] at h1
      rw [hht] at h2
      have h3 : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add h1 le_rfl).trans h2
      exact absurd h3 (by norm_num)
    · exact huinf (heq ▸ hu𝔯)
  · exact h

section poly

variable {K : Type*} [Field K]

theorem ideal_eq_span_prod_X_sub_C
    (I : Ideal K[X]) (h : K[X]) (hh : h.Separable) (hhI : h ∈ I)
    (S : Finset K) (n : K → ℕ) (hn : ∀ a ∈ S, 0 < n a) (c : K) (hc : c ≠ 0)
    (hfI : C c * ∏ a ∈ S, (X - C a) ^ n a ∈ I)
    (hIf : I ≤ (Ideal.span {C c * ∏ a ∈ S, (X - C a) ^ n a}).radical) :
    I = Ideal.span {∏ a ∈ S, (X - C a)} := by
  classical
  set f : K[X] := C c * ∏ a ∈ S, (X - C a) ^ n a with hf
  set P : K[X] := ∏ a ∈ S, (X - C a) with hP
  have hI : Ideal.span {Submodule.IsPrincipal.generator I} = I := Ideal.span_singleton_generator I
  set g : K[X] := Submodule.IsPrincipal.generator I
  rw [← hI] at hhI hfI hIf ⊢
  have hg0 : g ≠ 0 := by
    intro hg
    rw [hg, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at hhI
    exact hh.ne_zero hhI

  have hgh : g ∣ h := Ideal.mem_span_singleton.mp hhI
  have hgsq : Squarefree g := (hh.of_dvd hgh).squarefree
  apply Ideal.span_singleton_eq_span_singleton.mpr
  apply associated_of_dvd_dvd
  ·
    obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ a ∈ S, n a ≤ M :=
      ⟨S.sup n, fun a ha => Finset.le_sup ha⟩
    have hfPM : f ∣ P ^ M := by
      rw [hf, hP, ← Finset.prod_pow]
      refine (IsUnit.mul_left_dvd (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc))).mpr ?_
      exact Finset.prod_dvd_prod_of_dvd _ _ fun a ha => pow_dvd_pow _ (hM a ha)
    have hgPM : g ∣ P ^ M := by
      have hle : Ideal.span {f} ≤ Ideal.span {g} := (Ideal.span_singleton_le_iff_mem _).mpr hfI
      exact Ideal.mem_span_singleton.mp (hle (Ideal.mem_span_singleton.mpr hfPM))
    exact hgsq.isRadical M P hgPM
  ·
    have hgf : g ∈ (Ideal.span {f}).radical := hIf (Ideal.mem_span_singleton_self g)
    obtain ⟨m, hm⟩ := hgf
    have hfgm : f ∣ g ^ m := Ideal.mem_span_singleton.mp hm
    rw [hP]
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro a _ b _ hab
      exact (Polynomial.pairwise_coprime_X_sub_C (K := K) (fun x y hxy => hxy)) hab
    · intro a ha
      have h1 : X - C a ∣ f := by
        rw [hf]
        refine Dvd.dvd.mul_left ?_ _
        exact (dvd_pow_self _ (hn a ha).ne').trans (Finset.dvd_prod_of_mem _ ha)
      exact (Polynomial.prime_X_sub_C a).dvd_of_dvd_pow (h1.trans hfgm)

noncomputable def quotientSpanProdXSubCEquiv (S : Finset K) :
    (K[X] ⧸ Ideal.span {∏ a ∈ S, (X - C a)}) ≃+* (↥S → K) := by
  classical
  have hcop : Pairwise fun a b : ↥S => IsCoprime (X - C (a : K)) (X - C (b : K)) :=
    fun a b hab => Polynomial.pairwise_coprime_X_sub_C (K := K) (fun x y hxy => hxy)
      (fun h => hab (Subtype.ext h))
  have hinf : Ideal.span {∏ a ∈ S, (X - C a)} = ⨅ a : ↥S, Ideal.span {X - C (a : K)} := by
    rw [Ideal.iInf_span_singleton hcop, ← Finset.prod_coe_sort S]
  refine (Ideal.quotEquivOfEq hinf).trans ?_
  refine (Ideal.quotientInfRingEquivPiQuotient _ fun a b hab => ?_).trans ?_
  · exact (Ideal.isCoprime_span_singleton_iff _ _).mpr (hcop hab)
  · exact RingEquiv.piCongrRight fun a => (Polynomial.quotientSpanXSubCAlgEquiv (a : K)).toRingEquiv

theorem isReduced_pi_field (S : Finset K) : IsReduced (↥S → K) := inferInstance

theorem natCard_primeSpectrum_pi_field (S : Finset K) :
    Nat.card (PrimeSpectrum (↥S → K)) = S.card := by
  classical
  rw [← Nat.card_congr (Equiv.ofBijective _ (PrimeSpectrum.sigmaToPi_bijective fun _ : ↥S => K)),
    Nat.card_sigma, Finset.sum_const, smul_eq_mul]
  simp

end poly

section main

variable (p : ℕ) [hp : Fact p.Prime]
  {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CharZero A]
  (𝔭inf 𝔭zero : Ideal A) [𝔭inf.IsPrime] [𝔭zero.IsPrime]
  (hpinf : (p : A) ∈ 𝔭inf)
  (hcover : ∀ 𝔮 : Ideal A, 𝔮.IsPrime → (p : A) ∈ 𝔮 → 𝔭inf ≤ 𝔮 ∨ 𝔭zero ≤ 𝔮)
  (j jp u v : A) (huv : u * v = (p : A) ^ 12) (huzero : u ∈ 𝔭zero) (huinf : u ∉ 𝔭inf)
  {κ : Type*} [Field κ] [CharP κ p]
  (θ : A ⊗[ℤ] κ →+* κ[X]) (hθs : Function.Surjective θ)
  (hθk : RingHom.ker θ =
    𝔭inf.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := κ)))
  (hθj : θ (j ⊗ₜ 1) = X) (hθjp : θ (jp ⊗ₜ 1) = X ^ p)
  (hrel : j - jp ^ p ∈ 𝔭zero)
  (S : Finset κ) (n : κ → ℕ) (hn : ∀ a ∈ S, 0 < n a) (c : κ) (hc : c ≠ 0)
  (hθu : θ (u ⊗ₜ 1) = C c * ∏ a ∈ S, (X - C a) ^ n a)

include hpinf hcover huv huzero huinf in

theorem radical_span_unit_eq :
    (Ideal.span {u}).radical = 𝔭zero := by
  have hp0 : (p : A) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hinf : 𝔭inf ≠ ⊥ := fun h => hp0 (by simpa [h] using hpinf)
  refine radical_span_singleton_eq 𝔭inf 𝔭zero hinf u v (fun 𝔮 h𝔮 huv𝔮 => ?_) huzero huinf
  exact hcover 𝔮 h𝔮 (h𝔮.mem_of_pow_mem 12 (huv ▸ huv𝔮))

include hpinf hcover huv huzero huinf hθj hθjp hrel hn hc hθu in

theorem map_theta_eq_span_prod :
    (𝔭zero.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := κ))).map θ
      = Ideal.span {∏ a ∈ S, (X - C a)} := by
  classical
  set incl := Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := κ) with hincl
  have hincl_apply : ∀ a : A, incl a = a ⊗ₜ (1 : κ) := fun a => rfl
  set Jκ : Ideal κ[X] := (𝔭zero.map incl).map θ with hJκ

  have h1 : (X ^ (p ^ 2) - X : κ[X]) ∈ Jκ := by
    have hval : θ (incl (j - jp ^ p)) = X - X ^ (p ^ 2) := by
      rw [map_sub, map_pow, map_sub, map_pow, hincl_apply, hincl_apply, hθj, hθjp, ← pow_mul, sq]
    have hmem : θ (incl (j - jp ^ p)) ∈ Jκ :=
      Ideal.mem_map_of_mem θ (Ideal.mem_map_of_mem incl hrel)
    rw [hval] at hmem
    simpa using Jκ.neg_mem hmem

  have h2 : C c * ∏ a ∈ S, (X - C a) ^ n a ∈ Jκ := by
    rw [← hθu, ← hincl_apply]
    exact Ideal.mem_map_of_mem θ (Ideal.mem_map_of_mem incl huzero)

  have hrad : (Ideal.span {u}).radical = 𝔭zero :=
    radical_span_unit_eq p 𝔭inf 𝔭zero hpinf hcover u v huv huzero huinf
  have h3 : Jκ ≤ (Ideal.span {C c * ∏ a ∈ S, (X - C a) ^ n a}).radical := by
    rw [← hθu, ← hincl_apply]
    calc Jκ = ((Ideal.span {u}).radical.map incl).map θ := by rw [hrad]
      _ ≤ (((Ideal.span {u}).map incl).radical).map θ := Ideal.map_mono (Ideal.map_radical_le _)
      _ ≤ (((Ideal.span {u}).map incl).map θ).radical := Ideal.map_radical_le _
      _ = (Ideal.span {θ (incl u)}).radical := by
        rw [Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
  have hsep : (X ^ (p ^ 2) - X : κ[X]).Separable :=
    galois_poly_separable p (p ^ 2) (dvd_pow_self p two_ne_zero)
  exact ideal_eq_span_prod_X_sub_C Jκ _ hsep h1 S n hn c hc h2 h3

noncomputable def crossingEquivPi :
    ((A ⊗[ℤ] κ) ⧸
        (𝔭inf.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := κ)) ⊔
         𝔭zero.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := κ))))
      ≃+* (↥S → κ) := by
  classical
  let Iinf := 𝔭inf.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := κ))
  let Izero := 𝔭zero.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := κ))

  let θbar : ((A ⊗[ℤ] κ) ⧸ Iinf) ≃+* κ[X] :=
    (Ideal.quotEquivOfEq hθk.symm).trans (RingHom.quotientKerEquivOfSurjective hθs)
  have hθbar : ∀ x, θbar (Ideal.Quotient.mk Iinf x) = θ x := fun x => by
    change (RingHom.quotientKerEquivOfSurjective hθs)
        ((Ideal.quotEquivOfEq hθk.symm) (Ideal.Quotient.mk Iinf x)) = θ x
    rw [Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
  have hθbar' : θbar.toRingHom.comp (Ideal.Quotient.mk Iinf) = θ := RingHom.ext hθbar
  have hmap : (Izero.map (Ideal.Quotient.mk Iinf)).map θbar.toRingHom
      = Ideal.span {∏ a ∈ S, (X - C a)} := by
    rw [Ideal.map_map, hθbar']
    exact map_theta_eq_span_prod p 𝔭inf 𝔭zero hpinf hcover j jp u v huv huzero huinf θ hθj hθjp
      hrel S n hn c hc hθu
  exact (DoubleQuot.quotQuotEquivQuotSup Iinf Izero).symm.trans <|
    (Ideal.quotientEquiv _ _ θbar hmap.symm).trans (quotientSpanProdXSubCEquiv S)

include hpinf hcover huv huzero huinf hθs hθk hθj hθjp hrel hn hc hθu in

theorem isReduced_and_natCard_primeSpectrum_crossing :
    IsReduced ((A ⊗[ℤ] κ) ⧸
        (𝔭inf.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := κ)) ⊔
         𝔭zero.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := κ)))) ∧
    Nat.card (PrimeSpectrum ((A ⊗[ℤ] κ) ⧸
        (𝔭inf.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := κ)) ⊔
         𝔭zero.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := κ)))))
      = S.card := by
  let e := crossingEquivPi p 𝔭inf 𝔭zero hpinf hcover j jp u v huv huzero huinf θ hθs hθk hθj hθjp
    hrel S n hn c hc hθu
  refine ⟨isReduced_of_injective e e.injective, ?_⟩
  rw [Nat.card_congr (PrimeSpectrum.comapEquiv e).toEquiv]
  exact natCard_primeSpectrum_pi_field S

end main

end CrossingCount

open Polynomial TensorProduct in
universe u v in
theorem solution
    (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CharZero A]
    (𝔭inf 𝔭zero : Ideal A) [𝔭inf.IsPrime] [𝔭zero.IsPrime]
    (hpinf : (p : A) ∈ 𝔭inf)
    (hcover : ∀ 𝔮 : Ideal A, 𝔮.IsPrime → (p : A) ∈ 𝔮 → 𝔭inf ≤ 𝔮 ∨ 𝔭zero ≤ 𝔮)
    (j jp u v : A) (huv : u * v = (p : A) ^ 12) (huzero : u ∈ 𝔭zero) (huinf : u ∉ 𝔭inf)
    (κ : Type v) [Field κ] [CharP κ p]
    (θ : A ⊗[ℤ] κ →+* κ[X]) (hθs : Function.Surjective θ)
    (hθk : RingHom.ker θ =
      𝔭inf.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := κ)))
    (hθj : θ (j ⊗ₜ 1) = X) (hθjp : θ (jp ⊗ₜ 1) = X ^ p)
    (hrel : j - jp ^ p ∈ 𝔭zero)
    (S : Finset κ) (n : κ → ℕ) (hn : ∀ a ∈ S, 0 < n a) (c : κ) (hc : c ≠ 0)
    (hθu : θ (u ⊗ₜ 1) = C c * ∏ a ∈ S, (X - C a) ^ n a) :
    IsReduced ((A ⊗[ℤ] κ) ⧸
        (𝔭inf.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := κ)) ⊔
         𝔭zero.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := κ)))) ∧
    Nat.card (PrimeSpectrum ((A ⊗[ℤ] κ) ⧸
        (𝔭inf.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := κ)) ⊔
         𝔭zero.map (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := κ)))))
      = S.card :=
  CrossingCount.isReduced_and_natCard_primeSpectrum_crossing p 𝔭inf 𝔭zero hpinf hcover j jp u v
    huv huzero huinf θ hθs hθk hθj hθjp hrel S n hn c hc hθu

end S_Ideal_isReduced_quotient_tensorProduct_sup_and_natCard_primeSpectrum_eq_card_of_radical_witness
end P2MW
export P2MW.S_Ideal_isReduced_quotient_tensorProduct_sup_and_natCard_primeSpectrum_eq_card_of_radical_witness (solution)
