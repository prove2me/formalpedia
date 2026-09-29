-- Prove2me | solution 1 for Ideal.natCast_le_ringKrullDim_quotient_of_mem_minimalPrimes_map_of_algebraicIndependent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/6ecc7aa5-7f25-5ef6-8a1c-2693dcf6b83c

import Mathlib
import Theorems.Thm_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_natCast_le_ringKrullDim_quotient_of_mem_minimalPrimes_map_of_algebraicIndependent

set_option autoImplicit false

universe u v w

namespace P2mFibDim

open Ideal

private lemma exists_ltSeries_comap_eq_last {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S))
    (l : LTSeries (PrimeSpectrum R)) :
    ∃ L : LTSeries (PrimeSpectrum S), L.length = l.length ∧
      PrimeSpectrum.comap (algebraMap R S) L.last = l.last := by
  haveI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  induction l using RelSeries.inductionOn' with
  | singleton x =>
    obtain ⟨q, hq⟩ := Algebra.IsIntegral.comap_surjective R S x
    exact ⟨RelSeries.singleton _ q, rfl, hq⟩
  | snoc l x hx ih =>
    obtain ⟨L, hlen, hlast⟩ := ih
    have hle : L.last.asIdeal.comap (algebraMap R S) ≤ x.asIdeal := by
      have h1 : PrimeSpectrum.comap (algebraMap R S) L.last ≤ x := hlast ▸ le_of_lt hx
      exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr h1
    obtain ⟨Q, hQge, hQprime, hQcomap⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral x.asIdeal L.last.asIdeal hle
    have hlx : l.last < x := hx
    have hQlt : L.last < (⟨Q, hQprime⟩ : PrimeSpectrum S) := by
      refine lt_of_le_of_ne ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hQge) ?_
      intro h
      refine absurd ?_ (ne_of_lt hlx)
      calc l.last = PrimeSpectrum.comap (algebraMap R S) L.last := hlast.symm
        _ = PrimeSpectrum.comap (algebraMap R S) ⟨Q, hQprime⟩ := by rw [h]
        _ = x := PrimeSpectrum.ext hQcomap
    refine ⟨L.snoc ⟨Q, hQprime⟩ hQlt, by simp [hlen], ?_⟩
    simp only [RelSeries.last_snoc]
    exact PrimeSpectrum.ext hQcomap

theorem ringKrullDim_le_of_isIntegral_of_injective {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S)) :
    ringKrullDim R ≤ ringKrullDim S := by
  change Order.krullDim (PrimeSpectrum R) ≤ Order.krullDim (PrimeSpectrum S)
  refine iSup_le fun l => ?_
  obtain ⟨L, hlen, -⟩ := exists_ltSeries_comap_eq_last hinj l
  rw [← hlen]
  exact Order.LTSeries.length_le_krullDim L

theorem ringKrullDim_localization_le {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] : ringKrullDim S ≤ ringKrullDim R := by
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) ?_
  refine Monotone.strictMono_of_injective ?_ (PrimeSpectrum.localization_comap_injective S M)
  intro a b hab
  exact Ideal.comap_mono hab

lemma exists_nat_eq {x : WithBot ℕ∞} {n : ℕ} (h0 : 0 ≤ x) (h : x ≤ n) : ∃ a : ℕ, x = a := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h0 (by simp)
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      have : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ (n : ℕ∞) := h
      exact absurd (WithBot.coe_le_coe.mp this) (by simp)
    | coe a => exact ⟨a, rfl⟩

section Main

variable (k : Type u) [Field k] {R : Type v} {C : Type w} [CommRing R] [IsDomain R] [Algebra k R]
  [Algebra.FiniteType k R] [CommRing C] [IsDomain C] [Algebra k C] [Algebra R C]
  [IsScalarTower k R C] [Algebra.FiniteType R C]

theorem exists_ringKrullDim_eq_natCast (A : Type*) [CommRing A]
    [Nontrivial A] [Algebra k A] [Algebra.FiniteType k A] : ∃ n : ℕ, ringKrullDim A = n := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  letI : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨RingHom.Finite.to_isIntegral hfin⟩
  have h1 : ringKrullDim A ≤ ringKrullDim (MvPolynomial (Fin s) k) := by
    change Order.krullDim (PrimeSpectrum A) ≤ Order.krullDim (PrimeSpectrum (MvPolynomial (Fin s) k))
    refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap _ A)) ?_
    intro q1 q2 hlt
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
    obtain ⟨y, hy2, hy1⟩ := SetLike.exists_of_lt ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr hlt)
    exact Ideal.comap_lt_comap_of_integral_mem_sdiff
      ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hlt.le) ⟨hy2, hy1⟩
      (Algebra.IsIntegral.isIntegral y)
  have h2 : ringKrullDim (MvPolynomial (Fin s) k) = s := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [h2] at h1
  exact exists_nat_eq (ringKrullDim_nonneg_of_nontrivial) h1

include k in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 6400000 in

theorem ringKrullDim_localization_add_le
    {d : ℕ} (z : Fin d → C) (hz : AlgebraicIndependent R z) (r : R) (hr : r ≠ 0)
    (hint : ∀ c : C, ∃ n : ℕ, IsIntegral (Algebra.adjoin R (Set.range z)) (r ^ n • c)) :
    ringKrullDim (Localization.Away r) + d ≤ ringKrullDim C := by
  classical
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  have hrC : algebraMap R C r ≠ 0 := (map_ne_zero_iff _ hz.algebraMap_injective).mpr hr
  haveI : IsDomain (Localization.Away (algebraMap R C r)) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hrC)
  let f : Localization.Away r →+* Localization.Away (algebraMap R C r) :=
    IsLocalization.Away.map (Localization.Away r) (Localization.Away (algebraMap R C r)) (algebraMap R C) r
  letI : Algebra (Localization.Away r) (Localization.Away (algebraMap R C r)) := f.toAlgebra
  have hf : ∀ x : R, algebraMap (Localization.Away r) (Localization.Away (algebraMap R C r))
      (algebraMap R (Localization.Away r) x) =
      algebraMap C (Localization.Away (algebraMap R C r)) (algebraMap R C x) := by
    intro x
    change f _ = _
    exact IsLocalization.map_eq _ _
  haveI : IsScalarTower R (Localization.Away r) (Localization.Away (algebraMap R C r)) :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      rw [hf, ← IsScalarTower.algebraMap_apply])

  let ψ : MvPolynomial (Fin d) (Localization.Away r) →ₐ[Localization.Away r]
      Localization.Away (algebraMap R C r) :=
    MvPolynomial.aeval fun i => algebraMap C (Localization.Away (algebraMap R C r)) (z i)
  have hψC : ∀ y : Localization.Away r, ψ (MvPolynomial.C y) =
      algebraMap (Localization.Away r) (Localization.Away (algebraMap R C r)) y := fun y =>
    MvPolynomial.algHom_C ψ y
  have hψ : ∀ q : MvPolynomial (Fin d) R,
      ψ (MvPolynomial.map (algebraMap R (Localization.Away r)) q) =
        algebraMap C (Localization.Away (algebraMap R C r)) (MvPolynomial.aeval z q) := by
    intro q
    rw [MvPolynomial.aeval_map_algebraMap]
    rw [← MvPolynomial.aeval_algebraMap_apply]
    rfl

  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    letI : Algebra (MvPolynomial (Fin d) R) (MvPolynomial (Fin d) (Localization.Away r)) :=
      MvPolynomial.algebraMvPolynomial
    haveI hloc := MvPolynomial.isLocalization (σ := Fin d) (Submonoid.powers r) (Localization.Away r)
    obtain ⟨⟨q₀, s⟩, hqs⟩ := IsLocalization.surj
      ((Submonoid.powers r).map (MvPolynomial.C : R →+* MvPolynomial (Fin d) R)) q
    have hqs' : q * MvPolynomial.map (algebraMap R (Localization.Away r)) s =
        MvPolynomial.map (algebraMap R (Localization.Away r)) q₀ := hqs
    have h1 : ψ (MvPolynomial.map (algebraMap R (Localization.Away r)) q₀) = 0 := by
      rw [← hqs', map_mul, hq, zero_mul]
    rw [hψ] at h1
    obtain ⟨⟨_, m, rfl⟩, hm⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap R C r))
        (Localization.Away (algebraMap R C r)) _).mp h1
    have h2 : MvPolynomial.aeval z q₀ = 0 := by
      rcases mul_eq_zero.mp hm with h | h
      · exact absurd h (pow_ne_zero _ hrC)
      · exact h
    have h3 : q₀ = 0 := hz (by rw [h2, map_zero])
    have h4 : q * MvPolynomial.map (algebraMap R (Localization.Away r)) s = 0 := by
      rw [hqs', h3, map_zero]
    have hsunit : IsUnit (MvPolynomial.map (algebraMap R (Localization.Away r)) (s : MvPolynomial (Fin d) R)) :=
      IsLocalization.map_units (M := (Submonoid.powers r).map (MvPolynomial.C : R →+* MvPolynomial (Fin d) R))
        (MvPolynomial (Fin d) (Localization.Away r)) s
    exact (hsunit.mul_left_eq_zero).mp h4

  letI : Algebra (MvPolynomial (Fin d) (Localization.Away r)) (Localization.Away (algebraMap R C r)) :=
    ψ.toRingHom.toAlgebra
  have halg : ∀ t, algebraMap (MvPolynomial (Fin d) (Localization.Away r))
      (Localization.Away (algebraMap R C r)) t = ψ t := fun _ => rfl

  have hrange : ∀ a ∈ Algebra.adjoin R (Set.range z),
      algebraMap C (Localization.Away (algebraMap R C r)) a ∈ ψ.range := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨MvPolynomial.X i, by simp [ψ]⟩
    | algebraMap x =>
      refine ⟨MvPolynomial.C (algebraMap R (Localization.Away r) x), ?_⟩
      change ψ (MvPolynomial.C _) = _
      rw [hψC, hf, ← IsScalarTower.algebraMap_apply]
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

  have hunitR : IsUnit (algebraMap R (Localization.Away r) r) := IsLocalization.Away.algebraMap_isUnit r
  have hintC : ∀ c : C, IsIntegral (MvPolynomial (Fin d) (Localization.Away r))
      (algebraMap C (Localization.Away (algebraMap R C r)) c) := by
    intro c
    obtain ⟨n, P, hPm, hP⟩ := hint c

    let P₂ : Polynomial (Localization.Away (algebraMap R C r)) :=
      P.map ((algebraMap C (Localization.Away (algebraMap R C r))).comp
        (algebraMap (Algebra.adjoin R (Set.range z)) C))
    have hP₂m : P₂.Monic := hPm.map _
    have hP₂ : P₂.eval (algebraMap C (Localization.Away (algebraMap R C r)) (r ^ n • c)) = 0 := by
      rw [Polynomial.eval_map, ← Polynomial.hom_eval₂, hP, map_zero]
    have hlift : P₂ ∈ Polynomial.lifts (algebraMap (MvPolynomial (Fin d) (Localization.Away r))
        (Localization.Away (algebraMap R C r))) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro j
      rw [Polynomial.coeff_map, RingHom.comp_apply]
      obtain ⟨t, ht⟩ := hrange _ (P.coeff j).2
      exact ⟨t, ht⟩
    obtain ⟨Q, hQ, -, hQm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hP₂m
    have hint1 : IsIntegral (MvPolynomial (Fin d) (Localization.Away r))
        (algebraMap C (Localization.Away (algebraMap R C r)) (r ^ n • c)) := by
      refine ⟨Q, hQm, ?_⟩
      rw [Polynomial.eval₂_eq_eval_map, hQ]
      exact hP₂

    obtain ⟨u, hu⟩ := hunitR
    have hru : algebraMap C (Localization.Away (algebraMap R C r)) (algebraMap R C r) =
        algebraMap (Localization.Away r) (Localization.Away (algebraMap R C r)) u := by
      rw [hu, hf]
    have heq : algebraMap C (Localization.Away (algebraMap R C r)) c =
        algebraMap (MvPolynomial (Fin d) (Localization.Away r)) (Localization.Away (algebraMap R C r))
          (MvPolynomial.C (↑(u⁻¹ ^ n) : Localization.Away r)) *
        algebraMap C (Localization.Away (algebraMap R C r)) (r ^ n • c) := by
      rw [halg, hψC, Algebra.smul_def, map_mul, map_pow, map_pow, hru, ← map_pow, ← mul_assoc, ← map_mul,
        ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one, map_one,
        one_mul]
    rw [heq]
    exact (isIntegral_algebraMap).mul hint1

  haveI hIntAll : Algebra.IsIntegral (MvPolynomial (Fin d) (Localization.Away r))
      (Localization.Away (algebraMap R C r)) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨c, s, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers (algebraMap R C r)) x
    obtain ⟨m, hsm⟩ : ∃ m : ℕ, algebraMap R C r ^ m = (s : C) := (Submonoid.mem_powers_iff _ _).mp s.2
    have hsunit : IsUnit (algebraMap C (Localization.Away (algebraMap R C r)) (s : C)) :=
      IsLocalization.map_units _ s
    obtain ⟨u, hu⟩ := hunitR

    have hs : algebraMap C (Localization.Away (algebraMap R C r)) (s : C) =
        algebraMap (Localization.Away r) (Localization.Away (algebraMap R C r)) (↑(u ^ m)) := by
      rw [← hsm, map_pow, Units.val_pow_eq_pow_val, map_pow, hu, hf]
    have hx : IsLocalization.mk' (Localization.Away (algebraMap R C r)) c s =
        algebraMap C (Localization.Away (algebraMap R C r)) c *
          algebraMap (MvPolynomial (Fin d) (Localization.Away r)) (Localization.Away (algebraMap R C r))
            (MvPolynomial.C (↑(u ^ m)⁻¹ : Localization.Away r)) := by
      rw [halg, hψC]
      apply (hsunit.mul_left_inj).mp
      rw [IsLocalization.mk'_spec, mul_assoc, hs, ← map_mul, Units.inv_mul, map_one, mul_one]
    rw [hx]
    exact (hintC c).mul isIntegral_algebraMap

  have hinjAlg : Function.Injective (algebraMap (MvPolynomial (Fin d) (Localization.Away r))
      (Localization.Away (algebraMap R C r))) := hψinj
  have h1 := ringKrullDim_le_of_isIntegral_of_injective hinjAlg
  have h2 : ringKrullDim (Localization.Away (algebraMap R C r)) ≤ ringKrullDim C :=
    ringKrullDim_localization_le (Submonoid.powers (algebraMap R C r))
  have h3 : ringKrullDim (MvPolynomial (Fin d) (Localization.Away r)) =
      ringKrullDim (Localization.Away r) + d := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, Nat.card_eq_fintype_card, Fintype.card_fin]
  calc ringKrullDim (Localization.Away r) + d
      = ringKrullDim (MvPolynomial (Fin d) (Localization.Away r)) := h3.symm
    _ ≤ ringKrullDim (Localization.Away (algebraMap R C r)) := h1
    _ ≤ ringKrullDim C := h2

include k in
set_option backward.isDefEq.respectTransparency false in

theorem main {d : ℕ} (z : Fin d → C) (hz : AlgebraicIndependent R z) (r : R) (hr : r ≠ 0)
    (hint : ∀ c : C, ∃ n : ℕ, IsIntegral (Algebra.adjoin R (Set.range z)) (r ^ n • c))
    (p : Ideal R) [p.IsMaximal] (hrp : r ∉ p)
    (Q : Ideal C) (hQ : Q ∈ (p.map (algebraMap R C)).minimalPrimes) :
    (d : WithBot ℕ∞) ≤ ringKrullDim (C ⧸ Q) := by
  classical
  haveI hQprime : Q.IsPrime := hQ.1.1
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  haveI : Algebra.FiniteType k C := Algebra.FiniteType.trans (S := R) inferInstance inferInstance
  haveI : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing k C

  have hQp : Q.under R = p := by
    have h1 : p ≤ Q.under R := by
      rw [Ideal.under_def, ← Ideal.map_le_iff_le_comap]; exact hQ.1.2
    exact (Ideal.IsMaximal.eq_of_le inferInstance (Ideal.IsPrime.ne_top inferInstance) h1).symm
  haveI : Q.LiesOver p := ⟨hQp.symm⟩

  have hker : p.map (algebraMap R C) ≤ Q := hQ.1.2
  haveI hQb : (Q.map (Ideal.Quotient.mk (p.map (algebraMap R C)))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hfib : (Q.map (Ideal.Quotient.mk (p.map (algebraMap R C)))).height = 0 := by
    rw [Ideal.height_eq_zero_iff]
    refine ⟨⟨hQb, bot_le⟩, ?_⟩
    rintro P' ⟨hP', -⟩ hle
    haveI := hP'
    have hcm : (Q.map (Ideal.Quotient.mk (p.map (algebraMap R C)))).comap
        (Ideal.Quotient.mk (p.map (algebraMap R C))) = Q := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker]
      exact sup_eq_left.mpr hker
    have h1 : P'.comap (Ideal.Quotient.mk (p.map (algebraMap R C))) ≤ Q := by
      rw [← hcm]; exact Ideal.comap_mono hle
    have h2 : p.map (algebraMap R C) ≤ P'.comap (Ideal.Quotient.mk (p.map (algebraMap R C))) := by
      intro x hx
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact zero_mem _
    have h3 : Q ≤ P'.comap (Ideal.Quotient.mk (p.map (algebraMap R C))) :=
      hQ.2 ⟨Ideal.comap_isPrime _ P', h2⟩ h1
    exact (Ideal.map_mono h3).trans Ideal.map_comap_le
  have hhtQ : Q.height ≤ p.height := by
    have := Ideal.height_le_height_add_of_liesOver p Q
    rwa [hfib, add_zero] at this

  have hdisj : Disjoint ((Submonoid.powers r : Submonoid R) : Set R) (p : Set R) := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hrp (Ideal.IsPrime.mem_of_pow_mem inferInstance n hn)
  have hhtp : (p.height : WithBot ℕ∞) ≤ ringKrullDim (Localization.Away r) := by
    rw [← IsLocalization.height_map_of_disjoint (S := Localization.Away r) (Submonoid.powers r) p hdisj]
    exact Ideal.height_le_ringKrullDim_of_ne_top
      ((IsLocalization.map_algebraMap_ne_top_iff_disjoint (Submonoid.powers r) (Localization.Away r) p).mpr
        hdisj)

  have hDF := Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType k Q
  have hC := ringKrullDim_localization_add_le k z hz r hr hint

  haveI : Nontrivial (C ⧸ Q) := Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsPrime.ne_top inferInstance)
  haveI : Nontrivial (Localization.Away r) :=
    (IsLocalization.isDomain_localization (M := Submonoid.powers r)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hr)).toNontrivial
  obtain ⟨nR, hnR⟩ := exists_ringKrullDim_eq_natCast k R
  obtain ⟨nC, hnC⟩ := exists_ringKrullDim_eq_natCast k C
  obtain ⟨e, he⟩ := exists_ringKrullDim_eq_natCast k (C ⧸ Q)
  have hRr_le : ringKrullDim (Localization.Away r) ≤ nR :=
    hnR ▸ ringKrullDim_localization_le (Submonoid.powers r)
  obtain ⟨a, ha⟩ := exists_nat_eq (ringKrullDim_nonneg_of_nontrivial) hRr_le
  obtain ⟨hq, hhq⟩ : ∃ hq : ℕ, Q.height = hq :=
    ⟨_, (ENat.coe_toNat (Ideal.height_ne_top (Ideal.IsPrime.ne_top inferInstance))).symm⟩
  obtain ⟨hp, hhp⟩ : ∃ hp : ℕ, p.height = hp :=
    ⟨_, (ENat.coe_toNat (Ideal.height_ne_top (Ideal.IsPrime.ne_top inferInstance))).symm⟩
  rw [hhq, hnC, he] at hDF
  rw [ha, hnC] at hC
  rw [hhp, ha] at hhtp
  rw [hhq, hhp] at hhtQ
  rw [he]
  have e1 : hq + e = nC := by exact_mod_cast hDF
  have e2 : a + d ≤ nC := by exact_mod_cast hC
  have e3 : hp ≤ a := by exact_mod_cast hhtp
  have e4 : hq ≤ hp := by exact_mod_cast hhtQ
  have : d ≤ e := by omega
  exact_mod_cast this

end Main

end P2mFibDim

theorem solution
    (k : Type u) [Field k] {R : Type v} {C : Type w} [CommRing R] [IsDomain R] [Algebra k R]
    [Algebra.FiniteType k R] [CommRing C] [IsDomain C] [Algebra k C] [Algebra R C]
    [IsScalarTower k R C] [Algebra.FiniteType R C]
    {d : ℕ} (z : Fin d → C) (hz : AlgebraicIndependent R z) (r : R) (hr : r ≠ 0)
    (hint : ∀ c : C, ∃ n : ℕ, IsIntegral (Algebra.adjoin R (Set.range z)) (r ^ n • c))
    (p : Ideal R) [p.IsMaximal] (hrp : r ∉ p)
    (Q : Ideal C) (hQ : Q ∈ (p.map (algebraMap R C)).minimalPrimes) :
    (d : WithBot ℕ∞) ≤ ringKrullDim (C ⧸ Q) :=
  P2mFibDim.main k z hz r hr hint p hrp Q hQ

end S_Ideal_natCast_le_ringKrullDim_quotient_of_mem_minimalPrimes_map_of_algebraicIndependent
end P2MW
export P2MW.S_Ideal_natCast_le_ringKrullDim_quotient_of_mem_minimalPrimes_map_of_algebraicIndependent (solution)
