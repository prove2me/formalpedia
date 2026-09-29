-- Prove2me | solution 1 for Ideal.exists_valuationSubring_valuation_lt_one_iff_mem_of_finiteType
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/b75436a2-dff3-5346-8e86-739987c7c82a

import Mathlib
import Theorems.Thm_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType
import Theorems.Thm_Algebra_ringKrullDim_eq_toENat_trdeg_of_finiteType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_exists_valuationSubring_valuation_lt_one_iff_mem_of_finiteType

set_option autoImplicit false

universe u v w

open scoped nonZeroDivisors

namespace Ideal
p2m_export "Ideal" "height Quotient.eq_zero_iff_mem mul_mem_right Quotient.mkₐ span_empty image_subset_nonunits_valuationSubring primeCompl span primeCompl_le_nonZeroDivisors isPrime_bot isDomain comap_isPrime Quotient.isDomain Quotient.mk exists_minimalPrimes_le span_singleton_le_iff_mem height_le_one_of_isPrincipal_of_mem_minimalPrimes FG ext height_eq_zero_iff IsPrime span_le comap Quotient.mkₐ_eq_mk subset_span Quotient.mk_surjective span_eq_bot height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType"
namespace PrimeDivisorCentre
p2m_open "Ideal"

theorem exists_valuationSubring_centre {B : Type*} [CommRing B] [IsDomain B] {K : Type*} [Field K]
    [Algebra B K] [IsFractionRing B K] (Q : Ideal B) [Q.IsPrime] :
    ∃ V : ValuationSubring K, (∀ b : B, algebraMap B K b ∈ V) ∧
      ∀ b : B, V.valuation (algebraMap B K b) < 1 ↔ b ∈ Q := by
  classical
  let L : Subalgebra B K :=
    Localization.subalgebra.ofField K Q.primeCompl Q.primeCompl_le_nonZeroDivisors
  haveI : IsLocalization.AtPrime L Q :=
    Localization.subalgebra.isLocalization_ofField K Q.primeCompl Q.primeCompl_le_nonZeroDivisors
  haveI hLloc : IsLocalRing L := IsLocalization.AtPrime.isLocalRing L Q
  have hne : (IsLocalRing.maximalIdeal L : Ideal L.toSubring) ≠ ⊤ :=
    (IsLocalRing.maximalIdeal.isMaximal L).ne_top
  obtain ⟨V, hLV, hnon⟩ :=
    Ideal.image_subset_nonunits_valuationSubring (A := L.toSubring) (IsLocalRing.maximalIdeal L) hne
  refine ⟨V, fun b => hLV (algebraMap B L b).2, fun b => ?_⟩
  have hcoe : ((algebraMap B L b : L) : K) = algebraMap B K b := rfl
  constructor
  · intro hlt
    by_contra hb
    have hu : IsUnit (algebraMap B L b) := IsLocalization.map_units L (⟨b, hb⟩ : Q.primeCompl)
    have hu' : IsUnit (⟨algebraMap B K b, hLV (algebraMap B L b).2⟩ : V) := by
      obtain ⟨u, hu⟩ := hu
      refine ⟨⟨⟨(u.1 : K), hLV u.1.2⟩, ⟨(u.2 : K), hLV u.2.2⟩, ?_, ?_⟩, ?_⟩
      · exact Subtype.ext (by
          change ((u.1 : L) : K) * ((u.2 : L) : K) = 1
          rw [← Subalgebra.coe_mul, u.3]; rfl)
      · exact Subtype.ext (by
          change ((u.2 : L) : K) * ((u.1 : L) : K) = 1
          rw [← Subalgebra.coe_mul, u.4]; rfl)
      · exact Subtype.ext (by change ((u : L) : K) = _; rw [hu]; exact hcoe)
    have h1 := (V.valuation_eq_one_iff _).mp hu'
    change V.valuation (algebraMap B K b) = 1 at h1
    exact (lt_irrefl _) (h1 ▸ hlt)
  · intro hb
    have hmem : algebraMap B L b ∈ IsLocalRing.maximalIdeal L :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff L Q b).mpr hb
    have : algebraMap B K b ∈ V.nonunits := hnon ⟨algebraMap B L b, hmem, rfl⟩
    exact (ValuationSubring.mem_nonunits_iff V).mp this

theorem eq_of_one_add_eq_natCast_succ {x : WithBot ℕ∞} {d : ℕ}
    (h : (1 : WithBot ℕ∞) + x = ((d + 1 : ℕ) : WithBot ℕ∞)) : x = (d : WithBot ℕ∞) := by
  rw [← WithBot.coe_natCast] at h
  induction x using WithBot.recBotCoe with
  | bot => rw [WithBot.add_bot] at h; exact absurd h WithBot.bot_ne_coe
  | coe y =>
    rw [← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_inj] at h
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      have h1 : (1 : ℕ∞) + ⊤ = ⊤ := by simp
      rw [h1] at h
      exact ENat.top_ne_coe _ h
    | coe m =>
      have h' : ((1 + m : ℕ) : ℕ∞) = ((d + 1 : ℕ) : ℕ∞) := by rw [← h]; push_cast; rfl
      have : 1 + m = d + 1 := by exact_mod_cast h'
      have hm : m = d := by omega
      subst hm; rfl

theorem exists_ringKrullDim_eq_natCast (k : Type u) [Field k] (A : Type v) [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] :
    ∃ n : ℕ, ringKrullDim A = (n : WithBot ℕ∞) := by
  have h := Algebra.ringKrullDim_eq_toENat_trdeg_of_finiteType k A
  have hfin : Algebra.trdeg k A < Cardinal.aleph0 := trdeg_lt_aleph0_of_finiteType
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp hfin
  refine ⟨n, ?_⟩
  rw [h, hn]
  simp

theorem trdeg_eq_natCast_of_ringKrullDim_eq (k : Type u) [Field k] (A : Type v) [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] {n : ℕ}
    (h : ringKrullDim A = (n : WithBot ℕ∞)) : Algebra.trdeg k A = n := by
  have h1 := Algebra.ringKrullDim_eq_toENat_trdeg_of_finiteType k A
  rw [h] at h1
  have h2 : Cardinal.toENat (Algebra.trdeg k A) = n := by
    have : ((n : ℕ∞) : WithBot ℕ∞) = (Cardinal.toENat (Algebra.trdeg k A) : WithBot ℕ∞) := by
      rw [← h1]; rfl
    exact_mod_cast this.symm
  exact (Cardinal.toENat_eq_natCast).mp h2

theorem exists_algebraicIndependent_of_ringKrullDim_eq (k : Type u) [Field k] (C : Type v)
    [CommRing C] [IsDomain C] [Algebra k C] [Algebra.FiniteType k C] {d : ℕ}
    (h : ringKrullDim C = (d : WithBot ℕ∞)) :
    ∃ x : Fin d → C, AlgebraicIndependent k x := by
  classical
  haveI : FaithfulSMul k C :=
    (faithfulSMul_iff_algebraMap_injective k C).mpr (algebraMap k C).injective
  have htr : Algebra.trdeg k C = d := trdeg_eq_natCast_of_ringKrullDim_eq k C h
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k C
  have hcard : Cardinal.mk s = d := by rw [hs.cardinalMk_eq_trdeg, htr]
  have hfin : (s : Set C).Finite := by
    rw [← Cardinal.lt_aleph0_iff_set_finite, hcard]
    exact Cardinal.natCast_lt_aleph0
  haveI : Fintype s := hfin.fintype
  have hcard' : Fintype.card s = d := by
    have : Cardinal.mk s = Fintype.card s := Cardinal.mk_fintype s
    rw [this] at hcard
    exact_mod_cast hcard
  let e : s ≃ Fin d := Fintype.equivFinOfCardEq hcard'
  exact ⟨fun i => ((e.symm i : s) : C), hs.1.comp _ e.symm.injective⟩

section Main

variable (k : Type u) [Field k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
  [Algebra.FiniteType k A]
  (K : Type w) [Field K] [Algebra A K] [IsFractionRing A K] [Algebra k K] [IsScalarTower k A K]

theorem main (p : Ideal A) [hp : p.IsPrime] (hp0 : p ≠ ⊥) :
    ∃ (O : ValuationSubring K) (d : ℕ) (f : Fin d → K),
      O ≠ ⊤ ∧ (∀ a : A, algebraMap A K a ∈ O) ∧
      (∀ a : A, O.valuation (algebraMap A K a) < 1 ↔ a ∈ p) ∧
      ((d + 1 : ℕ) : WithBot ℕ∞) = ringKrullDim A ∧
      (∀ i, f i ∈ O) ∧
      ∀ Q : MvPolynomial (Fin d) k, O.valuation (MvPolynomial.aeval f Q) < 1 → Q = 0 := by
  classical
  have hinjA : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A

  obtain ⟨n, hn⟩ := exists_ringKrullDim_eq_natCast k A
  have hn1 : 1 ≤ n := by
    have hpos : 0 < ringKrullDim A := by
      rw [ringKrullDim, Order.krullDim_pos_iff]
      refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ⟨p, hp⟩, ?_⟩
      change (⊥ : Ideal A) < p
      exact bot_lt_iff_ne_bot.mpr hp0
    rw [hn] at hpos
    have : (0 : ℕ) < n := by exact_mod_cast hpos
    omega
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩

  obtain ⟨V, hAV, hVcen⟩ := exists_valuationSubring_centre (K := K) p
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian p : p.FG)
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply hp0
    rw [← hs, Finset.coe_empty]
    exact Ideal.span_empty
  obtain ⟨a₁, ha₁s, ha₁max⟩ :=
    s.exists_max_image (fun a => V.valuation (algebraMap A K a)) hsne
  have hsp : ∀ a ∈ s, a ∈ p := fun a ha => hs ▸ Ideal.subset_span ha
  have ha₁p : a₁ ∈ p := hsp a₁ ha₁s
  have ha₁0 : a₁ ≠ 0 := by
    intro h0
    apply hp0
    rw [← hs, Ideal.span_eq_bot]
    intro a ha
    have hle := ha₁max a ha
    rw [h0, map_zero, Valuation.map_zero, le_zero_iff, Valuation.zero_iff] at hle
    exact hinjA (by rw [hle, map_zero])
  set α₁ : K := algebraMap A K a₁ with hα₁
  have hα₁0 : α₁ ≠ 0 := fun h => ha₁0 (hinjA (by rw [← hα₁, h, map_zero]))
  have hα₁lt : V.valuation α₁ < 1 := (hVcen a₁).mpr ha₁p

  let T : Finset K := s.image fun a => algebraMap A K a / α₁
  let B : Subalgebra A K := Algebra.adjoin A (T : Set K)
  have hAB : ∀ a : A, algebraMap A K a ∈ B := fun a => B.algebraMap_mem a
  have hTV : (T : Set K) ⊆ V := by
    intro x hx
    rw [Finset.mem_coe, Finset.mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    apply V.mem_of_valuation_le_one
    rw [Valuation.map_div]
    exact div_le_one_of_le₀ (ha₁max a ha) zero_le'
  let SV : Subalgebra A K :=
    { V.toSubring with
      algebraMap_mem' := fun a => hAV a }
  have hBV : B ≤ SV := Algebra.adjoin_le hTV
  have hBV' : ∀ x : B, (x : K) ∈ V := fun x => hBV x.2

  haveI : Algebra.FiniteType A B :=
    (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset T)
  haveI : IsScalarTower k A B :=
    IsScalarTower.of_algebraMap_eq fun r => Subtype.ext (IsScalarTower.algebraMap_apply k A K r)
  haveI hBft : Algebra.FiniteType k B := Algebra.FiniteType.trans (inferInstance) (S := A) inferInstance
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have hinjAB : Function.Injective (algebraMap A B) := by
    intro a b hab
    apply hinjA
    have := congrArg (fun x : B => (x : K)) hab
    exact this
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinjAB
  haveI : FaithfulSMul k A :=
    (faithfulSMul_iff_algebraMap_injective k A).mpr (algebraMap k A).injective
  haveI : Algebra.IsAlgebraic A K := IsLocalization.isAlgebraic K (nonZeroDivisors A)
  haveI : Algebra.IsAlgebraic A B :=
    Algebra.IsAlgebraic.of_injective B.val Subtype.val_injective
  have htrB : Algebra.trdeg k B = (d + 1 : ℕ) := by
    have h1 := lift_trdeg_add_eq k A B
    rw [trdeg_eq_zero (R := A) (A := B), trdeg_eq_natCast_of_ringKrullDim_eq k A hn] at h1
    simp only [Cardinal.lift_natCast, Cardinal.lift_zero, add_zero] at h1
    exact (Cardinal.lift_eq_nat_iff.mp h1.symm)
  have hdimB : ringKrullDim B = ((d + 1 : ℕ) : WithBot ℕ∞) := by
    rw [Algebra.ringKrullDim_eq_toENat_trdeg_of_finiteType k B, htrB]
    simp

  let ψ : B →+* V := (B.val : B →ₐ[A] K).toRingHom.codRestrict V hBV'
  let Q₁ : Ideal B := (IsLocalRing.maximalIdeal V).comap ψ
  haveI : Q₁.IsPrime := Ideal.comap_isPrime ψ _
  have hQ₁ : ∀ x : B, x ∈ Q₁ ↔ V.valuation (x : K) < 1 := by
    intro x
    change ψ x ∈ IsLocalRing.maximalIdeal V ↔ _
    rw [ValuationSubring.valuation_lt_one_iff]
    rfl
  let b₁ : B := algebraMap A B a₁
  have hb₁K : (b₁ : K) = α₁ := rfl
  have hb₁0 : b₁ ≠ 0 := fun h => hα₁0 (by rw [← hb₁K, h]; rfl)
  have hb₁Q₁ : b₁ ∈ Q₁ := (hQ₁ b₁).mpr (by rw [hb₁K]; exact hα₁lt)
  let I : Ideal B := Ideal.span {b₁}
  have hIQ₁ : I ≤ Q₁ := (Ideal.span_singleton_le_iff_mem _).mpr hb₁Q₁
  obtain ⟨Q, hQmin, hQQ₁⟩ := Ideal.exists_minimalPrimes_le hIQ₁
  haveI hQ : Q.IsPrime := hQmin.1.1
  have hIQ : I ≤ Q := hQmin.1.2
  have hb₁Q : b₁ ∈ Q := hIQ (Ideal.subset_span rfl)

  have hQht : Q.height = 1 := by
    have hle : Q.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes I Q hQmin
    have hne : Q.height ≠ 0 := by
      intro h0
      rw [Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot,
        Set.mem_singleton_iff] at h0
      apply hb₁0
      have : b₁ ∈ (⊥ : Ideal B) := h0 ▸ hb₁Q
      exact this
    exact le_antisymm hle (ENat.one_le_iff_ne_zero.mpr hne)

  have hQA : ∀ a : A, algebraMap A B a ∈ Q ↔ a ∈ p := by
    intro a
    constructor
    · intro ha
      have h1 : V.valuation ((algebraMap A B a : B) : K) < 1 := (hQ₁ _).mp (hQQ₁ ha)
      exact (hVcen a).mp h1
    · intro ha
      have hpI : p ≤ I.comap (algebraMap A B) := by
        rw [← hs, Ideal.span_le]
        intro a' ha'
        change algebraMap A B a' ∈ I
        have hq : algebraMap A K a' / α₁ ∈ B :=
          Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ ha'))
        have hfac : algebraMap A B a' = b₁ * ⟨_, hq⟩ := by
          apply Subtype.ext
          change algebraMap A K a' = α₁ * (algebraMap A K a' / α₁)
          rw [mul_div_cancel₀ _ hα₁0]
        rw [hfac]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
      exact hIQ (hpI ha)

  have hdimBQ : ringKrullDim (B ⧸ Q) = (d : WithBot ℕ∞) := by
    have h := Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType k Q
    rw [hdimB, hQht] at h
    exact eq_of_one_add_eq_natCast_succ (by simpa using h)
  haveI : IsDomain (B ⧸ Q) := Ideal.Quotient.isDomain Q
  obtain ⟨x, hx⟩ := exists_algebraicIndependent_of_ringKrullDim_eq k (B ⧸ Q) hdimBQ
  let g : Fin d → B := fun i => (Ideal.Quotient.mk_surjective (x i)).choose
  have hg : ∀ i, Ideal.Quotient.mk Q (g i) = x i := fun i =>
    (Ideal.Quotient.mk_surjective (x i)).choose_spec
  let f : Fin d → K := fun i => (g i : K)

  obtain ⟨O, hBO, hOcen⟩ := exists_valuationSubring_centre (K := K) Q
  have hBO' : ∀ y : B, (y : K) ∈ O := hBO
  have hOcen' : ∀ y : B, O.valuation (y : K) < 1 ↔ y ∈ Q := hOcen
  refine ⟨O, d, f, ?_, fun a => hBO' (algebraMap A B a), fun a => ?_, hn.symm, fun i => hBO' _, ?_⟩
  ·
    intro htop
    have hlt : O.valuation α₁ < 1 := (hOcen' b₁).mpr hb₁Q
    have hmem : α₁⁻¹ ∈ O := htop ▸ ValuationSubring.mem_top _
    have hle : O.valuation α₁⁻¹ ≤ 1 := O.valuation_le_one_iff _ |>.mpr hmem
    rw [Valuation.map_inv, inv_le_one₀ ((Valuation.pos_iff _).mpr hα₁0)] at hle
    exact (not_le.mpr hlt) hle
  ·
    rw [← hQA a, ← hOcen' (algebraMap A B a)]
    rfl
  ·
    intro P hP
    have hval : MvPolynomial.aeval f P = ((MvPolynomial.aeval g P : B) : K) := by
      have := MvPolynomial.comp_aeval_apply g (IsScalarTower.toAlgHom k B K) P
      exact this.symm
    rw [hval] at hP
    have hmemQ : MvPolynomial.aeval g P ∈ Q := (hOcen' _).mp hP
    have hzero : MvPolynomial.aeval x P = 0 := by
      have h1 : Ideal.Quotient.mkₐ k Q (MvPolynomial.aeval g P) = MvPolynomial.aeval x P := by
        rw [MvPolynomial.comp_aeval_apply]
        have hfun : (fun i => Ideal.Quotient.mkₐ k Q (g i)) = x := funext hg
        rw [hfun]
      rw [← h1, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact hmemQ
    exact hx (by rw [hzero, map_zero])

end Main

end Ideal.PrimeDivisorCentre

open Ideal.PrimeDivisorCentre in

theorem solution
    (k : Type u) [Field k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A]
    (K : Type w) [Field K] [Algebra A K] [IsFractionRing A K] [Algebra k K] [IsScalarTower k A K]
    (p : Ideal A) [p.IsPrime] (hp : p ≠ ⊥) :
    ∃ (O : ValuationSubring K) (d : ℕ) (f : Fin d → K),
      O ≠ ⊤ ∧ (∀ a : A, algebraMap A K a ∈ O) ∧
      (∀ a : A, O.valuation (algebraMap A K a) < 1 ↔ a ∈ p) ∧
      ((d + 1 : ℕ) : WithBot ℕ∞) = ringKrullDim A ∧
      (∀ i, f i ∈ O) ∧
      ∀ Q : MvPolynomial (Fin d) k, O.valuation (MvPolynomial.aeval f Q) < 1 → Q = 0 :=
  Ideal.PrimeDivisorCentre.main k K p hp

end S_Ideal_exists_valuationSubring_valuation_lt_one_iff_mem_of_finiteType
end P2MW
export P2MW.S_Ideal_exists_valuationSubring_valuation_lt_one_iff_mem_of_finiteType (solution)
