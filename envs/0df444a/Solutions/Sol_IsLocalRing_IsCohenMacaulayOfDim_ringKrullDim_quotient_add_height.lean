-- Prove2me | solution 1 for IsLocalRing.IsCohenMacaulayOfDim.ringKrullDim_quotient_add_height
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/d5614db5-a2d6-55bd-b99d-1c9b422cfab8

import Mathlib
import Definitions.Def_Patching_CohenMacaulayOfDim
import Theorems.Thm_Module_depth_le_ringKrullDim_quotient_of_mem_associatedPrimes
import Theorems.Thm_Module_depth_quotSMulTop_succ_eq
import Theorems.Thm_Module_depth_quotient_eq_depth
import Theorems.Thm_Ideal_height_map_quotientMk_span_singleton_add_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_IsCohenMacaulayOfDim_ringKrullDim_quotient_add_height

set_option autoImplicit false

universe u

open IsLocalRing Pointwise

namespace CMDimFormula

theorem ringKrullDim_quotient_add_height_le {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] :
    ringKrullDim (R ⧸ p) + p.height ≤ ringKrullDim R := by
  let P : PrimeSpectrum R := ⟨p, ‹_›⟩
  have h1 : ringKrullDim (R ⧸ p) = Order.coheight P := by
    rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]
    have : PrimeSpectrum.zeroLocus (p : Set R) = Set.Ici P := by
      ext q
      simp only [PrimeSpectrum.mem_zeroLocus, Set.mem_Ici, SetLike.coe_subset_coe]
      rfl
    rw [this]
  have h2 : p.height = Order.height P := PrimeSpectrum.height_eq_orderHeight P
  haveI : Nonempty (PrimeSpectrum R) := ⟨P⟩
  rw [h1, h2, ringKrullDim, Order.krullDim_eq_iSup_height_add_coheight_of_nonempty, ← WithBot.coe_add,
    WithBot.coe_le_coe, add_comm]
  exact le_iSup (fun a => Order.height a + Order.coheight a) P

theorem depth_eq_of_linearEquiv {R : Type u} [CommRing R] [IsLocalRing R] {M N : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    Module.depth R M = Module.depth R N := by
  simp only [Module.depth, e.isWeaklyRegular_congr]

theorem enat_eq_of_add_one_eq {a : ℕ∞} {d : ℕ} (h : a + 1 = (d + 1 : ℕ)) : a = d := by
  have h' : a + 1 = (d : ℕ∞) + 1 := by rw [h]; push_cast; rfl
  exact WithTop.add_right_cancel WithTop.one_ne_top h'

theorem withBot_eq_of_add_one_eq {a : WithBot ℕ∞} {d : ℕ} (h : a + 1 = ((d + 1 : ℕ) : WithBot ℕ∞)) : a = d := by
  induction a with
  | bot =>
    exfalso
    rw [WithBot.bot_add] at h
    exact WithBot.bot_ne_coe h
  | coe a =>
    have : a + 1 = ((d + 1 : ℕ) : ℕ∞) := by exact_mod_cast h
    rw [enat_eq_of_add_one_eq this]
    rfl

theorem le_ringKrullDim_quotient_add (n : ℕ) :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {d : ℕ}
      (_h : IsCohenMacaulayOfDim R d) (p : Ideal R) [p.IsPrime], p.height = n →
      (d : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) + n := by
  induction n with
  | zero =>
    intro R _ _ _ d h p _ hp
    have hmin : p ∈ minimalPrimes R := Ideal.height_eq_zero_iff.mp (by exact_mod_cast hp)
    have hass : p ∈ associatedPrimes R R := by
      apply Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
      rwa [Module.annihilator_eq_bot.mpr inferInstance]
    have h1 := Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes R hass
    rw [h.2] at h1
    simpa using h1
  | succ n ih =>
    intro R _ _ _ d h p _ hp

    have hAss0 : ∀ q ∈ associatedPrimes R R, q.height = 0 := by
      intro q hq
      haveI : q.IsPrime := hq.1
      have h1 := Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes R hq
      have h2 := ringKrullDim_quotient_add_height_le q
      rw [h.2] at h1
      rw [h.1] at h2

      induction hrq : ringKrullDim (R ⧸ q) with
      | bot => rw [hrq] at h1; simp at h1
      | coe m =>
        rw [hrq] at h1 h2
        have h1' : (d : ℕ∞) ≤ m := by exact_mod_cast h1
        have h2' : m + q.height ≤ d := by exact_mod_cast h2
        have hm : m ≠ ⊤ := by rintro rfl; simp at h2'
        obtain ⟨k, rfl⟩ := ENat.ne_top_iff_exists.mp hm
        have hk : q.height ≠ ⊤ := by rintro hh; rw [hh] at h2'; simp at h2'
        obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp hk
        rw [← hj] at h2' ⊢
        norm_cast at h1' h2' ⊢
        omega

    have hp_not : ∀ q ∈ associatedPrimes R R, ¬ p ≤ q := by
      intro q hq hpq
      have := Ideal.height_mono hpq
      rw [hAss0 q hq, hp] at this
      simp at this

    have hfin := associatedPrimes.finite R R
    obtain ⟨x, hxp, hxreg⟩ : ∃ x ∈ p, IsSMulRegular R x := by
      by_contra hcon
      push Not at hcon
      have hsub : (p : Set R) ⊆ ⋃ q ∈ associatedPrimes R R, (q : Set R) := by
        rw [biUnion_associatedPrimes_eq_compl_regular]
        intro r hr
        exact hcon r hr
      have hsub' : (p : Set R) ⊆ ⋃ q ∈ associatedPrimes R R, ((id q : Ideal R) : Set R) := hsub
      obtain ⟨q, hq, hpq⟩ := (Ideal.subset_union_prime_finite hfin (f := id) p p
        (fun q hq _ _ => (hq.1 : (id q).IsPrime))).mp hsub'
      exact hp_not q hq hpq
    have hxm : x ∈ maximalIdeal R := IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›) hxp

    set J : Ideal R := Ideal.span {x} with hJ
    have hJp : J ≤ p := by rw [hJ, Ideal.span_singleton_le_iff_mem]; exact hxp
    have hJtop : J ≠ ⊤ := fun hh => Ideal.IsPrime.ne_top ‹_› (top_le_iff.mp (hh ▸ hJp))
    haveI : Nontrivial (R ⧸ J) :=
      ⟨⟨0, 1, fun h01 => hJtop (Ideal.Quotient.zero_eq_one_iff.mp h01)⟩⟩
    haveI : IsLocalRing (R ⧸ J) := IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective

    have hd : 1 ≤ d := by
      have := Ideal.height_le_ringKrullDim_of_isPrime (I := p)
      rw [h.1, hp] at this
      have : ((n + 1 : ℕ) : ℕ∞) ≤ d := by exact_mod_cast this
      norm_cast at this
      omega
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩

    have hdim' : ringKrullDim (R ⧸ J) = d' := by
      have := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hxreg hxm
      rw [h.1] at this
      exact withBot_eq_of_add_one_eq this
    have hsmul : (x • ⊤ : Submodule R R) = J := by
      rw [hJ, ← Submodule.set_smul_top_eq_span, Submodule.singleton_set_smul]
    have hdepth' : Module.depth (R ⧸ J) (R ⧸ J) = d' := by
      rw [Module.depth_quotient_eq_depth J (R ⧸ J)]
      have e : QuotSMulTop x R ≃ₗ[R] R ⧸ J := Submodule.quotEquivOfEq _ _ hsmul
      rw [← depth_eq_of_linearEquiv e]
      have := Module.depth_quotSMulTop_succ_eq R hxm hxreg
      rw [h.2] at this
      exact enat_eq_of_add_one_eq this
    have h' : IsCohenMacaulayOfDim (R ⧸ J) d' := ⟨hdim', hdepth'⟩

    have hxmin : ∀ q ∈ minimalPrimes R, q ≤ p → x ∉ q := by
      intro q hq _ hxq
      have hqass : q ∈ associatedPrimes R R := by
        apply Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
        rwa [Module.annihilator_eq_bot.mpr inferInstance]
      have : x ∈ ⋃ q ∈ associatedPrimes R R, (q : Set R) := Set.mem_biUnion hqass hxq
      rw [biUnion_associatedPrimes_eq_compl_regular] at this
      exact this hxreg
    have hht : (p.map (Ideal.Quotient.mk J)).height = n := by
      have := Ideal.height_map_quotientMk_span_singleton_add_one p hxp hxmin
      rw [hp] at this
      exact enat_eq_of_add_one_eq this
    haveI : (p.map (Ideal.Quotient.mk J)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hJp)
    have IH := ih h' (p.map (Ideal.Quotient.mk J)) hht
    rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hJp)] at IH
    calc ((d' + 1 : ℕ) : WithBot ℕ∞) = (d' : WithBot ℕ∞) + 1 := by push_cast; rfl
      _ ≤ (ringKrullDim (R ⧸ p) + n) + 1 := add_le_add IH le_rfl
      _ = ringKrullDim (R ⧸ p) + ((n + 1 : ℕ) : WithBot ℕ∞) := by push_cast; rw [add_assoc]

end CMDimFormula

open CMDimFormula in

theorem solution
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {d : ℕ}
    (h : IsCohenMacaulayOfDim R d) (p : Ideal R) [p.IsPrime] :
    ringKrullDim (R ⧸ p) + p.height = d := by
  have hfin : p.height ≠ ⊤ := Ideal.height_ne_top_of_isPrime
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  apply le_antisymm
  · rw [← h.1]
    exact ringKrullDim_quotient_add_height_le p
  · have := le_ringKrullDim_quotient_add n h p hn.symm
    rw [← hn]
    exact_mod_cast this

end S_IsLocalRing_IsCohenMacaulayOfDim_ringKrullDim_quotient_add_height
end P2MW
export P2MW.S_IsLocalRing_IsCohenMacaulayOfDim_ringKrullDim_quotient_add_height (solution)
