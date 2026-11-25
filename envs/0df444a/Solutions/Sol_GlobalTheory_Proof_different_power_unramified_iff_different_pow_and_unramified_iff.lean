-- Prove2me | solution 1 for GlobalTheory.Proof.different_power_unramified_iff.different_pow_and_unramified_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:07:07.68259+00:00
-- url     : https://prove2.me/submissions/d194099e-1c11-4473-bfec-a97e072a4d13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SplitUnramifiedPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_DifferentPowerUnramifiedIff
import Theorems.Thm_GlobalTheory_Proof_different_power_unramified_iff_ow_p_torsionFree
import Theorems.Thm_GlobalTheory_Proof_different_power_unramified_iff_map_eq_top_of_coprime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped TensorProduct
namespace GlobalTheory.Proof.different_power_unramified_iff
open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces
private lemma isIdempotentElem_Ow_eq_zero_or_one {p : ℕ} [Fact p.Prime] {OE : Type} [CommRing OE]
    (w : GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces.Place p OE) (g : w.Ow) (hg : IsIdempotentElem g) : g = 0 ∨ g = 1 := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective g
  have hee : w.e * w.e = w.e := w.idem
  have hyy : y * y - y ∈ Ideal.span {1 - w.e} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul]
    exact sub_eq_zero.mpr hg
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hyy
  have hey : w.e * (y * y) = w.e * y := by
    have : w.e * (y * y - y) = 0 := by
      rw [← ha]
      calc w.e * (a * (1 - w.e)) = a * (w.e - w.e * w.e) := by ring
        _ = 0 := by rw [hee, sub_self, mul_zero]
    rw [mul_sub] at this
    exact sub_eq_zero.mp this
  have hf : IsIdempotentElem (w.e * y) := by
    show w.e * y * (w.e * y) = w.e * y
    calc w.e * y * (w.e * y) = (w.e * w.e) * (y * y) := by ring
      _ = w.e * y := by rw [hee, hey]
  have hfe : w.e * y * w.e = w.e * y := by
    calc w.e * y * w.e = (w.e * w.e) * y := by ring
      _ = w.e * y := by rw [hee]
  have hmk : (Ideal.Quotient.mk (Ideal.span {1 - w.e}) y) =
      Ideal.Quotient.mk (Ideal.span {1 - w.e}) (w.e * y) := by
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
    exact ⟨y, by ring⟩
  rw [hmk]
  rcases w.primitive _ hf hfe with h | h
  · left
    rw [h, map_zero]
  · right
    rw [h, ← map_one (Ideal.Quotient.mk (Ideal.span {1 - w.e})), Ideal.Quotient.eq,
      Ideal.mem_span_singleton']
    exact ⟨-1, by ring⟩
end GlobalTheory.Proof.different_power_unramified_iff
end
end

set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.different_power_unramified_iff
open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
namespace GlobalTheory.Proof.different_power_unramified_iff
theorem _root_.solution (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    [IsDedekindDomain R] [CharZero R] [Module.Finite ℤ R] (w : GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces.Place p R)
    (P : Ideal R) (hP : P.IsMaximal) (hpP : (p : R) ∈ P) (hm : (P.map w.toOw).IsMaximal)
    (hQ : ∀ Q : Ideal R, Q.IsMaximal → Q ≠ P → Q.map w.toOw = ⊤) :
    (∃ a b : ℕ, 0 < b ∧ (differentIdeal ℤ R).map w.toOw ^ b = Ideal.span {(p : w.Ow) ^ a}) ∧
      (w.IsUnramified ↔ (differentIdeal ℤ R).map w.toOw = ⊤) := by
  have hp := (Fact.out : p.Prime)
  have hDne : differentIdeal ℤ R ≠ ⊥ := differentIdeal_ne_bot
  have hPtop : P.map w.toOw ≠ ⊤ := hm.ne_top
  have hpR : (p : R) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hIne : Ideal.span {(p : R)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hpR
  have hIP : Ideal.span {(p : R)} ≤ P := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hpP
  obtain ⟨J, hPJ, hIJ⟩ := Ideal.eq_prime_pow_mul_coprime hIne P
  set c := Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(p : R)}))
    with hc
  have hJne : J ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot] at hIJ
    exact hIne hIJ
  have hpOw : Ideal.span {(p : w.Ow)} = P.map w.toOw ^ c := by
    have hsp : Ideal.span {(p : w.Ow)} = (Ideal.span {(p : R)}).map w.toOw := by
      rw [Ideal.map_span, Set.image_singleton, map_natCast]
    rw [hsp, hIJ, Ideal.map_mul, Ideal.map_pow,
      map_eq_top_of_coprime w.toOw P hP hQ J hJne hPJ, Ideal.mul_top]
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · exfalso
      rw [h0, pow_zero, Ideal.one_eq_top, Ideal.top_mul] at hIJ
      rw [hIJ] at hIP
      apply hP.ne_top
      rw [← hPJ]
      exact (sup_eq_left.mpr hIP).symm
    · exact h0
  obtain ⟨J', hPJ', hDJ'⟩ := Ideal.eq_prime_pow_mul_coprime hDne P
  set k := Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (differentIdeal ℤ R))
    with hk
  have hJ'ne : J' ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot] at hDJ'
    exact hDne hDJ'
  have hDmap : (differentIdeal ℤ R).map w.toOw = P.map w.toOw ^ k := by
    rw [hDJ', Ideal.map_mul, Ideal.map_pow,
      map_eq_top_of_coprime w.toOw P hP hQ J' hJ'ne hPJ', Ideal.mul_top]
  refine ⟨⟨k, c, hcpos, ?_⟩, ?_⟩
  · rw [hDmap, ← pow_mul, Nat.mul_comm k c, pow_mul, ← hpOw, Ideal.span_singleton_pow]
  have hUnr : w.IsUnramified ↔ c = 1 := by
    show (Ideal.span {(p : w.Ow)}).IsMaximal ↔ c = 1
    rw [hpOw]
    constructor
    · intro hmax
      by_contra hc1
      have hc2 : 2 ≤ c := by omega
      have heq : P.map w.toOw ^ c = P.map w.toOw :=
        hmax.eq_of_le hPtop (Ideal.pow_le_self hcpos.ne')
      have hidem : IsIdempotentElem (P.map w.toOw) := by
        show P.map w.toOw * P.map w.toOw = P.map w.toOw
        apply le_antisymm Ideal.mul_le_right
        calc P.map w.toOw = P.map w.toOw ^ c := heq.symm
          _ ≤ P.map w.toOw ^ 2 := Ideal.pow_le_pow_right hc2
          _ = P.map w.toOw * P.map w.toOw := sq _
      have hfg : (P.map w.toOw).FG := Ideal.FG.map (IsNoetherian.noetherian P) w.toOw
      obtain ⟨g, hg, hgspan⟩ := (Ideal.isIdempotentElem_iff_of_fg _ hfg).mp hidem
      have hpmem : (p : w.Ow) ∈ P.map w.toOw := by
        rw [← map_natCast w.toOw p]
        exact Ideal.mem_map_of_mem _ hpP
      rcases isIdempotentElem_Ow_eq_zero_or_one w g hg with rfl | rfl
      · rw [hgspan] at hpmem
        have hp0 : (p : w.Ow) = 0 := by simpa using hpmem
        have h10 : (1 : w.Ow) = 0 := ow_p_torsionFree p R w 1 (by rw [mul_one]; exact hp0)
        apply hPtop
        rw [Ideal.eq_top_iff_one, h10]
        exact zero_mem _
      · apply hPtop
        rw [hgspan]
        exact Ideal.span_singleton_one
    · intro h1
      rw [h1, pow_one]
      exact hm
  have hDtop : (differentIdeal ℤ R).map w.toOw = ⊤ ↔ ¬ P ∣ differentIdeal ℤ R := by
    constructor
    · intro h hdvd
      apply hPtop
      rw [eq_top_iff, ← h]
      exact Ideal.map_mono (Ideal.le_of_dvd hdvd)
    · intro h
      apply map_eq_top_of_coprime w.toOw P hP hQ _ hDne
      by_contra hne
      apply h
      rw [Ideal.dvd_iff_le, hP.eq_of_le hne le_sup_left]
      exact le_sup_right
  have hunder : P.under ℤ = Ideal.span {(p : ℤ)} := by
    have hpZ : (Ideal.span {(p : ℤ)}).IsMaximal := by
      have hpr : (Ideal.span {(p : ℤ)}).IsPrime :=
        (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
          (Nat.prime_iff_prime_int.mp hp)
      exact hpr.isMaximal (by
        rw [Ne, Ideal.span_singleton_eq_bot]
        exact_mod_cast hp.ne_zero)
    symm
    apply hpZ.eq_of_le (Ideal.comap_ne_top _ hP.ne_top)
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ R (p : ℤ) ∈ P
    rw [map_natCast]
    exact hpP
  have : P.IsPrime := hP.isPrime
  have : P.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hunder.symm⟩
  have hspZ : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hmapZ : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ R) = Ideal.span {(p : R)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hram : (Ideal.span {(p : ℤ)}).ramificationIdx' P = c := by
    apply Ideal.ramificationIdx'_spec
    · rw [hmapZ, hIJ]
      exact le_trans (Ideal.mul_mono_right le_top) (le_of_eq (Ideal.mul_top _))
    · rw [hmapZ]
      intro hle
      have hdvd : P ^ c * P ∣ P ^ c * J := by
        rw [← pow_succ, ← hIJ, Ideal.dvd_iff_le]
        exact hle
      have hPc : P ^ c ≠ 0 := pow_ne_zero _ (by
        intro h0
        exact hP.ne_top (by
          rw [Ideal.zero_eq_bot] at h0
          rw [h0] at hIP
          exact absurd (le_bot_iff.mp hIP) hIne))
      have hPJdvd : P ∣ J := (mul_dvd_mul_iff_left hPc).mp hdvd
      apply hP.ne_top
      rw [← hPJ]
      exact (sup_eq_left.mpr (Ideal.le_of_dvd hPJdvd)).symm
  rw [hDtop, hUnr, not_dvd_differentIdeal_iff, Algebra.isUnramifiedAt_iff_of_isDedekindDomain,
    ← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P hspZ, hram]
end GlobalTheory.Proof.different_power_unramified_iff
