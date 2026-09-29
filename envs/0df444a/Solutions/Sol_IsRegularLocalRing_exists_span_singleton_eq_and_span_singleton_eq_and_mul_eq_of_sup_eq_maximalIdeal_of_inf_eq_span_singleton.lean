-- Prove2me | solution 1 for IsRegularLocalRing.exists_span_singleton_eq_and_span_singleton_eq_and_mul_eq_of_sup_eq_maximalIdeal_of_inf_eq_span_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/e28ab08e-7a41-54e9-aaac-4d1f17bdb529

import Mathlib
import Theorems.Thm_IsRegularLocalRing_isDomain
import Theorems.Thm_IsRegularLocalRing_quotient_span_singleton_of_notMem_sq_of_forall_minimalPrimes_notMem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsRegularLocalRing_exists_span_singleton_eq_and_span_singleton_eq_and_mul_eq_of_sup_eq_maximalIdeal_of_inf_eq_span_singleton

set_option autoImplicit false

set_option maxHeartbeats 3200000

namespace RegDim2

open IsLocalRing

theorem exists_eq_span_singleton {R : Type*} [CommRing R] [IsRegularLocalRing R] [IsDomain R] (hdim : ringKrullDim R ≤ 2)
    (P Q : Ideal R) [P.IsPrime] (hP : P ≠ maximalIdeal R) (hQ : Q ≠ maximalIdeal R)
    (hsup : P ⊔ Q = maximalIdeal R) :
    ∃ u : R, u ≠ 0 ∧ P = Ideal.span {u} := by
  classical
  have hPle : P ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
  have hQle : Q ≤ maximalIdeal R := by rw [← hsup]; exact le_sup_right

  have hP2 : ¬ P ≤ maximalIdeal R ^ 2 := by
    intro hle
    apply hQ
    apply le_antisymm hQle
    have hfg : (maximalIdeal R).FG := IsNoetherian.noetherian _
    refine Submodule.le_of_le_smul_of_le_jacobson_bot hfg (IsLocalRing.maximalIdeal_le_jacobson ⊥) ?_
    calc maximalIdeal R = P ⊔ Q := hsup.symm
      _ ≤ maximalIdeal R ^ 2 ⊔ Q := sup_le_sup_right hle Q
      _ = Q ⊔ maximalIdeal R • maximalIdeal R := by rw [sup_comm, Ideal.smul_eq_mul, pow_two]
  obtain ⟨u, huP, hu2⟩ := Set.not_subset.mp hP2
  have hu𝔪 : u ∈ maximalIdeal R := hPle huP
  have hu0 : u ≠ 0 := by rintro rfl; exact hu2 (Ideal.zero_mem _)

  haveI : Nontrivial (R ⧸ Ideal.span {u}) :=
    Ideal.Quotient.nontrivial_iff.mpr (by rw [Ne, Ideal.span_singleton_eq_top]; exact fun h => (IsLocalRing.mem_maximalIdeal _).mp hu𝔪 h)
  haveI : IsLocalRing (R ⧸ Ideal.span {u}) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have hmin : ∀ p ∈ minimalPrimes R, u ∉ p := by
    intro p hp
    rw [IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff] at hp
    subst hp
    simpa using hu0
  have hreg := (IsRegularLocalRing.quotient_span_singleton_of_notMem_sq_of_forall_minimalPrimes_notMem R hu𝔪 hu2 hmin).1
  haveI := hreg
  haveI : IsDomain (R ⧸ Ideal.span {u}) := IsRegularLocalRing.isDomain _
  haveI hprime : (Ideal.span {u}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance

  have hle : Ideal.span {u} ≤ P := by rw [Ideal.span_le, Set.singleton_subset_iff]; exact huP
  refine ⟨u, hu0, ?_⟩
  by_contra hne
  have hlt1 : (⊥ : Ideal R) < Ideal.span {u} := by
    rw [bot_lt_iff_ne_bot, Ne, Ideal.span_singleton_eq_bot]; exact hu0
  have hlt2 : Ideal.span {u} < P := lt_of_le_of_ne hle (Ne.symm hne)
  have hlt3 : P < maximalIdeal R := lt_of_le_of_ne hPle hP
  let p0 : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  let p1 : PrimeSpectrum R := ⟨Ideal.span {u}, hprime⟩
  let p2 : PrimeSpectrum R := ⟨P, inferInstance⟩
  let p3 : PrimeSpectrum R := ⟨maximalIdeal R, inferInstance⟩
  have h01 : p0 < p1 := (PrimeSpectrum.asIdeal_lt_asIdeal (x := p0) (y := p1)).mp hlt1
  have h12 : p1 < p2 := (PrimeSpectrum.asIdeal_lt_asIdeal (x := p1) (y := p2)).mp hlt2
  have h23 : p2 < p3 := (PrimeSpectrum.asIdeal_lt_asIdeal (x := p2) (y := p3)).mp hlt3
  let s : LTSeries (PrimeSpectrum R) :=
    { length := 3
      toFun := ![p0, p1, p2, p3]
      step := fun i => by
        fin_cases i
        · exact h01
        · exact h12
        · exact h23 }
  have hs : s.length = 3 := rfl
  have h3 : (3 : WithBot ℕ∞) ≤ ringKrullDim R := by
    have := Order.LTSeries.length_le_krullDim s
    rw [hs] at this
    exact_mod_cast this
  have h32 : (3 : WithBot ℕ∞) ≤ 2 := h3.trans hdim
  exact absurd h32 (by decide)

end RegDim2

open RegDim2 in

theorem solution
    {R : Type*} [CommRing R] [IsRegularLocalRing R] (hdim : ringKrullDim R ≤ 2)
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (hP : P ≠ IsLocalRing.maximalIdeal R) (hQ : Q ≠ IsLocalRing.maximalIdeal R)
    (hsup : P ⊔ Q = IsLocalRing.maximalIdeal R)
    (π : R) (hπ : π ≠ 0) (hinf : P ⊓ Q = Ideal.span {π}) :
    ∃ (u v : R) (c : Rˣ), P = Ideal.span {u} ∧ Q = Ideal.span {v} ∧ u * v = c * π := by

  classical
  haveI : IsDomain R := IsRegularLocalRing.isDomain R
  obtain ⟨u, hu0, hPu⟩ := exists_eq_span_singleton hdim P Q hP hQ hsup
  obtain ⟨v, hv0, hQv⟩ := exists_eq_span_singleton hdim Q P hQ hP (by rw [sup_comm]; exact hsup)

  have huQ : u ∉ Q := by
    intro huQ
    apply hQ
    have hPQ : P ≤ Q := by rw [hPu, Ideal.span_le, Set.singleton_subset_iff]; exact huQ
    rw [← hsup, sup_eq_right.mpr hPQ]

  have hπP : π ∈ P := by
    have : π ∈ P ⊓ Q := by rw [hinf]; exact Ideal.mem_span_singleton_self π
    exact this.1
  rw [hPu, Ideal.mem_span_singleton'] at hπP
  obtain ⟨π', hπ'⟩ := hπP
  have hπ'Q : π' ∈ Q := by
    have hmem : π' * u ∈ Q := by
      rw [hπ']
      have : π ∈ P ⊓ Q := by rw [hinf]; exact Ideal.mem_span_singleton_self π
      exact this.2
    exact (Ideal.IsPrime.mem_or_mem inferInstance hmem).resolve_right huQ
  rw [hQv, Ideal.mem_span_singleton'] at hπ'Q
  obtain ⟨c, hc⟩ := hπ'Q
  have huv : u * v ∈ Ideal.span {π} := by
    rw [← hinf]
    refine ⟨?_, ?_⟩
    · rw [hPu]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self u)
    · rw [hQv]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self v)
  rw [Ideal.mem_span_singleton'] at huv
  obtain ⟨d, hd⟩ := huv

  have hπuvc : π = c * (u * v) := by
    rw [← hπ', ← hc]; ring
  have hdc : d * c = 1 := by
    have h1 : (d * c - 1) * π = 0 := by
      have : π = d * c * π := by
        conv_lhs => rw [hπuvc, ← hd]
        ring
      linear_combination (-1 : R) * this
    rcases mul_eq_zero.mp h1 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hπ
  refine ⟨u, v, ⟨d, c, hdc, by rw [mul_comm]; exact hdc⟩, hPu, hQv, ?_⟩
  show u * v = d * π
  exact hd.symm

end S_IsRegularLocalRing_exists_span_singleton_eq_and_span_singleton_eq_and_mul_eq_of_sup_eq_maximalIdeal_of_inf_eq_span_singleton
end P2MW
export P2MW.S_IsRegularLocalRing_exists_span_singleton_eq_and_span_singleton_eq_and_mul_eq_of_sup_eq_maximalIdeal_of_inf_eq_span_singleton (solution)
