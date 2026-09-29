-- Prove2me | solution 1 for MvFormalGroup.coeff_rescaledLog_mem_span_of_three_le_degree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/7782b7e2-064e-5c82-a12f-16c4a152a24f

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Theorems.Thm_MvFormalGroup_natCast_mul_coeff_add_single_mem_span_pow_degree_of_subst_rescale_eq_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_coeff_rescaledLog_mem_span_of_three_le_degree
p2m_attr_erase "instance" "MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid"
p2m_attr_erase "simp" "MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast"

set_option autoImplicit false
open MvPowerSeries

universe u

namespace S17RQ

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]

theorem mem_of_natCast_mul_mem {u k : ℕ} (hu : ¬ p ∣ u) {x : 𝓞}
    (hx : (u : 𝓞) * x ∈ Ideal.span {(p : 𝓞) ^ k}) : x ∈ Ideal.span {(p : 𝓞) ^ k} := by
  have hcop : Nat.Coprime u (p ^ k) :=
    Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hu).symm
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have h1 : ((a : ℤ) : 𝓞) * (u : 𝓞) + ((b : ℤ) : 𝓞) * (p : 𝓞) ^ k = 1 := by
    have := congrArg (Int.castRingHom 𝓞) hab
    simpa using this
  have : x = ((a : ℤ) : 𝓞) * ((u : 𝓞) * x) + ((b : ℤ) : 𝓞) * x * (p : 𝓞) ^ k := by
    calc x = (((a : ℤ) : 𝓞) * (u : 𝓞) + ((b : ℤ) : 𝓞) * (p : 𝓞) ^ k) * x := by rw [h1, one_mul]
      _ = _ := by ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx)
    (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

theorem mem_of_pow_mul_mem (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) {v k : ℕ} (hvk : v ≤ k) {x : 𝓞}
    (hx : (p : 𝓞) ^ v * x ∈ Ideal.span {(p : 𝓞) ^ k}) : x ∈ Ideal.span {(p : 𝓞) ^ (k - v)} := by
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hx
  refine Ideal.mem_span_singleton'.2 ⟨t, ?_⟩
  have : (p : 𝓞) ^ v * (t * (p : 𝓞) ^ (k - v)) = (p : 𝓞) ^ v * x := by
    rw [← ht, mul_comm ((p:𝓞)^v), mul_assoc, ← pow_add, Nat.sub_add_cancel hvk]
  exact (mul_cancel_left_mem_nonZeroDivisors (pow_mem hp v)).1 this

theorem two_pow_gt : ∀ n : ℕ, 3 ≤ n → n < 2 ^ (n - 1)
  | 0, h => by omega
  | 1, h => by omega
  | 2, h => by omega
  | 3, _ => by norm_num
  | n + 4, _ => by
    have ih := two_pow_gt (n + 3) (by omega)
    rw [show n + 4 - 1 = (n + 3 - 1) + 1 by omega, pow_succ]
    omega

theorem main (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) {d : ℕ} (φi : MvPowerSeries (Fin d) 𝓞)
    (hφint : ∀ (j : Fin d) (m : Fin d →₀ ℕ),
      ((m j + 1 : ℕ) : 𝓞) * φi.coeff (m + Finsupp.single j 1) ∈ Ideal.span {(p : 𝓞) ^ m.degree}) :
    (∀ m : Fin d →₀ ℕ, 3 ≤ m.degree → φi.coeff m ∈ Ideal.span {(p : 𝓞)}) ∧
    (∀ j k : Fin d, j ≠ k → φi.coeff (Finsupp.single j 1 + Finsupp.single k 1) ∈ Ideal.span {(p : 𝓞)}) := by
  classical
  constructor
  · intro m' hm'
    have hne : m' ≠ 0 := by rintro rfl; simp at hm'
    obtain ⟨j, hj⟩ : ∃ j, m' j ≠ 0 := by
      by_contra h; push Not at h; exact hne (Finsupp.ext h)

    set m := m' - Finsupp.single j 1 with hm
    have hmm' : m + Finsupp.single j 1 = m' := by
      ext s
      simp only [hm, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
      split_ifs with hs
      · subst hs; omega
      · omega
    have hmj : m j + 1 = m' j := by
      have := congrArg (fun f => f j) hmm'
      simpa [Finsupp.single_eq_same] using this
    have hdeg : m.degree + 1 = m'.degree := by
      rw [← hmm', map_add, Finsupp.degree_single]
    have h0 := hφint j m
    rw [hmm', hmj] at h0

    obtain ⟨v, u, hu, hvu⟩ := Nat.exists_eq_pow_mul_and_not_dvd hj p (Nat.Prime.ne_one Fact.out)
    rw [hvu, Nat.cast_mul, Nat.cast_pow, mul_assoc] at h0

    have hpv : p ^ v ≤ m'.degree := by
      calc p ^ v ≤ p ^ v * u := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (by rintro rfl; exact hu (dvd_zero p)))
        _ = m' j := hvu.symm
        _ ≤ m'.degree := Finsupp.le_degree j m'
    have hv : v + 2 ≤ m'.degree := by
      by_contra hlt
      have hv1 : m'.degree - 1 ≤ v := by omega
      have h2 : 2 ^ (m'.degree - 1) ≤ p ^ v :=
        le_trans (Nat.pow_le_pow_left (Nat.Prime.two_le Fact.out) _) (Nat.pow_le_pow_right (Nat.Prime.pos Fact.out) hv1)
      have := two_pow_gt m'.degree hm'
      omega

    have h1 : (u : 𝓞) * φi.coeff m' ∈ Ideal.span {(p : 𝓞) ^ (m.degree - v)} := by
      apply mem_of_pow_mul_mem p hp (by omega)
      rw [← mul_assoc, mul_comm ((p:𝓞)^v), mul_assoc] at h0
      rw [mul_left_comm] at h0

      exact h0
    have h2 := mem_of_natCast_mul_mem p hu h1
    refine Ideal.span_singleton_le_span_singleton.2 ?_ h2
    exact dvd_pow_self _ (by omega)
  · intro j k hjk
    have h0 := hφint j (Finsupp.single k 1)
    rw [Finsupp.single_apply, if_neg (Ne.symm hjk), zero_add, Nat.cast_one, one_mul, Finsupp.degree_single,
      pow_one, add_comm] at h0
    exact h0

end S17RQ

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
    (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
    (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
    (φ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφ1 : MvFormalGroup.linearPart φ = 1)
    (hφF : ∀ i, subst Fp (φ i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i)) :
    (∀ (i : Fin d) (m : Fin d →₀ ℕ), 3 ≤ m.degree → (φ i).coeff m ∈ Ideal.span {(p : 𝓞)}) ∧
    (∀ (i j k : Fin d), j ≠ k →
      (φ i).coeff (Finsupp.single j 1 + Finsupp.single k 1) ∈ Ideal.span {(p : 𝓞)}) := by
  refine ⟨fun i m hm => ?_, fun i j k hjk => ?_⟩
  · exact (S17RQ.main p hp (φ i) (fun j m =>
      MvFormalGroup.natCast_mul_coeff_add_single_mem_span_pow_degree_of_subst_rescale_eq_add p hp F Fp hFp hFp0 φ
        hφ0 hφ1 hφF i j m)).1 m hm
  · exact (S17RQ.main p hp (φ i) (fun j m =>
      MvFormalGroup.natCast_mul_coeff_add_single_mem_span_pow_degree_of_subst_rescale_eq_add p hp F Fp hFp hFp0 φ
        hφ0 hφ1 hφF i j m)).2 j k hjk

end S_MvFormalGroup_coeff_rescaledLog_mem_span_of_three_le_degree
end P2MW
export P2MW.S_MvFormalGroup_coeff_rescaledLog_mem_span_of_three_le_degree (solution)
