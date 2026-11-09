-- Prove2me | solution 1 for LLLFactor.Factors.claim_2_11
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T21:51:32.013762+00:00
-- url     : https://prove2.me/submissions/b2f0a63b-d759-400b-b40c-b7a78d5f3dfa

import Definitions.Def_LLLFactor_Factors_Setting

open Polynomial LLLFactor.Factors

namespace Claim211Proof

lemma modPk_surjective (q : ℕ) : Function.Surjective (modPk q) :=
  Polynomial.map_surjective _ ZMod.intCast_surjective

lemma modPk_eq_zero_iff (q : ℕ) (f : ℤ[X]) :
    modPk q f = 0 ↔ C (q : ℤ) ∣ f := by
  rw [C_dvd_iff_dvd_coeff]
  constructor
  · intro hf i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (f.coeff i) q).mp
    have hi := congrArg (fun g : (ZMod q)[X] => g.coeff i) hf
    simpa [modPk] using hi
  · intro hf
    ext i
    simpa [modPk] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd (f.coeff i) q).mpr (hf i)

lemma coprime_mod_prime_power {p k : ℕ} {h g : ℤ[X]}
    (hc : IsCoprime (modPk p h) (modPk p g)) :
    IsCoprime (modPk (p ^ k) h) (modPk (p ^ k) g) := by
  obtain ⟨a, c, hac⟩ := hc
  obtain ⟨A, rfl⟩ := modPk_surjective p a
  obtain ⟨C', rfl⟩ := modPk_surjective p c
  have hz : modPk p (1 - (A * h + C' * g)) = 0 := by
    simpa [modPk, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul] using
      sub_eq_zero.mpr hac.symm
  obtain ⟨V, hV⟩ := (modPk_eq_zero_iff p _).mp hz
  let R := (ZMod (p ^ k))[X]
  let v : R := Polynomial.C (p : ZMod (p ^ k)) * modPk (p ^ k) V
  have hv : v ^ k = 0 := by
    dsimp [v]
    rw [mul_pow, ← map_pow]
    have hp : (p : ZMod (p ^ k)) ^ k = 0 := by
      rw [← Nat.cast_pow]
      exact ZMod.natCast_self (p ^ k)
    rw [hp, map_zero, zero_mul]
  have he : modPk (p ^ k) A * modPk (p ^ k) h +
      modPk (p ^ k) C' * modPk (p ^ k) g = 1 - v := by
    have ht := congrArg (modPk (p ^ k)) hV
    simp only [modPk, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_add,
      Polynomial.map_mul, map_natCast, Polynomial.map_natCast] at ht
    dsimp [v, modPk]
    simp only [map_natCast]
    linear_combination -ht
  refine ⟨(∑ i ∈ Finset.range k, v ^ i) * modPk (p ^ k) A,
    (∑ i ∈ Finset.range k, v ^ i) * modPk (p ^ k) C', ?_⟩
  calc
    _ = (∑ i ∈ Finset.range k, v ^ i) *
        (modPk (p ^ k) A * modPk (p ^ k) h +
          modPk (p ^ k) C' * modPk (p ^ k) g) := by ring
    _ = 1 := by rw [he, geom_sum_mul_neg, hv, sub_zero]

lemma cancel_mod_prime_power {p k : ℕ} {h g u : ℤ[X]}
    (hc : IsCoprime (modPk p h) (modPk p g))
    (hd : modPk (p ^ k) h ∣ modPk (p ^ k) (g * u)) :
    modPk (p ^ k) h ∣ modPk (p ^ k) u := by
  apply (coprime_mod_prime_power (k := k) hc).dvd_of_dvd_mul_left
  simpa [modPk, Polynomial.map_mul] using hd

end Claim211Proof

theorem solution {p k : ℕ} (f h : ℤ[X]) (hS : IsSetting p k f h)
    (m : ℕ) (_hm : h.natDegree ≤ m)
    (b : ℤ[X]) (hbL : b ∈ latticeL p k h m) (hb0 : b ≠ 0)
    (g : ℤ[X]) (hgf : g ∣ f) (hgb : g ∣ b) (_hg_gcd : ∀ d : ℤ[X], d ∣ f → d ∣ b → d ∣ g)
    (hndvd : ¬ modPk p h ∣ modPk p g) :
    ∀ lam mu' : ℤ[X],
      lam.degree < ((b.natDegree - g.natDegree : ℕ) : WithBot ℕ) →
      mu'.degree < ((f.natDegree - g.natDegree : ℕ) : WithBot ℕ) →
      (lam * f + mu' * b).degree < ((g.natDegree + h.natDegree : ℕ) : WithBot ℕ) →
      ∀ i : ℕ, ((p ^ k : ℕ) : ℤ) ∣ (lam * f + mu' * b).coeff i := by
  intro lam mu' _hlam _hmu hdeg i
  let : Fact p.Prime := ⟨hS.prime⟩
  have : Nontrivial (ZMod (p ^ k)) :=
    ZMod.nontrivial_iff.mpr (ne_of_gt (one_lt_pow₀ hS.prime.one_lt (ne_of_gt hS.k_pos)))
  let v : ℤ[X] := lam * f + mu' * b
  have hgv : g ∣ v := dvd_add (dvd_mul_of_dvd_right hgf lam) (dvd_mul_of_dvd_right hgb mu')
  obtain ⟨w, hw⟩ := hgv
  have hmod_v : modPk (p ^ k) h ∣ modPk (p ^ k) v := by
    dsimp [v]
    simp only [modPk, Polynomial.map_add, Polynomial.map_mul]
    exact dvd_add (dvd_mul_of_dvd_right hS.dvd_mod_pk _) (dvd_mul_of_dvd_right hbL.2 _)
  have hcop : IsCoprime (modPk p h) (modPk p g) :=
    hS.irreducible_mod_p.coprime_iff_not_dvd.mpr hndvd
  have hmod_w : modPk (p ^ k) h ∣ modPk (p ^ k) w :=
    Claim211Proof.cancel_mod_prime_power hcop (hw ▸ hmod_v)
  have hw_zero : modPk (p ^ k) w = 0 := by
    by_contra hw_ne
    obtain ⟨q, hq⟩ := hmod_w
    have hq_ne : q ≠ 0 := by
      intro hq0
      apply hw_ne
      simp [hq, hq0]
    have hmonic : (modPk (p ^ k) h).Monic := hS.monic.map _
    have hdeg_mod_w : (modPk (p ^ k) h).natDegree ≤ (modPk (p ^ k) w).natDegree := by
      rw [hq, hmonic.natDegree_mul' hq_ne]
      omega
    have hdeg_h : (modPk (p ^ k) h).natDegree = h.natDegree := hS.monic.natDegree_map _
    have hdeg_w : h.natDegree ≤ w.natDegree := by
      calc h.natDegree = (modPk (p ^ k) h).natDegree := hdeg_h.symm
        _ ≤ (modPk (p ^ k) w).natDegree := hdeg_mod_w
        _ ≤ w.natDegree := Polynomial.natDegree_map_le
    have hg0 : g ≠ 0 := by
      rintro rfl
      exact hb0 (zero_dvd_iff.mp hgb)
    have hw0 : w ≠ 0 := by
      rintro rfl
      exact hw_ne (by simp [modPk])
    have hv0 : v ≠ 0 := by
      rw [hw]
      exact mul_ne_zero hg0 hw0
    have hv_nat : v.natDegree = g.natDegree + w.natDegree := by
      rw [hw, Polynomial.natDegree_mul hg0 hw0]
    have hv_deg : v.degree = ((g.natDegree + w.natDegree : ℕ) : WithBot ℕ) := by
      rw [Polynomial.degree_eq_natDegree hv0, hv_nat]
    change v.degree < ((g.natDegree + h.natDegree : ℕ) : WithBot ℕ) at hdeg
    rw [hv_deg, Nat.cast_lt] at hdeg
    omega
  have hv_zero : modPk (p ^ k) v = 0 := by
    rw [hw]
    unfold modPk at hw_zero ⊢
    rw [Polynomial.map_mul, hw_zero, mul_zero]
  exact (C_dvd_iff_dvd_coeff _ _).mp ((Claim211Proof.modPk_eq_zero_iff (p ^ k) v).mp hv_zero) i
