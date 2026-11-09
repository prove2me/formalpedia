-- Prove2me | solution 1 for LLLFactor.Factors.prop_2_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T22:03:03.477617+00:00
-- url     : https://prove2.me/submissions/82df1c48-2d10-48f4-8f7c-599c61bd6db5

import Definitions.Def_LLLFactor_Factors_Setting

open Polynomial LLLFactor.Factors

namespace Prop25Proof

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

lemma modPk_dvd_modP {p k : ℕ} (hk : 0 < k) {a b : ℤ[X]}
    (hd : modPk (p ^ k) a ∣ modPk (p ^ k) b) : modPk p a ∣ modPk p b := by
  let φ : ZMod (p ^ k) →+* ZMod p := ZMod.castHom (dvd_pow_self p (ne_of_gt hk)) (ZMod p)
  have hcomp : φ.comp (Int.castRingHom (ZMod (p ^ k))) = Int.castRingHom (ZMod p) :=
    RingHom.ext_int _ _
  have hmap : ∀ g : ℤ[X], (modPk (p ^ k) g).map φ = modPk p g := by
    intro g
    dsimp [modPk]
    rw [Polynomial.map_map, hcomp]
  rw [← hmap a, ← hmap b]
  exact Polynomial.map_dvd φ hd

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

lemma h0_dvd_mod_pk {p k : ℕ} {f h h0 : ℤ[X]}
    (hS : IsSetting p k f h) (hh0 : IsH0 p f h h0) :
    modPk (p ^ k) h ∣ modPk (p ^ k) h0 := by
  let : Fact p.Prime := ⟨hS.prime⟩
  obtain ⟨q, hf⟩ := hh0.2.1
  have hn : ¬ modPk p h ∣ modPk p q := by
    intro hq
    apply hS.sq_not_dvd_mod_p
    rw [hf]
    simpa [modPk, Polynomial.map_mul, pow_two] using mul_dvd_mul hh0.2.2 hq
  have hc := hS.irreducible_mod_p.coprime_iff_not_dvd.mpr hn
  apply cancel_mod_prime_power hc
  simpa [hf, mul_comm] using hS.dvd_mod_pk

lemma h0_dvd_of_factor_mod_p {p k : ℕ} {f h h0 g : ℤ[X]}
    (hS : IsSetting p k f h) (hh0 : IsH0 p f h h0)
    (hgf : g ∣ f) (hhg : modPk p h ∣ modPk p g) : h0 ∣ g := by
  obtain ⟨q, hf⟩ := hgf
  have hd : h0 ∣ g * q := hf ▸ hh0.2.1
  rcases hh0.1.prime.dvd_or_dvd hd with hg | hq
  · exact hg
  · exfalso
    apply hS.sq_not_dvd_mod_p
    have hmodq : modPk p h ∣ modPk p q :=
      hh0.2.2.trans (Polynomial.map_dvd (Int.castRingHom (ZMod p)) hq)
    rw [hf]
    simpa [modPk, Polynomial.map_mul, pow_two] using mul_dvd_mul hhg hmodq

lemma exists_h0 {p k : ℕ} {f h : ℤ[X]} (hS : IsSetting p k f h) :
    ∃ h₀ : ℤ[X], IsH0 p f h h₀ := by
  let : Fact p.Prime := ⟨hS.prime⟩
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact lt_irrefl 0 hS.deg_f_pos
  have hdf : modPk p h ∣ modPk p f := modPk_dvd_modP hS.k_pos hS.dvd_mod_pk
  have hind : ∀ q : ℤ[X], q ≠ 0 → modPk p h ∣ modPk p q →
      ∃ h₀ : ℤ[X], Irreducible h₀ ∧ h₀ ∣ q ∧ modPk p h ∣ modPk p h₀ := by
    intro q
    refine WfDvdMonoid.induction_on_irreducible q ?_ ?_ ?_
    · intro hq0
      exact False.elim (hq0 rfl)
    · intro u hu _ hdu
      exfalso
      have hu_mod : IsUnit (modPk p u) :=
        hu.map (Polynomial.mapRingHom (Int.castRingHom (ZMod p)))
      exact hS.irreducible_mod_p.not_isUnit (isUnit_of_dvd_unit hdu hu_mod)
    · intro a b ha0 hb ih _ hmod
      unfold modPk at hmod
      rw [Polynomial.map_mul] at hmod
      rcases hS.irreducible_mod_p.prime.dvd_or_dvd hmod with hpb | hpa
      · exact ⟨b, hb, dvd_mul_right b a, hpb⟩
      · obtain ⟨h₀, hh₀, hdvd, hmod0⟩ := ih ha0 hpa
        exact ⟨h₀, hh₀, hdvd.trans (dvd_mul_left a b), hmod0⟩
  obtain ⟨h₀, hh₀, hdvd, hmod0⟩ := hind f hf0 hdf
  exact ⟨h₀, hh₀, hdvd, hmod0⟩

end Prop25Proof

theorem solution {p k : ℕ} (f h : ℤ[X]) (hS : IsSetting p k f h) :
    (∃ h₀ : ℤ[X], IsH0 p f h h₀) ∧
    (∀ h₀ h₀' : ℤ[X], IsH0 p f h h₀ → IsH0 p f h h₀' → h₀' = h₀ ∨ h₀' = -h₀) ∧
    (∀ h₀ : ℤ[X], IsH0 p f h h₀ → ∀ g : ℤ[X], g ∣ f →
      ((modPk p h ∣ modPk p g ↔ modPk (p ^ k) h ∣ modPk (p ^ k) g) ∧
       (modPk (p ^ k) h ∣ modPk (p ^ k) g ↔ h₀ ∣ g))) ∧
    (∀ h₀ : ℤ[X], IsH0 p f h h₀ → modPk (p ^ k) h ∣ modPk (p ^ k) h₀) := by
  refine ⟨Prop25Proof.exists_h0 hS, ?_, ?_, fun h₀ hh₀ => Prop25Proof.h0_dvd_mod_pk hS hh₀⟩
  · intro h₀ h₀' hh₀ hh₀'
    have hd1 : h₀ ∣ h₀' := Prop25Proof.h0_dvd_of_factor_mod_p hS hh₀ hh₀'.2.1 hh₀'.2.2
    have hd2 : h₀' ∣ h₀ := Prop25Proof.h0_dvd_of_factor_mod_p hS hh₀' hh₀.2.1 hh₀.2.2
    obtain ⟨c, hc⟩ := hd1
    obtain ⟨d, hd⟩ := hd2
    have h0_ne : h₀ ≠ 0 := hh₀.1.ne_zero
    have hcd : c * d = 1 := by
      apply mul_left_cancel₀ h0_ne
      calc h₀ * (c * d) = (h₀ * c) * d := (mul_assoc h₀ c d).symm
        _ = h₀' * d := by rw [hc]
        _ = h₀ := hd.symm
        _ = h₀ * 1 := (mul_one h₀).symm
    have huc : IsUnit c := ⟨⟨c, d, hcd, mul_comm c d ▸ hcd⟩, rfl⟩
    obtain ⟨r, hr, hcr⟩ := Polynomial.isUnit_iff.mp huc
    rcases Int.isUnit_iff.mp hr with rfl | rfl
    · left
      rw [hc, ← hcr, map_one, mul_one]
    · right
      rw [hc, ← hcr, map_neg, map_one, mul_neg, mul_one]
  · intro h₀ hh₀ g hgf
    have h_h0_pk : modPk (p ^ k) h ∣ modPk (p ^ k) h₀ := Prop25Proof.h0_dvd_mod_pk hS hh₀
    have h13 : modPk p h ∣ modPk p g → h₀ ∣ g :=
      Prop25Proof.h0_dvd_of_factor_mod_p hS hh₀ hgf
    have h32 : h₀ ∣ g → modPk (p ^ k) h ∣ modPk (p ^ k) g := fun hd =>
      h_h0_pk.trans (Polynomial.map_dvd (Int.castRingHom (ZMod (p ^ k))) hd)
    have h21 : modPk (p ^ k) h ∣ modPk (p ^ k) g → modPk p h ∣ modPk p g :=
      Prop25Proof.modPk_dvd_modP hS.k_pos
    exact ⟨⟨fun h1 => h32 (h13 h1), h21⟩, ⟨fun h2 => h13 (h21 h2), h32⟩⟩
