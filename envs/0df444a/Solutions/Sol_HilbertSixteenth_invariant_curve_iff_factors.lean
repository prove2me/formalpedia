-- Prove2me | solution 1 for HilbertSixteenth.invariant_curve_iff_factors
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T03:59:27.330456+00:00
-- url     : https://prove2.me/submissions/a1aec718-943c-4d5f-aa64-95879f5f8f8d

import Mathlib
import Definitions.Def_HilbertSixteenth_PolyFields

namespace HilbertSixteenth.EE35788E

open HilbertSixteenth

noncomputable def Dv (V : PolyField) : Derivation ℝ Poly2 Poly2 :=
  V.P • MvPolynomial.pderiv 0 + V.Q • MvPolynomial.pderiv 1

lemma Dv_apply (V : PolyField) (f : Poly2) : V.derivation f = Dv V f := by
  simp [Dv, PolyField.derivation, Derivation.add_apply, Derivation.smul_apply, smul_eq_mul]

lemma D_C_mul (D : Derivation ℝ Poly2 Poly2) (c : ℝ) (x : Poly2) :
    D (MvPolynomial.C c * x) = MvPolynomial.C c * D x := by
  rw [Derivation.leibniz]
  have : D (MvPolynomial.C c) = 0 := by
    rw [← MvPolynomial.algebraMap_eq]; exact D.map_algebraMap c
  rw [this, smul_zero, add_zero, smul_eq_mul]

lemma D_pow_of (D : Derivation ℝ Poly2 Poly2) (g K : Poly2) (h : D g = K * g) (n : ℕ) :
    D (g ^ n) = ((n : Poly2) * K) * g ^ n := by
  rw [Derivation.leibniz_pow, h]
  rcases n with _ | m
  · simp
  · simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel, pow_succ]
    ring

lemma D_prod_of {r : ℕ} (D : Derivation ℝ Poly2 Poly2) (g Ks : Fin r → Poly2) (n : Fin r → ℕ)
    (h : ∀ i, D (g i) = Ks i * g i) (s : Finset (Fin r)) :
    D (∏ i ∈ s, g i ^ n i) = (∑ i ∈ s, (n i : Poly2) * Ks i) * ∏ i ∈ s, g i ^ n i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Derivation.leibniz, ih,
      D_pow_of D (g a) (Ks a) (h a), smul_eq_mul, smul_eq_mul]
    ring

lemma prime_of_irr {g : Poly2} (h : Irreducible g) : Prime g := h.prime

lemma not_dvd_rest {r : ℕ} (c : ℝ) (hc : c ≠ 0) (g : Fin r → Poly2) (n : Fin r → ℕ)
    (hirr : ∀ i, Irreducible (g i))
    (hdist : ∀ i j, i ≠ j → ¬ Associated (g i) (g j)) (i : Fin r) :
    ¬ g i ∣ MvPolynomial.C c * ∏ j ∈ Finset.univ.erase i, g j ^ n j := by
  intro hd
  have hp : Prime (g i) := (hirr i).prime
  rcases hp.dvd_or_dvd hd with h1 | h1
  · apply (hirr i).not_isUnit
    exact isUnit_of_dvd_unit h1 ((Ne.isUnit hc).map MvPolynomial.C)
  · rcases (hp.dvd_finsetProd_iff _).mp h1 with ⟨j, hj, hdj⟩
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have := hp.dvd_of_dvd_pow hdj
    exact hdist i j (Ne.symm hji) ((hirr i).associated_of_dvd (hirr j) this)

lemma f_ne_zero {r : ℕ} (c : ℝ) (hc : c ≠ 0) (g : Fin r → Poly2) (n : Fin r → ℕ)
    (hirr : ∀ i, Irreducible (g i)) :
    MvPolynomial.C c * ∏ i, g i ^ n i ≠ 0 := by
  refine mul_ne_zero ?_ ?_
  · simpa using hc
  · rw [Finset.prod_ne_zero_iff]
    intro i _
    exact pow_ne_zero _ (hirr i).ne_zero

lemma factor_inv {r : ℕ} (D : Derivation ℝ Poly2 Poly2) (c : ℝ) (hc : c ≠ 0)
    (g : Fin r → Poly2) (n : Fin r → ℕ) (hirr : ∀ i, Irreducible (g i))
    (hdist : ∀ i j, i ≠ j → ¬ Associated (g i) (g j)) (hn : ∀ i, 1 ≤ n i)
    (K : Poly2) (hK : D (MvPolynomial.C c * ∏ i, g i ^ n i) = K * (MvPolynomial.C c * ∏ i, g i ^ n i))
    (i : Fin r) : ∃ K' : Poly2, D (g i) = K' * g i := by
  classical
  set u := MvPolynomial.C c * ∏ j ∈ Finset.univ.erase i, g j ^ n j with hu
  have hf : MvPolynomial.C c * ∏ j, g j ^ n j = g i ^ n i * u := by
    rw [hu, ← Finset.mul_prod_erase Finset.univ (fun j => g j ^ n j) (Finset.mem_univ i)]
    ring
  rw [hf, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    nsmul_eq_mul] at hK
  obtain ⟨m, hm⟩ : ∃ m, n i = m + 1 := ⟨n i - 1, by have := hn i; omega⟩
  rw [hm, Nat.add_sub_cancel, pow_succ] at hK
  have hg0 : g i ≠ 0 := (hirr i).ne_zero
  have key : g i ^ m * (u * ((m + 1 : ℕ) : Poly2) * D (g i)) =
      g i ^ m * (g i * (K * u - D u)) := by
    linear_combination hK
  have key2 := mul_left_cancel₀ (pow_ne_zero m hg0) key
  have hdvd : g i ∣ u * (((m + 1 : ℕ) : Poly2) * D (g i)) := ⟨K * u - D u, by rw [← key2]; ring⟩
  have hp : Prime (g i) := (hirr i).prime
  rcases hp.dvd_or_dvd hdvd with h1 | h1
  · exact absurd h1 (not_dvd_rest c hc g n hirr hdist i)
  · have hunit : IsUnit (((m + 1 : ℕ) : Poly2)) := by
      have he : ((m + 1 : ℕ) : Poly2) = MvPolynomial.C ((m + 1 : ℕ) : ℝ) := (map_natCast _ _).symm
      rw [he]
      exact (Ne.isUnit (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m) : ((m + 1 : ℕ) : ℝ) ≠ 0)).map
        MvPolynomial.C
    obtain ⟨q, hq⟩ := (hunit.dvd_mul_left).mp h1
    exact ⟨q, by rw [hq]; ring⟩

end HilbertSixteenth.EE35788E

set_option autoImplicit false

open HilbertSixteenth in
theorem solution (V : PolyField) (r : ℕ) (c : ℝ) (hc : c ≠ 0)
    (g : Fin r → Poly2) (n : Fin r → ℕ) (hirr : ∀ i, Irreducible (g i))
    (hdist : ∀ i j, i ≠ j → ¬ Associated (g i) (g j)) (hn : ∀ i, 1 ≤ n i) :
    ((∃ K : Poly2, IsInvariantCurve V (MvPolynomial.C c * ∏ i, g i ^ n i) K) ↔
        ∀ i, ∃ K : Poly2, IsInvariantCurve V (g i) K) ∧
      ∀ (K : Poly2) (Ks : Fin r → Poly2),
        IsInvariantCurve V (MvPolynomial.C c * ∏ i, g i ^ n i) K →
        (∀ i, IsInvariantCurve V (g i) (Ks i)) →
        K = ∑ i, (n i : Poly2) * Ks i := by
  simp only [IsInvariantCurve, EE35788E.Dv_apply]
  refine ⟨⟨fun ⟨K, hK⟩ i => EE35788E.factor_inv (EE35788E.Dv V) c hc g n hirr hdist hn K hK i, fun h => ?_⟩, ?_⟩
  · choose Ks hKs using h
    refine ⟨∑ i, (n i : Poly2) * Ks i, ?_⟩
    rw [EE35788E.D_C_mul, EE35788E.D_prod_of (EE35788E.Dv V) g Ks n hKs]
    ring
  · intro K Ks hK hKs
    rw [EE35788E.D_C_mul, EE35788E.D_prod_of (EE35788E.Dv V) g Ks n hKs] at hK
    have h0 := EE35788E.f_ne_zero c hc g n hirr
    have : (K - ∑ i, (n i : Poly2) * Ks i) * (MvPolynomial.C c * ∏ i, g i ^ n i) = 0 := by
      linear_combination -hK
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right h0)
