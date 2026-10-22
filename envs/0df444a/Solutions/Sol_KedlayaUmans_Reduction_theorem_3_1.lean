-- Prove2me | solution 1 for KedlayaUmans.Reduction.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T17:59:10.371765+00:00
-- url     : https://prove2.me/submissions/9a6df87d-1790-4287-a6fb-507f25a05642

import Mathlib
import Definitions.Def_KedlayaUmans_Reduction_Algorithm

set_option autoImplicit false

namespace KU31

open Polynomial

lemma digit_sum (b x ℓ : ℕ) (hb : 2 ≤ b) :
    ∑ j : Fin ℓ, (Nat.digits b x).getD j 0 * b ^ (j : ℕ) = x % b ^ ℓ := by
  simp only [Nat.getD_digits _ _ hb]
  rw [Fin.sum_univ_eq_sum_range (fun j => x / b ^ j % b * b ^ j) ℓ]
  induction ℓ with
  | zero => simp [Nat.mod_one]
  | succ k ih => rw [Finset.sum_range_succ, ih, Nat.mod_pow_succ]; ring

lemma digit_le (b x j : ℕ) (hb : 2 ≤ b) : (Nat.digits b x).getD j 0 ≤ b - 1 := by
  rw [Nat.getD_digits _ _ hb]
  have := Nat.mod_lt (x / b ^ j) (by omega : b > 0)
  omega

variable {R : Type*} [CommRing R]

lemma interp_natDegree {n : ℕ} (β v : Fin n → R) :
    (KedlayaUmans.Reduction.interpolate β v).natDegree ≤ n - 1 := by
  unfold KedlayaUmans.Reduction.interpolate
  apply natDegree_sum_le_of_forall_le
  intro k _
  refine (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ j ∈ Finset.univ.erase k, natDegree ((X - C (β j)) * C (Ring.inverse (β k - β j)))
      ≤ ∑ j ∈ Finset.univ.erase k, 1 := by
        apply Finset.sum_le_sum
        intro j _
        exact (natDegree_mul_C_le _ _).trans (natDegree_X_sub_C_le _)
    _ = n - 1 := by simp [Finset.card_erase_of_mem]

lemma interp_eval {n : ℕ} (β v : Fin n → R) (hβu : ∀ j k, j ≠ k → IsUnit (β j - β k))
    (k : Fin n) : (KedlayaUmans.Reduction.interpolate β v).eval (β k) = v k := by
  unfold KedlayaUmans.Reduction.interpolate
  rw [eval_finsetSum, Finset.sum_eq_single k]
  · rw [eval_mul, eval_C, eval_prod, Finset.prod_eq_one, mul_one]
    intro j hj
    have hjk : j ≠ k := Finset.ne_of_mem_erase hj
    simp only [eval_mul, eval_sub, eval_X, eval_C]
    exact Ring.mul_inverse_cancel _ (hβu k j hjk.symm)
  · intro k' _ hk'
    rw [eval_mul, eval_prod,
      Finset.prod_eq_zero (i := k) (Finset.mem_erase.2 ⟨hk'.symm, Finset.mem_univ _⟩), mul_zero]
    simp
  · intro h
    exact absurd (Finset.mem_univ k) h

lemma eq_zero_of_eval [Nontrivial R] {n : ℕ} (β : Fin n → R)
    (hβu : ∀ j k, j ≠ k → IsUnit (β j - β k)) (D : R[X]) (hD : D.natDegree < n)
    (hz : ∀ k, D.eval (β k) = 0) : D = 0 := by
  have hmon : (∏ k, (X - C (β k))).Monic :=
    monic_prod_of_monic _ _ (fun k _ => monic_X_sub_C _)
  have hdvd : (∏ k, (X - C (β k))) ∣ D := by
    apply Fintype.prod_dvd_of_coprime
    · intro i j hij
      exact isCoprime_X_sub_C_of_isUnit_sub (hβu i j hij)
    · intro i
      exact dvd_iff_isRoot.2 (hz i)
  have hdeg : (∏ k, (X - C (β k))).natDegree = n := by
    rw [natDegree_prod_of_monic _ _ (fun k _ => monic_X_sub_C _)]
    simp
  have h1 := (modByMonic_eq_zero_iff_dvd hmon).2 hdvd
  have h2 : D %ₘ (∏ k, (X - C (β k))) = D := by
    rw [modByMonic_eq_self_iff hmon]
    calc degree D ≤ D.natDegree := degree_le_natDegree
      _ < (n : WithBot ℕ) := by exact_mod_cast hD
      _ = degree (∏ k, (X - C (β k))) := by rw [degree_eq_natDegree hmon.ne_zero, hdeg]
  rw [← h2, h1]

lemma interp_eq [Nontrivial R] {n : ℕ} (β : Fin n → R)
    (hβu : ∀ j k, j ≠ k → IsUnit (β j - β k)) (P : R[X]) (hP : P.natDegree < n) :
    KedlayaUmans.Reduction.interpolate β (fun k => P.eval (β k)) = P := by
  have := eq_zero_of_eval β hβu (KedlayaUmans.Reduction.interpolate β (fun k => P.eval (β k)) - P)
    ?_ ?_
  · exact sub_eq_zero.1 this
  · refine (natDegree_sub_le _ _).trans_lt (max_lt ?_ hP)
    have := interp_natDegree β (fun k => P.eval (β k))
    omega
  · intro k
    rw [eval_sub, interp_eval β _ hβu, sub_self]

lemma modLc_monic [Nontrivial R] {h : R[X]} (hlc : IsUnit h.leadingCoeff) :
    (h * C (Ring.inverse h.leadingCoeff)).Monic := by
  have e : h.leadingCoeff * Ring.inverse h.leadingCoeff = 1 := Ring.mul_inverse_cancel _ hlc
  unfold Monic
  rw [leadingCoeff_mul' (by rw [leadingCoeff_C, e]; exact one_ne_zero), leadingCoeff_C, e]

lemma modLc_dvd (h p : R[X]) : h ∣ p - KedlayaUmans.Reduction.modLc p h := by
  unfold KedlayaUmans.Reduction.modLc
  have := modByMonic_add_div p (h * C (Ring.inverse h.leadingCoeff))
  refine ⟨C (Ring.inverse h.leadingCoeff) * (p /ₘ (h * C (Ring.inverse h.leadingCoeff))), ?_⟩
  linear_combination -this

lemma modLc_degree [Nontrivial R] {h : R[X]} (hlc : IsUnit h.leadingCoeff) (p : R[X]) :
    (KedlayaUmans.Reduction.modLc p h).degree < h.degree := by
  unfold KedlayaUmans.Reduction.modLc
  have hmon := modLc_monic hlc
  have hne : h ≠ 0 := by
    intro h0
    rw [h0, leadingCoeff_zero] at hlc
    exact not_isUnit_zero hlc
  calc degree (p %ₘ (h * C (Ring.inverse h.leadingCoeff)))
      < degree (h * C (Ring.inverse h.leadingCoeff)) := degree_modByMonic_lt _ hmon
    _ = (natDegree (h * C (Ring.inverse h.leadingCoeff)) : WithBot ℕ) :=
        degree_eq_natDegree hmon.ne_zero
    _ ≤ (natDegree h : WithBot ℕ) := by exact_mod_cast natDegree_mul_C_le h _
    _ = degree h := (degree_eq_natDegree hne).symm

lemma modLc_natDegree [Nontrivial R] {h : R[X]} (hlc : IsUnit h.leadingCoeff) (p : R[X]) :
    (KedlayaUmans.Reduction.modLc p h).natDegree ≤ h.natDegree := by
  unfold KedlayaUmans.Reduction.modLc
  exact (natDegree_modByMonic_le p (modLc_monic hlc)).trans (natDegree_mul_C_le h _)

lemma aeval_congr_mod {σ : Type*} (h : R[X]) (a b : σ → R[X]) (hab : ∀ i, h ∣ a i - b i)
    (p : MvPolynomial σ R) : h ∣ MvPolynomial.aeval a p - MvPolynomial.aeval b p := by
  refine MvPolynomial.induction_on
    (motive := fun p => h ∣ MvPolynomial.aeval a p - MvPolynomial.aeval b p) p ?_ ?_ ?_
  · intro r
    simp
  · intro p q hp hq
    rw [map_add, map_add]
    have := dvd_add hp hq
    convert this using 1
    ring
  · intro p i hp
    simp only [map_mul, MvPolynomial.aeval_X]
    have := dvd_add (dvd_mul_of_dvd_left hp (a i))
      (dvd_mul_of_dvd_right (hab i) (MvPolynomial.aeval b p))
    convert this using 1
    ring

lemma eval_aeval_poly {σ : Type*} (a : σ → R[X]) (p : MvPolynomial σ R) (x : R) :
    (MvPolynomial.aeval a p).eval x = MvPolynomial.eval (fun i => (a i).eval x) p := by
  refine MvPolynomial.induction_on
    (motive := fun p => (MvPolynomial.aeval a p).eval x = MvPolynomial.eval (fun i => (a i).eval x) p)
    p ?_ ?_ ?_
  · intro r
    simp
  · intro p q hp hq
    simp [hp, hq]
  · intro p i hp
    simp [hp]

lemma psi_pow_eval {m : ℕ} (d₀ ℓ : ℕ) (hd₀ : 2 ≤ d₀) (f : MvPolynomial (Fin m) R)
    (hf : ∀ e ∈ f.support, ∀ i, e i < d₀ ^ ℓ) (g : Fin m → R[X]) :
    MvPolynomial.aeval (fun ij : Fin m × Fin ℓ => g ij.1 ^ (d₀ ^ (ij.2 : ℕ)))
      (KedlayaUmans.Reduction.psi d₀ ℓ f) = MvPolynomial.aeval g f := by
  unfold KedlayaUmans.Reduction.psi
  rw [map_sum]
  conv_rhs => rw [f.as_sum, map_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]
  congr 1
  rw [Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp),
    Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i _
  simp only [KedlayaUmans.Reduction.digitExp, Finsupp.coe_equivFunOnFinite_symm]
  simp_rw [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  have := digit_sum d₀ (e i) ℓ hd₀
  rw [Nat.mod_eq_of_lt (hf e he i)] at this
  refine Eq.trans ?_ this
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma psi_aeval_natDegree {m : ℕ} (d₀ ℓ D : ℕ) (hd₀ : 2 ≤ d₀) (a : Fin m × Fin ℓ → R[X])
    (ha : ∀ ij, (a ij).natDegree ≤ D) (f : MvPolynomial (Fin m) R) :
    (MvPolynomial.aeval a (KedlayaUmans.Reduction.psi d₀ ℓ f)).natDegree
      ≤ m * ℓ * ((d₀ - 1) * D) := by
  unfold KedlayaUmans.Reduction.psi
  rw [map_sum]
  apply natDegree_sum_le_of_forall_le
  intro e _
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (by simp)]
  refine natDegree_mul_le.trans ?_
  rw [Polynomial.algebraMap_eq, natDegree_C, zero_add]
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ ij : Fin m × Fin ℓ, natDegree (a ij ^ (KedlayaUmans.Reduction.digitExp d₀ ℓ e ij))
      ≤ ∑ _ij : Fin m × Fin ℓ, (d₀ - 1) * D := by
        apply Finset.sum_le_sum
        intro ij _
        refine natDegree_pow_le.trans ?_
        apply Nat.mul_le_mul _ (ha ij)
        simp only [KedlayaUmans.Reduction.digitExp, Finsupp.coe_equivFunOnFinite_symm]
        exact digit_le _ _ _ hd₀
    _ = m * ℓ * ((d₀ - 1) * D) := by
        simp [Finset.card_univ, Fintype.card_prod]

end KU31

open Polynomial KedlayaUmans.Reduction in
theorem solution {R : Type*} [CommRing R] {m d N d₀ : ℕ}
    (hd₀ : 2 ≤ d₀) (hd₀d : d₀ < d) (hm : 1 ≤ m) (hN : 1 ≤ N)
    (f : MvPolynomial (Fin m) R) (hf : ∀ i, f.degreeOf i ≤ d - 1)
    (g : Fin m → R[X]) (hg : ∀ i, (g i).natDegree ≤ N - 1)
    (h : R[X]) (hh : h.natDegree ≤ N - 1) (hlc : IsUnit h.leadingCoeff)
    (β : Fin (Nprime N m d₀ d) → R) (hβ : Function.Injective β)
    (hβu : ∀ j k, j ≠ k → IsUnit (β j - β k)) :
    h ∣ MvPolynomial.aeval g f - algorithm d₀ d f g h β ∧
      ((algorithm d₀ d f g h β).degree < h.degree ∨ algorithm d₀ d f g h β = 0) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · refine ⟨?_, Or.inr (Subsingleton.elim _ _)⟩
    rw [Subsingleton.elim (MvPolynomial.aeval g f - algorithm d₀ d f g h β) 0]
    exact dvd_zero _
  have hℓ : 0 < ell d₀ d := Nat.clog_pos (by omega) (by omega)
  have hpow : d ≤ d₀ ^ ell d₀ d := Nat.le_pow_clog (by omega) d
  set P := MvPolynomial.aeval (step2 d₀ d g h) (step1 d₀ d f) with hPdef
  have hP : h ∣ MvPolynomial.aeval g f - P := by
    have e1 := KU31.psi_pow_eval d₀ (ell d₀ d) hd₀ f ?_ g
    · rw [← e1, hPdef]
      apply KU31.aeval_congr_mod
      intro ij
      exact KU31.modLc_dvd h _
    · intro e he i
      have h1 := MvPolynomial.monomial_le_degreeOf i he
      have h2 := hf i
      omega
  have hPdeg : P.natDegree < Nprime N m d₀ d := by
    have hb := KU31.psi_aeval_natDegree d₀ (ell d₀ d) (N - 1) hd₀ (step2 d₀ d g h)
      (fun ij => (KU31.modLc_natDegree hlc _).trans hh) f
    have hlt : (d₀ - 1) * (N - 1) < d₀ * N := by
      calc (d₀ - 1) * (N - 1) ≤ (d₀ - 1) * N := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ < d₀ * N := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    have hA : 0 < m * ell d₀ d := Nat.mul_pos (by omega) hℓ
    have h3 : m * ell d₀ d * ((d₀ - 1) * (N - 1)) < m * ell d₀ d * (d₀ * N) :=
      Nat.mul_lt_mul_of_pos_left hlt hA
    have h4 : Nprime N m d₀ d = m * ell d₀ d * (d₀ * N) := by
      unfold Nprime
      ring
    rw [h4]
    exact lt_of_le_of_lt hb h3
  have h4 : step4 d₀ d f g h β = fun k => P.eval (β k) := by
    funext k
    rw [hPdef, KU31.eval_aeval_poly]
    rfl
  have h5 : step5 d₀ d f g h β = P := by
    unfold step5
    rw [h4]
    exact KU31.interp_eq β hβu P hPdeg
  unfold algorithm
  rw [h5]
  refine ⟨?_, Or.inl (KU31.modLc_degree hlc P)⟩
  have := dvd_add hP (KU31.modLc_dvd h P)
  convert this using 1
  ring
