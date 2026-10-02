-- Prove2me | solution 1 for LiouvilleDiffAlg.ratFunc_descent_log
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-01T11:56:10.60687+00:00
-- url     : https://prove2.me/submissions/273b24b0-d080-4e8a-b53f-ec4dfabfb614

import Mathlib
import Theorems.Thm_LiouvilleDiffAlg_ratFunc_liouville_key
import Theorems.Thm_LiouvilleDiffAlg_ratFunc_deriv_poly

open scoped Differential
open Polynomial

private lemma kappa_eq {K : Type*} [Field K] (k : K) :
    algebraMap K (RatFunc K) k = algebraMap K[X] (RatFunc K) (C k) := by
  rw [IsScalarTower.algebraMap_apply K K[X] (RatFunc K), Polynomial.algebraMap_eq]

private lemma coeff_implicitDeriv {K : Type*} [Field K] [Differential K] (w0 : K) (V : K[X])
    (k : ℕ) :
    (Differential.implicitDeriv (C w0) V).coeff k =
      (V.coeff k)′ + w0 * (V.coeff (k + 1) * ((k : K) + 1)) := by
  simp [Differential.implicitDeriv, coeff_derivative]

private lemma X_not_mem_range {K : Type*} [Field K] :
    (RatFunc.X : RatFunc K) ∉ Set.range (algebraMap K (RatFunc K)) := by
  rintro ⟨k, hk⟩
  rw [kappa_eq, ← RatFunc.algebraMap_X] at hk
  have := (RatFunc.algebraMap_injective K) hk
  have h2 := congrArg natDegree this
  simp at h2

private lemma degree_implicitDeriv_lt {K : Type*} [Field K] [Differential K] (w0 : K) (p : K[X])
    (hp : Monic p) :
    degree (Differential.implicitDeriv (C w0) p) < degree p := by
  have hp0 : p ≠ 0 := hp.ne_zero
  rw [degree_eq_natDegree hp0, degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_implicitDeriv]
  rcases Nat.eq_or_lt_of_le hm with h | h
  · subst h
    have h1 : p.coeff p.natDegree = 1 := hp
    rw [h1, coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _)]
    simp
  · rw [coeff_eq_zero_of_natDegree_lt h, coeff_eq_zero_of_natDegree_lt (by omega)]
    simp

private lemma natDegree_le_one {K : Type*} [Field K] [Differential K] [CharZero K]
    [Differential (RatFunc K)] [DifferentialAlgebra K (RatFunc K)]
    (w0 : K) (hX : (RatFunc.X : RatFunc K)′ = algebraMap K (RatFunc K) w0)
    (hcon : ∀ x : RatFunc K, x′ = 0 → x ∈ Set.range (algebraMap K (RatFunc K)))
    (V : K[X]) (T : K) (hV : Differential.implicitDeriv (C w0) V = C T) :
    V.natDegree ≤ 1 := by
  by_contra hlt
  have hlt : 1 < V.natDegree := not_le.1 hlt
  obtain ⟨e, he⟩ : ∃ e, V.natDegree = e + 1 := ⟨V.natDegree - 1, by omega⟩
  have he1 : 1 ≤ e := by omega
  have h1 := congrArg (fun P => P.coeff (e + 1)) hV
  have h2 := congrArg (fun P => P.coeff e) hV
  simp only [coeff_implicitDeriv, coeff_C] at h1 h2
  rw [if_neg (by omega)] at h1 h2
  rw [coeff_eq_zero_of_natDegree_lt (by omega : V.natDegree < e + 1 + 1)] at h1
  simp at h1
  have hc0 : V.coeff (e + 1) * ((e : K) + 1) ≠ 0 := by
    have : V.coeff (e + 1) ≠ 0 := by
      have := V.leadingCoeff_ne_zero.2 (by rintro rfl; simp at he)
      rwa [leadingCoeff, he] at this
    exact mul_ne_zero this (by exact_mod_cast Nat.succ_ne_zero e)
  set c := V.coeff (e + 1) * ((e : K) + 1) with hc
  have hc' : c′ = 0 := by
    rw [hc]
    simp [Derivation.leibniz, h1]
  have hy : (algebraMap K (RatFunc K) (V.coeff e) +
      algebraMap K (RatFunc K) c * (RatFunc.X : RatFunc K))′ = 0 := by
    simp only [Derivation.leibniz, map_add, hX, DifferentialAlgebra.deriv_algebraMap, hc']
    have h3 : (V.coeff e)′ + c * w0 = 0 := by rw [mul_comm]; exact h2
    simp only [smul_eq_mul, map_zero, mul_zero, add_zero]
    rw [← map_mul, ← map_add, h3, map_zero]
  obtain ⟨r, hr⟩ := hcon _ hy
  have hκ : algebraMap K (RatFunc K) c ≠ 0 := (_root_.map_ne_zero _).2 hc0
  refine X_not_mem_range ⟨(r - V.coeff e) / c, ?_⟩
  rw [map_div₀, map_sub, hr]
  field_simp
  ring

theorem solution {K : Type*} [Field K] [Differential K] [CharZero K]
    [Differential (RatFunc K)] [DifferentialAlgebra K (RatFunc K)]
    {s : K} (hs : s ≠ 0) (hX : (RatFunc.X : RatFunc K)′ = algebraMap K (RatFunc K) (s′ / s))
    (hcon : ∀ x : RatFunc K, x′ = 0 → x ∈ Set.range (algebraMap K (RatFunc K)))
    {n : ℕ} (c : Fin n → K) (hc : ∀ i, (c i)′ = 0) (h : K)
    (u : Fin n → RatFunc K) (hu : ∀ i, u i ≠ 0) (v : RatFunc K)
    (hfe : algebraMap K (RatFunc K) h = ∑ i, algebraMap K (RatFunc K) (c i) * ((u i)′ / u i) + v′) :
    ∃ (m : ℕ) (c' a : Fin m → K) (b : K), (∀ i, (c' i)′ = 0) ∧ (∀ i, a i ≠ 0) ∧
      h = ∑ i, c' i * ((a i)′ / a i) + b′ := by
  classical
  have hX' : (RatFunc.X : RatFunc K)′ = algebraMap K[X] (RatFunc K) (C (s′ / s)) := by
    rw [hX, kappa_eq]
  have hD := fun r : K[X] => LiouvilleDiffAlg.ratFunc_deriv_poly (C (s′ / s)) hX' r
  have hpoly : ∀ r : K[X], ∃ q : K[X], (algebraMap K[X] (RatFunc K) r)′ =
      algebraMap K[X] (RatFunc K) q := fun r => ⟨_, hD r⟩
  have hExc : ∀ p q : K[X], Monic p → Irreducible p → ¬ (fun _ : K[X] => False) p →
      (algebraMap K[X] (RatFunc K) p)′ = algebraMap K[X] (RatFunc K) q → ¬ p ∣ q := by
    intro p q hm hirr _ hq hdvd
    have hq' : q = Differential.implicitDeriv (C (s′ / s)) p :=
      (RatFunc.algebraMap_injective K) (hq.symm.trans (hD p))
    have hlt := degree_implicitDeriv_lt (s′ / s) p hm
    rw [← hq'] at hlt
    have hq0 : q = 0 := eq_zero_of_dvd_of_degree_lt hdvd hlt
    subst hq0
    rw [map_zero] at hq
    obtain ⟨k, hk⟩ := hcon _ hq
    rw [kappa_eq] at hk
    have := (RatFunc.algebraMap_injective K) hk
    exact not_irreducible_C k (this ▸ hirr)
  obtain ⟨a, E, C', A, B, ha, hE, hC, hB0, hv, hBp, hfe'⟩ :=
    LiouvilleDiffAlg.ratFunc_liouville_key hpoly (fun _ => False) hExc c hc h u hu v hfe
  have hE0 : E = ∅ := Finset.eq_empty_of_forall_notMem (fun p hp => (hE p hp).2.2)
  have hBu : IsUnit B := by
    by_contra hnu
    obtain ⟨p, hm, hirr, hdvd⟩ := exists_monic_irreducible_factor B hnu
    exact hBp p hm hirr hdvd
  obtain ⟨r, hr, hCb⟩ := Polynomial.isUnit_iff.1 hBu
  have hr0 : r ≠ 0 := hr.ne_zero
  set V : K[X] := C r⁻¹ * A with hVdef
  have hvV : v = algebraMap K[X] (RatFunc K) V := by
    have hne : algebraMap K[X] (RatFunc K) B ≠ 0 :=
      (_root_.map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).2 hB0
    rw [hv, div_eq_iff hne, hVdef, ← map_mul, ← hCb]
    congr 1
    rw [mul_comm, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hr0, C_1, one_mul]
  set T : K := h - ∑ i, c i * ((a i)′ / a i) with hTdef
  have hT : algebraMap K (RatFunc K) T = v′ := by
    have h1 : algebraMap K (RatFunc K) (∑ i, c i * ((a i)′ / a i)) =
        ∑ i, algebraMap K (RatFunc K) (c i) *
          ((algebraMap K (RatFunc K) (a i))′ / algebraMap K (RatFunc K) (a i)) := by
      simp only [map_sum, map_mul, map_div₀, DifferentialAlgebra.deriv_algebraMap]
    rw [hE0] at hfe'
    rw [hTdef, map_sub, h1, hfe']
    simp
  have hVT : Differential.implicitDeriv (C (s′ / s)) V = C T := by
    apply RatFunc.algebraMap_injective K
    rw [← hD V, ← hvV, ← kappa_eq, hT]
  have hdeg := natDegree_le_one (s′ / s) hX hcon V T hVT
  have hV1 := congrArg (fun P => P.coeff 1) hVT
  have hV0 := congrArg (fun P => P.coeff 0) hVT
  simp only [coeff_implicitDeriv, coeff_C] at hV1 hV0
  rw [coeff_eq_zero_of_natDegree_lt (by omega : V.natDegree < 1 + 1)] at hV1
  simp at hV1 hV0
  refine ⟨n + 1, Fin.snoc (α := fun _ => K) c (V.coeff 1),
    Fin.snoc (α := fun _ => K) a s, V.coeff 0, ?_, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hV1
    · simpa using hc j
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hs
    · simpa using ha j
  · rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    have : h = ∑ i, c i * ((a i)′ / a i) + T := by rw [hTdef]; ring
    rw [this, ← hV0]
    ring
