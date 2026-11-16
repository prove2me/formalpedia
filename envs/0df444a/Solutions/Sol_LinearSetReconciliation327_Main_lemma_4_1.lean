-- Prove2me | solution 1 for LinearSetReconciliation327.Main.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @djwj233
-- created : 2026-11-15T12:49:55.846204+00:00
-- url     : https://prove2.me/submissions/7ca3ab3a-acab-4d98-8780-8e8a9cc0cb16

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

/-! ## Counting lemmas for Lemma 4.1 -/

open Classical in
/-- Of the `K`-element subsets of `[N]`, exactly `C(N-|A|, K-|A|)` contain a fixed set `A`. -/
lemma card_powersetCard_filter_subset {N : ℕ} (A : Finset (Fin N)) {K : ℕ} (hA : A.card ≤ K) :
    ((powersetCard K (univ : Finset (Fin N))).filter (fun S => A ⊆ S)).card
      = (N - A.card).choose (K - A.card) := by
  classical
  have hcard : (univ \ A : Finset (Fin N)).card = N - A.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ A), Finset.card_univ,
      Fintype.card_fin]
  have key : ((powersetCard K (univ : Finset (Fin N))).filter (fun S => A ⊆ S)).card
      = (powersetCard (K - A.card) (univ \ A)).card := by
    refine Finset.card_bij (fun S _ => S \ A) ?_ ?_ ?_
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powersetCard] at hS ⊢
      obtain ⟨⟨-, hScard⟩, hAS⟩ := hS
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx ⊢
        exact hx.2
      · rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hAS, hScard]
    · intro S1 hS1 S2 hS2 heq
      simp only [Finset.mem_filter] at hS1 hS2
      rw [← Finset.union_sdiff_of_subset hS1.2, ← Finset.union_sdiff_of_subset hS2.2, heq]
    · intro T hT
      simp only [Finset.mem_powersetCard] at hT
      obtain ⟨hTsub, hTcard⟩ := hT
      have hTdisj : Disjoint A T := Finset.disjoint_left.mpr fun x hxA hxT => by
        have hx := hTsub hxT
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx
        exact hx hxA
      refine ⟨A ∪ T, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨by simp, ?_⟩,
          Finset.subset_union_left⟩
        rw [Finset.card_union_of_disjoint hTdisj, hTcard]
        omega
      · ext x
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨hxA | hxT, hxnA⟩
          · exact absurd hxA hxnA
          · exact hxT
        · intro hxT
          have hx := hTsub hxT
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx
          exact ⟨Or.inr hxT, hx⟩
  rw [key, Finset.card_powersetCard, hcard]

/-- `C(N-r, K-r) * (N)_r = C(N,K) * (K)_r` where `(x)_r` is the falling factorial. -/
lemma choose_mul_descFactorial {N K r : ℕ} (hKN : K ≤ N) (hr : r ≤ K) :
    (N - r).choose (K - r) * N.descFactorial r = N.choose K * K.descFactorial r := by
  have h1 : (N - r).choose (K - r) * (K - r).factorial * (N - K).factorial = (N - r).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (n := N - r) (k := K - r) (by omega)
    rwa [show N - r - (K - r) = N - K by omega] at h
  have h2 : N.choose K * K.factorial * (N - K).factorial = N.factorial :=
    Nat.choose_mul_factorial_mul_factorial (n := N) (k := K) hKN
  have h3 : (N - r).factorial * N.descFactorial r = N.factorial := by
    have h := Nat.descFactorial_mul_descFactorial (k := r) (m := N) (n := N) (by omega : r ≤ N)
    rwa [Nat.descFactorial_self, Nat.descFactorial_self] at h
  have h4 : (K - r).factorial * K.descFactorial r = K.factorial := by
    have h := Nat.descFactorial_mul_descFactorial (k := r) (m := K) (n := K) hr
    rwa [Nat.descFactorial_self, Nat.descFactorial_self] at h
  have hmain : ((N - r).choose (K - r) * N.descFactorial r)
        * ((K - r).factorial * (N - K).factorial)
      = (N.choose K * K.descFactorial r) * ((K - r).factorial * (N - K).factorial) := by
    calc ((N - r).choose (K - r) * N.descFactorial r) * ((K - r).factorial * (N - K).factorial)
        = ((N - r).choose (K - r) * (K - r).factorial * (N - K).factorial)
            * N.descFactorial r := by ring
      _ = (N - r).factorial * N.descFactorial r := by rw [h1]
      _ = N.factorial := h3
      _ = (N.choose K * K.factorial) * (N - K).factorial := by rw [h2]
      _ = (N.choose K * K.descFactorial r) * ((K - r).factorial * (N - K).factorial) := by
            rw [← h4]; ring
  exact Nat.mul_right_cancel (by positivity) hmain

/-- `(K)_r * N^r ≤ (N)_r * K^r`. -/
lemma descFactorial_mul_pow_le {N K r : ℕ} (hKN : K ≤ N) (hr : r ≤ K) :
    K.descFactorial r * N ^ r ≤ N.descFactorial r * K ^ r := by
  have hL : (∏ i ∈ Finset.range r, (K - i)) * N ^ r = ∏ i ∈ Finset.range r, ((K - i) * N) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have hR : (∏ i ∈ Finset.range r, (N - i)) * K ^ r = ∏ i ∈ Finset.range r, ((N - i) * K) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range, hL, hR]
  refine Finset.prod_le_prod' fun i hi => ?_
  simp only [Finset.mem_range] at hi
  have hiK : i ≤ K := by omega
  have hiN : i ≤ N := by omega
  rw [Nat.sub_mul, Nat.sub_mul, Nat.mul_comm K N]
  exact Nat.sub_le_sub_left (Nat.mul_le_mul_left i hKN) _

/-- The hypergeometric ratio bound: `C(N-r,K-r) * N^r ≤ C(N,K) * K^r`. -/
lemma choose_sub_mul_pow_le {N K r : ℕ} (hKN : K ≤ N) (hr : r ≤ K) :
    (N - r).choose (K - r) * N ^ r ≤ N.choose K * K ^ r := by
  have hstar := choose_mul_descFactorial hKN hr
  have hprod := descFactorial_mul_pow_le hKN hr
  have key : (N - r).choose (K - r) * N.descFactorial r * N ^ r
      ≤ N.choose K * N.descFactorial r * K ^ r := by
    rw [hstar]
    calc N.choose K * K.descFactorial r * N ^ r = N.choose K * (K.descFactorial r * N ^ r) := by
          ring
      _ ≤ N.choose K * (N.descFactorial r * K ^ r) := Nat.mul_le_mul_left _ hprod
      _ = N.choose K * N.descFactorial r * K ^ r := by ring
  have hrN : r ≤ N := le_trans hr hKN
  have hD : 0 < N.descFactorial r := Nat.descFactorial_pos.mpr hrN
  refine Nat.le_of_mul_le_mul_left ?_ hD
  calc N.descFactorial r * ((N - r).choose (K - r) * N ^ r)
      = (N - r).choose (K - r) * N.descFactorial r * N ^ r := by ring
    _ ≤ N.choose K * N.descFactorial r * K ^ r := key
    _ = N.descFactorial r * (N.choose K * K ^ r) := by ring

/-- The hypergeometric ratio bound in the form used below. -/
lemma choose_sub_le_pow_mul {N K r : ℕ} (hN : 0 < N) (hKN : K ≤ N) (hr : r ≤ K) :
    ((N - r).choose (K - r) : ℝ) ≤ ((K : ℝ) / (N : ℝ)) ^ r * (N.choose K : ℝ) := by
  have hnat := choose_sub_mul_pow_le hKN hr
  have hcast : ((N - r).choose (K - r) : ℝ) * (N : ℝ) ^ r
      ≤ (N.choose K : ℝ) * (K : ℝ) ^ r := by
    exact_mod_cast hnat
  have hNr : (0 : ℝ) < (N : ℝ) ^ r := pow_pos (by exact_mod_cast hN) r
  rw [div_pow]
  have h2 : (K : ℝ) ^ r / (N : ℝ) ^ r * (N.choose K : ℝ)
      = (K : ℝ) ^ r * (N.choose K : ℝ) / (N : ℝ) ^ r := by ring
  rw [h2, le_div_iff₀ hNr]
  linarith [hcast]

/-- The moment generating function bound for the hypergeometric law, in counting form:
`∑_{|S|=K} (1+u)^{|S∩I|} ≤ C(N,K) · exp(μ u)` where `μ = K|I|/N`. -/
theorem mgf_le {N K : ℕ} (hN : 0 < N) (hKN : K ≤ N) (I : Finset (Fin N)) {u : ℝ} (hu : 0 ≤ u) :
    ∑ S ∈ powersetCard K (univ : Finset (Fin N)), (1 + u) ^ ((S ∩ I).card)
      ≤ (N.choose K : ℝ) * Real.exp ((K : ℝ) * (I.card : ℝ) / (N : ℝ) * u) := by
  classical
  -- STEP 1: expand `(1+u)^{|S∩I|}` as a sum over the subsets of `S ∩ I`
  have hterm : ∀ S ∈ powersetCard K (univ : Finset (Fin N)),
      (1 + u) ^ ((S ∩ I).card) = ∑ A ∈ I.powerset, if A ⊆ S then u ^ A.card else 0 := by
    intro S _
    have hexp : (1 + u) ^ ((S ∩ I).card) = ∑ A ∈ (S ∩ I).powerset, u ^ A.card := by
      have h := Finset.sum_pow_mul_eq_add_pow u (1 : ℝ) (S ∩ I)
      simpa [add_comm] using h.symm
    have hset : (S ∩ I).powerset = I.powerset.filter (fun A => A ⊆ S) := by
      ext A
      simp only [Finset.mem_powerset, Finset.mem_filter]
      constructor
      · intro h
        refine ⟨?_, ?_⟩
        · intro x hx; exact (Finset.mem_inter.mp (h hx)).2
        · intro x hx; exact (Finset.mem_inter.mp (h hx)).1
      · rintro ⟨h1, h2⟩ x hx
        exact Finset.mem_inter.mpr ⟨h2 hx, h1 hx⟩
    rw [hexp, hset, Finset.sum_filter]
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  -- STEP 2: evaluate the inner sum
  have hinner : ∀ A ∈ I.powerset,
      ∑ S ∈ powersetCard K (univ : Finset (Fin N)), (if A ⊆ S then u ^ A.card else 0)
        = u ^ A.card *
            (((powersetCard K (univ : Finset (Fin N))).filter (fun S => A ⊆ S)).card : ℝ) := by
    intro A _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hinner]
  -- STEP 3: bound each term by the binomial ratio bound
  have hbound : ∀ A ∈ I.powerset,
      u ^ A.card *
          (((powersetCard K (univ : Finset (Fin N))).filter (fun S => A ⊆ S)).card : ℝ)
        ≤ u ^ A.card * (((K : ℝ) / (N : ℝ)) ^ A.card * (N.choose K : ℝ)) := by
    intro A _
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hu _)
    by_cases haK : A.card ≤ K
    · rw [card_powersetCard_filter_subset A haK]
      exact choose_sub_le_pow_mul hN hKN haK
    · have haK' : K < A.card := not_le.mp haK
      have hzero : ((powersetCard K (univ : Finset (Fin N))).filter (fun S => A ⊆ S)).card = 0 := by
        have hempty : (powersetCard K (univ : Finset (Fin N))).filter (fun S => A ⊆ S) = ∅ := by
          refine Finset.filter_false_of_mem ?_
          intro S hS hAS
          simp only [Finset.mem_powersetCard] at hS
          have hle : A.card ≤ S.card := Finset.card_le_card hAS
          omega
        rw [hempty, Finset.card_empty]
      rw [hzero, Nat.cast_zero]
      positivity
  refine le_trans (Finset.sum_le_sum hbound) ?_
  -- STEP 4: sum the geometric-type series
  have hsum : ∑ A ∈ I.powerset, u ^ A.card * (((K : ℝ) / (N : ℝ)) ^ A.card * (N.choose K : ℝ))
      = (N.choose K : ℝ) * (1 + u * ((K : ℝ) / (N : ℝ))) ^ I.card := by
    have h1 : ∀ A ∈ I.powerset, u ^ A.card * (((K : ℝ) / (N : ℝ)) ^ A.card * (N.choose K : ℝ))
        = (N.choose K : ℝ) * ((u * ((K : ℝ) / (N : ℝ))) ^ A.card) := by
      intro A _
      rw [mul_pow]
      ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
    have h2 : ∑ A ∈ I.powerset, (u * ((K : ℝ) / (N : ℝ))) ^ A.card
        = (u * ((K : ℝ) / (N : ℝ)) + 1) ^ I.card := by
      have h := Finset.sum_pow_mul_eq_add_pow (u * ((K : ℝ) / (N : ℝ))) (1 : ℝ) I
      simpa using h
    rw [h2]
    ring
  rw [hsum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hs : (0 : ℝ) ≤ u * ((K : ℝ) / (N : ℝ)) :=
    mul_nonneg hu (by positivity)
  have hexp : (1 + u * ((K : ℝ) / (N : ℝ))) ≤ Real.exp (u * ((K : ℝ) / (N : ℝ))) := by
    have h := Real.add_one_le_exp (u * ((K : ℝ) / (N : ℝ)))
    linarith
  have hpow : (1 + u * ((K : ℝ) / (N : ℝ))) ^ I.card
      ≤ (Real.exp (u * ((K : ℝ) / (N : ℝ)))) ^ I.card := by
    apply pow_le_pow_left₀ (by linarith) hexp
  refine le_trans hpow ?_
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have harg : (I.card : ℝ) * (u * ((K : ℝ) / (N : ℝ))) = (K : ℝ) * (I.card : ℝ) / (N : ℝ) * u := by
    rw [div_eq_mul_inv]
    ring
  linarith [harg]

/-- The elementary log inequality behind the Chernoff bound:
`δ²/(2(1+δ)) ≤ (1+δ)log(1+δ) - δ` for `δ ≥ 0`. -/
lemma log_chernoff_aux {δ : ℝ} (hδ : 0 ≤ δ) :
    δ ^ 2 / (2 * (1 + δ)) ≤ (1 + δ) * Real.log (1 + δ) - δ := by
  have h1δ : (0:ℝ) < 1 + δ := by linarith
  have hlog : 2 * δ / (δ + 2) ≤ Real.log (1 + δ) := Real.le_log_one_add_of_nonneg hδ
  have hstep : (1 + δ) * (2 * δ / (δ + 2)) ≤ (1 + δ) * Real.log (1 + δ) :=
    mul_le_mul_of_nonneg_left hlog h1δ.le
  have heq : (1 + δ) * (2 * δ / (δ + 2)) - δ = δ ^ 2 / (δ + 2) := by
    field_simp
    ring
  have h2 : δ ^ 2 / (2 * (1 + δ)) ≤ δ ^ 2 / (δ + 2) := by
    gcongr
    linarith
  linarith

open Classical in
/-- Lemma 4.1 (Chernoff bound for hypergeometric random variables), PDF p.16 (printed p.15). `S` is
uniform among the `K`-subsets of `[N]`. -/
theorem lemma_4_1 (N K : ℕ) (hK : K ≤ N) (I : Finset (Fin N))
    (hμ : 0 < (K : ℝ) * I.card / N) :
    let μ : ℝ := (K : ℝ) * I.card / N
    let Pr : (Finset (Fin N) → Prop) → ℝ := fun E =>
      (((powersetCard K (univ : Finset (Fin N))).filter E).card : ℝ) /
        ((powersetCard K (univ : Finset (Fin N))).card : ℝ)
    (∀ t : ℝ, 0 ≤ t →
      Pr (fun S => μ + t ≤ ((S ∩ I).card : ℝ)) ≤ Real.exp (-(t ^ 2 / (2 * (μ + t))))) ∧
    (∀ k : ℝ, 2 * μ ≤ k → Pr (fun S => k ≤ ((S ∩ I).card : ℝ)) ≤ Real.exp (-(k / 8))) := by
  classical
  dsimp only
  set μ : ℝ := (K : ℝ) * (I.card : ℝ) / (N : ℝ) with hμdef
  set D : ℝ := ((powersetCard K (univ : Finset (Fin N))).card : ℝ) with hDdef
  have hNne : (N : ℝ) ≠ 0 := by
    intro h0
    rw [hμdef, h0] at hμ
    simp at hμ
  have hNpos : 0 < N := by
    have h1 : (0:ℝ) < (N : ℝ) := by
      rcases lt_or_eq_of_le (Nat.cast_nonneg N : (0:ℝ) ≤ (N:ℝ)) with hh | hh
      · exact hh
      · exact absurd hh.symm hNne
    exact_mod_cast h1
  have hμpos : 0 < μ := hμ
  have hDval : D = (N.choose K : ℝ) := by
    rw [hDdef, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hDpos : 0 < D := by
    rw [hDval]
    exact_mod_cast Nat.choose_pos hK
  have key : ∀ t : ℝ, 0 ≤ t →
      (((powersetCard K (univ : Finset (Fin N))).filter
          (fun S => μ + t ≤ ((S ∩ I).card : ℝ))).card : ℝ) / D
        ≤ Real.exp (-(t ^ 2 / (2 * (μ + t)))) := by
    intro t ht
    set δ : ℝ := t / μ with hδdef
    have hδ : 0 ≤ δ := div_nonneg ht hμpos.le
    have ht_eq : t = μ * δ := by
      rw [hδdef]
      field_simp
    have hδpos : (0:ℝ) < 1 + δ := by linarith
    set θ : ℝ := Real.log (1 + δ) with hθdef
    have hexpθ : Real.exp θ = 1 + δ := by
      rw [hθdef]
      exact Real.exp_log hδpos
    have hθ : 0 ≤ θ := by
      rw [hθdef]
      exact Real.log_nonneg (by linarith)
    have hu : 0 ≤ Real.exp θ - 1 := by rw [hexpθ]; linarith
    set z : ℝ := μ + t with hzdef
    have hz : z = μ * (1 + δ) := by rw [hzdef, ht_eq]; ring
    -- Markov's inequality, step 1: bound by the exponential moment
    have hstep1 : (((powersetCard K (univ : Finset (Fin N))).filter
          (fun S => z ≤ ((S ∩ I).card : ℝ))).card : ℝ) * Real.exp (θ * z)
        ≤ ∑ S ∈ powersetCard K (univ : Finset (Fin N)), Real.exp (θ * ((S ∩ I).card : ℝ)) := by
      have h1 : (((powersetCard K (univ : Finset (Fin N))).filter
            (fun S => z ≤ ((S ∩ I).card : ℝ))).card : ℝ) * Real.exp (θ * z)
          = ∑ S ∈ (powersetCard K (univ : Finset (Fin N))).filter
              (fun S => z ≤ ((S ∩ I).card : ℝ)), Real.exp (θ * z) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      rw [h1, Finset.sum_filter]
      refine Finset.sum_le_sum fun S _ => ?_
      by_cases hp : z ≤ ((S ∩ I).card : ℝ)
      · simp only [hp, if_true]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hp hθ)
      · simp only [hp, if_false]
        positivity
    -- step 2: the exponential moment bound
    have hstep2 : ∑ S ∈ powersetCard K (univ : Finset (Fin N)),
        Real.exp (θ * ((S ∩ I).card : ℝ)) ≤ D * Real.exp (μ * (Real.exp θ - 1)) := by
      have hpt : ∀ S ∈ powersetCard K (univ : Finset (Fin N)),
          Real.exp (θ * ((S ∩ I).card : ℝ)) = (1 + (Real.exp θ - 1)) ^ ((S ∩ I).card) := by
        intro S _
        rw [show (1:ℝ) + (Real.exp θ - 1) = Real.exp θ by ring]
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      rw [Finset.sum_congr rfl hpt]
      have h := mgf_le hNpos hK I (u := Real.exp θ - 1) hu
      simpa [← hDval, hμdef] using h
    -- divide by `exp (θ z)`
    have hA : (((powersetCard K (univ : Finset (Fin N))).filter
          (fun S => z ≤ ((S ∩ I).card : ℝ))).card : ℝ)
        ≤ D * Real.exp (μ * (Real.exp θ - 1) - θ * z) := by
      have hcomb := le_trans hstep1 hstep2
      have hpos : (0:ℝ) < Real.exp (θ * z) := Real.exp_pos _
      have hexp_split : Real.exp (μ * (Real.exp θ - 1))
          = Real.exp (μ * (Real.exp θ - 1) - θ * z) * Real.exp (θ * z) := by
        rw [← Real.exp_add]; congr 1; ring
      have hkey : D * Real.exp (μ * (Real.exp θ - 1))
          = (D * Real.exp (μ * (Real.exp θ - 1) - θ * z)) * Real.exp (θ * z) := by
        rw [hexp_split]; ring
      rw [hkey] at hcomb
      exact (mul_le_mul_iff_of_pos_right hpos).mp hcomb
    -- the final numerical comparison
    have hfinal : Real.exp (μ * (Real.exp θ - 1) - θ * z) ≤ Real.exp (-(t ^ 2 / (2 * z))) := by
      apply Real.exp_le_exp.mpr
      have hnum := log_chernoff_aux hδ
      have h1 : μ * (Real.exp θ - 1) - θ * z = -(μ * ((1 + δ) * Real.log (1 + δ) - δ)) := by
        rw [hexpθ, hθdef, hz]
        ring
      have h2 : t ^ 2 / (2 * z) = μ * (δ ^ 2 / (2 * (1 + δ))) := by
        rw [hz, ht_eq]
        field_simp
      have h3 : μ * (δ ^ 2 / (2 * (1 + δ))) ≤ μ * ((1 + δ) * Real.log (1 + δ) - δ) :=
        mul_le_mul_of_nonneg_left hnum hμpos.le
      rw [h1, h2]
      linarith
    rw [div_le_iff₀ hDpos]
    calc (((powersetCard K (univ : Finset (Fin N))).filter
          (fun S => z ≤ ((S ∩ I).card : ℝ))).card : ℝ)
        ≤ D * Real.exp (μ * (Real.exp θ - 1) - θ * z) := hA
      _ ≤ D * Real.exp (-(t ^ 2 / (2 * z))) := mul_le_mul_of_nonneg_left hfinal hDpos.le
      _ = Real.exp (-(t ^ 2 / (2 * z))) * D := by ring
  refine ⟨key, ?_⟩
  intro k hk
  have hkpos : (0:ℝ) < k := by linarith
  have ht : 0 ≤ k - μ := by linarith
  have h1 := key (k - μ) ht
  have heq1 : μ + (k - μ) = k := by ring
  rw [heq1] at h1
  refine le_trans h1 (Real.exp_le_exp.mpr ?_)
  have htarget : k / 8 ≤ (k - μ) ^ 2 / (2 * k) := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < 2 * k)]
    have h1 : 0 ≤ k - 2 * μ := by linarith
    have h2 : 0 ≤ 3 * k - 2 * μ := by linarith
    nlinarith [mul_nonneg h1 h2]
  linarith

end LinearSetReconciliation327.Main

open Classical in
/-- Lemma 4.1 (Chernoff bound for hypergeometric random variables) — submission wrapper matching
the target statement. -/
theorem solution (N K : ℕ) (hK : K ≤ N) (I : Finset (Fin N))
    (hμ : 0 < (K : ℝ) * I.card / N) :
    let μ : ℝ := (K : ℝ) * I.card / N
    let Pr : (Finset (Fin N) → Prop) → ℝ := fun E =>
      (((powersetCard K (univ : Finset (Fin N))).filter E).card : ℝ) /
        ((powersetCard K (univ : Finset (Fin N))).card : ℝ)
    (∀ t : ℝ, 0 ≤ t →
      Pr (fun S => μ + t ≤ ((S ∩ I).card : ℝ)) ≤ Real.exp (-(t ^ 2 / (2 * (μ + t))))) ∧
    (∀ k : ℝ, 2 * μ ≤ k → Pr (fun S => k ≤ ((S ∩ I).card : ℝ)) ≤ Real.exp (-(k / 8))) :=
  LinearSetReconciliation327.Main.lemma_4_1 N K hK I hμ
