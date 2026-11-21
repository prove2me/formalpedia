-- Prove2me | solution 2 for MomentSearch.Supplement.smoothed_step_certificate
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-21T01:31:15.793163+00:00
-- url     : https://prove2.me/submissions/0d7eaff0-375e-4d8b-9f9f-2bee745c657c

import Mathlib
open Polynomial Real
open scoped BigOperators

private lemma chebyshev_growth (d : ℕ) (δ y : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1/2)
    (hy : 1+δ^2/4 ≤ y) : Real.exp ((d:ℝ)*δ)/4 ≤ ((Polynomial.Chebyshev.T ℝ (d:ℤ)).eval y)^2 := by
  have hδ2 : 0 ≤ δ^2 := sq_nonneg δ
  have hδsq : δ^2 ≤ 1 := by nlinarith
  have he := Real.abs_exp_sub_one_le (x:=δ^2/8) (by rw [abs_of_nonneg (by positivity)]; nlinarith)
  have hc := Real.cosh_le_exp_half_sq (δ/2)
  have heq : (δ/2)^2/2 = δ^2/8 := by ring
  rw [heq] at hc
  rw [abs_of_nonneg (by positivity : 0 ≤ δ^2/8)] at he
  have hcosh : Real.cosh (δ/2) ≤ y := by have := (abs_le.mp he).2; nlinarith
  have hy1 : 1 ≤ y := by nlinarith
  have ha := Real.arcosh_nonneg hy1
  have hθ : δ/2 ≤ Real.arcosh y := by
    rw [← Real.cosh_arcosh hy1] at hcosh
    have hh := Real.cosh_le_cosh.mp hcosh
    simpa [abs_of_nonneg ha, abs_of_nonneg (by positivity : 0 ≤ δ/2)] using hh
  have ht : (Polynomial.Chebyshev.T ℝ (d:ℤ)).eval y = Real.cosh ((d:ℝ)*Real.arcosh y) := by
    nth_rw 1 [← Real.cosh_arcosh hy1]
    simpa using Polynomial.Chebyshev.T_real_cosh (Real.arcosh y) (d:ℤ)
  rw [ht]
  have hexp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hθ (Nat.cast_nonneg d))
  have hch : Real.exp ((d:ℝ)*Real.arcosh y) ≤ 2*Real.cosh ((d:ℝ)*Real.arcosh y) := by
    rw [Real.cosh_eq]
    have := Real.exp_pos (-((d:ℝ)*Real.arcosh y))
    linarith
  have e : Real.exp ((d:ℝ)*δ) = Real.exp ((d:ℝ)*(δ/2))^2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [e]
  nlinarith [Real.exp_pos ((d:ℝ)*(δ/2)), Real.cosh_pos ((d:ℝ)*Real.arcosh y)]

private lemma polynomial_bump (d : ℕ) (c δ : ℝ) (hc : c ∈ Set.Icc (-1:ℝ) 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) :
    ∃ b : Polynomial ℝ, b.natDegree ≤ 4*d ∧
      (∀ x : ℝ, 0 ≤ b.eval x) ∧
      (∀ x ∈ Set.Icc (-1:ℝ) 1, δ ≤ |x-c| → b.eval x ≤ 1) ∧
      (∀ x : ℝ, |x-c| ≤ δ/2 → Real.exp ((d:ℝ)*δ)/4 ≤ b.eval x) := by
  let a : Polynomial ℝ := 1 + Polynomial.C (1/2:ℝ) * (Polynomial.C (δ^2) - (Polynomial.X - Polynomial.C c)^2)
  let b := ((Polynomial.Chebyshev.T ℝ (d:ℤ)).comp a)^2
  have ha (x : ℝ) : a.eval x = 1+(δ^2-(x-c)^2)/2 := by simp [a]; ring
  have hb (x : ℝ) : b.eval x = ((Polynomial.Chebyshev.T ℝ (d:ℤ)).eval (1+(δ^2-(x-c)^2)/2))^2 := by
    simp only [b, Polynomial.eval_pow, Polynomial.eval_comp, ha]
  have hadeg : a.natDegree ≤ 2 := by
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · simp
    · apply (Polynomial.natDegree_mul_le).trans
      simp only [Polynomial.natDegree_C, zero_add]
      apply (Polynomial.natDegree_sub_le _ _).trans
      apply max_le
      · simp
      · apply Polynomial.natDegree_pow_le.trans
        have hh : (Polynomial.X - Polynomial.C c).natDegree ≤ 1 := by simp
        omega
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · calc
      b.natDegree ≤ 2 * ((Polynomial.Chebyshev.T ℝ (d:ℤ)).comp a).natDegree := Polynomial.natDegree_pow_le
      _ ≤ 2 * ((Polynomial.Chebyshev.T ℝ (d:ℤ)).natDegree * a.natDegree) := Nat.mul_le_mul_left _ Polynomial.natDegree_comp_le
      _ ≤ 2 * (d*2) := by simp only [Polynomial.Chebyshev.natDegree_T, Int.natAbs_natCast]; gcongr
      _ = _ := by omega
  · intro x; rw [hb]; positivity
  · intro x hx hdist
    rw [hb]
    have h1 : (x-c)^2 ≤ 4 := by rcases hx with ⟨hxl,hxu⟩; rcases hc with ⟨hcl,hcu⟩; nlinarith [sq_nonneg (x-c-2),sq_nonneg (x-c+2)]
    have h2 : δ^2 ≤ (x-c)^2 := by nlinarith [sq_abs (x-c)]
    have habs : |1+(δ^2-(x-c)^2)/2| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith [sq_nonneg δ]
    have hh := Polynomial.Chebyshev.abs_eval_T_real_le_one (d:ℤ) habs
    have hh0 := abs_nonneg ((Polynomial.Chebyshev.T ℝ (d:ℤ)).eval (1+(δ^2-(x-c)^2)/2))
    nlinarith [sq_abs ((Polynomial.Chebyshev.T ℝ (d:ℤ)).eval (1+(δ^2-(x-c)^2)/2))]
  · intro x hx
    rw [hb]
    apply chebyshev_growth d δ _ hδ hδ1
    have hh := sq_abs (x-c)
    nlinarith [abs_nonneg (x-c)]

private lemma localized_bump (d : ℕ) (N M W : ℝ) (hN : 0 < N) (hM : 0 ≤ M)
    (hW : 0 < W) (hhalf : W ≤ N/2) (hMW : M+W ≤ N) :
    ∃ g : Polynomial ℝ, g.natDegree ≤ 4*d ∧
      (∀ t : ℝ, 0 ≤ g.eval t) ∧
      (∀ t ∈ Set.Icc (0:ℝ) N, (t ≤ M ∨ M+W ≤ t) → g.eval t ≤ 1) ∧
      W/8 * Real.exp ((d:ℝ)*(W/N)) ≤ ∫ t in (0:ℝ)..N, g.eval t := by
  let δ := W/N
  let c := (2*M+W)/N-1
  have hd : δ*N=W := by dsimp [δ]; field_simp
  have hc : c*N=2*M+W-N := by dsimp [c]; field_simp <;> ring
  have hδ : 0 < δ := div_pos hW hN
  have hδ1 : δ ≤ 1/2 := by nlinarith
  have hcc : c ∈ Set.Icc (-1:ℝ) 1 := by constructor <;> nlinarith
  obtain ⟨b, hdeg, hnon, htail, hcenter⟩ := polynomial_bump d c δ hcc hδ hδ1
  let x : Polynomial ℝ := Polynomial.C (2/N) * Polynomial.X - 1
  let g := b.comp x
  have hx (t : ℝ) : x.eval t * N = 2*t-N := by simp [x]; field_simp <;> ring
  have hg (t : ℝ) : g.eval t = b.eval (x.eval t) := by simp [g]
  have hxdeg : x.natDegree ≤ 1 := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · apply Polynomial.natDegree_mul_le.trans
      simp
    · simp
  have hgdeg : g.natDegree ≤ 4*d := by
    calc
      g.natDegree ≤ b.natDegree * x.natDegree := Polynomial.natDegree_comp_le
      _ ≤ (4*d)*1 := Nat.mul_le_mul hdeg hxdeg
      _ = _ := Nat.mul_one _
  have hgnon (t : ℝ) : 0 ≤ g.eval t := by rw [hg]; exact hnon _
  have hgint (a b : ℝ) : IntervalIntegrable (fun t => g.eval t) MeasureTheory.volume a b := g.continuous.intervalIntegrable _ _
  refine ⟨g, hgdeg, hgnon, ?_, ?_⟩
  · intro t ht htout
    rw [hg]
    have hxx : x.eval t ∈ Set.Icc (-1:ℝ) 1 := by have := hx t; constructor <;> nlinarith [ht.1,ht.2]
    apply htail _ hxx
    rcases htout with hleft | hright
    · have := hx t
      have ha := neg_le_abs (x.eval t-c)
      nlinarith
    · have := hx t
      have ha := le_abs_self (x.eval t-c)
      nlinarith
  · have ha : 0 ≤ M+W/4 := by positivity
    have hab : M+W/4 ≤ M+3*W/4 := by linarith
    have hb : M+3*W/4 ≤ N := by linarith
    have hsmall : (∫ t in (M+W/4)..(M+3*W/4), g.eval t) ≤ ∫ t in (0:ℝ)..N, g.eval t :=
      intervalIntegral.integral_mono_interval ha hab hb (Filter.Eventually.of_forall hgnon) (hgint 0 N)
    have hlower : (∫ t in (M+W/4)..(M+3*W/4), (Real.exp ((d:ℝ)*δ)/4)) ≤
        ∫ t in (M+W/4)..(M+3*W/4), g.eval t := by
      apply intervalIntegral.integral_mono_on hab (continuous_const.intervalIntegrable _ _) (hgint _ _)
      intro t ht
      rw [hg]
      apply hcenter
      rw [abs_le]
      have := hx t
      constructor <;> nlinarith [ht.1,ht.2]
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hlower
    have heq : (M+3*W/4-(M+W/4))*(Real.exp ((d:ℝ)*δ)/4) = W/8*Real.exp ((d:ℝ)*δ) := by ring
    rw [heq] at hlower
    exact hlower.trans hsmall

private lemma polynomial_primitive (g : Polynomial ℝ) :
    ∃ G : Polynomial ℝ, G.derivative = g ∧ G.natDegree ≤ g.natDegree+1 := by
  classical
  let G : Polynomial ℝ := ∑ i ∈ Finset.range (g.natDegree+1), Polynomial.monomial (i+1) (g.coeff i / (i+1:ℕ))
  refine ⟨G, ?_, ?_⟩
  · dsimp [G]
    rw [Polynomial.derivative_sum]
    simp only [Polynomial.derivative_monomial, Nat.add_sub_cancel]
    have heq (i : ℕ) : g.coeff i / ((i+1:ℕ):ℝ) * ((i+1:ℕ):ℝ) = g.coeff i := by
      apply div_mul_cancel₀
      positivity
    simp only [heq]
    exact g.as_sum_range.symm
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    apply (Polynomial.natDegree_monomial_le _).trans
    have := Finset.mem_range.mp hi
    omega

private lemma normalize_bump (n k : ℕ) (hn : 3 ≤ n) (M W : ℝ)
    (hM : 0 ≤ M) (hW : 0 ≤ W) (hMW : M+W ≤ (n:ℝ)-1)
    (g : Polynomial ℝ) (hdeg : g.natDegree+1 ≤ k)
    (hnon : ∀ t : ℝ, 0 ≤ g.eval t)
    (htail : ∀ t ∈ Set.Icc (0:ℝ) ((n:ℝ)-1), (t ≤ M ∨ M+W ≤ t) → g.eval t ≤ 1)
    (hmass : (n:ℝ)^4 ≤ ∫ t in (0:ℝ)..((n:ℝ)-1), g.eval t) :
    ∃ q : Polynomial ℝ, q.natDegree ≤ k ∧
      (∀ t ∈ Set.Icc (0:ℝ) ((n:ℝ)-1), 0 ≤ q.eval t) ∧
      (∀ t ∈ Set.Icc (0:ℝ) M, 1 ≤ q.eval t) ∧
      (∀ t ∈ Set.Icc (0:ℝ) ((n:ℝ)-1), q.eval t ≤ 1 + 1/(n:ℝ)^2) ∧
      (∀ t ∈ Set.Icc (M+W) ((n:ℝ)-1), q.eval t ≤ 1/(n:ℝ)^2) := by
  have hnR : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0:ℝ) < n := by linarith
  have hMN : M ≤ (n:ℝ)-1 := by linarith
  have hgi (a b : ℝ) : IntervalIntegrable (fun t => g.eval t) MeasureTheory.volume a b :=
    g.continuous.intervalIntegrable _ _
  let D : ℝ := ∫ t in M..((n:ℝ)-1), g.eval t
  have hleft : (∫ t in (0:ℝ)..M, g.eval t) ≤ M := by
    have hh := intervalIntegral.integral_mono_on hM (hgi 0 M)
      (continuous_const.intervalIntegrable 0 M) (fun t (ht : t ∈ Set.Icc (0:ℝ) M) => htail t ⟨ht.1,ht.2.trans hMN⟩ (Or.inl ht.2))
    simpa using hh
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hgi 0 M) (hgi M ((n:ℝ)-1))
  change (∫ t in (0:ℝ)..M, g.eval t) + D = _ at hsplit
  have hn3 : (n:ℝ) ≤ (n:ℝ)^3 := by
    have hh : 1 ≤ (n:ℝ)^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hh hnpos.le]
  have hn4 : (n:ℝ)^3 + (n:ℝ) ≤ (n:ℝ)^4 := by
    nlinarith [mul_nonneg (show 0 ≤ (n:ℝ)-2 by linarith) (show 0 ≤ (n:ℝ)^3 by positivity)]
  have hD : (n:ℝ)^3 ≤ D := by linarith
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hD
  have herror : ((n:ℝ)-1)/D ≤ 1/(n:ℝ)^2 := by
    apply (div_le_div_iff₀ hDpos (sq_pos_of_pos hnpos)).2
    nlinarith [sq_nonneg (n:ℝ)]
  obtain ⟨G, hderiv, hGdeg⟩ := polynomial_primitive g
  have hint (a b : ℝ) : (∫ t in a..b, g.eval t) = G.eval b-G.eval a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (hgi a b)
    intro x _
    simpa [hderiv] using G.hasDerivAt x
  let q := Polynomial.C (1/D) * (Polynomial.C (G.eval ((n:ℝ)-1)) - G)
  have heval (t : ℝ) : q.eval t = (∫ x in t..((n:ℝ)-1), g.eval x)/D := by
    simp only [q, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, hint]
    ring
  have hqdeg : q.natDegree ≤ k := by
    apply Polynomial.natDegree_mul_le.trans
    simp only [Polynomial.natDegree_C, zero_add]
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le (by simpa using (Nat.zero_le k)) (hGdeg.trans hdeg))
  refine ⟨q, hqdeg, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [heval]
    exact div_nonneg (intervalIntegral.integral_nonneg_of_forall (μ:=MeasureTheory.volume) ht.2 hnon) hDpos.le
  · intro t ht
    rw [heval]
    apply (one_le_div hDpos).2
    have hh := intervalIntegral.integral_add_adjacent_intervals (hgi t M) (hgi M ((n:ℝ)-1))
    have h0 := intervalIntegral.integral_nonneg_of_forall (μ:=MeasureTheory.volume) ht.2 hnon
    change (∫ x in t..M, g.eval x) + D = _ at hh
    linarith
  · intro t ht
    rw [heval]
    have hh := intervalIntegral.integral_add_adjacent_intervals (hgi 0 t) (hgi t ((n:ℝ)-1))
    have h0 := intervalIntegral.integral_nonneg_of_forall (μ:=MeasureTheory.volume) ht.1 hnon
    have hupper : (∫ x in t..((n:ℝ)-1), g.eval x) ≤ D+((n:ℝ)-1) := by linarith
    calc
      _ ≤ (D+((n:ℝ)-1))/D := div_le_div_of_nonneg_right hupper hDpos.le
      _ = 1+((n:ℝ)-1)/D := by rw [add_div, div_self hDpos.ne']
      _ ≤ _ := by linarith
  · intro t ht
    rw [heval]
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have hh := intervalIntegral.integral_mono_on ht.2 (hgi t ((n:ℝ)-1))
      (continuous_const.intervalIntegrable t ((n:ℝ)-1))
      (fun x (hx : x ∈ Set.Icc t ((n:ℝ)-1)) => htail x ⟨ht0.trans hx.1,hx.2⟩ (Or.inr (ht.1.trans hx.1)))
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at hh
    have hu : (∫ x in t..((n:ℝ)-1), g.eval x) ≤ (n:ℝ)-1 := by linarith
    exact (div_le_div_of_nonneg_right hu hDpos.le).trans herror

theorem solution (n k M W : ℕ) (hn : 3 ≤ n) (hk : 16 ≤ k)
    (hW : 96 * ((n : ℝ) / k) * Real.logb 2 n ≤ (W : ℝ))
    (hhalf : 2 * W ≤ n - 1) (hMW : M + W ≤ n - 1) :
    ∃ q : Polynomial ℝ, q.natDegree ≤ k ∧
      (∀ t : Fin n, 0 ≤ q.eval (t.val : ℝ)) ∧
      (∀ t : Fin n, t.val ≤ M → 1 ≤ q.eval (t.val : ℝ)) ∧
      (∀ t : Fin n, q.eval (t.val : ℝ) ≤ 1 + 1 / (n : ℝ)^2) ∧
      (∀ t : Fin n, M + W ≤ t.val → q.eval (t.val : ℝ) ≤ 1 / (n : ℝ)^2) := by
  have hnR : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0:ℝ) < n := by linarith
  have hkp : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hN : 0 < (n:ℝ)-1 := by linarith
  have hlog : 0 < Real.logb 2 n := Real.logb_pos (by norm_num) (by linarith)
  have hWp : (0:ℝ) < W := lt_of_lt_of_le (by positivity) hW
  have hWnat : 1 ≤ W := by exact_mod_cast hWp
  have hW1 : (1:ℝ) ≤ W := by exact_mod_cast hWnat
  have hhalfR : (W:ℝ) ≤ ((n:ℝ)-1)/2 := by
    have hh : (2:ℝ)*W+1 ≤ (n:ℝ) := by exact_mod_cast (show 2*W+1 ≤ n by omega)
    linarith
  have hMWR : (M:ℝ)+W ≤ (n:ℝ)-1 := by
    have hh : (M:ℝ)+W+1 ≤ (n:ℝ) := by exact_mod_cast (show M+W+1 ≤ n by omega)
    linarith
  let d := k/8
  have hdegree : 4*d+1 ≤ k := by dsimp [d]; omega
  have hdk : (k:ℝ) ≤ 16*(d:ℝ) := by exact_mod_cast (show k ≤ 16*d by dsimp [d]; omega)
  obtain ⟨g,hgdeg,hgnon,hgtail,hgmass⟩ := localized_bump d ((n:ℝ)-1) M W hN
    (Nat.cast_nonneg M) hWp hhalfR hMWR
  have hkW : 96*(n:ℝ)*Real.logb 2 n ≤ (W:ℝ)*k := by
    have he : 96*(n:ℝ)*Real.logb 2 n / k = 96*((n:ℝ)/k)*Real.logb 2 n := by ring
    exact (div_le_iff₀ hkp).1 (he.symm ▸ hW)
  have hscale : 6*Real.logb 2 n ≤ (d:ℝ)*((W:ℝ)/((n:ℝ)-1)) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hN).2
    nlinarith [mul_le_mul_of_nonneg_right hdk hWp.le]
  have hln : Real.log n ≤ Real.logb 2 n := by
    unfold Real.logb
    apply (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).2
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
    have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    nlinarith
  have hexp : (n:ℝ)^6 ≤ Real.exp ((d:ℝ)*((W:ℝ)/((n:ℝ)-1))) := by
    have hh := Real.exp_le_exp.mpr (show 6*Real.log n ≤ (d:ℝ)*((W:ℝ)/((n:ℝ)-1)) by linarith)
    have he : Real.exp (6*Real.log (n:ℝ)) = (n:ℝ)^6 := by
      rw [show (6:ℝ) = ((6:ℕ):ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hnp]
    rwa [he] at hh
  have hnum : (n:ℝ)^4 ≤ (W:ℝ)/8 * (n:ℝ)^6 := by
    have hsq : (8:ℝ) ≤ (n:ℝ)^2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hsq (show 0 ≤ (n:ℝ)^4 by positivity)
    have hhW := mul_le_mul_of_nonneg_right hW1 (show 0 ≤ (n:ℝ)^6 by positivity)
    nlinarith
  have hmass : (n:ℝ)^4 ≤ ∫ t in (0:ℝ)..((n:ℝ)-1), g.eval t :=
    (hnum.trans (mul_le_mul_of_nonneg_left hexp (by positivity))).trans hgmass
  obtain ⟨q,hq,hqnon,hqone,hqupper,hqtail⟩ := normalize_bump n k hn M W (Nat.cast_nonneg M)
    hWp.le hMWR g (by omega) hgnon hgtail hmass
  have ht (t : Fin n) : (t.val:ℝ) ∈ Set.Icc (0:ℝ) ((n:ℝ)-1) := by
    refine ⟨Nat.cast_nonneg _, ?_⟩
    have hh : t.val+1 ≤ n := t.isLt
    have hhR : (t.val:ℝ)+1 ≤ (n:ℝ) := by exact_mod_cast hh
    linarith
  refine ⟨q,hq,fun t => hqnon _ (ht t),?_,fun t => hqupper _ (ht t),?_⟩
  · intro t htm
    exact hqone _ ⟨Nat.cast_nonneg _, by exact_mod_cast htm⟩
  · intro t htm
    exact hqtail _ ⟨by exact_mod_cast htm, (ht t).2⟩
