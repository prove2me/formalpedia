-- Prove2me | solution 1 for MarkovChain.isStationary_of_reversible
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-12T19:30:18.033982+00:00
-- url     : https://prove2.me/submissions/603af700-30cb-4094-9b32-f16a0204fb57

import Definitions.Def_MarkovChain

set_option linter.unusedSectionVars false

namespace MCloc

open MarkovChain

open Finset Matrix Filter Topology

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Distributions and the transition operator -/

theorem nonempty_of_mem_stdSimplex {μ : n → ℝ} (h : μ ∈ stdSimplex ℝ n) : Nonempty n := by
  by_contra hc
  rw [not_nonempty_iff] at hc
  have h1 : ∑ i, μ i = 1 := h.2
  simp [Finset.univ_eq_empty] at h1

theorem mem_stdSimplex_vecMul {M : Matrix n n ℝ} (hM : M ∈ rowStochastic ℝ n)
    {μ : n → ℝ} (hμ : μ ∈ stdSimplex ℝ n) : μ ᵥ* M ∈ stdSimplex ℝ n := by
  obtain ⟨hμ0, hμ1⟩ := hμ
  refine ⟨fun j => ?_, ?_⟩
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (hμ0 i) (hM.1 i j)
  · show ∑ j, ∑ i, μ i * M i j = 1
    rw [Finset.sum_comm]
    calc ∑ i, ∑ j, μ i * M i j = ∑ i, μ i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.mul_sum, Matrix.sum_row_of_mem_rowStochastic hM i, mul_one]
      _ = 1 := hμ1

/-! ### Existence of a stationary distribution -/

theorem exists_isStationary {M : Matrix n n ℝ} (hne : Nonempty n)
    (hM : M ∈ rowStochastic ℝ n) : ∃ π : n → ℝ, IsStationary M π := by
  classical
  set S : (n → ℝ) → (n → ℝ) := fun μ => μ ᵥ* M with hSdef
  have hScont : Continuous S := by
    refine continuous_pi fun j => continuous_finsetSum _ fun i _ => ?_
    exact (continuous_apply i).mul continuous_const
  have hSmaps : ∀ μ ∈ stdSimplex ℝ n, S μ ∈ stdSimplex ℝ n :=
    fun μ hμ => mem_stdSimplex_vecMul hM hμ
  obtain ⟨i₀⟩ := hne
  set v : n → ℝ := fun i => if i = i₀ then 1 else 0 with hvdef
  have hv : v ∈ stdSimplex ℝ n := by
    refine ⟨fun i => ?_, ?_⟩
    · by_cases h : i = i₀ <;> simp [hvdef, h]
    · simp [hvdef]
  set x : ℕ → (n → ℝ) := fun m => S^[m] v with hxdef
  have hxsucc : ∀ m, x (m + 1) = S (x m) := fun m => Function.iterate_succ_apply' S m v
  have hx : ∀ m, x m ∈ stdSimplex ℝ n := by
    intro m
    induction m with
    | zero => simpa [hxdef] using hv
    | succ m ih => rw [hxsucc m]; exact hSmaps _ ih
  have hx01 : ∀ m i, x m i ∈ Set.Icc (0 : ℝ) 1 := by
    intro m i
    refine ⟨(hx m).1 i, ?_⟩
    rw [← (hx m).2]
    exact Finset.single_le_sum (fun j _ => (hx m).1 j) (Finset.mem_univ i)
  set a : ℕ → (n → ℝ) := fun m i => (∑ r ∈ range (m + 1), x r i) / ((m : ℝ) + 1) with hadef
  have hmpos : ∀ m : ℕ, (0 : ℝ) < (m : ℝ) + 1 := fun m => by positivity
  have ha : ∀ m, a m ∈ stdSimplex ℝ n := by
    intro m
    refine ⟨fun i => div_nonneg (Finset.sum_nonneg fun r _ => (hx r).1 i) (hmpos m).le, ?_⟩
    show ∑ i, (∑ r ∈ range (m + 1), x r i) / ((m : ℝ) + 1) = 1
    rw [← Finset.sum_div, Finset.sum_comm,
      Finset.sum_congr rfl (fun r _ => (hx r).2), Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast
    exact div_self (hmpos m).ne'
  have hdiff : ∀ m i, S (a m) i - a m i = (x (m + 1) i - x 0 i) / ((m : ℝ) + 1) := by
    intro m i
    have hstep : ∀ r, ∑ k, x r k * M k i = x (r + 1) i := by
      intro r; rw [hxsucc r]; rfl
    have hSam : S (a m) i = (∑ r ∈ range (m + 1), x (r + 1) i) / ((m : ℝ) + 1) := by
      show ∑ k, a m k * M k i = _
      rw [eq_div_iff (hmpos m).ne', Finset.sum_mul]
      calc ∑ k, a m k * M k i * ((m : ℝ) + 1)
          = ∑ k, ∑ r ∈ range (m + 1), x r k * M k i := by
            refine Finset.sum_congr rfl fun k _ => ?_
            show (∑ r ∈ range (m + 1), x r k) / ((m : ℝ) + 1) * M k i * ((m : ℝ) + 1) = _
            field_simp
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun r _ => by ring
        _ = ∑ r ∈ range (m + 1), ∑ k, x r k * M k i := Finset.sum_comm
        _ = ∑ r ∈ range (m + 1), x (r + 1) i := Finset.sum_congr rfl fun r _ => hstep r
    rw [hSam]
    show _ = _
    rw [hadef, div_sub_div_same, ← Finset.sum_sub_distrib,
      Finset.sum_range_sub (fun r => x r i) (m + 1)]
  have htend0 : Tendsto (fun m => S (a m) - a m) atTop (𝓝 0) := by
    rw [tendsto_pi_nhds]
    intro i
    have hz : (0 : n → ℝ) i = 0 := rfl
    rw [hz]
    have hb2 : ∀ m : ℕ, (S (a m) - a m) i ≤ 1 / ((m : ℝ) + 1) := by
      intro m
      rw [show (S (a m) - a m) i = (x (m + 1) i - x 0 i) / ((m : ℝ) + 1) from hdiff m i,
        div_le_div_iff_of_pos_right (hmpos m)]
      linarith [(hx01 (m + 1) i).2, (hx01 0 i).1]
    have hb1 : ∀ m : ℕ, -(1 / ((m : ℝ) + 1)) ≤ (S (a m) - a m) i := by
      intro m
      rw [show (S (a m) - a m) i = (x (m + 1) i - x 0 i) / ((m : ℝ) + 1) from hdiff m i,
        neg_div', div_le_div_iff_of_pos_right (hmpos m)]
      linarith [(hx01 (m + 1) i).1, (hx01 0 i).2]
    have hlim0 : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa using hlim0.neg) hlim0 hb1 hb2
  obtain ⟨π, hπ, φ, hφ, hlim⟩ := (isCompact_stdSimplex ℝ n).tendsto_subseq ha
  have hSlim : Tendsto (fun k => S (a (φ k))) atTop (𝓝 (S π)) := (hScont.tendsto π).comp hlim
  have hdlim : Tendsto (fun k => S (a (φ k)) - a (φ k)) atTop (𝓝 0) :=
    htend0.comp hφ.tendsto_atTop
  have hback : Tendsto (fun k => a (φ k)) atTop (𝓝 (S π - 0)) := by
    have := hSlim.sub hdlim; simpa using this
  exact ⟨π, hπ, by simpa using (tendsto_nhds_unique hback hlim)⟩

/-! ### Total variation distance -/

theorem tvDist_nonneg (μ ν : n → ℝ) : 0 ≤ tvDist μ ν := by
  refine div_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) (by norm_num)

theorem tvDist_metric (μ ν ρ : n → ℝ) :
    0 ≤ tvDist μ ν ∧ tvDist μ ν = tvDist ν μ ∧ (tvDist μ ν = 0 ↔ μ = ν) ∧
      tvDist μ ρ ≤ tvDist μ ν + tvDist ν ρ := by
  refine ⟨tvDist_nonneg μ ν, ?_, ?_, ?_⟩
  · simp only [tvDist]
    congr 1
    exact Finset.sum_congr rfl fun i _ => abs_sub_comm _ _
  · constructor
    · intro h
      have hs : ∑ i, |μ i - ν i| = 0 := by
        simpa [tvDist] using h
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => abs_nonneg (μ i - ν i))).1 hs i
        (Finset.mem_univ i)
      have := abs_eq_zero.1 this
      linarith [this]
    · rintro rfl; simp [tvDist]
  · simp only [tvDist]
    rw [← add_div, div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 2),
      ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => by
      have := abs_sub_abs_le_abs_sub (μ i - ν i) (ρ i - ν i)
      calc |μ i - ρ i| = |(μ i - ν i) + (ν i - ρ i)| := by ring_nf
        _ ≤ |μ i - ν i| + |ν i - ρ i| := abs_add_le _ _

theorem abs_sub_le_two_mul_tvDist (μ ν : n → ℝ) (i : n) :
    |μ i - ν i| ≤ 2 * tvDist μ ν := by
  have h : |μ i - ν i| ≤ ∑ j, |μ j - ν j| :=
    Finset.single_le_sum (f := fun j => |μ j - ν j|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  simp only [tvDist]
  linarith

theorem tvDist_le_one {μ ν : n → ℝ} (hμ : μ ∈ stdSimplex ℝ n) (hν : ν ∈ stdSimplex ℝ n) :
    tvDist μ ν ≤ 1 := by
  have h : ∑ i, |μ i - ν i| ≤ 2 := by
    calc ∑ i, |μ i - ν i| ≤ ∑ i, (μ i + ν i) :=
          Finset.sum_le_sum fun i _ => by
            rw [abs_le]
            refine ⟨?_, ?_⟩
            · linarith [hμ.1 i, hν.1 i]
            · linarith [hμ.1 i, hν.1 i]
      _ = 2 := by rw [Finset.sum_add_distrib, hμ.2, hν.2]; norm_num
  simp only [tvDist]
  linarith

/-! ### Doeblin's condition and contraction of the transition operator -/

theorem doeblin_le_one {M : Matrix n n ℝ} {ε : ℝ} {ν : n → ℝ}
    (hM : M ∈ rowStochastic ℝ n) (hD : IsDoeblin M ε ν) : ε ≤ 1 := by
  obtain ⟨hε, hν, hD'⟩ := hD
  obtain ⟨i₀⟩ := nonempty_of_mem_stdSimplex hν
  have h1 : ∑ j, ε * ν j ≤ ∑ j, M i₀ j := Finset.sum_le_sum fun j _ => hD' i₀ j
  rwa [← Finset.mul_sum, hν.2, mul_one,
    Matrix.sum_row_of_mem_rowStochastic hM i₀] at h1

theorem tvDist_vecMul_le_of_doeblin {M : Matrix n n ℝ} {ε : ℝ} {ν : n → ℝ}
    (hM : M ∈ rowStochastic ℝ n) (hD : IsDoeblin M ε ν)
    {μ μ' : n → ℝ} (hμ : μ ∈ stdSimplex ℝ n) (hμ' : μ' ∈ stdSimplex ℝ n) :
    tvDist (μ ᵥ* M) (μ' ᵥ* M) ≤ (1 - ε) * tvDist μ μ' := by
  obtain ⟨hε, hν, hD'⟩ := hD
  have hQ0 : ∀ i j, 0 ≤ M i j - ε * ν j := fun i j => sub_nonneg.2 (hD' i j)
  have hQsum : ∀ i, ∑ j, (M i j - ε * ν j) = 1 - ε := by
    intro i
    rw [Finset.sum_sub_distrib, Matrix.sum_row_of_mem_rowStochastic hM i,
      ← Finset.mul_sum, hν.2, mul_one]
  have hd0 : ∑ i, (μ i - μ' i) = 0 := by
    rw [Finset.sum_sub_distrib, hμ.2, hμ'.2, sub_self]
  have hkey : ∀ j, (μ ᵥ* M) j - (μ' ᵥ* M) j
      = ∑ i, (μ i - μ' i) * (M i j - ε * ν j) := by
    intro j
    have e1 : ∑ i, (μ i - μ' i) * (M i j - ε * ν j)
        = (∑ i, (μ i - μ' i) * M i j) - (ε * ν j) * ∑ i, (μ i - μ' i) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, hd0, mul_zero, sub_zero]
    show (∑ i, μ i * M i j) - (∑ i, μ' i * M i j) = _
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hbound : ∑ j, |(μ ᵥ* M) j - (μ' ᵥ* M) j| ≤ (1 - ε) * ∑ i, |μ i - μ' i| := by
    calc ∑ j, |(μ ᵥ* M) j - (μ' ᵥ* M) j|
        = ∑ j, |∑ i, (μ i - μ' i) * (M i j - ε * ν j)| :=
          Finset.sum_congr rfl fun j _ => by rw [hkey j]
      _ ≤ ∑ j, ∑ i, |μ i - μ' i| * (M i j - ε * ν j) := by
          refine Finset.sum_le_sum fun j _ => ?_
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          exact Finset.sum_le_sum fun i _ => by
            rw [abs_mul, abs_of_nonneg (hQ0 i j)]
      _ = ∑ i, |μ i - μ' i| * (1 - ε) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => by rw [← Finset.mul_sum, hQsum i]
      _ = (1 - ε) * ∑ i, |μ i - μ' i| := by rw [← Finset.sum_mul]; ring
  show (∑ j, |(μ ᵥ* M) j - (μ' ᵥ* M) j|) / 2 ≤ (1 - ε) * ((∑ i, |μ i - μ' i|) / 2)
  rw [mul_div_assoc', div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 2)]
  exact hbound

theorem isStationary_unique_of_doeblin {M : Matrix n n ℝ} {ε : ℝ} {ν : n → ℝ}
    (hM : M ∈ rowStochastic ℝ n) (hD : IsDoeblin M ε ν)
    {π π' : n → ℝ} (h1 : IsStationary M π) (h2 : IsStationary M π') : π = π' := by
  have hc := tvDist_vecMul_le_of_doeblin hM hD h1.1 h2.1
  rw [h1.2, h2.2] at hc
  have hnn := tvDist_nonneg π π'
  have hzero : tvDist π π' = 0 := by nlinarith [hD.1]
  exact ((tvDist_metric π π' π).2.2.1).1 hzero

/-! ### Convergence to equilibrium -/

theorem vecMul_pow_of_isStationary {M : Matrix n n ℝ} {π : n → ℝ}
    (hπ : IsStationary M π) (k : ℕ) : π ᵥ* M ^ k = π := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hπ.2]

theorem tvDist_vecMul_pow_le {M : Matrix n n ℝ} {ε : ℝ} {ν : n → ℝ}
    (hM : M ∈ rowStochastic ℝ n) (hD : IsDoeblin M ε ν)
    {μ π : n → ℝ} (hμ : μ ∈ stdSimplex ℝ n) (hπ : IsStationary M π) (k : ℕ) :
    tvDist (μ ᵥ* M ^ k) π ≤ (1 - ε) ^ k * tvDist μ π := by
  have hε1 : ε ≤ 1 := doeblin_le_one hM hD
  have hpos : (0 : ℝ) ≤ 1 - ε := by linarith
  induction k with
  | zero => simp
  | succ k ih =>
      have hmem : μ ᵥ* M ^ k ∈ stdSimplex ℝ n :=
        mem_stdSimplex_vecMul (pow_mem hM k) hμ
      have hstep : μ ᵥ* M ^ (k + 1) = (μ ᵥ* M ^ k) ᵥ* M := by
        rw [pow_succ, ← Matrix.vecMul_vecMul]
      rw [hstep]
      calc tvDist ((μ ᵥ* M ^ k) ᵥ* M) π
          = tvDist ((μ ᵥ* M ^ k) ᵥ* M) (π ᵥ* M) := by rw [hπ.2]
        _ ≤ (1 - ε) * tvDist (μ ᵥ* M ^ k) π :=
            tvDist_vecMul_le_of_doeblin hM hD hmem hπ.1
        _ ≤ (1 - ε) * ((1 - ε) ^ k * tvDist μ π) := mul_le_mul_of_nonneg_left ih hpos
        _ = (1 - ε) ^ (k + 1) * tvDist μ π := by ring

theorem tendsto_vecMul_pow_of_doeblin {M : Matrix n n ℝ} {ε : ℝ} {ν : n → ℝ}
    (hM : M ∈ rowStochastic ℝ n) (hD : IsDoeblin M ε ν)
    {μ π : n → ℝ} (hμ : μ ∈ stdSimplex ℝ n) (hπ : IsStationary M π) :
    Tendsto (fun k => tvDist (μ ᵥ* M ^ k) π) atTop (𝓝 0) ∧
      ∀ i, Tendsto (fun k => (μ ᵥ* M ^ k) i) atTop (𝓝 (π i)) := by
  have hε1 : ε ≤ 1 := doeblin_le_one hM hD
  have hpos : (0 : ℝ) ≤ 1 - ε := by linarith
  have hlt : (1 : ℝ) - ε < 1 := by linarith [hD.1]
  have hgeo : Tendsto (fun k : ℕ => (1 - ε) ^ k * tvDist μ π) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hpos hlt).mul_const (tvDist μ π)
  have htv : Tendsto (fun k => tvDist (μ ᵥ* M ^ k) π) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgeo
      (fun k => tvDist_nonneg _ _) (fun k => tvDist_vecMul_pow_le hM hD hμ hπ k)
  refine ⟨htv, fun i => ?_⟩
  have h2 : Tendsto (fun k => 2 * tvDist (μ ᵥ* M ^ k) π) atTop (𝓝 0) := by
    simpa using htv.const_mul 2
  have hsub : Tendsto (fun k => (μ ᵥ* M ^ k) i - π i) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using h2.neg) h2
      (fun k => (abs_le.1 (abs_sub_le_two_mul_tvDist (μ ᵥ* M ^ k) π i)).1)
      (fun k => (abs_le.1 (abs_sub_le_two_mul_tvDist (μ ᵥ* M ^ k) π i)).2)
  simpa using hsub.add_const (π i)

/-! ### Recognizing Doeblin chains and stationary distributions -/

theorem isDoeblin_of_pos {M : Matrix n n ℝ} {c : ℝ} (hne : Nonempty n) (hc : 0 < c)
    (h : ∀ i j, c ≤ M i j) : IsDoeblin M (Fintype.card n * c) (unif n) := by
  have hcard : (0 : ℝ) < (Fintype.card n : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.2 hne
  refine ⟨by positivity, ⟨fun i => inv_nonneg.2 hcard.le, ?_⟩, fun i j => ?_⟩
  · simp only [unif, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  · have he : (Fintype.card n : ℝ) * c * unif n j = c := by
      simp only [unif]; field_simp
    rw [he]
    exact h i j

theorem isStationary_of_reversible {M : Matrix n n ℝ} (hM : M ∈ rowStochastic ℝ n)
    {π : n → ℝ} (hπ : π ∈ stdSimplex ℝ n) (hrev : IsReversible M π) :
    IsStationary M π := by
  refine ⟨hπ, ?_⟩
  funext j
  show ∑ i, π i * M i j = π j
  calc ∑ i, π i * M i j = ∑ i, π j * M j i := Finset.sum_congr rfl fun i _ => hrev i j
    _ = π j := by
        rw [← Finset.mul_sum, Matrix.sum_row_of_mem_rowStochastic hM j, mul_one]

theorem isStationary_unif_of_colSum {M : Matrix n n ℝ} (hne : Nonempty n)
    (hcol : ∀ j, ∑ i, M i j = 1) : IsStationary M (unif n) := by
  have hcard : (0 : ℝ) < (Fintype.card n : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.2 hne
  refine ⟨⟨fun i => inv_nonneg.2 hcard.le, ?_⟩, ?_⟩
  · simp only [unif, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  · funext j
    show ∑ i, unif n i * M i j = unif n j
    simp only [unif]
    rw [← Finset.mul_sum, hcol j, mul_one]

theorem existsUnique_isStationary_of_pos {M : Matrix n n ℝ} {c : ℝ} (hne : Nonempty n)
    (hM : M ∈ rowStochastic ℝ n) (hc : 0 < c) (h : ∀ i j, c ≤ M i j) :
    ∃! π : n → ℝ, IsStationary M π := by
  obtain ⟨π, hπ⟩ := exists_isStationary hne hM
  exact ⟨π, hπ, fun π' hπ' =>
    isStationary_unique_of_doeblin hM (isDoeblin_of_pos hne hc h) hπ' hπ⟩

end MCloc

open Finset Matrix Filter Topology MarkovChain in
theorem solution {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℝ} (hM : M ∈ rowStochastic ℝ n)
    {π : n → ℝ} (hπ : π ∈ stdSimplex ℝ n) (hrev : IsReversible M π) :
    IsStationary M π :=
  MCloc.isStationary_of_reversible hM hπ hrev
