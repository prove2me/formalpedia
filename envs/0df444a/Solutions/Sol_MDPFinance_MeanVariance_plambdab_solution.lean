-- Prove2me | solution 1 for MDPFinance.MeanVariance.plambdab_solution
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T18:46:42.993114+00:00
-- url     : https://prove2.me/submissions/a2244f59-8c17-49e4-b08d-9f8a6545faf6

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MeanRiskMarket
import Definitions.Def_MDPFinance_MeanVariance_PLambdaBValueFunction
import Definitions.Def_MDPFinance_MeanVariance_MRcdSeq

open MeasureTheory ProbabilityTheory

namespace S100PLB
open MDPFinance.MeanVariance

variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def val (M : MeanRiskMarket Ω) (b : Bool) : ℝ := if b then M.u - 1 else M.d - 1
noncomputable def wt (M : MeanRiskMarket Ω) (b : Bool) : ℝ := if b then M.p else 1 - M.p

noncomputable def det (M : MeanRiskMarket Ω) (π : ℕ → ℝ → ℝ) :
    (k : ℕ) → ℕ → ℝ → (Fin k → Bool) → ℝ
  | 0, _, x, _ => x
  | k + 1, n, x, s => det M π k (n + 1) (x + π n x * val M (s 0)) (Fin.tail s)

def Aset (M : MeanRiskMarket Ω) (k n : ℕ) (s : Fin k → Bool) : Set Ω :=
  {ω | ∀ i : Fin k, M.R (n + 1 + i) ω = val M (s i)}

lemma tw_eq_det (M : MeanRiskMarket Ω) (π : ℕ → ℝ → ℝ) : ∀ (k n : ℕ) (x : ℝ)
    (s : Fin k → Bool) (ω : Ω), ω ∈ Aset M k n s →
    M.terminalWealth π k n x ω = det M π k n x s
  | 0, n, x, s, ω, _ => rfl
  | k + 1, n, x, s, ω, h => by
      have h0 : M.R (n + 1) ω = val M (s 0) := by simpa using h 0
      have h1 : ω ∈ Aset M k (n + 1) (Fin.tail s) := fun i => by
        have := h i.succ
        simp only [Fin.val_succ, Fin.tail] at this ⊢
        rw [show n + 1 + 1 + (i : ℕ) = n + 1 + ((i : ℕ) + 1) by ring]
        exact this
      show M.terminalWealth π k (n + 1) (x + π n x * M.R (n + 1) ω) ω = _
      rw [h0]
      exact tw_eq_det M π k (n + 1) _ _ ω h1


lemma measure_Aset (M : MeanRiskMarket Ω) (k n : ℕ) (hk : n + k ≤ M.N) (s : Fin k → Bool) :
    M.measIP (Aset M k n s) = ∏ i : Fin k, ENNReal.ofReal (wt M (s i)) := by
  classical
  let v : Fin M.N → ℝ := fun j =>
    if h : n ≤ j.val ∧ j.val < n + k then val M (s ⟨j.val - n, by omega⟩) else 0
  let S : Finset (Fin M.N) := Finset.univ.filter (fun j => n ≤ j.val ∧ j.val < n + k)
  have hA : Aset M k n s = ⋂ j ∈ S, (fun (j : Fin M.N) ω => M.R (j.val + 1) ω) j ⁻¹' {v j} := by
    ext ω
    simp only [Aset, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff,
      S, Finset.mem_filter, Finset.mem_univ, true_and, v]
    constructor
    · intro h j hj
      rw [dif_pos hj]
      have := h ⟨j.val - n, by omega⟩
      simp only at this
      rw [show n + 1 + (j.val - n) = j.val + 1 by omega] at this
      exact this
    · intro h i
      have := h ⟨n + i, by omega⟩ ⟨by simp, by simp⟩
      rw [dif_pos (by simp)] at this
      simp only at this
      rw [show n + 1 + (i : ℕ) = n + i + 1 by ring, this]
      congr 2
      ext; simp
  rw [hA, M.hR_indep.measure_inter_preimage_eq_mul S
    (fun j _ => measurableSet_singleton (v j))]
  symm
  refine Finset.prod_bij (fun i _ => (⟨n + i, by omega⟩ : Fin M.N)) ?_ ?_ ?_ ?_
  · intro i _; simp [S]
  · intro i _ j _ h; simpa [Fin.ext_iff] using h
  · intro j hj
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact ⟨⟨j.val - n, by omega⟩, Finset.mem_univ _, by ext; simp; omega⟩
  · intro i _
    have hv : v ⟨n + i, by omega⟩ = val M (s i) := by
      simp only [v]; rw [dif_pos (by simp)]; congr 2; ext; simp
    simp only [Set.preimage, hv]
    have hl := M.hR_law (n + i + 1) (by omega) (by omega)
    cases s i <;> simp [val, wt, hl.1, hl.2]


lemma ae_good (M : MeanRiskMarket Ω) :
    ∀ᵐ ω ∂M.measIP, ∀ j : ℕ, 1 ≤ j → j ≤ M.N → M.R j ω = M.u - 1 ∨ M.R j ω = M.d - 1 := by
  have := M.isProb
  rw [ae_all_iff]; intro j
  by_cases hj : 1 ≤ j ∧ j ≤ M.N
  swap
  · exact Filter.Eventually.of_forall fun ω h1 h2 => absurd ⟨h1, h2⟩ hj
  have hm := M.hR_meas j hj.1 hj.2
  have hl := M.hR_law j hj.1 hj.2
  have hU : MeasurableSet {ω | M.R j ω = M.u - 1} := hm (measurableSet_singleton _)
  have hD : MeasurableSet {ω | M.R j ω = M.d - 1} := hm (measurableSet_singleton _)
  have hdisj : Disjoint {ω | M.R j ω = M.u - 1} {ω | M.R j ω = M.d - 1} := by
    rw [Set.disjoint_left]; intro ω h1 h2
    simp only [Set.mem_ofPred_eq] at h1 h2
    have := M.hd_lt_one; have := M.hone_lt_u; linarith
  have hp := M.hp_mem
  have hunion : M.measIP ({ω | M.R j ω = M.u - 1} ∪ {ω | M.R j ω = M.d - 1}) = 1 := by
    rw [measure_union hdisj hD, hl.1, hl.2, ← ENNReal.ofReal_add hp.1.le (by linarith [hp.2])]
    simp
  have hc : M.measIP ({ω | M.R j ω = M.u - 1} ∪ {ω | M.R j ω = M.d - 1})ᶜ = 0 := by
    rw [prob_compl_eq_one_sub (hU.union hD), hunion]; simp
  rw [ae_iff]
  refine measure_mono_null ?_ hc
  intro ω hω
  simp only [Set.mem_ofPred_eq, not_forall] at hω
  obtain ⟨_, _, h⟩ := hω
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq]
  tauto

lemma integral_eq_sum (M : MeanRiskMarket Ω) (π : ℕ → ℝ → ℝ) (φ : ℝ → ℝ) (k n : ℕ)
    (hk : n + k ≤ M.N) (x : ℝ) :
    ∫ ω, φ (M.terminalWealth π k n x ω) ∂M.measIP =
      ∑ s : Fin k → Bool, (∏ i, wt M (s i)) * φ (det M π k n x s) := by
  classical
  have := M.isProb
  have hmeas : ∀ s, MeasurableSet (Aset M k n s) := by
    intro s
    have : Aset M k n s = ⋂ i : Fin k, (M.R (n + 1 + i)) ⁻¹' {val M (s i)} := by
      ext ω; simp [Aset]
    rw [this]
    exact MeasurableSet.iInter fun i =>
      M.hR_meas _ (by omega) (by omega) (measurableSet_singleton _)
  have hae : (fun ω => φ (M.terminalWealth π k n x ω)) =ᵐ[M.measIP]
      fun ω => ∑ s : Fin k → Bool, (Aset M k n s).indicator (fun _ => φ (det M π k n x s)) ω := by
    filter_upwards [ae_good M] with ω hω
    let s0 : Fin k → Bool := fun i => decide (M.R (n + 1 + i) ω = M.u - 1)
    have hs0 : ω ∈ Aset M k n s0 := by
      intro i
      rcases hω (n + 1 + i) (by omega) (by omega) with h | h
      · simp [s0, h, val]
      · have : M.d - 1 ≠ M.u - 1 := by have := M.hd_lt_one; have := M.hone_lt_u; intro h; linarith
        simp [s0, h, val, this]
    have huniq : ∀ s, ω ∈ Aset M k n s → s = s0 := by
      intro s hs; funext i
      have h := hs i
      have : M.d - 1 ≠ M.u - 1 := by have := M.hd_lt_one; have := M.hone_lt_u; intro h; linarith
      simp only [s0, h]
      cases s i <;> simp [val, this]
    rw [Finset.sum_eq_single s0, Set.indicator_of_mem hs0, tw_eq_det M π k n x s0 ω hs0]
    · intro s _ hne
      rw [Set.indicator_of_notMem]
      exact fun h => hne (huniq s h)
    · simp
  rw [integral_congr_ae hae, integral_finsetSum]
  · refine Finset.sum_congr rfl fun s _ => ?_
    rw [integral_indicator_const _ (hmeas s), smul_eq_mul, Measure.real, measure_Aset M k n hk s,
      ENNReal.toReal_prod]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    have hp := M.hp_mem
    rw [ENNReal.toReal_ofReal]
    cases s i <;> simp [wt] <;> linarith [hp.1, hp.2]
  · intro s _
    exact (integrable_const _).indicator (hmeas s)

noncomputable def Ev (M : MeanRiskMarket Ω) (π : ℕ → ℝ → ℝ) (φ : ℝ → ℝ) : ℕ → ℕ → ℝ → ℝ
  | 0, _, x => φ x
  | k + 1, n, x => M.p * Ev M π φ k (n + 1) (x + π n x * (M.u - 1)) +
      (1 - M.p) * Ev M π φ k (n + 1) (x + π n x * (M.d - 1))

lemma sum_eq_Ev (M : MeanRiskMarket Ω) (π : ℕ → ℝ → ℝ) (φ : ℝ → ℝ) : ∀ (k n : ℕ) (x : ℝ),
    ∑ s : Fin k → Bool, (∏ i, wt M (s i)) * φ (det M π k n x s) = Ev M π φ k n x
  | 0, n, x => by simp [det, Ev]
  | k + 1, n, x => by
      rw [← (Fin.consEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
      have hce : ∀ b (t : Fin k → Bool), (Fin.consEquiv (fun _ => Bool)) (b, t) =
          (Fin.cons b t : Fin (k + 1) → Bool) := fun _ _ => rfl
      simp only [hce, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, det, Fin.tail_cons,
        mul_assoc, ← Finset.mul_sum, sum_eq_Ev M π φ k (n + 1)]
      simp [Ev, wt, val]

lemma integral_eq_Ev (M : MeanRiskMarket Ω) (π : ℕ → ℝ → ℝ) (φ : ℝ → ℝ) (k n : ℕ)
    (hk : n + k ≤ M.N) (x : ℝ) :
    ∫ ω, φ (M.terminalWealth π k n x ω) ∂M.measIP = Ev M π φ k n x := by
  rw [integral_eq_sum M π φ k n hk x, sum_eq_Ev]

lemma Ev_lin (M : MeanRiskMarket Ω) (π : ℕ → ℝ → ℝ) (φ ψ : ℝ → ℝ) (A B : ℝ) :
    ∀ (k n : ℕ) (x : ℝ), Ev M π (fun X => A * φ X - B * ψ X) k n x =
      A * Ev M π φ k n x - B * Ev M π ψ k n x
  | 0, n, x => rfl
  | k + 1, n, x => by
      simp only [Ev, Ev_lin M π φ ψ A B k (n + 1)]; ring


/-! ### One-step real algebra -/

lemma h_ge (C D l t : ℝ) (hDl : D ≤ l) (hlC : l ≤ C) :
    -l * t ≤ C * max (-t) 0 - D * max t 0 := by
  rcases le_total t 0 with ht | ht
  · rw [max_eq_left (by linarith), max_eq_right ht]; nlinarith
  · rw [max_eq_right (by linarith), max_eq_left ht]; nlinarith

lemma step_lower (p u d C D y a yu yd : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hu : 1 < u) (hd : d < 1)
    (hpq : (1 - p) * (1 - d) ≤ p * (u - 1)) (hD0 : 0 ≤ D) (hDC : D ≤ C)
    (hcd : D * (p * (u - d) / (1 - d)) ≤ C * ((1 - p) * (u - d) / (u - 1)))
    (hyu : yu = y + a * (u - 1)) (hyd : yd = y + a * (d - 1)) :
    C * ((1 - p) * (u - d) / (u - 1)) * max (-y) 0 - D * (p * (u - d) / (1 - d)) * max y 0 ≤
      p * (C * max (-yu) 0 - D * max yu 0) + (1 - p) * (C * max (-yd) 0 - D * max yd 0) := by
  have hu1 : 0 < u - 1 := by linarith
  have hd1 : 0 < 1 - d := by linarith
  have hq1 : 0 < 1 - p := by linarith
  -- bound 1
  have b1 : -(D * (p * (u - d) / (1 - d))) * y ≤
      p * (C * max (-yu) 0 - D * max yu 0) + (1 - p) * (C * max (-yd) 0 - D * max yd 0) := by
    set l2 := D * p * (u - 1) / ((1 - p) * (1 - d)) with hl2
    have hl2D : D ≤ l2 := by
      rw [hl2, le_div_iff₀ (by positivity)]; nlinarith
    have hl2C : l2 ≤ C := by
      rw [hl2, div_le_iff₀ (by positivity)]
      rw [mul_div_assoc', mul_div_assoc', div_le_div_iff₀ hd1 hu1] at hcd
      nlinarith
    have e1 := mul_le_mul_of_nonneg_left (h_ge C D D yu le_rfl hDC) hp0.le
    have e2 := mul_le_mul_of_nonneg_left (h_ge C D l2 yd hl2D hl2C) hq1.le
    have hid : p * (-D * yu) + (1 - p) * (-l2 * yd) = -(D * (p * (u - d) / (1 - d))) * y := by
      rw [hl2, hyu, hyd]; field_simp; ring
    linarith
  have b2 : -(C * ((1 - p) * (u - d) / (u - 1))) * y ≤
      p * (C * max (-yu) 0 - D * max yu 0) + (1 - p) * (C * max (-yd) 0 - D * max yd 0) := by
    set l1 := C * (1 - p) * (1 - d) / (p * (u - 1)) with hl1
    have hl1C : l1 ≤ C := by
      rw [hl1, div_le_iff₀ (by positivity)]; nlinarith
    have hl1D : D ≤ l1 := by
      rw [hl1, le_div_iff₀ (by positivity)]
      rw [mul_div_assoc', mul_div_assoc', div_le_div_iff₀ hd1 hu1] at hcd
      nlinarith
    have e1 := mul_le_mul_of_nonneg_left (h_ge C D l1 yu hl1D hl1C) hp0.le
    have e2 := mul_le_mul_of_nonneg_left (h_ge C D C yd hDC le_rfl) hq1.le
    have hid : p * (-l1 * yu) + (1 - p) * (-C * yd) = -(C * ((1 - p) * (u - d) / (u - 1))) * y := by
      rw [hl1, hyu, hyd]; field_simp; ring
    linarith
  rcases le_total y 0 with hy | hy
  · rw [max_eq_left (by linarith), max_eq_right hy]; linarith
  · rw [max_eq_right (by linarith), max_eq_left hy]; linarith

lemma step_eq (p u d C D y yu yd : ℝ) (hu : 1 < u) (hd : d < 1)
    (hyu : yu = y + max (y / (1 - u)) (y / (1 - d)) * (u - 1))
    (hyd : yd = y + max (y / (1 - u)) (y / (1 - d)) * (d - 1)) :
    p * (C * max (-yu) 0 - D * max yu 0) + (1 - p) * (C * max (-yd) 0 - D * max yd 0) =
      C * ((1 - p) * (u - d) / (u - 1)) * max (-y) 0 - D * (p * (u - d) / (1 - d)) * max y 0 := by
  have hu1 : 0 < u - 1 := by linarith
  have hd1 : 0 < 1 - d := by linarith
  have hu1' : 1 - u < 0 := by linarith
  have n1 : u - 1 ≠ 0 := hu1.ne'
  have n2 : 1 - d ≠ 0 := hd1.ne'
  have n3 : 1 - u ≠ 0 := hu1'.ne
  rcases le_total y 0 with hy | hy
  · have hm : max (y / (1 - u)) (y / (1 - d)) = y / (1 - u) := by
      apply max_eq_left
      have : y / (1 - d) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hy hd1.le
      have : 0 ≤ y / (1 - u) := div_nonneg_of_nonpos hy hu1'.le
      linarith
    rw [hm] at hyu hyd
    have e1 : yu = 0 := by rw [hyu]; field_simp; ring
    have e2 : yd = y * (u - d) / (u - 1) := by rw [hyd]; field_simp; ring
    have e3 : yd ≤ 0 := by
      rw [e2]; exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) hu1.le
    rw [e1, show max (-yd) 0 = -yd from max_eq_left (by linarith), max_eq_right e3,
      show max (-y) 0 = -y from max_eq_left (by linarith), max_eq_right hy, e2]
    simp; field_simp
  · have hm : max (y / (1 - u)) (y / (1 - d)) = y / (1 - d) := by
      apply max_eq_right
      have : 0 ≤ y / (1 - d) := div_nonneg hy hd1.le
      have : y / (1 - u) ≤ 0 := div_nonpos_of_nonneg_of_nonpos hy hu1'.le
      linarith
    rw [hm] at hyu hyd
    have e1 : yd = 0 := by rw [hyd]; field_simp; ring
    have e2 : yu = y * (u - d) / (1 - d) := by rw [hyu]; field_simp; ring
    have e3 : 0 ≤ yu := by rw [e2]; exact div_nonneg (by nlinarith) hd1.le
    rw [e1, show max (-yu) 0 = 0 from max_eq_right (by linarith), max_eq_left e3,
      show max (-y) 0 = 0 from max_eq_right (by linarith), max_eq_left hy, e2]
    simp; field_simp

lemma step_unbounded (p u d C D y r : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hu : 1 < u) (hd : d < 1)
    (hs : C * (1 - p) * (1 - d) < D * p * (u - 1)) :
    ∃ a : ℝ, p * (C * max (-(y + a * (u - 1))) 0 - D * max (y + a * (u - 1)) 0) +
      (1 - p) * (C * max (-(y + a * (d - 1))) 0 - D * max (y + a * (d - 1)) 0) < r := by
  have hu1 : 0 < u - 1 := by linarith
  have hd1 : 0 < 1 - d := by linarith
  set s := C * (1 - p) * (1 - d) - D * p * (u - 1) with hsdef
  have hs' : s < 0 := by rw [hsdef]; linarith
  set K := -(p * D * y) - (1 - p) * C * y with hK
  set a0 := |y| / (u - 1) + |y| / (1 - d) with ha0
  have hy1 : |y| / (u - 1) * (u - 1) = |y| := div_mul_cancel₀ _ hu1.ne'
  have hy2 : |y| / (1 - d) * (1 - d) = |y| := div_mul_cancel₀ _ hd1.ne'
  have hya := abs_nonneg y
  have hyb := le_abs_self y
  have hyc := neg_abs_le y
  have hq1 : 0 ≤ |y| / (u - 1) := by positivity
  have hq2 : 0 ≤ |y| / (1 - d) := by positivity
  set t := (|K| + |r| + 1) / (-s) with ht
  have htn : 0 ≤ t := div_nonneg (by positivity) (by linarith)
  have hts : t * s = -(|K| + |r| + 1) := by
    rw [ht, div_mul_eq_mul_div, div_eq_iff (by linarith)]; ring
  refine ⟨a0 + t, ?_⟩
  have hyu : 0 ≤ y + (a0 + t) * (u - 1) := by rw [ha0]; nlinarith
  have hyd : y + (a0 + t) * (d - 1) ≤ 0 := by rw [ha0]; nlinarith
  rw [max_eq_right (by linarith : -(y + (a0 + t) * (u - 1)) ≤ 0), max_eq_left hyu,
    max_eq_left (by linarith : 0 ≤ -(y + (a0 + t) * (d - 1))), max_eq_right hyd]
  have hval : p * (C * 0 - D * (y + (a0 + t) * (u - 1))) +
      (1 - p) * (C * -(y + (a0 + t) * (d - 1)) - D * 0) = K + a0 * s + t * s := by
    rw [hK, hsdef]; ring
  have ha0s : a0 * s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hs'.le
  rw [hval, hts]
  linarith [le_abs_self K, neg_abs_le r]


/-! ### Market-level dynamic programming -/

noncomputable def g (M : MeanRiskMarket Ω) (lam b : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  M.cSeq lam n * max (-(x + b)) 0 - M.dSeq lam n * max (x + b) 0

noncomputable def phi (M : MeanRiskMarket Ω) (lam b : ℝ) (X : ℝ) : ℝ :=
  ((1 - M.γ)⁻¹ + lam) * max (-(X + b)) 0 - lam * max (X + b) 0

noncomputable def fstar (M : MeanRiskMarket Ω) (b : ℝ) (x : ℝ) : ℝ :=
  max ((x + b) / (1 - M.u)) ((x + b) / (1 - M.d))

lemma fstar_meas (M : MeanRiskMarket Ω) (b : ℝ) : Measurable (fstar M b) := by
  unfold fstar; fun_prop

lemma q_eq (M : MeanRiskMarket Ω) : M.q = (1 - M.d) / (M.u - M.d) := rfl

lemma cSeq_succ (M : MeanRiskMarket Ω) (lam : ℝ) (n : ℕ) (hn : n < M.N) :
    M.cSeq lam n = M.cSeq lam (n + 1) * ((1 - M.p) * (M.u - M.d) / (M.u - 1)) := by
  have hu := M.hone_lt_u; have hd := M.hd_lt_one
  have h1 : (1 - M.p) / (1 - M.q) = (1 - M.p) * (M.u - M.d) / (M.u - 1) := by
    rw [q_eq]
    have : M.u - M.d ≠ 0 := by intro h; linarith
    have : M.u - 1 ≠ 0 := by intro h; linarith
    rw [show 1 - (1 - M.d) / (M.u - M.d) = (M.u - 1) / (M.u - M.d) by field_simp; ring]
    field_simp
  unfold MeanRiskMarket.cSeq
  rw [show M.N - n = M.N - (n + 1) + 1 by omega, pow_succ, h1]; ring

lemma dSeq_succ (M : MeanRiskMarket Ω) (lam : ℝ) (n : ℕ) (hn : n < M.N) :
    M.dSeq lam n = M.dSeq lam (n + 1) * (M.p * (M.u - M.d) / (1 - M.d)) := by
  have hu := M.hone_lt_u; have hd := M.hd_lt_one
  have h1 : M.p / M.q = M.p * (M.u - M.d) / (1 - M.d) := by
    rw [q_eq]
    have : M.u - M.d ≠ 0 := by intro h; linarith
    have : 1 - M.d ≠ 0 := by intro h; linarith
    field_simp
  unfold MeanRiskMarket.dSeq
  rw [show M.N - n = M.N - (n + 1) + 1 by omega, pow_succ, h1]; ring

lemma dSeq_nonneg (M : MeanRiskMarket Ω) (lam : ℝ) (hlam : 0 ≤ lam) (n : ℕ) :
    0 ≤ M.dSeq lam n := by
  have hu := M.hone_lt_u; have hd := M.hd_lt_one; have hp := M.hp_mem.1
  have hq : 0 < M.q := by rw [q_eq]; apply div_pos <;> linarith
  unfold MeanRiskMarket.dSeq; positivity

lemma g_N (M : MeanRiskMarket Ω) (lam b x : ℝ) : g M lam b M.N x = phi M lam b x := by
  unfold g phi MeanRiskMarket.cSeq MeanRiskMarket.dSeq
  simp only [Nat.sub_self, pow_zero, mul_one]; ring

lemma hpq_alg (M : MeanRiskMarket Ω) (hpq : M.q < M.p) :
    (1 - M.p) * (1 - M.d) ≤ M.p * (M.u - 1) := by
  have hu := M.hone_lt_u; have hd := M.hd_lt_one
  rw [q_eq, div_lt_iff₀ (by linarith)] at hpq
  nlinarith

lemma Ev_lower (M : MeanRiskMarket Ω) (lam b : ℝ) (hlam : 0 ≤ lam) (hpq : M.q < M.p)
    (π : ℕ → ℝ → ℝ) : ∀ (k n : ℕ) (x : ℝ), n + k = M.N →
    (∀ m, n ≤ m → m ≤ M.N → M.dSeq lam m ≤ M.cSeq lam m) →
    g M lam b n x ≤ Ev M π (phi M lam b) k n x
  | 0, n, x, hk, _ => by
      simp only [add_zero] at hk; subst hk; rw [g_N]; rfl
  | k + 1, n, x, hk, hcd => by
      have hn : n < M.N := by omega
      have hp := M.hp_mem
      have IH := fun y => Ev_lower M lam b hlam hpq π k (n + 1) y (by omega)
        (fun m h1 h2 => hcd m (by omega) h2)
      have hcdn := hcd n le_rfl hn.le
      rw [cSeq_succ M lam n hn, dSeq_succ M lam n hn] at hcdn
      have hDC := hcd (n + 1) (by omega) (by omega)
      have hst := step_lower M.p M.u M.d (M.cSeq lam (n + 1)) (M.dSeq lam (n + 1)) (x + b)
        (π n x) (x + π n x * (M.u - 1) + b) (x + π n x * (M.d - 1) + b) hp.1 hp.2 M.hone_lt_u
        M.hd_lt_one (hpq_alg M hpq) (dSeq_nonneg M lam hlam _) hDC hcdn (by ring) (by ring)
      have e1 := mul_le_mul_of_nonneg_left (IH (x + π n x * (M.u - 1))) hp.1.le
      have e2 := mul_le_mul_of_nonneg_left (IH (x + π n x * (M.d - 1))) (by linarith [hp.2] :
        (0:ℝ) ≤ 1 - M.p)
      have hg : g M lam b n x = M.cSeq lam (n + 1) * ((1 - M.p) * (M.u - M.d) / (M.u - 1)) *
          max (-(x + b)) 0 - M.dSeq lam (n + 1) * (M.p * (M.u - M.d) / (1 - M.d)) *
          max (x + b) 0 := by
        rw [g, cSeq_succ M lam n hn, dSeq_succ M lam n hn]
      simp only [Ev]
      simp only [g] at e1 e2
      linarith

lemma Ev_fstar (M : MeanRiskMarket Ω) (lam b : ℝ) (π : ℕ → ℝ → ℝ) :
    ∀ (k n : ℕ) (x : ℝ), n + k = M.N → (∀ m, n ≤ m → m < M.N → π m = fstar M b) →
    Ev M π (phi M lam b) k n x = g M lam b n x
  | 0, n, x, hk, _ => by
      simp only [add_zero] at hk; subst hk; rw [g_N]; rfl
  | k + 1, n, x, hk, hπ => by
      have hn : n < M.N := by omega
      have IH := fun y => Ev_fstar M lam b π k (n + 1) y (by omega)
        (fun m h1 h2 => hπ m (by omega) h2)
      simp only [Ev, IH, hπ n le_rfl hn]
      simp only [g]
      rw [cSeq_succ M lam n hn, dSeq_succ M lam n hn]
      exact step_eq M.p M.u M.d _ _ (x + b) _ _ M.hone_lt_u M.hd_lt_one
        (by simp only [fstar]; ring) (by simp only [fstar]; ring)

lemma Ev_zero_prefix (M : MeanRiskMarket Ω) (π : ℕ → ℝ → ℝ) (φ : ℝ → ℝ) (k : ℕ) :
    ∀ (j n : ℕ) (x : ℝ), (∀ i, n ≤ i → i < n + j → ∀ y, π i y = 0) →
    Ev M π φ (j + k) n x = Ev M π φ k (n + j) x
  | 0, n, x, _ => by simp
  | j + 1, n, x, hπ => by
      rw [show j + 1 + k = (j + k) + 1 by omega]
      simp only [Ev, hπ n le_rfl (by omega), zero_mul, add_zero]
      rw [Ev_zero_prefix M π φ k j (n + 1) x (fun i h1 h2 => hπ i (by omega) (by omega)),
        show n + 1 + j = n + (j + 1) by omega]
      ring

lemma val_eq (M : MeanRiskMarket Ω) (lam b : ℝ) (π : ℕ → ℝ → ℝ) (k n : ℕ) (hk : n + k ≤ M.N)
    (x : ℝ) :
    (((1 - M.γ)⁻¹ + lam) * ∫ ω, max (-(M.terminalWealth π k n x ω + b)) 0 ∂M.measIP -
      lam * ∫ ω, max (M.terminalWealth π k n x ω + b) 0 ∂M.measIP : EReal) =
      ((Ev M π (phi M lam b) k n x : ℝ) : EReal) := by
  have h1 := integral_eq_Ev M π (fun X => max (-(X + b)) 0) k n hk x
  have h2 := integral_eq_Ev M π (fun X => max (X + b) 0) k n hk x
  rw [h1, h2, show phi M lam b = fun X => ((1 - M.γ)⁻¹ + lam) * (fun X => max (-(X + b)) 0) X -
    lam * (fun X => max (X + b) 0) X from rfl, Ev_lin]
  norm_cast

end S100PLB

open MDPFinance.MeanVariance MeasureTheory ProbabilityTheory in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : MeanRiskMarket Ω)
    (hpq : M.q < M.p) (lam b : ℝ) (hlam : 0 ≤ lam) :
    (M.cSeq lam 0 ≥ M.dSeq lam 0 →
      (∀ n ≤ M.N, ∀ x : ℝ,
        M.VPlambdabFrom lam b n x = ((M.cSeq lam n * max (-(x + b)) 0) -
          M.dSeq lam n * max (x + b) 0 : EReal)) ∧
      (∃ πstar : ℕ → ℝ → ℝ, M.IsAdmissible 0 πstar ∧
        (∀ n < M.N, ∀ x : ℝ, πstar n x = max ((x + b) / (1 - M.u)) ((x + b) / (1 - M.d))) ∧
        M.IsOptimalPlambdab lam b πstar)) ∧
      (M.cSeq lam 0 < M.dSeq lam 0 → M.VPlambdab lam b = ⊥) := by
  have hp := M.hp_mem
  have hu := M.hone_lt_u
  have hd := M.hd_lt_one
  have hγ := M.hγ
  have hγpos : 0 < (1 - M.γ)⁻¹ := inv_pos.2 (by linarith [hγ.2])
  have hNcd : M.dSeq lam M.N < M.cSeq lam M.N := by
    simp only [MeanRiskMarket.cSeq, MeanRiskMarket.dSeq, Nat.sub_self, pow_zero, mul_one]
    linarith
  have hfs : M.IsAdmissible 0 (fun _ => S100PLB.fstar M b) :=
    fun _ _ _ => S100PLB.fstar_meas M b
  have hud : 0 < M.u - M.d := by linarith
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · have hall : ∀ m, m ≤ M.N → M.dSeq lam m ≤ M.cSeq lam m := by
      intro m
      induction m with
      | zero => intro _; exact h0
      | succ m ih =>
        intro hm
        have h := ih (by omega)
        rw [S100PLB.cSeq_succ M lam m (by omega), S100PLB.dSeq_succ M lam m (by omega)] at h
        have hD := S100PLB.dSeq_nonneg M lam hlam (m + 1)
        have hαβ : (1 - M.p) * (M.u - M.d) / (M.u - 1) ≤ M.p * (M.u - M.d) / (1 - M.d) := by
          rw [div_le_div_iff₀ (by linarith) (by linarith)]
          have := mul_le_mul_of_nonneg_left (S100PLB.hpq_alg M hpq) hud.le
          nlinarith
        have hα : 0 < (1 - M.p) * (M.u - M.d) / (M.u - 1) :=
          div_pos (mul_pos (by linarith [hp.2]) hud) (by linarith)
        by_contra hc
        push_neg at hc
        have h1 := mul_le_mul_of_nonneg_left hαβ hD
        have h2 := mul_lt_mul_of_pos_right hc hα
        linarith
    have hV : ∀ n ≤ M.N, ∀ x, M.VPlambdabFrom lam b n x =
        ((S100PLB.g M lam b n x : ℝ) : EReal) := by
      intro n hn x
      apply le_antisymm
      · refine (iInf₂_le (fun _ => S100PLB.fstar M b)
          (fun _ _ _ => S100PLB.fstar_meas M b)).trans (le_of_eq ?_)
        rw [S100PLB.val_eq M lam b _ (M.N - n) n (by omega) x,
          S100PLB.Ev_fstar M lam b _ (M.N - n) n x (by omega) (fun _ _ _ => rfl)]
      · refine le_iInf₂ fun π _ => ?_
        rw [S100PLB.val_eq M lam b _ (M.N - n) n (by omega) x]
        exact EReal.coe_le_coe_iff.2 (S100PLB.Ev_lower M lam b hlam hpq π (M.N - n) n x
          (by omega) (fun m _ h2 => hall m h2))
    refine ⟨fun n hn x => by rw [hV n hn x, S100PLB.g]; norm_cast,
      ⟨fun _ => S100PLB.fstar M b, hfs, fun n _ x => rfl, hfs, ?_⟩⟩
    have e : M.VPlambdab lam b = M.VPlambdabFrom lam b 0 M.x0 := rfl
    rw [e, hV 0 (Nat.zero_le _) M.x0, S100PLB.val_eq M lam b _ M.N 0 (by omega) M.x0,
      S100PLB.Ev_fstar M lam b _ M.N 0 M.x0 (by omega) (fun _ _ _ => rfl)]
  · classical
    have hex : ∃ j, M.dSeq lam j ≤ M.cSeq lam j := ⟨M.N, hNcd.le⟩
    have hj0spec : M.dSeq lam (Nat.find hex) ≤ M.cSeq lam (Nat.find hex) := Nat.find_spec hex
    have hj0N : Nat.find hex ≤ M.N := Nat.find_min' hex hNcd.le
    have hj0pos : Nat.find hex ≠ 0 := by
      intro h; rw [h] at hj0spec; linarith
    obtain ⟨m, hm1⟩ : ∃ m, m + 1 = Nat.find hex := ⟨Nat.find hex - 1, by omega⟩
    have hm : ¬ (M.dSeq lam m ≤ M.cSeq lam m) := Nat.find_min hex (by omega)
    have hmN : m < M.N := by omega
    rw [S100PLB.cSeq_succ M lam m hmN, S100PLB.dSeq_succ M lam m hmN] at hm
    push_neg at hm
    have hs : M.cSeq lam (m + 1) * (1 - M.p) * (1 - M.d) <
        M.dSeq lam (m + 1) * M.p * (M.u - 1) := by
      rw [mul_div_assoc', mul_div_assoc', div_lt_div_iff₀ (by linarith) (by linarith)] at hm
      by_contra hc
      push_neg at hc
      have := mul_le_mul_of_nonneg_left hc hud.le
      nlinarith
    rw [EReal.eq_bot_iff_forall_lt]
    intro r
    obtain ⟨a, ha⟩ := S100PLB.step_unbounded M.p M.u M.d (M.cSeq lam (m + 1))
      (M.dSeq lam (m + 1)) (M.x0 + b) r hp.1 hp.2 hu hd hs
    let π : ℕ → ℝ → ℝ := fun k =>
      if k < m then fun _ => 0 else if k = m then fun _ => a else S100PLB.fstar M b
    have hπ : M.IsAdmissible 0 π := by
      intro k _ _
      simp only [π]
      split_ifs
      · exact measurable_const
      · exact measurable_const
      · exact S100PLB.fstar_meas M b
    refine lt_of_le_of_lt (iInf₂_le π hπ) ?_
    rw [S100PLB.val_eq M lam b π M.N 0 (by omega) M.x0]
    refine EReal.coe_lt_coe_iff.2 (lt_of_eq_of_lt ?_ ha)
    have hz := S100PLB.Ev_zero_prefix M π (S100PLB.phi M lam b) (M.N - m) m 0 M.x0
      (fun i _ h2 _ => by simp only [π]; rw [if_pos (by omega)])
    rw [show m + (M.N - m) = M.N by omega, zero_add] at hz
    rw [hz, show M.N - m = (M.N - (m + 1)) + 1 by omega]
    simp only [S100PLB.Ev]
    have hπm : π m M.x0 = a := by simp [π]
    rw [hπm]
    have hf : ∀ y, S100PLB.Ev M π (S100PLB.phi M lam b) (M.N - (m + 1)) (m + 1) y =
        S100PLB.g M lam b (m + 1) y := fun y =>
      S100PLB.Ev_fstar M lam b π _ (m + 1) y (by omega) (fun i h1 _ => by
        simp only [π]; rw [if_neg (by omega), if_neg (by omega)])
    rw [hf, hf]
    simp only [S100PLB.g]
    rw [show M.x0 + a * (M.u - 1) + b = M.x0 + b + a * (M.u - 1) by ring,
      show M.x0 + a * (M.d - 1) + b = M.x0 + b + a * (M.d - 1) by ring]
