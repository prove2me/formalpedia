-- Prove2me | solution 1 for HubSpokePricing.Lagrangian.proposition_4_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T19:13:08.152203+00:00
-- url     : https://prove2.me/submissions/1319d7d8-53ca-4904-a82c-5cf9e60de25b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MarkovChain
import Definitions.Def_HubSpokePricing_Lagrangian_Model
import Definitions.Def_HubSpokePricing_Lagrangian_Prob
import Theorems.Thm_HubSpokePricing_Lagrangian_lemma_A_12
import Theorems.Thm_HubSpokePricing_Lagrangian_proposition_B_9
import Theorems.Thm_HubSpokePricing_Lagrangian_proposition_3_4_perturbed

namespace HubSpoke46Aux

open HubSpokePricing.Lagrangian Finset

/-- law of `∑ xᵢ` under the product of the `ps i` restricted to `[0, M]` -/
noncomputable def Q (M : ℕ) : (n : ℕ) → (Fin n → ℕ → ℝ) → ℕ → ℝ := fun n ps k =>
  ∑ x : Fin n → Fin (M + 1), if ∑ i, (x i : ℕ) = k then ∏ i, ps i (x i) else 0

lemma Q_succ (M n : ℕ) (ps : Fin (n + 1) → ℕ → ℝ) (k : ℕ) :
    Q M (n + 1) ps k = ∑ a : Fin (M + 1),
      (if (a : ℕ) ≤ k then ps (Fin.last n) a * Q M n (fun i => ps i.castSucc) (k - a) else 0) := by
  unfold Q
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => Fin (M + 1))).sum_comp, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a _
  simp only [Fin.snocEquiv_apply, Fin.sum_univ_castSucc, Fin.prod_univ_castSucc, Fin.snoc_castSucc,
    Fin.snoc_last]
  split_ifs with hak
  · rw [mul_sum]
    apply sum_congr rfl
    intro x _
    by_cases h : ∑ i, (x i : ℕ) = k - a
    · rw [if_pos (by omega), if_pos h]; ring
    · rw [if_neg (by omega), if_neg h, mul_zero]
  · apply sum_eq_zero
    intro x _
    rw [if_neg (by omega)]

lemma sumLaw_eq_Q (M : ℕ) : ∀ (n : ℕ) (ps : Fin n → ℕ → ℝ), (∀ i k, M < k → ps i k = 0) →
    ∀ k, sumLaw n ps k = Q M n ps k
  | 0, ps, _, k => by
    simp only [sumLaw, Q, univ_eq_empty, sum_empty, prod_empty]
    rw [Fintype.sum_unique]
    by_cases hk : k = 0
    · subst hk; simp
    · rw [if_neg hk, if_neg (Ne.symm hk)]
  | n + 1, ps, hps, k => by
    rw [Q_succ]
    simp only [sumLaw, conv]
    have ih := sumLaw_eq_Q M n (fun i => ps i.castSucc) (fun i k hk => hps _ k hk)
    simp_rw [ih]
    -- reflect the convolution
    rw [← sum_range_reflect]
    set F : ℕ → ℝ := fun a => if a ≤ k then ps (Fin.last n) a *
      Q M n (fun i => ps i.castSucc) (k - a) else 0 with hF
    have hs1 : ∑ a ∈ range (k + 1), F a = ∑ a ∈ range (M + k + 1), F a := by
      apply sum_subset (by intro a ha; simp at ha ⊢; omega)
      intro a ha ha'
      simp at ha ha'
      simp only [hF]; rw [if_neg (by omega)]
    have hs2 : ∑ a ∈ range (M + 1), F a = ∑ a ∈ range (M + k + 1), F a := by
      apply sum_subset (by intro a ha; simp at ha ⊢; omega)
      intro a ha ha'
      simp at ha ha'
      simp only [hF]
      split_ifs
      · rw [hps _ a (by omega), zero_mul]
      · rfl
    have e1 : ∑ j ∈ range (k + 1), Q M n (fun i => ps i.castSucc) (k + 1 - 1 - j) *
        ps (Fin.last n) (k - (k + 1 - 1 - j)) = ∑ a ∈ range (k + 1), F a := by
      apply sum_congr rfl
      intro a ha
      simp at ha
      simp only [hF]
      rw [if_pos (by omega), show k + 1 - 1 - a = k - a by omega,
        show k - (k - a) = a by omega]
      ring
    rw [e1, hs1, ← hs2, ← Fin.sum_univ_eq_sum_range F]

lemma Q_zero_of_gt (M n : ℕ) (ps : Fin n → ℕ → ℝ) (k : ℕ) (hk : n * M < k) : Q M n ps k = 0 := by
  unfold Q
  apply sum_eq_zero
  intro x _
  rw [if_neg]
  intro h
  have : ∑ i, (x i : ℕ) ≤ ∑ _i : Fin n, M := sum_le_sum fun i _ => Nat.lt_succ_iff.mp (x i).2
  simp at this
  omega

lemma sum_eq_Q (M n : ℕ) (ps : Fin n → ℕ → ℝ) (g : ℕ → ℝ) :
    ∑ x : Fin n → Fin (M + 1), g (∑ i, (x i : ℕ)) * ∏ i, ps i (x i) =
      ∑ k ∈ range (n * M + 1), g k * Q M n ps k := by
  unfold Q
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  have hx : ∑ i, (x i : ℕ) ∈ range (n * M + 1) := by
    have : ∑ i, (x i : ℕ) ≤ ∑ _i : Fin n, M := sum_le_sum fun i _ => Nat.lt_succ_iff.mp (x i).2
    simp at this ⊢; omega
  rw [sum_eq_single (∑ i, (x i : ℕ))]
  · rw [if_pos rfl]
  · intro b _ hb; rw [if_neg (Ne.symm hb), mul_zero]
  · intro h; exact absurd hx h

lemma pN_zero {m : ℕ} (s : SpokeSol m) (k : ℕ) (hk : m < k) : s.pN k = 0 := by
  unfold SpokeSol.pN; rw [dif_neg (by omega)]

lemma pN_fin {m : ℕ} (s : SpokeSol m) (x : Fin (m + 1)) : s.pN x = s.p x := by
  unfold SpokeSol.pN; rw [dif_pos (Nat.lt_succ_iff.mp x.2)]

lemma pmfMean_pN {m : ℕ} (s : SpokeSol m) : pmfMean s.pN = spokeMean s := by
  unfold pmfMean spokeMean
  rw [tsum_eq_sum (s := range (m + 1))]
  · rw [← Fin.sum_univ_eq_sum_range (fun k => (k : ℝ) * s.pN k)]
    apply sum_congr rfl; intro x _; rw [pN_fin]
  · intro k hk; simp at hk; rw [pN_zero s k (by omega), mul_zero]

/-- `2 log u ≥ u − 1/u` for `0 < u ≤ 1`. -/
lemma two_log_ge (u : ℝ) (hu : 0 < u) (hu1 : u ≤ 1) : u - u⁻¹ ≤ 2 * Real.log u := by
  let f : ℝ → ℝ := fun v => 2 * Real.log v - v + v⁻¹
  have hderiv : ∀ v ∈ Set.Ioi (0 : ℝ), HasDerivAt f (2 * v⁻¹ - 1 - (v ^ 2)⁻¹) v := by
    intro v hv
    have hv' : v ≠ 0 := ne_of_gt hv
    have h1 := ((Real.hasDerivAt_log hv').const_mul 2).sub (hasDerivAt_id v)
    have h2 := h1.add (hasDerivAt_inv hv')
    exact h2.congr_deriv (by ring)
  have hanti : AntitoneOn f (Set.Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    · intro v hv; exact (hderiv v hv).continuousAt.continuousWithinAt
    · intro v hv; rw [interior_Ioi] at hv; exact (hderiv v hv).differentiableAt.differentiableWithinAt
    · intro v hv
      rw [interior_Ioi] at hv
      rw [(hderiv v hv).deriv]
      have hv0 : 0 < v := hv
      have : 2 * v⁻¹ - 1 - (v ^ 2)⁻¹ = -(1 - v⁻¹) ^ 2 := by field_simp; ring
      rw [this]; nlinarith [sq_nonneg (1 - v⁻¹)]
  have := hanti (show u ∈ Set.Ioi (0 : ℝ) from hu) (show (1 : ℝ) ∈ Set.Ioi (0 : ℝ) by norm_num) hu1
  simp only [f, Real.log_one, inv_one] at this
  linarith

/-- the analytic step of (43): `a ln(A/a) − d ≤ −d²/(2A)` for `A = a + d`, `a > 0`, `d ≥ 0`. -/
lemma spade (a d : ℝ) (ha : 0 < a) (hd : 0 ≤ d) :
    -d - a * Real.log (a / (a + d)) ≤ -(d ^ 2 / (2 * (a + d))) := by
  have hA : 0 < a + d := by linarith
  have hu : 0 < a / (a + d) := div_pos ha hA
  have hu1 : a / (a + d) ≤ 1 := by rw [div_le_one hA]; linarith
  have h := two_log_ge _ hu hu1
  have e : a / (a + d) - (a / (a + d))⁻¹ = (a ^ 2 - (a + d) ^ 2) / (a * (a + d)) := by
    field_simp
  rw [e] at h
  have h2 : a * ((a ^ 2 - (a + d) ^ 2) / (a * (a + d))) ≤ a * (2 * Real.log (a / (a + d))) :=
    mul_le_mul_of_nonneg_left h ha.le
  have e2 : a * ((a ^ 2 - (a + d) ^ 2) / (a * (a + d))) = (a ^ 2 - (a + d) ^ 2) / (a + d) := by
    field_simp
  rw [e2] at h2
  have e3 : -(d ^ 2 / (2 * (a + d))) = -d + ((a + d) ^ 2 - a ^ 2) / (2 * (a + d)) := by
    field_simp; ring
  rw [e3]
  have e4 : ((a + d) ^ 2 - a ^ 2) / (2 * (a + d)) = -((a ^ 2 - (a + d) ^ 2) / (a + d)) / 2 := by
    field_simp; ring
  rw [e4]
  linarith

end HubSpoke46Aux

open HubSpokePricing.Lagrangian Finset HubSpoke46Aux

theorem solution (N : Network) (hN : N.Standing) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδm : δ < N.m)
    (lam : ℝ) (hlam : IsDualOpt N δ lam)
    (sol : Fin N.n → SpokeSol N.m) (hsol : ∀ i, SpokeOptimal N lam i (sol i))
    (c : ℝ) (hc : 0 < c) (hmean : ∀ i, spokeMean (sol i) ≤ c) :
    relaxDepletionProb N sol ≤
      Real.exp (-((1 / (1 + c)) / 2) * (δ ^ 2 / ((N.m : ℝ) + N.n))) := by
  set ps : Fin N.n → ℕ → ℝ := fun i => (sol i).pN with hps
  have hps0 : ∀ i k, N.m < k → ps i k = 0 := fun i k hk => pN_zero _ k hk
  have hlc : ∀ i, IsLogConcave (ps i) := fun i =>
    proposition_B_9 N hN lam hlam.1 i (sol i) (hsol i)
  have hmeanp : ∀ i, pmfMean (ps i) = spokeMean (sol i) := fun i => pmfMean_pN _
  set μ : ℝ := ∑ i, spokeMean (sol i) with hμ
  have hμ' : ∑ i, pmfMean (ps i) = μ := by rw [hμ]; exact sum_congr rfl fun i _ => hmeanp i
  obtain ⟨hKKT, -⟩ := proposition_3_4_perturbed N hN δ hδ0 hδm lam hlam sol hsol
  have hspm0 : ∀ i, 0 ≤ spokeMean (sol i) := fun i => by
    rw [← hmeanp]; exact tsum_nonneg fun k => mul_nonneg (Nat.cast_nonneg _) ((hlc i).1 k)
  have hμ0 : 0 ≤ μ := sum_nonneg fun i _ => hspm0 i
  have hn1 : (1 : ℝ) ≤ N.n := by exact_mod_cast hN.1
  have hm0 : (0 : ℝ) < N.m := lt_of_le_of_lt hδ0 hδm
  -- the depletion probability as a tail of the convolution law
  have hdep : relaxDepletionProb N sol =
      ∑' k : ℕ, (if (N.m : ℝ) ≤ (k : ℝ) then sumLaw N.n ps k else 0) := by
    unfold relaxDepletionProb prodLaw
    have h1 := sum_eq_Q N.m N.n ps (fun k => if N.m ≤ k then (1 : ℝ) else 0)
    have h1' : ∑ x : RelaxState N, (if N.m ≤ ∑ i, ((x i : ℕ)) then ∏ i, (sol i).p (x i) else 0) =
        ∑ x : Fin N.n → Fin (N.m + 1), (if N.m ≤ ∑ i, (x i : ℕ) then (1 : ℝ) else 0) *
          ∏ i, ps i (x i) := by
      apply sum_congr rfl; intro x _
      simp only [hps, pN_fin]
      split_ifs <;> simp
    rw [h1', h1, tsum_eq_sum (s := range (N.n * N.m + 1))]
    · apply sum_congr rfl; intro k _
      rw [sumLaw_eq_Q N.m N.n ps hps0 k]
      by_cases h : N.m ≤ k
      · have h' : (N.m : ℝ) ≤ k := by exact_mod_cast h
        simp [h, h']
      · have h' : ¬ (N.m : ℝ) ≤ k := by exact_mod_cast h
        simp [h, h']
    · intro k hk
      simp at hk
      rw [sumLaw_eq_Q N.m N.n ps hps0 k, Q_zero_of_gt _ _ _ _ (by omega)]
      simp
  rw [hdep]
  rcases hμ0.lt_or_eq with hμp | hμz
  · -- apply Lemma A.12 with `λ = m / μ`
    set L : ℝ := (N.m : ℝ) / μ with hL
    have hLμ : L * μ = N.m := by rw [hL]; field_simp
    have hL1 : 1 ≤ L := by rw [hL, le_div_iff₀ hμp]; linarith
    have hA := lemma_A_12 N.n ps hlc c hc (fun i => by rw [hmeanp]; exact hmean i) L hL1
    rw [hμ', hLμ] at hA
    refine hA.trans (Real.exp_le_exp.2 ?_)
    -- exponent comparison
    have hsp := spade ((N.n : ℝ) + μ) ((N.m : ℝ) - μ) (by linarith) (by linarith)
    have e1 : (N.n : ℝ) + μ + ((N.m : ℝ) - μ) = (N.m : ℝ) + N.n := by ring
    rw [e1] at hsp
    have e2 : 1 - ((N.m : ℝ) - μ) / ((N.m : ℝ) + N.n) = ((N.n : ℝ) + μ) / ((N.m : ℝ) + N.n) := by
      field_simp; ring
    have e3 : (L - 1) * μ = (N.m : ℝ) - μ := by linear_combination hLμ
    rw [e3, e2]
    have hb : 0 < 1 / (1 + c) := by positivity
    have hmn : 0 < (N.m : ℝ) + N.n := by linarith
    have hd2 : δ ^ 2 ≤ ((N.m : ℝ) - μ) ^ 2 := by
      have : δ ≤ (N.m : ℝ) - μ := by linarith
      nlinarith
    have hfin : -(((N.m : ℝ) - μ) ^ 2 / (2 * ((N.m : ℝ) + N.n))) ≤
        -(δ ^ 2 / (2 * ((N.m : ℝ) + N.n))) := by
      apply neg_le_neg; apply div_le_div_of_nonneg_right hd2; linarith
    have key : -((N.m : ℝ) - μ) - ((N.n : ℝ) + μ) *
        Real.log (((N.n : ℝ) + μ) / ((N.m : ℝ) + N.n)) ≤ -(δ ^ 2 / (2 * ((N.m : ℝ) + N.n))) :=
      hsp.trans hfin
    have e4 : -((N.m : ℝ) - μ) / (1 + c) - ((N.n : ℝ) + μ) / (1 + c) *
        Real.log (((N.n : ℝ) + μ) / ((N.m : ℝ) + N.n)) =
        (1 / (1 + c)) * (-((N.m : ℝ) - μ) - ((N.n : ℝ) + μ) *
          Real.log (((N.n : ℝ) + μ) / ((N.m : ℝ) + N.n))) := by ring
    have e5 : -((1 / (1 + c)) / 2) * (δ ^ 2 / ((N.m : ℝ) + N.n)) =
        (1 / (1 + c)) * (-(δ ^ 2 / (2 * ((N.m : ℝ) + N.n)))) := by
      field_simp
    rw [e4, e5]
    exact mul_le_mul_of_nonneg_left key hb.le
  · -- `μ = 0`: every spoke is empty almost surely, so the tail `{k ≥ m}` has probability `0`
    have hall : ∀ i, spokeMean (sol i) = 0 := by
      intro i
      have := (sum_eq_zero_iff_of_nonneg (fun i _ => hspm0 i)).1 hμz.symm i (mem_univ i)
      exact this
    have hz : ∀ i k, 1 ≤ k → ps i k = 0 := by
      intro i k hk
      by_cases hkm : k ≤ N.m
      · have hsm := hall i
        unfold spokeMean at hsm
        have hterm := (sum_eq_zero_iff_of_nonneg (fun x _ => mul_nonneg (Nat.cast_nonneg _)
          ((hsol i).1.1 x))).1 hsm ⟨k, by omega⟩ (mem_univ _)
        simp only [hps]
        rw [pN_fin (sol i) ⟨k, by omega⟩] at *
        rcases mul_eq_zero.1 hterm with h | h
        · simp at h; omega
        · exact h
      · exact pN_zero _ k (by omega)
    have hzero : ∀ k, 1 ≤ k → sumLaw N.n ps k = 0 := by
      intro k hk
      rw [sumLaw_eq_Q N.m N.n ps hps0 k]
      unfold Q
      apply sum_eq_zero
      intro x _
      split_ifs with hx
      · obtain ⟨i, hi⟩ : ∃ i, 1 ≤ (x i : ℕ) := by
          by_contra hcon
          push_neg at hcon
          have : ∑ i, (x i : ℕ) = 0 := sum_eq_zero fun i _ => by have := hcon i; omega
          omega
        exact prod_eq_zero (mem_univ i) (hz i _ hi)
      · rfl
    have hfun : ∀ k : ℕ, (if (N.m : ℝ) ≤ (k : ℝ) then sumLaw N.n ps k else 0) = 0 := by
      intro k
      split_ifs with h
      · apply hzero
        have h1 : (1 : ℝ) ≤ N.m := by
          have : 1 ≤ N.m := by
            rcases Nat.eq_zero_or_pos N.m with h0 | h0
            · rw [h0] at hm0; simp at hm0
            · exact h0
          exact_mod_cast this
        have : (1 : ℝ) ≤ k := by linarith
        exact_mod_cast this
      · rfl
    have : ∑' k : ℕ, (if (N.m : ℝ) ≤ (k : ℝ) then sumLaw N.n ps k else 0) = 0 := by
      simp only [hfun, tsum_zero]
    rw [this]; exact (Real.exp_pos _).le
