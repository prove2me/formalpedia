-- Prove2me | solution 1 for HubSpokePricing.Lagrangian.corollary_4_7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T18:52:15.979101+00:00
-- url     : https://prove2.me/submissions/b8dad0c6-70bb-4de9-9936-28ce94964ef0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MarkovChain
import Definitions.Def_HubSpokePricing_Lagrangian_Model
import Theorems.Thm_HubSpokePricing_Lagrangian_theorem_4_1
import Theorems.Thm_HubSpokePricing_Lagrangian_corollary_4_5
import Theorems.Thm_HubSpokePricing_Lagrangian_proposition_4_6
import Theorems.Thm_HubSpokePricing_Lagrangian_corollary_B_11

namespace HubSpokeC47Aux



lemma asymp (κ₁ κ₂ c rb om : ℝ) (hκ1 : 0 < κ₁) (hκ : κ₁ ≤ κ₂) (hc : 0 < c) (hrb : 0 < rb)
    (hom : 0 < om) :
    ∃ C N₀ : ℝ, ∀ n m : ℕ, N₀ ≤ (n : ℝ) → κ₁ * n ≤ (m : ℝ) → (m : ℝ) ≤ κ₂ * n →
      Real.sqrt ((1 + c) * ((m : ℝ) + n) * Real.log n) < m ∧
      rb * Real.sqrt ((1 + c) * ((m : ℝ) + n) * Real.log n) /
          ((m : ℝ) - Real.sqrt ((1 + c) * ((m : ℝ) + n) * Real.log n)) +
        (rb + om) * Real.exp (-((1 / (1 + c)) / 2) *
          (Real.sqrt ((1 + c) * ((m : ℝ) + n) * Real.log n) ^ 2 / ((m : ℝ) + n)))
        ≤ C * Real.sqrt (Real.log n / n) := by
  set A : ℝ := (1 + c) * (1 + κ₂) with hA
  have hκ2 : 0 < κ₂ := lt_of_lt_of_le hκ1 hκ
  have hApos : 0 < A := by positivity
  set ε : ℝ := κ₁ ^ 2 / (4 * A) with hε
  have hεpos : 0 < ε := by positivity
  refine ⟨2 * rb * Real.sqrt A / κ₁ + (rb + om), max 3 (4 / ε ^ 2), ?_⟩
  intro n m hN hm1 hm2
  have hn3 : (3 : ℝ) ≤ n := le_trans (le_max_left _ _) hN
  have hnε : 4 / ε ^ 2 ≤ (n : ℝ) := le_trans (le_max_right _ _) hN
  have hnpos : (0 : ℝ) < n := by linarith
  set L : ℝ := Real.log n with hL
  -- L ≥ 1
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le hnpos]
    have := Real.exp_one_lt_d9
    linarith
  have hL0 : 0 ≤ L := by linarith
  -- L ≤ ε n
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hLsq : L ≤ 2 * Real.sqrt n := by
    have h1 : Real.log (Real.sqrt n) ≤ Real.sqrt n - 1 := Real.log_le_sub_one_of_pos hsq
    have h2 : Real.log n = 2 * Real.log (Real.sqrt n) := by
      rw [← Real.log_rpow hsq]
      congr 1
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.sq_sqrt hnpos.le]
    rw [hL, h2]; linarith
  have hsqn : 2 / ε ≤ Real.sqrt n := by
    rw [Real.le_sqrt (by positivity) hnpos.le]
    calc (2 / ε) ^ 2 = 4 / ε ^ 2 := by field_simp; norm_num
      _ ≤ (n : ℝ) := hnε
  have hLε : L ≤ ε * n := by
    have : 2 * Real.sqrt n ≤ ε * n := by
      have h3 : (Real.sqrt n) ^ 2 = n := Real.sq_sqrt hnpos.le
      have h4 : 2 ≤ ε * Real.sqrt n := by
        rw [div_le_iff₀ hεpos] at hsqn; linarith
      nlinarith
    linarith
  have hmpos : (0 : ℝ) < m := by nlinarith
  set δ : ℝ := Real.sqrt ((1 + c) * ((m : ℝ) + n) * L) with hδ
  have hδ0 : 0 ≤ δ := Real.sqrt_nonneg _
  have hmn : (m : ℝ) + n ≤ (1 + κ₂) * n := by linarith
  have hmnpos : 0 < (m : ℝ) + n := by linarith
  have hδA : δ ≤ Real.sqrt (A * n * L) := by
    apply Real.sqrt_le_sqrt
    rw [hA]
    have : (1 + c) * ((m : ℝ) + n) ≤ (1 + c) * ((1 + κ₂) * n) :=
      mul_le_mul_of_nonneg_left hmn (by linarith)
    nlinarith
  have hAeq : Real.sqrt (A * n * L) = Real.sqrt A * n * Real.sqrt (L / n) := by
    have : A * n * L = (A * (n : ℝ) ^ 2) * (L / n) := by field_simp
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_mul hApos.le, Real.sqrt_sq hnpos.le]
  have hhalf : Real.sqrt (A * n * L) ≤ κ₁ * n / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    have : A * ε = κ₁ ^ 2 / 4 := by rw [hε]; field_simp
    have h5 : A * n * L ≤ A * n * (ε * n) := by
      apply mul_le_mul_of_nonneg_left hLε; positivity
    have h6 : A * n * (ε * n) = (κ₁ * n / 2) ^ 2 := by
      calc A * n * (ε * n) = (A * ε) * n ^ 2 := by ring
        _ = _ := by rw [this]; ring
    linarith
  have hδm2 : δ ≤ (m : ℝ) / 2 := by linarith
  refine ⟨by linarith, ?_⟩
  -- first term
  have hT1 : rb * δ / ((m : ℝ) - δ) ≤ 2 * rb * Real.sqrt A / κ₁ * Real.sqrt (L / n) := by
    have hmd : (m : ℝ) / 2 ≤ (m : ℝ) - δ := by linarith
    have hmdpos : 0 < (m : ℝ) - δ := by linarith
    have hs0 : 0 ≤ Real.sqrt (L / n) := Real.sqrt_nonneg _
    rw [div_le_iff₀ hmdpos]
    have e1 : δ ≤ Real.sqrt A * n * Real.sqrt (L / n) := hAeq ▸ hδA
    have e2 : 2 * rb * Real.sqrt A / κ₁ * Real.sqrt (L / n) * ((m : ℝ) - δ) ≥
        2 * rb * Real.sqrt A / κ₁ * Real.sqrt (L / n) * ((m : ℝ) / 2) := by
      apply mul_le_mul_of_nonneg_left hmd; positivity
    have e3 : 2 * rb * Real.sqrt A / κ₁ * Real.sqrt (L / n) * ((m : ℝ) / 2) ≥
        rb * (Real.sqrt A * n * Real.sqrt (L / n)) := by
      have : 2 * rb * Real.sqrt A / κ₁ * Real.sqrt (L / n) * ((m : ℝ) / 2) =
          rb * Real.sqrt A * Real.sqrt (L / n) * ((m : ℝ) / κ₁) := by field_simp
      rw [this]
      have hmk : (n : ℝ) ≤ (m : ℝ) / κ₁ := by rw [le_div_iff₀ hκ1]; linarith
      have : rb * (Real.sqrt A * n * Real.sqrt (L / n)) =
          rb * Real.sqrt A * Real.sqrt (L / n) * n := by ring
      rw [this]
      apply mul_le_mul_of_nonneg_left hmk; positivity
    have e4 : rb * δ ≤ rb * (Real.sqrt A * n * Real.sqrt (L / n)) :=
      mul_le_mul_of_nonneg_left e1 hrb.le
    linarith
  -- second term
  have hT2 : Real.exp (-((1 / (1 + c)) / 2) * (δ ^ 2 / ((m : ℝ) + n))) ≤ Real.sqrt (L / n) := by
    have hδsq : δ ^ 2 = (1 + c) * ((m : ℝ) + n) * L := Real.sq_sqrt (by positivity)
    have hexp : -((1 / (1 + c)) / 2) * (δ ^ 2 / ((m : ℝ) + n)) = -L / 2 := by
      rw [hδsq]; field_simp
    rw [hexp]
    have h6 : Real.exp (-L / 2) = Real.sqrt ((n : ℝ)⁻¹) := by
      rw [← Real.sqrt_sq (Real.exp_pos _).le, ← Real.exp_nat_mul]
      congr 1
      rw [show ((2 : ℕ) : ℝ) * (-L / 2) = -L by push_cast; ring, Real.exp_neg, hL,
        Real.exp_log hnpos]
    rw [h6]
    apply Real.sqrt_le_sqrt
    rw [inv_eq_one_div]
    exact div_le_div_of_nonneg_right hL1 hnpos.le
  have hrbom : 0 ≤ rb + om := by linarith
  have := mul_le_mul_of_nonneg_left hT2 hrbom
  calc rb * δ / ((m : ℝ) - δ) + (rb + om) * Real.exp (-((1 / (1 + c)) / 2) *
          (δ ^ 2 / ((m : ℝ) + n)))
      ≤ 2 * rb * Real.sqrt A / κ₁ * Real.sqrt (L / n) + (rb + om) * Real.sqrt (L / n) := by
        linarith
    _ = (2 * rb * Real.sqrt A / κ₁ + (rb + om)) * Real.sqrt (L / n) := by ring



open HubSpokePricing.Lagrangian Finset

abbrev E (m : ℕ) : Type := (Fin (m + 1) → ℝ) × (Fin (m + 1) → ℝ) × (Fin (m + 1) → ℝ)

def toSol {m : ℕ} (e : E m) : SpokeSol m := ⟨e.1, e.2.1, e.2.2⟩

lemma feas_zero (N : Network) (i : Fin N.n) :
    SpokeFeasible N i (toSol ((Pi.single 0 1, 0, 0) : E N.m)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [toSol]
    by_cases hx : x = 0
    · subst hx; simp
    · simp [Pi.single_apply, hx]
  · simp [toSol]
  · intro x; simp [toSol]
  · intro x; simp [toSol]
  · intro x; simp [toSol]
  · simp [toSol]
  · simp [toSol]

lemma obj_zero (N : Network) (hN : N.Standing) (lam : ℝ) (i : Fin N.n) :
    spokeObj N lam i (toSol ((Pi.single 0 1, 0, 0) : E N.m)) = 0 := by
  obtain ⟨_, _, _, _, _, _, hr⟩ := hN
  have h1 := (hr i).1.2.1
  have h2 := (hr i).2.2.1
  simp only [spokeObj, toSol]
  simp [h1, h2]
  right
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : x = 0
  · subst hx; simp
  · simp [Pi.single_apply, hx]

lemma feas_closed (N : Network) (i : Fin N.n) :
    IsClosed {e : E N.m | SpokeFeasible N i (toSol e)} := by
  simp only [SpokeFeasible, toSol, Set.setOf_and, Set.setOf_forall]
  refine IsClosed.inter (isClosed_iInter fun x => isClosed_le continuous_const (by fun_prop))
    (IsClosed.inter (isClosed_eq (by fun_prop) continuous_const)
    (IsClosed.inter (isClosed_iInter fun x => IsClosed.inter
        (isClosed_le continuous_const (by fun_prop)) (isClosed_le (by fun_prop) continuous_const))
    (IsClosed.inter (isClosed_iInter fun x => IsClosed.inter
        (isClosed_le continuous_const (by fun_prop)) (isClosed_le (by fun_prop) continuous_const))
    (IsClosed.inter (isClosed_iInter fun x => isClosed_eq (by fun_prop) (by fun_prop))
    (IsClosed.inter (isClosed_eq (by fun_prop) continuous_const)
      (isClosed_eq (by fun_prop) continuous_const))))))

lemma feas_sub (N : Network) (i : Fin N.n) :
    {e : E N.m | SpokeFeasible N i (toSol e)} ⊆ Set.Icc (0, 0, 0) (1, 1, 1) := by
  intro e he
  obtain ⟨hp0, hp1, hdo, hdi, -⟩ := he
  simp only [toSol] at hp0 hp1 hdo hdi
  refine ⟨⟨fun x => hp0 x, fun x => (hdo x).1, fun x => (hdi x).1⟩,
    ⟨fun x => ?_, fun x => (hdo x).2, fun x => (hdi x).2⟩⟩
  show e.1 x ≤ 1
  rw [← hp1]
  exact Finset.single_le_sum (fun y _ => hp0 y) (Finset.mem_univ x)

lemma feas_compact (N : Network) (i : Fin N.n) :
    IsCompact {e : E N.m | SpokeFeasible N i (toSol e)} :=
  (isCompact_Icc).of_isClosed_subset (feas_closed N i) (feas_sub N i)

lemma obj_contOn (N : Network) (hN : N.Standing) (lam : ℝ) (i : Fin N.n) :
    ContinuousOn (fun e : E N.m => spokeObj N lam i (toSol e))
      {e : E N.m | SpokeFeasible N i (toSol e)} := by
  obtain ⟨_, _, _, _, _, _, hr⟩ := hN
  have hcO : ContinuousOn (N.rOut i) (Set.Icc 0 1) := (hr i).1.2.2.2.1.continuousOn
  have hcI : ContinuousOn (N.rIn i) (Set.Icc 0 1) := (hr i).2.2.2.2.1.continuousOn
  simp only [spokeObj, toSol]
  apply ContinuousOn.sub
  · apply continuousOn_finset_sum
    intro x _
    apply ContinuousOn.mul (by fun_prop)
    apply ContinuousOn.add
    · apply ContinuousOn.mul continuousOn_const
      exact hcO.comp (by fun_prop) (fun e he => (he.2.2.1 x))
    · apply ContinuousOn.mul continuousOn_const
      exact hcI.comp (by fun_prop) (fun e he => (he.2.2.2.1 x))
  · exact Continuous.continuousOn (by fun_prop)

/-- Existence of an optimal solution of the spoke problem (6), with the maximality property. -/
lemma spoke_max (N : Network) (hN : N.Standing) (lam : ℝ) (i : Fin N.n) :
    ∃ s : SpokeSol N.m, SpokeOptimal N lam i s ∧
      ∀ s' : SpokeSol N.m, SpokeFeasible N i s' → spokeObj N lam i s' ≤ h N lam i := by
  obtain ⟨e, he, hmax⟩ := (feas_compact N i).exists_isMaxOn ⟨_, feas_zero N i⟩
    (obj_contOn N hN lam i)
  have hG : IsGreatest (spokeObj N lam i '' {s | SpokeFeasible N i s})
      (spokeObj N lam i (toSol e)) := by
    refine ⟨⟨toSol e, he, rfl⟩, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have : s = toSol (s.p, s.dOut, s.dIn) := rfl
    rw [this] at hs ⊢
    exact hmax hs
  have hh : h N lam i = spokeObj N lam i (toSol e) := hG.csSup_eq
  refine ⟨toSol e, ⟨he, hh.symm⟩, fun s' hs' => ?_⟩
  rw [hh]
  exact hG.2 ⟨s', hs', rfl⟩

lemma h_nonneg (N : Network) (hN : N.Standing) (lam : ℝ) (i : Fin N.n) : 0 ≤ h N lam i := by
  obtain ⟨s, -, hmax⟩ := spoke_max N hN lam i
  have := hmax _ (feas_zero N i)
  rwa [obj_zero N hN] at this

lemma mean_bounds (N : Network) (i : Fin N.n) (s : SpokeSol N.m) (hs : SpokeFeasible N i s) :
    0 ≤ ∑ x : Fin (N.m + 1), ((x : ℕ) : ℝ) * s.p x ∧
      ∑ x : Fin (N.m + 1), ((x : ℕ) : ℝ) * s.p x ≤ N.m := by
  obtain ⟨hp0, hp1, -⟩ := hs
  constructor
  · exact Finset.sum_nonneg fun x _ => mul_nonneg (Nat.cast_nonneg _) (hp0 x)
  · calc ∑ x : Fin (N.m + 1), ((x : ℕ) : ℝ) * s.p x ≤ ∑ x : Fin (N.m + 1), (N.m : ℝ) * s.p x := by
          apply Finset.sum_le_sum
          intro x _
          apply mul_le_mul_of_nonneg_right _ (hp0 x)
          exact_mod_cast Nat.lt_succ_iff.mp x.2
      _ = N.m := by rw [← Finset.mul_sum, hp1, mul_one]

lemma h_lip (N : Network) (hN : N.Standing) (i : Fin N.n) (a b : ℝ) :
    h N a i ≤ h N b i + (N.m : ℝ) * dist a b := by
  obtain ⟨s, ⟨hs, hsa⟩, -⟩ := spoke_max N hN a i
  obtain ⟨-, -, hmaxb⟩ := spoke_max N hN b i
  have hb := hmaxb s hs
  have hdiff : spokeObj N a i s = spokeObj N b i s +
      (b - a) * ∑ x : Fin (N.m + 1), ((x : ℕ) : ℝ) * s.p x := by
    simp only [spokeObj]; ring
  obtain ⟨hm0, hm1⟩ := mean_bounds N i s hs
  have : (b - a) * ∑ x : Fin (N.m + 1), ((x : ℕ) : ℝ) * s.p x ≤ (N.m : ℝ) * dist a b := by
    rw [Real.dist_eq]
    calc (b - a) * ∑ x : Fin (N.m + 1), ((x : ℕ) : ℝ) * s.p x
        ≤ |a - b| * ∑ x : Fin (N.m + 1), ((x : ℕ) : ℝ) * s.p x := by
          apply mul_le_mul_of_nonneg_right _ hm0
          rw [abs_sub_comm]; exact le_abs_self _
      _ ≤ |a - b| * N.m := mul_le_mul_of_nonneg_left hm1 (abs_nonneg _)
      _ = _ := by ring
  rw [← hsa]; linarith

lemma h_cont (N : Network) (hN : N.Standing) (i : Fin N.n) : Continuous (fun l => h N l i) :=
  (LipschitzWith.of_le_add_mul' (N.m : ℝ) (fun a b => h_lip N hN i a b)).continuous

/-- Existence of an optimal solution `λ*(δ)` of (11) for `0 ≤ δ < m`. -/
lemma dual_exists (N : Network) (hN : N.Standing) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδm : δ < N.m) :
    ∃ lam : ℝ, IsDualOpt N δ lam := by
  set F : ℝ → ℝ := fun l => Vbar N l - δ * l with hF
  have hFc : Continuous F := by
    simp only [hF, Vbar]
    have : Continuous (fun l => ∑ i, h N l i) := continuous_finset_sum _ fun i _ => h_cont N hN i
    fun_prop
  have hmd : 0 < (N.m : ℝ) - δ := by linarith
  set L : ℝ := F 0 / ((N.m : ℝ) - δ) with hL
  have hF0 : 0 ≤ F 0 := by
    simp only [hF, Vbar]; simp
    exact Finset.sum_nonneg fun i _ => h_nonneg N hN 0 i
  have hL0 : 0 ≤ L := div_nonneg hF0 hmd.le
  obtain ⟨l, hl, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := L)).exists_isMinOn
    ⟨0, ⟨le_rfl, hL0⟩⟩ hFc.continuousOn
  refine ⟨l, hl.1, fun l' hl' => ?_⟩
  change F l ≤ F l'
  by_cases h' : l' ≤ L
  · exact hmin ⟨hl', h'⟩
  · push_neg at h'
    have h1 : F l ≤ F 0 := hmin ⟨le_rfl, hL0⟩
    have h2 : ((N.m : ℝ) - δ) * L = F 0 := by rw [hL]; field_simp
    have h3 : ((N.m : ℝ) - δ) * L < ((N.m : ℝ) - δ) * l' := mul_lt_mul_of_pos_left h' hmd
    have h4 : 0 ≤ ∑ i, h N l' i := Finset.sum_nonneg fun i _ => h_nonneg N hN l' i
    have h5 : F l' = ((N.m : ℝ) - δ) * l' + ∑ i, h N l' i := by
      simp only [hF, Vbar]; ring
    linarith

end HubSpokeC47Aux

open HubSpokePricing.Lagrangian

theorem solution :
    (∀ N : Network, N.Standing → ∀ δ : ℝ, 0 ≤ δ → δ < N.m →
      (∃ lam : ℝ, IsDualOpt N δ lam) ∧
      (∀ lam : ℝ, 0 ≤ lam → ∀ i : Fin N.n, ∃ s : SpokeSol N.m, SpokeOptimal N lam i s) ∧
      (∀ lam : ℝ, 0 ≤ lam → ∀ sol : Fin N.n → SpokeSol N.m,
        (∀ i, SpokeOptimal N lam i (sol i)) →
        ∃ μ : OrigState N → ℝ, MarkovChain.IsStationary (origKernel N sol) μ)) ∧
    (∀ N : Network, N.Standing → ∀ c : ℝ, 0 < c → ∀ δ : ℝ, 0 ≤ δ → δ < N.m →
      ∀ lam : ℝ, IsDualOpt N δ lam →
      ∀ sol : Fin N.n → SpokeSol N.m, (∀ i, SpokeOptimal N lam i (sol i)) →
      (∀ i, spokeMean (sol i) ≤ c) →
      ∀ μ : OrigState N → ℝ, MarkovChain.IsStationary (origKernel N sol) μ →
      ∀ x0 : Fin N.n → ℕ, InX N x0 →
        Vpi N sol μ ≤ VOPT N x0 ∧ VOPT N x0 ≤ VRstar N ∧
        VRstar N ≤ Vpi N sol μ + N.rbar * δ / ((N.m : ℝ) - δ) +
          (N.rbar + N.omega) * Real.exp (-((1 / (1 + c)) / 2) * (δ ^ 2 / ((N.m : ℝ) + N.n)))) ∧
    (∀ κ₁ κ₂ c rb om : ℝ, 0 < κ₁ → κ₁ ≤ κ₂ → 0 < c → 0 < rb → 0 < om →
      ∃ C N₀ : ℝ, ∀ N : Network, N.Standing → N.rbar = rb → N.omega = om →
        N₀ ≤ (N.n : ℝ) → κ₁ * N.n ≤ (N.m : ℝ) → (N.m : ℝ) ≤ κ₂ * N.n →
        Real.sqrt ((1 + c) * ((N.m : ℝ) + N.n) * Real.log N.n) < N.m ∧
        ∀ lam : ℝ, IsDualOpt N (Real.sqrt ((1 + c) * ((N.m : ℝ) + N.n) * Real.log N.n)) lam →
        ∀ sol : Fin N.n → SpokeSol N.m, (∀ i, SpokeOptimal N lam i (sol i)) →
        (∀ i, spokeMean (sol i) ≤ c) →
        ∀ μ : OrigState N → ℝ, MarkovChain.IsStationary (origKernel N sol) μ →
        ∀ x0 : Fin N.n → ℕ, InX N x0 →
          VOPT N x0 - Vpi N sol μ ≤ C * Real.sqrt (Real.log N.n / N.n)) := by
  -- Part (1): Theorem 4.1 + Corollary 4.5 + Proposition 4.6
  have part1 : ∀ N : Network, N.Standing → ∀ c : ℝ, 0 < c → ∀ δ : ℝ, 0 ≤ δ → δ < N.m →
      ∀ lam : ℝ, IsDualOpt N δ lam →
      ∀ sol : Fin N.n → SpokeSol N.m, (∀ i, SpokeOptimal N lam i (sol i)) →
      (∀ i, spokeMean (sol i) ≤ c) →
      ∀ μ : OrigState N → ℝ, MarkovChain.IsStationary (origKernel N sol) μ →
      ∀ x0 : Fin N.n → ℕ, InX N x0 →
        Vpi N sol μ ≤ VOPT N x0 ∧ VOPT N x0 ≤ VRstar N ∧
        VRstar N ≤ Vpi N sol μ + N.rbar * δ / ((N.m : ℝ) - δ) +
          (N.rbar + N.omega) * Real.exp (-((1 / (1 + c)) / 2) * (δ ^ 2 / ((N.m : ℝ) + N.n))) := by
    intro N hN c hc δ hδ0 hδm lam hlam sol hsol hmean μ hμ x0 hx0
    obtain ⟨h1, h2, h3⟩ := theorem_4_1 N hN δ hδ0 hδm lam hlam sol hsol μ hμ x0 hx0
    have h4 := corollary_4_5 N hN δ hδ0 hδm lam hlam sol hsol μ hμ
    have h5 := proposition_4_6 N hN δ hδ0 hδm lam hlam sol hsol c hc hmean
    have hro : 0 ≤ N.rbar + N.omega := by
      obtain ⟨_, _, _, _, hr, ho, _⟩ := hN; linarith
    refine ⟨h1, h2, ?_⟩
    have := mul_le_mul_of_nonneg_left (h4.trans h5) hro
    linarith
  refine ⟨?_, part1, ?_⟩
  · -- Part (0): existence
    intro N hN δ hδ0 hδm
    refine ⟨HubSpokeC47Aux.dual_exists N hN δ hδ0 hδm, ?_, ?_⟩
    · intro lam _ i
      obtain ⟨s, hs, -⟩ := HubSpokeC47Aux.spoke_max N hN lam i
      exact ⟨s, hs⟩
    · intro lam hlam sol hsol
      exact (corollary_B_11 N hN lam hlam sol hsol).1.exists
  · -- Part (2): asymptotics
    intro κ₁ κ₂ c rb om hκ1 hκ hc hrb hom
    obtain ⟨C, N₀, hC⟩ := HubSpokeC47Aux.asymp κ₁ κ₂ c rb om hκ1 hκ hc hrb hom
    refine ⟨C, N₀, ?_⟩
    intro N hN hrbN homN hN₀ hm1 hm2
    obtain ⟨hδm, hbound⟩ := hC N.n N.m hN₀ hm1 hm2
    refine ⟨hδm, ?_⟩
    intro lam hlam sol hsol hmean μ hμ x0 hx0
    obtain ⟨-, h2, h3⟩ := part1 N hN c hc _ (Real.sqrt_nonneg _) hδm lam hlam sol hsol hmean
      μ hμ x0 hx0
    rw [hrbN, homN] at h3
    linarith
