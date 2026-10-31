-- Prove2me | solution 1 for LargeCongestion.Poisson.lemma_1_eq_21_corrected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T09:45:54.71253+00:00
-- url     : https://prove2.me/submissions/4cf881f0-49c7-4d2f-8154-51b486e6cd0f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_LargeCongestion_Poisson_PoissonCalculus
import Definitions.Def_LargeCongestion_Poisson_Game
import Theorems.Thm_LargeCongestion_Poisson_theorem_9_b
import Theorems.Thm_LargeCongestion_Poisson_lemma_1_smooth

open MeasureTheory ProbabilityTheory LargeCongestion.Poisson

namespace LCPEq21Aux

/-! ### Generic finite-sum lemmas -/

/-- Splitting `ι → Bool` into the coordinates satisfying `P` and the others, when the remaining
coordinates do not influence the integrand on the support of the product weight. -/
lemma split_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (P : ι → Prop) [DecidablePred P]
    (W : ι → Bool → ℝ) (hW : ∀ j, W j true + W j false = 1) (K : (ι → Bool) → ℝ)
    (L : ({j // P j} → Bool) → ℝ)
    (hK : ∀ b : ι → Bool, (∏ j, W j (b j)) ≠ 0 → K b = L (fun j => b j)) :
    ∑ b : ι → Bool, (∏ j, W j (b j)) * K b =
      ∑ c : {j // P j} → Bool, (∏ j : {j // P j}, W j (c j)) * L c := by
  set e := Equiv.piEquivPiSubtypeProd P (fun _ => Bool)
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have hprod : ∀ d : {j // ¬ P j} → Bool,
      (∏ j, W j (e.symm (c, d) j)) = (∏ j : {j // P j}, W j (c j)) * ∏ j : {j // ¬ P j}, W j (d j) := by
    intro d
    rw [← Fintype.prod_subtype_mul_prod_subtype P]
    congr 1
    · refine Finset.prod_congr rfl (fun j _ => ?_)
      simp [e, Equiv.piEquivPiSubtypeProd, j.2]
    · refine Finset.prod_congr rfl (fun j _ => ?_)
      simp [e, Equiv.piEquivPiSubtypeProd, j.2]
  have hterm : ∀ d : {j // ¬ P j} → Bool,
      (∏ j, W j (e.symm (c, d) j)) * K (e.symm (c, d)) =
        ((∏ j : {j // P j}, W j (c j)) * L c) * ∏ j : {j // ¬ P j}, W j (d j) := by
    intro d
    by_cases h0 : (∏ j, W j (e.symm (c, d) j)) = 0
    · rw [h0, zero_mul]
      rw [hprod d] at h0
      rcases mul_eq_zero.1 h0 with h | h <;> simp [h]
    · rw [hK _ h0, hprod d]
      have : (fun j : {j // P j} => e.symm (c, d) j) = c := by
        funext j; simp [e, Equiv.piEquivPiSubtypeProd, j.2]
      rw [this]; ring
  simp_rw [hterm, ← Finset.mul_sum]
  rw [← Fintype.prod_sum (fun (j : {j // ¬ P j}) (b : Bool) => W j b)]
  simp [Fintype.sum_bool, hW]

/-- Reindexing a Bernoulli-sum expectation along an equivalence. -/
lemma reindex {κ : Type*} [Fintype κ] [DecidableEq κ] {n : ℕ} (eJ : Fin n ≃ κ) (p : κ → ℝ)
    (h : ℕ → ℝ) :
    ∑ c : κ → Bool, (∏ j, (if c j then p j else 1 - p j)) *
        h (∑ j, if c j then 1 else 0) =
      bernoulliSumMean (fun k => p (eJ k)) h := by
  unfold bernoulliSumMean bernoulliWeight successCount
  symm
  refine Fintype.sum_equiv (Equiv.arrowCongr eJ (Equiv.refl Bool)) _ _ (fun ω => ?_)
  have h1 : (∏ i, if ω i then p (eJ i) else 1 - p (eJ i)) =
      ∏ j, if (Equiv.arrowCongr eJ (Equiv.refl Bool) ω) j then p j else 1 - p j := by
    refine Fintype.prod_equiv eJ _ _ (fun k => ?_)
    simp [Equiv.arrowCongr_apply]
  have h2 : (∑ i, if ω i then 1 else 0) =
      ∑ j, if (Equiv.arrowCongr eJ (Equiv.refl Bool) ω) j then 1 else 0 := by
    refine Fintype.sum_equiv eJ _ _ (fun k => ?_)
    simp [Equiv.arrowCongr_apply]
  rw [h1, h2]

/-! ### Product-space expectations -/

variable {E T : Type*} [Fintype E] [DecidableEq E] [Fintype T] [DecidableEq T]

lemma sum_all_sigma (S : T → Finset (Finset E)) {N : ℕ} (τ : Fin N → T)
    (σ : Fin N → Finset E → ℝ) (hσ : IsMixedProfile S τ σ) (j : Fin N) (g : Finset E → ℝ) :
    ∑ s : Finset E, σ j s * g s = ∑ s ∈ S (τ j), σ j s * g s := by
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro s _ hs
  rw [hσ.2.1 j s hs, zero_mul]

lemma sum_sigma_one (S : T → Finset (Finset E)) {N : ℕ} (τ : Fin N → T)
    (σ : Fin N → Finset E → ℝ) (hσ : IsMixedProfile S τ σ) (j : Fin N) :
    ∑ s : Finset E, σ j s = 1 := by
  have h := sum_all_sigma S τ σ hσ j (fun _ => 1)
  simp only [mul_one] at h
  rw [h, hσ.2.2 j]

lemma sum_sigma_mem (S : T → Finset (Finset E)) {N : ℕ} (τ : Fin N → T)
    (σ : Fin N → Finset E → ℝ) (hσ : IsMixedProfile S τ σ) (j : Fin N) (e : E) :
    ∑ s : Finset E, σ j s * (if e ∈ s then 1 else 0) = sigmaE S τ σ j e := by
  rw [sum_all_sigma S τ σ hσ j, sigmaE]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  split_ifs <;> simp

lemma sigmaE_mem (S : T → Finset (Finset E)) {N : ℕ} (τ : Fin N → T)
    (σ : Fin N → Finset E → ℝ) (hσ : IsMixedProfile S τ σ) (i : Fin N) (e : E) :
    0 ≤ sigmaE S τ σ i e ∧ sigmaE S τ σ i e ≤ 1 := by
  unfold sigmaE
  constructor
  · exact Finset.sum_nonneg (fun s _ => by split_ifs; exact hσ.1 i s; exact le_rfl)
  · rw [← hσ.2.2 i]
    exact Finset.sum_le_sum (fun s _ => by split_ifs; exact le_rfl; exact hσ.1 i s)

/-- The marginal law of player `j`'s indicator `U_{j,e}`. -/
lemma marg (S : T → Finset (Finset E)) {N : ℕ} (τ : Fin N → T) (u : Fin N → ℝ)
    (σ : Fin N → Finset E → ℝ) (hσ : IsMixedProfile S τ σ) (j : Fin N) (e : E) (b : Bool) :
    ∑ a ∈ (Finset.univ : Finset (Bool × Finset E)).filter
        (fun a => decide (a.1 = true ∧ e ∈ a.2) = b),
      (if a.1 then u j else 1 - u j) * σ j a.2 =
    if b then u j * sigmaE S τ σ j e else 1 - u j * sigmaE S τ σ j e := by
  rw [Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  have hm := sum_sigma_mem S τ σ hσ j e
  have h1 := sum_sigma_one S τ σ hσ j
  cases b
  · simp only [if_true, true_and, Bool.false_eq_true, false_and, decide_false, if_false]
    have e1 : ∀ s : Finset E, (if decide (e ∈ s) = false then u j * σ j s else 0) =
        u j * σ j s - u j * (σ j s * (if e ∈ s then 1 else 0)) := by
      intro s; by_cases hs : e ∈ s <;> simp [hs]
    simp only [e1, Finset.sum_sub_distrib, ← Finset.mul_sum, hm, h1]
    simp
  · simp only [if_true, true_and, Bool.false_eq_true, false_and, decide_false, if_false,
      Finset.sum_const_zero, add_zero]
    have e1 : ∀ s : Finset E, (if decide (e ∈ s) = true then u j * σ j s else 0) =
        u j * (σ j s * (if e ∈ s then 1 else 0)) := by
      intro s; by_cases hs : e ∈ s <;> simp [hs]
    simp only [e1, ← Finset.mul_sum, hm]

/-- The expectation of a function of the indicator vector `(U_{j,e})_j`. -/
lemma expect_bool (S : T → Finset (Finset E)) {N : ℕ} (τ : Fin N → T) (u : Fin N → ℝ)
    (σ : Fin N → Finset E → ℝ) (hσ : IsMixedProfile S τ σ) (e : E)
    (F : (Fin N → Bool) → ℝ) :
    expect u σ (fun ω => F (fun j => decide ((ω j).1 = true ∧ e ∈ (ω j).2))) =
      ∑ b : Fin N → Bool, (∏ j, if b j then u j * sigmaE S τ σ j e
        else 1 - u j * sigmaE S τ σ j e) * F b := by
  unfold expect
  set β : Outcome E N → (Fin N → Bool) :=
    fun ω j => decide ((ω j).1 = true ∧ e ∈ (ω j).2) with hβ
  rw [← Finset.sum_fiberwise Finset.univ β]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have hc : ∀ ω ∈ Finset.univ.filter (fun ω => β ω = b),
      weight u σ ω * F (β ω) = weight u σ ω * F b := by
    intro ω hω
    rw [(Finset.mem_filter.1 hω).2]
  rw [Finset.sum_congr rfl hc, ← Finset.sum_mul]
  congr 1
  have hset : Finset.univ.filter (fun ω => β ω = b) =
      Fintype.piFinset (fun j => (Finset.univ : Finset (Bool × Finset E)).filter
        (fun a => decide (a.1 = true ∧ e ∈ a.2) = b j)) := by
    ext ω
    simp [Fintype.mem_piFinset, hβ, funext_iff]
  rw [hset]
  unfold weight
  rw [← Finset.prod_congr rfl (fun j _ => marg S τ u σ hσ j e (b j)), Finset.prod_univ_sum]

lemma expect_add {N : ℕ} (u : Fin N → ℝ) (σ : Fin N → Finset E → ℝ)
    {ι : Type*} (s : Finset ι) (f : ι → Outcome E N → ℝ) :
    expect u σ (fun ω => ∑ k ∈ s, f k ω) = ∑ k ∈ s, expect u σ (f k) := by
  unfold expect
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

lemma sum_weight_one (S : T → Finset (Finset E)) {N : ℕ} (τ : Fin N → T) (u : Fin N → ℝ)
    (σ : Fin N → Finset E → ℝ) (hσ : IsMixedProfile S τ σ) (j : Fin N) :
    ∑ p : Bool × Finset E, (if p.1 then u j else 1 - u j) * σ j p.2 = 1 := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [if_true, Bool.false_eq_true, if_false]
  rw [← Finset.mul_sum, ← Finset.mul_sum, sum_sigma_one S τ σ hσ j]
  ring

lemma expect_single (S : T → Finset (Finset E)) {N : ℕ} (τ : Fin N → T) (u : Fin N → ℝ)
    (σ : Fin N → Finset E → ℝ) (hσ : IsMixedProfile S τ σ) (i : Fin N)
    (g : Bool × Finset E → ℝ) :
    expect u σ (fun ω => g (ω i)) =
      ∑ p : Bool × Finset E, ((if p.1 then u i else 1 - u i) * σ i p.2) * g p := by
  set w : Fin N → Bool × Finset E → ℝ := fun j p => (if p.1 then u j else 1 - u j) * σ j p.2
    with hw
  have key : ∀ ω : Outcome E N,
      weight u σ ω * g (ω i) = ∏ j, (w j (ω j) * if j = i then g (ω j) else 1) := by
    intro ω
    rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq']
    rfl
  unfold expect
  simp_rw [key]
  rw [← Fintype.prod_sum (fun j p => w j p * if j = i then g p else 1)]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  rw [Finset.prod_eq_one]
  · simp [w]
  · intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp only [hji, if_false, mul_one]
    exact sum_weight_one S τ u σ hσ j

lemma expect_use (S : T → Finset (Finset E)) {N : ℕ} (τ : Fin N → T) (u : Fin N → ℝ)
    (σ : Fin N → Finset E → ℝ) (hσ : IsMixedProfile S τ σ) (e : E) (i : Fin N) :
    expect u σ (fun ω => (useIndicator i e ω : ℝ)) = u i * sigmaE S τ σ i e := by
  have := expect_single S τ u σ hσ i
    (fun p => ((if p.1 = true ∧ e ∈ p.2 then 1 else 0 : ℕ) : ℝ))
  have h2 : (fun ω : Outcome E N => ((useIndicator i e ω : ℕ) : ℝ)) =
      fun ω => ((if (ω i).1 = true ∧ e ∈ (ω i).2 then 1 else 0 : ℕ) : ℝ) := rfl
  rw [h2, this, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [if_true, true_and, Bool.false_eq_true, false_and, if_false, Nat.cast_zero,
    mul_zero, Finset.sum_const_zero, add_zero]
  rw [← sum_sigma_mem S τ σ hσ i e, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  split_ifs <;> simp

lemma pmf_le (x d : ℝ) (hx : 0 ≤ x) (hxd : x ≤ d) (k : ℕ) :
    poissonPmf x k ≤ Real.exp (d - x) * poissonPmf d k := by
  rw [poissonPmf_eq hx, poissonPmf_eq (hx.trans hxd)]
  have hk : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have : Real.exp (d - x) * (Real.exp (-d) * d ^ k / k.factorial) =
      Real.exp (-x) * d ^ k / k.factorial := by
    rw [← mul_div_assoc, ← mul_assoc, ← Real.exp_add]; ring_nf
  rw [this]
  apply div_le_div_of_nonneg_right _ hk.le
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxd k) (Real.exp_pos _).le

lemma poissonMean_zero (g : ℕ → ℝ) : poissonMean g 0 = g 0 := by
  unfold poissonMean
  rw [tsum_eq_single 0]
  · rw [poissonPmf_eq le_rfl]; simp
  · intro k hk
    rw [poissonPmf_eq le_rfl, zero_pow hk]; simp

end LCPEq21Aux

open LCPEq21Aux in
theorem solution {E T : Type*} [Fintype E] [DecidableEq E] [Fintype T]
    [DecidableEq T] (S : T → Finset (Finset E)) (c : E → ℕ → ℝ) (hc : IsCostFamily c)
    (ν dmax : ℝ) (hd : 0 < dmax) (hM : MomentBound c ν dmax) {N : ℕ} (τ : Fin N → T)
    (u : Fin N → ℝ) (hu : IsBernoulliGame u) (σ : Fin N → Finset E → ℝ)
    (hσ : IsMixedProfile S τ σ) (htot : ∑ i, u i ≤ dmax) (hu1 : maxU u < 1)
    (i : Fin N) (e : E) :
    |expect u σ (fun ω => (othersLoadRV i e ω : ℝ)) - expect u σ (fun ω => (loadRV e ω : ℝ))| =
        expect u σ (fun ω => (useIndicator i e ω : ℝ)) ∧
      expect u σ (fun ω => (useIndicator i e ω : ℝ)) ≤ maxU u ∧
      |expect u σ (fun ω => c e (1 + othersLoadRV i e ω)) -
          cBreve c e (expect u σ (fun ω => (loadRV e ω : ℝ)))| ≤ LamCorr c ν dmax (maxU u) := by
  -- participation-use probabilities `p_j = u_j σ_{j,e}`
  set p : Fin N → ℝ := fun j => u j * sigmaE S τ σ j e with hp
  have hp0 : ∀ j, 0 ≤ p j := fun j => mul_nonneg (hu j).1.le (sigmaE_mem S τ σ hσ j e).1
  have hpu : ∀ j, p j ≤ u j := fun j => by
    have := sigmaE_mem S τ σ hσ j e
    simp only [hp]; nlinarith [(hu j).1]
  have hbdd : BddAbove (Set.range u) := (Set.finite_range u).bddAbove
  have humax : ∀ j, u j ≤ maxU u := fun j => le_ciSup hbdd j
  have hEU : ∀ j, expect u σ (fun ω => (useIndicator j e ω : ℝ)) = p j :=
    fun j => expect_use S τ u σ hσ e j
  have hEX : expect u σ (fun ω => (loadRV e ω : ℝ)) = ∑ j, p j := by
    have : (fun ω : Outcome E N => (loadRV e ω : ℝ)) =
        fun ω => ∑ j ∈ Finset.univ, (useIndicator j e ω : ℝ) := by
      funext ω; unfold loadRV; push_cast; rfl
    rw [this, expect_add]
    exact Finset.sum_congr rfl (fun j _ => hEU j)
  have hEZ : expect u σ (fun ω => (othersLoadRV i e ω : ℝ)) = ∑ j ∈ Finset.univ.erase i, p j := by
    have : (fun ω : Outcome E N => (othersLoadRV i e ω : ℝ)) =
        fun ω => ∑ j ∈ Finset.univ.erase i, (useIndicator j e ω : ℝ) := by
      funext ω; unfold othersLoadRV; push_cast; rfl
    rw [this, expect_add]
    exact Finset.sum_congr rfl (fun j _ => hEU j)
  have hsplit : ∑ j, p j = p i + ∑ j ∈ Finset.univ.erase i, p j :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  set z : ℝ := ∑ j ∈ Finset.univ.erase i, p j with hz
  set x : ℝ := ∑ j, p j with hx
  have hz0 : 0 ≤ z := Finset.sum_nonneg (fun j _ => hp0 j)
  have hxd : x ≤ dmax := le_trans (Finset.sum_le_sum (fun j _ => hpu j)) htot
  refine ⟨?_, ?_, ?_⟩
  · rw [hEZ, hEX, hEU, hsplit]
    rw [show z - (p i + z) = -p i by ring, abs_neg, abs_of_nonneg (hp0 i)]
  · rw [hEU]; exact (hpu i).trans (humax i)
  -- the main estimate
  rw [hEX]
  set h : ℕ → ℝ := fun k => c e (1 + k) with hh
  have hΔ2 : ∀ k, deltaPow 2 h k = deltaPow 2 (c e) (1 + k) := by
    intro k
    rw [deltaPow_two, deltaPow_two]
    simp only [hh, add_assoc]
  have hint : Summable (fun k : ℕ => |deltaPow 2 h k| * poissonPmf dmax k) := by
    simpa only [hΔ2] using (hM e).1
  have hνb : ∑' k : ℕ, |deltaPow 2 h k| * poissonPmf dmax k ≤ ν := by
    simpa only [hΔ2] using (hM e).2
  have hν0 : 0 ≤ ν := le_trans (tsum_nonneg (fun k => mul_nonneg (abs_nonneg _)
    measureReal_nonneg)) hνb
  -- `u = max_i u_i ≥ 0` and `< 1`
  set U := maxU u with hU
  have hU0 : 0 ≤ U := le_trans (hu i).1.le (humax i)
  have hpU : ∀ j, p j ≤ U := fun j => (hpu j).trans (humax j)
  -- the Poisson-binomial representation of `E[h(Z_{i,e})]`
  set P : Fin N → Prop := fun j => j ≠ i ∧ 0 < p j with hPdef
  set n := Fintype.card {j // P j} with hn
  set eJ : Fin n ≃ {j // P j} := (Fintype.equivFin _).symm with heJ
  set p' : Fin n → ℝ := fun k => p (eJ k) with hp'
  have hrep : expect u σ (fun ω => c e (1 + othersLoadRV i e ω)) = bernoulliSumMean p' h := by
    have h1 : (fun ω : Outcome E N => c e (1 + othersLoadRV i e ω)) =
        fun ω => (fun b : Fin N → Bool => h (∑ j ∈ Finset.univ.erase i, if b j then 1 else 0))
          (fun j => decide ((ω j).1 = true ∧ e ∈ (ω j).2)) := by
      funext ω
      simp only [hh, othersLoadRV, useIndicator]
      congr 2
      refine Finset.sum_congr rfl (fun j _ => ?_)
      by_cases hj : (ω j).1 = true ∧ e ∈ (ω j).2 <;> simp [hj]
    rw [h1, expect_bool S τ u σ hσ e
      (fun b : Fin N → Bool => h (∑ j ∈ Finset.univ.erase i, if b j then 1 else 0))]
    have h2 := split_sum P (fun k b => if b then p k else 1 - p k) (fun k => by simp)
      (fun b => h (∑ j ∈ Finset.univ.erase i, if b j then 1 else 0))
      (fun cc => h (∑ j, if cc j then 1 else 0)) ?_
    · simp only [hp] at h2 ⊢
      rw [h2]
      exact reindex eJ (fun j => u j * sigmaE S τ σ j e) h
    · intro b hb
      simp only []
      congr 1
      have hsub : (∑ x : {j // P j}, (if b x then 1 else 0 : ℕ)) =
          ∑ j ∈ Finset.univ.filter P, (if b j then 1 else 0 : ℕ) :=
        (Finset.sum_subtype (Finset.univ.filter P) (by simp) (fun j => if b j then 1 else 0)).symm
      rw [hsub]
      symm
      apply Finset.sum_subset
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hPdef] at hj
        exact Finset.mem_erase.2 ⟨hj.1, Finset.mem_univ _⟩
      · intro j hj hjP
        have hji : j ≠ i := Finset.ne_of_mem_erase hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hPdef, not_and, not_lt] at hjP
        have hpj : p j = 0 := le_antisymm (hjP hji) (hp0 j)
        have hne := Finset.prod_ne_zero_iff.1 hb j (Finset.mem_univ j)
        cases hbj : b j
        · simp
        · rw [hbj] at hne; simp [hpj] at hne
  -- `∑ p' = z`
  have hsum' : ∑ k, p' k = z := by
    have h1 : ∑ k, p' k = ∑ j : {j // P j}, p j :=
      Fintype.sum_equiv eJ _ _ (fun k => rfl)
    rw [h1, ← Finset.sum_subtype (Finset.univ.filter P) (by simp)]
    apply Finset.sum_subset
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hPdef] at hj
      exact Finset.mem_erase.2 ⟨hj.1, Finset.mem_univ _⟩
    · intro j hj hjP
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hPdef, not_and, not_lt] at hjP
      exact le_antisymm (hjP hji) (hp0 j)
  -- the function `φ(t) = t e^t / (1 - t)^2`
  set φ : ℝ → ℝ := fun t => t * Real.exp t / (1 - t) ^ 2 with hφ
  have hφ0 : 0 ≤ φ U := by
    simp only [hφ]; exact div_nonneg (mul_nonneg hU0 (Real.exp_pos _).le) (sq_nonneg _)
  have hφmono : ∀ t, 0 ≤ t → t ≤ U → φ t ≤ φ U := by
    intro t ht0 htU
    simp only [hφ]
    have h1U : 0 < 1 - U := by linarith
    apply div_le_div₀ (mul_nonneg hU0 (Real.exp_pos _).le)
      (mul_le_mul htU (Real.exp_le_exp.2 htU) (Real.exp_pos _).le hU0) (by positivity)
    exact pow_le_pow_left₀ h1U.le (by linarith) 2
  -- Theorem 9(b), Borisov–Ruzankin
  have hzd : z ≤ dmax := by
    have : z ≤ x := by linarith [hx, hsplit, hp0 i]
    linarith
  have hT9 : |bernoulliSumMean p' h - poissonMean h z| ≤ ν * Real.exp dmax * z / 2 * φ U := by
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · haveI : IsEmpty (Fin n) := by rw [hn0]; infer_instance
      have hz' : z = 0 := by rw [← hsum']; simp
      have hbs : bernoulliSumMean p' h = h 0 := by
        simp [bernoulliSumMean, bernoulliWeight, successCount]
      rw [hbs, hz', poissonMean_zero]
      simp
    · have hp'pos : ∀ k, 0 < p' k ∧ p' k < 1 := fun k =>
        ⟨(eJ k).2.2, lt_of_le_of_lt (hpU _) hu1⟩
      have hb : ∀ k : ℕ, |deltaPow 2 h k| * poissonPmf z k ≤
          Real.exp (dmax - z) * (|deltaPow 2 h k| * poissonPmf dmax k) := by
        intro k
        calc |deltaPow 2 h k| * poissonPmf z k ≤
            |deltaPow 2 h k| * (Real.exp (dmax - z) * poissonPmf dmax k) :=
              mul_le_mul_of_nonneg_left (pmf_le z dmax hz0 hzd k) (abs_nonneg _)
          _ = _ := by ring
      have hint9 : Summable (fun k : ℕ => |deltaPow 2 h k| * poissonPmf (∑ k, p' k) k) := by
        rw [hsum']
        exact Summable.of_nonneg_of_le (fun k => mul_nonneg (abs_nonneg _) measureReal_nonneg)
          hb (hint.mul_left _)
      have hν9 : ∑' k : ℕ, |deltaPow 2 h k| * poissonPmf (∑ k, p' k) k ≤ ν * Real.exp dmax := by
        rw [hsum']
        calc ∑' k : ℕ, |deltaPow 2 h k| * poissonPmf z k
            ≤ ∑' k : ℕ, Real.exp (dmax - z) * (|deltaPow 2 h k| * poissonPmf dmax k) :=
              (hsum' ▸ hint9).tsum_le_tsum hb (hint.mul_left _)
          _ = Real.exp (dmax - z) * ∑' k : ℕ, |deltaPow 2 h k| * poissonPmf dmax k := tsum_mul_left
          _ ≤ Real.exp (dmax - z) * ν := mul_le_mul_of_nonneg_left hνb (Real.exp_pos _).le
          _ ≤ Real.exp dmax * ν := mul_le_mul_of_nonneg_right
              (Real.exp_le_exp.2 (by linarith)) hν0
          _ = ν * Real.exp dmax := by ring
      have T := (theorem_9_b hnpos p' hp'pos h (ν * Real.exp dmax) hint9 hν9).2
      rw [hsum'] at T
      haveI : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
      have hsup0 : 0 ≤ ⨆ k, p' k := le_trans (hp'pos ⟨0, hnpos⟩).1.le
        (le_ciSup (Set.finite_range p').bddAbove ⟨0, hnpos⟩)
      have hsupU : (⨆ k, p' k) ≤ U := ciSup_le (fun k => hpU _)
      have hc0 : 0 ≤ ν * Real.exp dmax * z / 2 := by
        have := Real.exp_pos dmax; positivity
      calc |bernoulliSumMean p' h - poissonMean h z|
          ≤ ν * Real.exp dmax * z / 2 * ((⨆ k, p' k) * Real.exp (⨆ k, p' k) /
              (1 - ⨆ k, p' k) ^ 2) := T
        _ ≤ ν * Real.exp dmax * z / 2 * φ U :=
            mul_le_mul_of_nonneg_left (hφmono _ hsup0 hsupU) hc0
  -- Lipschitz continuity of `c̆_e` (Lemma 1)
  have hsm := lemma_1_smooth c hc ν dmax hd hM e
  have hζ0 : 0 ≤ zeta c ν dmax := le_trans (hsm.2.2 0 ⟨le_rfl, hd.le⟩).1 (hsm.2.2 0 ⟨le_rfl, hd.le⟩).2
  have hdiff : DifferentiableOn ℝ (cBreve c e) (Set.Icc 0 dmax) :=
    hsm.2.1.differentiableOn (by norm_num)
  have hbound : ∀ y ∈ Set.Icc 0 dmax,
      ‖derivWithin (cBreve c e) (Set.Icc 0 dmax) y‖ ≤ zeta c ν dmax := by
    intro y hy
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [(hsm.2.2 y hy).1, (hsm.2.2 y hy).2]
  have hxI : x ∈ Set.Icc 0 dmax := ⟨le_trans hz0 (by linarith [hx, hsplit, hp0 i]), hxd⟩
  have hzI : z ∈ Set.Icc 0 dmax := ⟨hz0, hzd⟩
  have hlip := (convex_Icc 0 dmax).norm_image_sub_le_of_norm_derivWithin_le hdiff hbound hzI hxI
  rw [Real.norm_eq_abs, Real.norm_eq_abs, show x - z = p i by linarith [hx, hsplit],
    abs_of_nonneg (hp0 i)] at hlip
  have hcB : cBreve c e = poissonMean h := rfl
  rw [hcB] at hlip
  rw [hrep, hcB]
  have hpiU : p i * zeta c ν dmax ≤ U * zeta c ν dmax := mul_le_mul_of_nonneg_right (hpU i) hζ0
  have hzz : ν * Real.exp dmax * z / 2 * φ U ≤ ν * dmax * Real.exp dmax / 2 * φ U := by
    have := Real.exp_pos dmax
    have h1 : ν * Real.exp dmax * z ≤ ν * Real.exp dmax * dmax :=
      mul_le_mul_of_nonneg_left hzd (by positivity)
    have h2 : ν * Real.exp dmax * z / 2 ≤ ν * dmax * Real.exp dmax / 2 := by linarith
    exact mul_le_mul_of_nonneg_right h2 hφ0
  unfold LamCorr
  calc |bernoulliSumMean p' h - poissonMean h x|
      = |(bernoulliSumMean p' h - poissonMean h z) + (poissonMean h z - poissonMean h x)| := by
        ring_nf
    _ ≤ |bernoulliSumMean p' h - poissonMean h z| + |poissonMean h z - poissonMean h x| :=
        abs_add_le _ _
    _ ≤ ν * Real.exp dmax * z / 2 * φ U + zeta c ν dmax * p i := by
        rw [abs_sub_comm (poissonMean h z)]; linarith
    _ ≤ ν * dmax * Real.exp dmax / 2 * (U * Real.exp U / (1 - U) ^ 2) + U * zeta c ν dmax := by
        simp only [hφ] at hzz ⊢; linarith
