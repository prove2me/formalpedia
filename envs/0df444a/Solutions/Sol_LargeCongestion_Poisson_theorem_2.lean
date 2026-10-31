-- Prove2me | solution 1 for LargeCongestion.Poisson.theorem_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T09:24:42.245935+00:00
-- url     : https://prove2.me/submissions/f3aa1e49-eff8-4c38-ada0-10d22d3fd07a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_LargeCongestion_Poisson_PoissonCalculus
import Definitions.Def_LargeCongestion_Poisson_Game
import Theorems.Thm_LargeCongestion_Poisson_proposition_1
import Theorems.Thm_LargeCongestion_Poisson_lemma_1_smooth
import Theorems.Thm_LargeCongestion_Poisson_lemma_1_eq_21_corrected

open MeasureTheory ProbabilityTheory Filter LargeCongestion.Poisson
open scoped Topology

namespace LCPThm2Aux

variable {E T : Type*} [Fintype E] [DecidableEq E] [Fintype T] [DecidableEq T]

lemma sum_all_sigma (S : T → Finset (Finset E)) {N : ℕ} (τ : Fin N → T)
    (σ : Fin N → Finset E → ℝ) (hσ : IsMixedProfile S τ σ) (j : Fin N) (g : Finset E → ℝ) :
    ∑ s : Finset E, σ j s * g s = ∑ s ∈ S (τ j), σ j s * g s := by
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro s _ hs
  rw [hσ.2.1 j s hs, zero_mul]

lemma sum_weight_one (S : T → Finset (Finset E)) {N : ℕ} (τ : Fin N → T) (u : Fin N → ℝ)
    (σ : Fin N → Finset E → ℝ) (hσ : IsMixedProfile S τ σ) (j : Fin N) :
    ∑ p : Bool × Finset E, (if p.1 then u j else 1 - u j) * σ j p.2 = 1 := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [if_true, Bool.false_eq_true, if_false]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have h := sum_all_sigma S τ σ hσ j (fun _ => 1)
  simp only [mul_one] at h
  rw [h, hσ.2.2 j]
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

lemma expect_load (S : T → Finset (Finset E)) {N : ℕ} (τ : Fin N → T) (u : Fin N → ℝ)
    (σ : Fin N → Finset E → ℝ) (hσ : IsMixedProfile S τ σ) (e : E) :
    expect u σ (fun ω => (loadRV e ω : ℝ)) = expLoad S τ u σ e := by
  have hlin : expect u σ (fun ω => (loadRV e ω : ℝ)) =
      ∑ i, expect u σ (fun ω => ((useIndicator i e ω : ℕ) : ℝ)) := by
    unfold expect loadRV
    simp_rw [Nat.cast_sum, Finset.mul_sum]
    exact Finset.sum_comm
  rw [hlin]
  unfold expLoad
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have := expect_single S τ u σ hσ i
    (fun p => ((if p.1 = true ∧ e ∈ p.2 then 1 else 0 : ℕ) : ℝ))
  have h2 : (fun ω : Outcome E N => ((useIndicator i e ω : ℕ) : ℝ)) =
      fun ω => ((if (ω i).1 = true ∧ e ∈ (ω i).2 then 1 else 0 : ℕ) : ℝ) := rfl
  rw [h2, this, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [if_true, true_and, Bool.false_eq_true, false_and, if_false, Nat.cast_zero,
    mul_zero, Finset.sum_const_zero, add_zero]
  unfold sigmaE
  rw [Finset.mul_sum]
  have h3 := sum_all_sigma S τ σ hσ i (fun s => if e ∈ s then u i else 0)
  calc ∑ s : Finset E, u i * σ i s * ((if e ∈ s then 1 else 0 : ℕ) : ℝ)
      = ∑ s : Finset E, σ i s * (if e ∈ s then u i else 0) := by
        refine Finset.sum_congr rfl (fun s _ => ?_)
        split_ifs <;> simp; ring
    _ = ∑ s ∈ S (τ i), σ i s * (if e ∈ s then u i else 0) := h3
    _ = ∑ s ∈ S (τ i), u i * (if e ∈ s then σ i s else 0) := by
        refine Finset.sum_congr rfl (fun s _ => ?_)
        split_ifs <;> ring

lemma sigmaE_mem (S : T → Finset (Finset E)) {N : ℕ} (τ : Fin N → T)
    (σ : Fin N → Finset E → ℝ) (hσ : IsMixedProfile S τ σ) (i : Fin N) (e : E) :
    0 ≤ sigmaE S τ σ i e ∧ sigmaE S τ σ i e ≤ 1 := by
  unfold sigmaE
  constructor
  · exact Finset.sum_nonneg (fun s _ => by split_ifs; exact hσ.1 i s; exact le_rfl)
  · rw [← hσ.2.2 i]
    exact Finset.sum_le_sum (fun s _ => by split_ifs; exact le_rfl; exact hσ.1 i s)

lemma expLoad_mem (S : T → Finset (Finset E)) {N : ℕ} (τ : Fin N → T) (u : Fin N → ℝ)
    (hu : IsBernoulliGame u) (σ : Fin N → Finset E → ℝ) (hσ : IsMixedProfile S τ σ) (e : E)
    (dmax : ℝ) (htot : ∑ i, u i ≤ dmax) :
    expLoad S τ u σ e ∈ Set.Icc 0 dmax := by
  unfold expLoad
  constructor
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (hu i).1.le (sigmaE_mem S τ σ hσ i e).1)
  · refine le_trans (Finset.sum_le_sum (fun i _ => ?_)) htot
    have := sigmaE_mem S τ σ hσ i e
    nlinarith [(hu i).1]

end LCPThm2Aux

open LCPThm2Aux in
theorem solution {E T : Type*} [Fintype E] [DecidableEq E] [Fintype T] [DecidableEq T]
    (S : T → Finset (Finset E)) (hS : StrategiesNonempty S) (c : E → ℕ → ℝ)
    (hc : IsCostFamily c) (d : T → ℝ) (ν dmax : ℝ) (h18 : Condition18 c d ν dmax)
    (N : ℕ → ℕ) (τ : ∀ n, Fin (N n) → T) (u : ∀ n, Fin (N n) → ℝ)
    (hu : ∀ n, IsBernoulliGame (u n)) (h14 : Condition14 N τ u d)
    (σ : ∀ n, Fin (N n) → Finset E → ℝ) (hσ : ∀ n, IsBNE S c (τ n) (u n) (σ n)) :
    (∃ B : ℝ, ∀ n t s e,
        |expFlow (τ n) (u n) (σ n) t s| ≤ B ∧ |expLoad S (τ n) (u n) (σ n) e| ≤ B) ∧
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ (y : T → Finset E → ℝ) (x : E → ℝ),
        (∀ t s, Tendsto (fun k => expFlow (τ (φ k)) (u (φ k)) (σ (φ k)) t s) atTop
          (𝓝 (y t s))) →
        (∀ e, Tendsto (fun k => expLoad S (τ (φ k)) (u (φ k)) (σ (φ k)) e) atTop
          (𝓝 (x e))) →
        IsWardrop S (cBreve c) d y x ∧
          (∀ t, ∀ s ∈ S t, Tendsto (fun k => MarkovChainCLT.tvDist
              (law (u (φ k)) (σ (φ k)) (flowRV (τ (φ k)) t s))
              (poissonMeasure (y t s).toNNReal)) atTop (𝓝 0)) ∧
          (∀ e, Tendsto (fun k => MarkovChainCLT.tvDist
              (law (u (φ k)) (σ (φ k)) (loadRV e))
              (poissonMeasure (x e).toNNReal)) atTop (𝓝 0)) ∧
          Tendsto (fun k => MarkovChainCLT.tvDist
              (law (u (φ k)) (σ (φ k)) (flowVec S (τ (φ k))))
              (Measure.pi fun p : FlowIdx S => poissonMeasure (y p.1.1 p.1.2).toNNReal))
            atTop (𝓝 0) := by
  have hmix : ∀ n, IsMixedProfile S (τ n) (σ n) := fun n => (hσ n).1
  obtain ⟨hB, hrest⟩ := proposition_1 S hS d N τ u hu h14 σ hmix
  refine ⟨hB, ?_⟩
  intro φ hφ y x hy hx
  obtain ⟨hfeas, hY, hX, hV⟩ := hrest φ hφ y x hy hx
  refine ⟨⟨hfeas, ?_⟩, hY, hX, hV⟩
  intro t s hs s' hs' hpos
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  obtain ⟨_, h14b, h14c⟩ := h14
  have hd_nonneg : ∀ t, 0 ≤ d t := fun t =>
    ge_of_tendsto' (h14c t) (fun n => Finset.sum_nonneg (fun i _ => by
      split_ifs
      · exact (hu n i).1.le
      · exact le_rfl))
  have hdmax : 0 < dmax := lt_of_le_of_lt (Finset.sum_nonneg fun t _ => hd_nonneg t) h18.1
  have htot_eq : ∀ n, ∑ i, u n i = ∑ t, demand (τ n) (u n) t := by
    intro n
    unfold demand
    rw [Finset.sum_comm]
    simp
  have htot_ev : ∀ᶠ n in atTop, ∑ i, u n i ≤ dmax := by
    have hlim : Tendsto (fun n => ∑ t, demand (τ n) (u n) t) atTop (𝓝 (∑ t, d t)) :=
      tendsto_finsetSum _ (fun t _ => h14c t)
    filter_upwards [hlim.eventually (gt_mem_nhds h18.1)] with n hn
    rw [htot_eq]
    exact hn.le
  have hu1_ev : ∀ᶠ n in atTop, maxU (u n) < 1 := h14b.eventually (gt_mem_nhds one_pos)
  have hev1 : ∀ᶠ k in atTop, (∑ i, u (φ k) i ≤ dmax) ∧ maxU (u (φ k)) < 1 :=
    hφt.eventually (htot_ev.and hu1_ev)
  have hev : ∀ᶠ k in atTop, ((∑ i, u (φ k) i ≤ dmax) ∧ maxU (u (φ k)) < 1) ∧
      0 < expFlow (τ (φ k)) (u (φ k)) (σ (φ k)) t s :=
    hev1.and ((hy t s).eventually (lt_mem_nhds hpos))
  -- continuity of the auxiliary costs
  have hcont : ∀ e, ContinuousOn (cBreve c e) (Set.Icc 0 dmax) := fun e =>
    (lemma_1_smooth c hc ν dmax hdmax h18.2 e).2.1.continuousOn
  have hmem_ev : ∀ e, ∀ᶠ k in atTop,
      expLoad S (τ (φ k)) (u (φ k)) (σ (φ k)) e ∈ Set.Icc 0 dmax := fun e => by
    filter_upwards [hev1] with k hk
    exact expLoad_mem S (τ (φ k)) (u (φ k)) (hu _) (σ (φ k)) (hmix _) e dmax hk.1
  have hx_mem : ∀ e, x e ∈ Set.Icc 0 dmax := fun e =>
    isClosed_Icc.mem_of_tendsto (hx e) (hmem_ev e)
  have hcx : ∀ e, Tendsto (fun k => cBreve c e (expLoad S (τ (φ k)) (u (φ k)) (σ (φ k)) e))
      atTop (𝓝 (cBreve c e (x e))) := fun e =>
    ((hcont e) (x e) (hx_mem e)).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hx e, hmem_ev e⟩)
  -- the error term Λ̃(u^n) tends to zero
  have hLam0 : LamCorr c ν dmax 0 = 0 := by simp [LamCorr]
  have hLamc : ContinuousAt (LamCorr c ν dmax) 0 := by
    unfold LamCorr
    fun_prop (disch := norm_num)
  have hLam : Tendsto (fun k => LamCorr c ν dmax (maxU (u (φ k)))) atTop (𝓝 0) := by
    have := hLamc.tendsto.comp (h14b.comp hφt)
    rw [hLam0] at this
    exact this
  -- the approximate equilibrium inequality at stage φ k
  set xL : ℕ → E → ℝ := fun k e => expLoad S (τ (φ k)) (u (φ k)) (σ (φ k)) e with hxL
  set L : ℕ → ℝ := fun k => LamCorr c ν dmax (maxU (u (φ k))) with hL
  have hineq : ∀ᶠ k in atTop, ∑ e ∈ s, cBreve c e (xL k e) ≤
      ∑ e ∈ s', cBreve c e (xL k e) + ((s.card : ℝ) + s'.card) * L k := by
    filter_upwards [hev] with k ⟨⟨hk1, hk2⟩, hk3⟩
    have hk3' : ∑ i : Fin (N (φ k)), (0 : ℝ) < ∑ i, (if τ (φ k) i = t then u (φ k) i * σ (φ k) i s else 0) := by
      simpa [expFlow] using hk3
    obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt hk3'
    by_cases hτ : τ (φ k) i = t
    · rw [if_pos hτ] at hi
      have hσpos : 0 < σ (φ k) i s := pos_of_mul_pos_right hi (hu _ i).1.le
      have hsi : s ∈ S (τ (φ k) i) := hτ ▸ hs
      have hsi' : s' ∈ S (τ (φ k) i) := hτ ▸ hs'
      have hbne := (hσ (φ k)).2 i s hsi s' hsi' hσpos
      have h21 : ∀ e, |expect (u (φ k)) (σ (φ k)) (fun ω => c e (1 + othersLoadRV i e ω)) -
          cBreve c e (xL k e)| ≤ L k := fun e => by
        have := (lemma_1_eq_21_corrected S c hc ν dmax hdmax h18.2 (τ (φ k)) (u (φ k)) (hu _)
          (σ (φ k)) (hmix _) hk1 hk2 i e).2.2
        rw [expect_load S (τ (φ k)) (u (φ k)) (σ (φ k)) (hmix _) e] at this
        exact this
      set A : E → ℝ := fun e => expect (u (φ k)) (σ (φ k)) (fun ω => c e (1 + othersLoadRV i e ω))
        with hA
      have hup : ∀ e, cBreve c e (xL k e) ≤ A e + L k := fun e =>
        by have := (abs_le.1 (h21 e)); linarith [this.1]
      have hlo : ∀ e, A e ≤ cBreve c e (xL k e) + L k := fun e =>
        by have := (abs_le.1 (h21 e)); linarith [this.2]
      calc ∑ e ∈ s, cBreve c e (xL k e) ≤ ∑ e ∈ s, (A e + L k) :=
            Finset.sum_le_sum (fun e _ => hup e)
        _ = ∑ e ∈ s, A e + s.card * L k := by
            rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ e ∈ s', A e + s.card * L k := by linarith [hbne]
        _ ≤ ∑ e ∈ s', (cBreve c e (xL k e) + L k) + s.card * L k := by
            linarith [Finset.sum_le_sum (fun e (_ : e ∈ s') => hlo e)]
        _ = ∑ e ∈ s', cBreve c e (xL k e) + ((s.card : ℝ) + s'.card) * L k := by
            rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
            ring
    · rw [if_neg hτ] at hi
      exact absurd hi (lt_irrefl _)
  have hlimL : Tendsto (fun k => ∑ e ∈ s, cBreve c e (xL k e)) atTop
      (𝓝 (∑ e ∈ s, cBreve c e (x e))) := tendsto_finsetSum _ (fun e _ => hcx e)
  have hlimR : Tendsto (fun k => ∑ e ∈ s', cBreve c e (xL k e) +
      ((s.card : ℝ) + s'.card) * L k) atTop (𝓝 (∑ e ∈ s', cBreve c e (x e))) := by
    have h1 : Tendsto (fun k => ∑ e ∈ s', cBreve c e (xL k e)) atTop
        (𝓝 (∑ e ∈ s', cBreve c e (x e))) := tendsto_finsetSum _ (fun e _ => hcx e)
    have h2 := h1.add (hLam.const_mul ((s.card : ℝ) + s'.card))
    simpa using h2
  exact le_of_tendsto_of_tendsto hlimL hlimR hineq
