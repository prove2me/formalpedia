-- Prove2me | solution 1 for KellyKolmogorov.theorem_1_8_kolmogorov_criterion
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-03T23:54:59.73999+00:00
-- url     : https://prove2.me/submissions/c3bd1eb3-703c-447a-b57d-79b376072c58

import Mathlib
import Definitions.Def_KellyKolmogorov_StandingAssumptions
import Definitions.Def_KellyKolmogorov_IsStationary
import Definitions.Def_KellyKolmogorov_IsTransitionRate
import Definitions.Def_KellyKolmogorov_IsReversible
import Definitions.Def_KellyKolmogorov_KolmogorovCycle

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace KKCrit
open KellyKolmogorov

section basics

variable {Ω 𝒮 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  {μ : Measure Ω} {X : ℝ → Ω → 𝒮}

lemma meas_eq (hX : ∀ t, Measurable (X t)) (t : ℝ) (a : 𝒮) : MeasurableSet {ω | X t ω = a} :=
  hX t (measurableSet_singleton a)

lemma stat_one (hs : IsStationary μ X) (s : ℝ) (a : 𝒮) :
    μ {ω | X s ω = a} = μ {ω | X 0 ω = a} := by
  have h := hs 1 (fun _ => 0) s (fun _ => a)
  simp only [cylProb, Fin.forall_fin_one, zero_add] at h
  exact h

lemma stat_two (hs : IsStationary μ X) (s u τ : ℝ) (a b : 𝒮) :
    μ ({ω | X (s + τ) ω = a} ∩ {ω | X (u + τ) ω = b}) =
      μ ({ω | X s ω = a} ∩ {ω | X u ω = b}) := by
  have h := hs 2 ![s, u] τ ![a, b]
  simp only [cylProb, Fin.forall_fin_two] at h
  simpa [Set.ofPred_and] using h

lemma pi_ne_zero [IsProbabilityMeasure μ] (hs : IsStationary μ X) (hirr : IsIrreducible μ X)
    (c : 𝒮) : μ {ω | X 0 ω = c} ≠ 0 := by
  intro h0
  have hne : ({ω | X 0 ω = c}ᶜ : Set Ω).Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at hc
    rw [hc, measure_univ] at h0
    exact one_ne_zero h0
  obtain ⟨ω, hω⟩ := hne
  obtain ⟨s, τ, -, hpos⟩ := hirr c (X 0 ω) (fun h => hω h.symm)
  apply hpos
  apply measure_mono_null Set.inter_subset_left
  rw [stat_one hs]
  exact h0

lemma pi_toReal_pos [IsProbabilityMeasure μ] (hs : IsStationary μ X) (hirr : IsIrreducible μ X)
    (c : 𝒮) : 0 < (μ {ω | X 0 ω = c}).toReal :=
  ENNReal.toReal_pos (pi_ne_zero hs hirr c) (measure_ne_top _ _)

/-- The joint probability `P(X 0 = a, X τ = b)` divided by `τ` tends to `π a * q a b`. -/
lemma joint_rate [IsProbabilityMeasure μ] (hX : StandingAssumptions μ X) (hs : IsStationary μ X)
    {q : 𝒮 → 𝒮 → ℝ≥0} (hq : IsTransitionRate μ X q) {a b : 𝒮} (hab : a ≠ b) :
    Tendsto (fun τ : ℝ => (μ ({ω | X 0 ω = a} ∩ {ω | X τ ω = b})).toReal / τ) (𝓝[>] 0)
      (𝓝 ((μ {ω | X 0 ω = a}).toReal * q a b)) := by
  have hπ := pi_ne_zero hs hX.irreducible a
  have h := (hq.2 a b hab 0 hπ).const_mul (μ {ω | X 0 ω = a}).toReal
  refine h.congr (fun τ => ?_)
  simp only [transProb, zero_add]
  rw [ProbabilityTheory.cond_apply (meas_eq hX.measurable 0 a), ENNReal.toReal_mul,
    ENNReal.toReal_inv]
  have : (μ {ω | X 0 ω = a}).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hπ, measure_ne_top _ _⟩
  rw [← mul_div_assoc, ← mul_assoc, mul_inv_cancel₀ this, one_mul]

lemma rev_two (hr : IsReversible μ X) (τ : ℝ) (a b : 𝒮) :
    μ ({ω | X 0 ω = a} ∩ {ω | X τ ω = b}) = μ ({ω | X 0 ω = b} ∩ {ω | X τ ω = a}) := by
  have h := hr 2 ![0, τ] τ ![a, b]
  simp only [cylProb, Fin.forall_fin_two] at h
  convert h using 2 <;> ext ω <;> simp [and_comm]

end basics

/-- Detailed balance with a positive weight implies Kolmogorov's cycle condition. -/
lemma kolmo_of_db {𝒮 : Type*} (π : 𝒮 → ℝ) (hπ : ∀ a, 0 < π a) (q : 𝒮 → 𝒮 → ℝ≥0)
    (hdb : ∀ a b, π a * (q a b : ℝ) = π b * (q b a : ℝ)) : KolmogorovCycle q := by
  intro n j
  have key : (∏ i, π (j i)) * (∏ i, (q (j i) (j (finRotate (n + 1) i)) : ℝ)) =
      (∏ i, π (j i)) * (∏ i, (q (j (finRotate (n + 1) i)) (j i) : ℝ)) := by
    calc (∏ i, π (j i)) * (∏ i, (q (j i) (j (finRotate (n + 1) i)) : ℝ))
        = ∏ i, (π (j i) * (q (j i) (j (finRotate (n + 1) i)) : ℝ)) :=
          (Finset.prod_mul_distrib).symm
      _ = ∏ i, (π (j (finRotate (n + 1) i)) * (q (j (finRotate (n + 1) i)) (j i) : ℝ)) :=
          Finset.prod_congr rfl (fun i _ => hdb _ _)
      _ = (∏ i, π (j (finRotate (n + 1) i))) * (∏ i, (q (j (finRotate (n + 1) i)) (j i) : ℝ)) :=
          Finset.prod_mul_distrib
      _ = (∏ i, π (j i)) * (∏ i, (q (j (finRotate (n + 1) i)) (j i) : ℝ)) := by
          rw [Equiv.prod_comp (finRotate (n + 1)) (fun i => π (j i))]
  have hne : (∏ i, π (j i)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => (hπ _).ne')
  have := mul_left_cancel₀ hne key
  exact_mod_cast this

section forward

variable {Ω 𝒮 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  {μ : Measure Ω} {X : ℝ → Ω → 𝒮}

/-- The easy direction: reversibility gives detailed balance with the stationary law, hence
Kolmogorov's cycle condition. -/
theorem forward [IsProbabilityMeasure μ] (hX : StandingAssumptions μ X) (hs : IsStationary μ X)
    {q : 𝒮 → 𝒮 → ℝ≥0} (hq : IsTransitionRate μ X q) (hr : IsReversible μ X) :
    KolmogorovCycle q := by
  refine kolmo_of_db (fun a => (μ {ω | X 0 ω = a}).toReal)
    (fun a => pi_toReal_pos hs hX.irreducible a) q ?_
  intro a b
  by_cases hab : a = b
  · subst hab; rfl
  · have h1 := joint_rate hX hs hq hab
    have h2 := joint_rate hX hs hq (Ne.symm hab)
    have h3 : (fun τ : ℝ => (μ ({ω | X 0 ω = a} ∩ {ω | X τ ω = b})).toReal / τ) =
        (fun τ : ℝ => (μ ({ω | X 0 ω = b} ∩ {ω | X τ ω = a})).toReal / τ) := by
      funext τ; rw [rev_two hr τ a b]
    rw [h3] at h1
    exact tendsto_nhds_unique h1 h2

end forward

section walks
/-! ### Walks and Kolmogorov's criterion: a positive detailed-balance weight -/

variable {𝒮 : Type*} (w : 𝒮 → 𝒮 → ℝ≥0)

/-- forward product along the walk `γ 0 → γ 1 → ⋯ → γ n` -/
def fwd (γ : ℕ → 𝒮) (n : ℕ) : ℝ≥0 := ∏ i ∈ Finset.range n, w (γ i) (γ (i + 1))
/-- backward product along the walk -/
def bwd (γ : ℕ → 𝒮) (n : ℕ) : ℝ≥0 := ∏ i ∈ Finset.range n, w (γ (i + 1)) (γ i)

lemma cycle_nat (hK : KolmogorovCycle w) (δ : ℕ → 𝒮) (L : ℕ) (hc : δ L = δ 0) :
    fwd w δ L = bwd w δ L := by
  cases L with
  | zero => simp [fwd, bwd]
  | succ n =>
    have hr : ∀ i : Fin (n + 1), δ ((finRotate (n + 1) i : ℕ)) = δ ((i : ℕ) + 1) := by
      intro i
      by_cases hi : i = Fin.last n
      · subst hi
        simp [hc]
      · rw [coe_finRotate_of_ne_last hi]
    have h : ∏ i : Fin (n + 1), w (δ i) (δ ((i : ℕ) + 1)) =
        ∏ i : Fin (n + 1), w (δ ((i : ℕ) + 1)) (δ i) := by
      have := hK n (fun i => δ i)
      simpa only [hr] using this
    rw [Fin.prod_univ_eq_prod_range (fun i => w (δ i) (δ (i + 1))) (n + 1),
      Fin.prod_univ_eq_prod_range (fun i => w (δ (i + 1)) (δ i)) (n + 1)] at h
    exact h

/-- concatenation of two walks (the second starts where the first ends) -/
def cat (γ₁ : ℕ → 𝒮) (n₁ : ℕ) (γ₂ : ℕ → 𝒮) : ℕ → 𝒮 :=
  fun i => if i ≤ n₁ then γ₁ i else γ₂ (i - n₁)

lemma cat_left (γ₁ : ℕ → 𝒮) (n₁ : ℕ) (γ₂ : ℕ → 𝒮) {i : ℕ} (hi : i ≤ n₁) :
    cat γ₁ n₁ γ₂ i = γ₁ i := by simp [cat, hi]

lemma cat_right (γ₁ : ℕ → 𝒮) (n₁ : ℕ) (γ₂ : ℕ → 𝒮) (h : γ₂ 0 = γ₁ n₁) (x : ℕ) :
    cat γ₁ n₁ γ₂ (n₁ + x) = γ₂ x := by
  rcases Nat.eq_zero_or_pos x with hx | hx
  · subst hx; simp [cat, h]
  · have : ¬ (n₁ + x ≤ n₁) := by omega
    simp [cat, this]

lemma fwd_cat (γ₁ γ₂ : ℕ → 𝒮) (n₁ n₂ : ℕ) (h : γ₂ 0 = γ₁ n₁) :
    fwd w (cat γ₁ n₁ γ₂) (n₁ + n₂) = fwd w γ₁ n₁ * fwd w γ₂ n₂ := by
  unfold fwd
  rw [Finset.prod_range_add]
  congr 1
  · refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [cat_left _ _ _ (by omega), cat_left _ _ _ (by omega)]
  · refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [cat_right _ _ _ h, add_assoc, cat_right _ _ _ h]

lemma bwd_cat (γ₁ γ₂ : ℕ → 𝒮) (n₁ n₂ : ℕ) (h : γ₂ 0 = γ₁ n₁) :
    bwd w (cat γ₁ n₁ γ₂) (n₁ + n₂) = bwd w γ₁ n₁ * bwd w γ₂ n₂ := by
  unfold bwd
  rw [Finset.prod_range_add]
  congr 1
  · refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [cat_left _ _ _ (by omega), cat_left _ _ _ (by omega)]
  · refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [cat_right _ _ _ h, add_assoc, cat_right _ _ _ h]

/-- reversal of a walk of length `n` -/
def rv (γ : ℕ → 𝒮) (n : ℕ) : ℕ → 𝒮 := fun i => γ (n - i)

lemma fwd_rv (γ : ℕ → 𝒮) (n : ℕ) : fwd w (rv γ n) n = bwd w γ n := by
  unfold fwd bwd rv
  rw [← Finset.prod_range_reflect (fun i => w (γ (i + 1)) (γ i)) n]
  refine Finset.prod_congr rfl (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  have e1 : n - 1 - i + 1 = n - i := by omega
  have e2 : n - 1 - i = n - (i + 1) := by omega
  rw [e1, e2]

lemma bwd_rv (γ : ℕ → 𝒮) (n : ℕ) : bwd w (rv γ n) n = fwd w γ n := by
  unfold fwd bwd rv
  rw [← Finset.prod_range_reflect (fun i => w (γ i) (γ (i + 1))) n]
  refine Finset.prod_congr rfl (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  have e1 : n - 1 - i + 1 = n - i := by omega
  have e2 : n - 1 - i = n - (i + 1) := by omega
  rw [e1, e2]

/-- a walk from `a` to `b` of length `n` all of whose steps have positive weight -/
def PW (a b : 𝒮) (γ : ℕ → 𝒮) (n : ℕ) : Prop :=
  γ 0 = a ∧ γ n = b ∧ ∀ i < n, 0 < w (γ i) (γ (i + 1))

lemma fwd_pos {a b : 𝒮} {γ : ℕ → 𝒮} {n : ℕ} (h : PW w a b γ n) : 0 < fwd w γ n :=
  Finset.prod_pos (fun i hi => h.2.2 i (Finset.mem_range.mp hi))

lemma exists_walk {a b : 𝒮} (h : Relation.ReflTransGen (fun x y => 0 < w x y) a b) :
    ∃ γ n, PW w a b γ n := by
  induction h with
  | refl => exact ⟨fun _ => a, 0, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | @tail b c _ hbc ih =>
    obtain ⟨γ, n, h0, hn, hpos⟩ := ih
    refine ⟨fun i => if i ≤ n then γ i else c, n + 1, ?_, ?_, ?_⟩
    · simp [h0]
    · simp
    · intro i hi
      rcases Nat.lt_or_ge i n with h1 | h1
      · have h2 : i + 1 ≤ n := h1
        simp only [le_of_lt h1, h2, if_true]
        exact hpos i h1
      · have hin : i = n := by omega
        subst hin
        simp only [le_refl, if_true, show ¬ (i + 1 ≤ i) by omega, if_false, hn]
        exact hbc

/-- two positive walks from `o` to `a` have the same backward/forward ratio -/
lemma ratio_eq (hK : KolmogorovCycle w) {o a : 𝒮} {γ γ' : ℕ → 𝒮} {n n' : ℕ}
    (h : PW w o a γ n) (h' : PW w o a γ' n') :
    fwd w γ n * bwd w γ' n' = bwd w γ n * fwd w γ' n' := by
  have hj : rv γ' n' 0 = γ n := by simp [rv, h.2.1, h'.2.1]
  have hc := cycle_nat w hK (cat γ n (rv γ' n')) (n + n') (by
    rw [cat_right _ _ _ hj, cat_left _ _ _ (Nat.zero_le _)]
    simp [rv, h.1, h'.1])
  rw [fwd_cat w _ _ _ _ hj, bwd_cat w _ _ _ _ hj, fwd_rv, bwd_rv] at hc
  exact hc

lemma bwd_pos (hK : KolmogorovCycle w) {o a : 𝒮} {γ β : ℕ → 𝒮} {n m : ℕ}
    (h : PW w o a γ n) (hb : PW w a o β m) : 0 < bwd w γ n := by
  have hj : β 0 = γ n := by rw [hb.1, h.2.1]
  have hc := cycle_nat w hK (cat γ n β) (n + m) (by
    rw [cat_right _ _ _ hj, cat_left _ _ _ (Nat.zero_le _), hb.2.1, h.1])
  rw [fwd_cat w _ _ _ _ hj, bwd_cat w _ _ _ _ hj] at hc
  have hp : 0 < fwd w γ n * fwd w β m := mul_pos (fwd_pos w h) (fwd_pos w hb)
  rw [hc] at hp
  rcases eq_or_lt_of_le (zero_le : (0:ℝ≥0) ≤ bwd w γ n) with h0 | h0
  · rw [← h0, zero_mul] at hp; exact absurd hp (lt_irrefl _)
  · exact h0

/-- Kolmogorov's criterion plus connectivity of the positive-rate graph gives a positive
detailed-balance weight. -/
lemma exists_db (hK : KolmogorovCycle w)
    (hconn : ∀ a b, Relation.ReflTransGen (fun x y => 0 < w x y) a b) (o : 𝒮) :
    ∃ m : 𝒮 → ℝ, (∀ a, 0 < m a) ∧ ∀ a b, m a * (w a b : ℝ) = m b * (w b a : ℝ) := by
  choose γ n hγ using fun a => exists_walk w (hconn o a)
  choose β k hβ using fun a => exists_walk w (hconn a o)
  have hbp : ∀ a, 0 < bwd w (γ a) (n a) := fun a => bwd_pos w hK (hγ a) (hβ a)
  refine ⟨fun a => (fwd w (γ a) (n a) : ℝ) / bwd w (γ a) (n a),
    fun a => div_pos (by exact_mod_cast fwd_pos w (hγ a)) (by exact_mod_cast hbp a), ?_⟩
  -- the one-step extension
  have key : ∀ a b, 0 < w a b →
      (fwd w (γ a) (n a) : ℝ) / bwd w (γ a) (n a) * (w a b : ℝ) =
        (fwd w (γ b) (n b) : ℝ) / bwd w (γ b) (n b) * (w b a : ℝ) := by
    intro a b hab
    let st : ℕ → 𝒮 := fun i => if i = 0 then a else b
    have hj : st 0 = γ a (n a) := by simp [st, (hγ a).2.1]
    have hext : PW w o b (cat (γ a) (n a) st) (n a + 1) := by
      refine ⟨by rw [cat_left _ _ _ (Nat.zero_le _), (hγ a).1], by
        rw [cat_right _ _ _ hj]; simp [st], ?_⟩
      intro i hi
      rcases Nat.lt_or_ge i (n a) with h1 | h1
      · rw [cat_left _ _ _ (le_of_lt h1), cat_left _ _ _ h1]
        exact (hγ a).2.2 i h1
      · have hin : i = n a := by omega
        subst hin
        have e0 := cat_right _ _ _ hj 0
        rw [add_zero] at e0
        rw [e0, cat_right _ _ _ hj 1]
        simpa [st] using hab
    have hr := ratio_eq w hK hext (hγ b)
    rw [fwd_cat w _ _ _ _ hj, bwd_cat w _ _ _ _ hj] at hr
    have f1 : fwd w st 1 = w a b := by simp [fwd, st]
    have b1 : bwd w st 1 = w b a := by simp [bwd, st]
    rw [f1, b1] at hr
    have hr' : ((fwd w (γ a) (n a) : ℝ) * w a b) * bwd w (γ b) (n b) =
        ((bwd w (γ a) (n a) : ℝ) * w b a) * fwd w (γ b) (n b) := by exact_mod_cast hr
    have h1 : (0 : ℝ) < bwd w (γ a) (n a) := by exact_mod_cast hbp a
    have h2 : (0 : ℝ) < bwd w (γ b) (n b) := by exact_mod_cast hbp b
    field_simp
    linarith [hr']
  intro a b
  rcases eq_or_lt_of_le (zero_le : (0:ℝ≥0) ≤ w a b) with hab | hab
  · rcases eq_or_lt_of_le (zero_le : (0:ℝ≥0) ≤ w b a) with hba | hba
    · rw [← hab, ← hba]; simp
    · have := key b a hba
      rw [← hab] at this
      have hm : (0 : ℝ) < (fwd w (γ b) (n b) : ℝ) / bwd w (γ b) (n b) :=
        div_pos (by exact_mod_cast fwd_pos w (hγ b)) (by exact_mod_cast hbp b)
      simp only [NNReal.coe_zero, mul_zero] at this
      have : (w b a : ℝ) = 0 := by
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hm.ne'
        · exact h
      have : w b a = 0 := by exact_mod_cast this
      exact absurd this hba.ne'
  · exact key a b hab

end walks

section harmonic
/-! ### A maximum principle: a positive function in "detailed balance" with a doubly
stochastic-type kernel is constant along positive entries -/

variable {𝒮 : Type*}

lemma tsum_eq_of_le {f g : 𝒮 → ℝ≥0∞} (hle : ∀ a, f a ≤ g a) (hs : ∑' a, f a = ∑' a, g a)
    (hfin : ∑' a, f a ≠ ∞) (a : 𝒮) : f a = g a := by
  by_contra hne
  have := ENNReal.tsum_lt_tsum hfin hle (lt_of_le_of_ne (hle a) hne)
  rw [hs] at this
  exact lt_irrefl _ this

lemma max_principle (π : 𝒮 → ℝ≥0∞) (A : 𝒮 → 𝒮 → ℝ≥0∞) (F : 𝒮 → ℝ≥0∞)
    (hrow : ∀ j, ∑' k, A j k = π j) (hcol : ∀ k, ∑' j, A j k = π k)
    (hπ : ∀ j, π j ≠ ∞) (hπs : ∑' j, π j ≠ ∞) (hF : ∀ j, F j ≠ ∞)
    (hsym : ∀ j k, F j * A k j = F k * A j k) (j k : 𝒮) (hjk : A j k ≠ 0) : F j ≤ F k := by
  set C := F j
  set g : 𝒮 → ℝ≥0∞ := fun a => min (F a) C with hg
  have hharm : ∀ a, ∑' b, A a b * F b = F a * π a := by
    intro a
    have : ∑' b, F a * A b a = ∑' b, F b * A a b := tsum_congr (fun b => hsym a b)
    rw [ENNReal.tsum_mul_left, hcol a] at this
    rw [this]
    exact tsum_congr (fun b => mul_comm _ _)
  have hle : ∀ a, ∑' b, A a b * g b ≤ π a * g a := by
    intro a
    have h1 : ∑' b, A a b * g b ≤ F a * π a := by
      rw [← hharm a]
      exact ENNReal.tsum_le_tsum (fun b => mul_le_mul' le_rfl (min_le_left _ _))
    have h2 : ∑' b, A a b * g b ≤ C * π a := by
      calc ∑' b, A a b * g b ≤ ∑' b, A a b * C :=
            ENNReal.tsum_le_tsum (fun b => mul_le_mul' le_rfl (min_le_right _ _))
        _ = C * π a := by rw [ENNReal.tsum_mul_right, hrow a, mul_comm]
    rcases le_total (F a) C with h | h
    · simp only [hg, min_eq_left h]; rw [mul_comm]; exact h1
    · simp only [hg, min_eq_right h]; rw [mul_comm]; exact h2
  have hsum : ∑' a, ∑' b, A a b * g b = ∑' a, π a * g a := by
    rw [ENNReal.tsum_comm]
    refine tsum_congr (fun b => ?_)
    rw [ENNReal.tsum_mul_right, hcol b, mul_comm]
  have hfin : ∑' a, ∑' b, A a b * g b ≠ ∞ := by
    rw [hsum]
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hπs (hF j)) ?_
    rw [← ENNReal.tsum_mul_right]
    exact ENNReal.tsum_le_tsum (fun a => mul_le_mul' le_rfl (min_le_right _ _))
  have heq := tsum_eq_of_le hle hsum hfin j
  -- at `j` the function `g` attains its maximum `C`
  have hgj : g j = C := by simp [hg, C]
  rw [hgj] at heq
  by_contra hlt
  push Not at hlt
  have hgk : g k < C := by simp only [hg, min_lt_iff]; left; exact hlt
  have hAfin : A j k ≠ ∞ := ne_top_of_le_ne_top (hπ j) (by rw [← hrow j]; exact ENNReal.le_tsum k)
  have hlt2 : ∑' b, A j b * g b < ∑' b, A j b * C := by
    refine ENNReal.tsum_lt_tsum (i := k) ?_ (fun b => mul_le_mul' le_rfl (min_le_right _ _)) ?_
    · rw [heq]; exact ENNReal.mul_ne_top (hπ j) (hF j)
    · rw [mul_comm (A j k), mul_comm (A j k)]; exact ENNReal.mul_lt_mul_left hjk hAfin hgk
  rw [heq, ENNReal.tsum_mul_right, hrow j, mul_comm] at hlt2
  exact lt_irrefl _ hlt2

end harmonic

section fdd
/-! ### Finite-dimensional distributions of a stationary Markov process -/

variable {Ω 𝒮 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  {μ : Measure Ω} {X : ℝ → Ω → 𝒮}

/-- two-point joint law `P(X 0 = a, X h = b)` -/
def D2 (μ : Measure Ω) (X : ℝ → Ω → 𝒮) (h : ℝ) (a b : 𝒮) : ℝ≥0∞ :=
  μ ({ω | X 0 ω = a} ∩ {ω | X h ω = b})

lemma meas_cyl (hX : ∀ t, Measurable (X t)) {n : ℕ} (t : Fin n → ℝ) (j : Fin n → 𝒮) :
    MeasurableSet {ω | ∀ i, X (t i) ω = j i} := by
  rw [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => meas_eq hX (t i) (j i))

lemma ennreal_alg {e c x y : ℝ≥0∞} (he0 : e ≠ 0) (het : e ≠ ∞) (hc0 : c ≠ 0) (hct : c ≠ ∞)
    (h : e⁻¹ * x = c⁻¹ * y) : x * c = e * y := by
  calc x * c = (e * e⁻¹) * x * c := by rw [ENNReal.mul_inv_cancel he0 het, one_mul]
    _ = e * (e⁻¹ * x) * c := by ring
    _ = e * (c⁻¹ * y) * c := by rw [h]
    _ = e * y * (c⁻¹ * c) := by ring
    _ = e * y := by rw [ENNReal.inv_mul_cancel hc0 hct, mul_one]

lemma markov_step [IsProbabilityMeasure μ] (hX : StandingAssumptions μ X) (hs : IsStationary μ X)
    (n : ℕ) (t : Fin (n + 2) → ℝ) (j : Fin (n + 2) → 𝒮) (ht : StrictMono t) :
    μ {ω | ∀ i, X (t i) ω = j i} * μ {ω | X 0 ω = j (Fin.last n).castSucc} =
      μ {ω | ∀ i : Fin (n + 1), X (t i.castSucc) ω = j i.castSucc} *
        D2 μ X (t (Fin.last (n + 1)) - t (Fin.last n).castSucc) (j (Fin.last n).castSucc)
          (j (Fin.last (n + 1))) := by
  have hEB : {ω | ∀ i, X (t i) ω = j i} =
      {ω | ∀ i : Fin (n + 1), X (t i.castSucc) ω = j i.castSucc} ∩
        {ω | X (t (Fin.last (n + 1))) ω = j (Fin.last (n + 1))} := by
    ext ω; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Fin.forall_fin_succ']
  have hCB : μ ({ω | X (t (Fin.last n).castSucc) ω = j (Fin.last n).castSucc} ∩
        {ω | X (t (Fin.last (n + 1))) ω = j (Fin.last (n + 1))}) =
      D2 μ X (t (Fin.last (n + 1)) - t (Fin.last n).castSucc) (j (Fin.last n).castSucc)
        (j (Fin.last (n + 1))) := by
    have := stat_two hs 0 (t (Fin.last (n + 1)) - t (Fin.last n).castSucc)
      (t (Fin.last n).castSucc) (j (Fin.last n).castSucc) (j (Fin.last (n + 1)))
    rw [zero_add, sub_add_cancel] at this
    exact this
  have hCπ : μ {ω | X (t (Fin.last n).castSucc) ω = j (Fin.last n).castSucc} =
      μ {ω | X 0 ω = j (Fin.last n).castSucc} := stat_one hs _ _
  rw [hEB, ← hCB, ← hCπ]
  by_cases h0 : μ {ω | ∀ i : Fin (n + 1), X (t i.castSucc) ω = j i.castSucc} = 0
  · rw [h0, zero_mul, measure_mono_null Set.inter_subset_left h0, zero_mul]
  have hM := hX.markov n t j ht h0
  rw [ProbabilityTheory.cond_apply (meas_cyl hX.measurable _ _),
    ProbabilityTheory.cond_apply (meas_eq hX.measurable _ _)] at hM
  have hCne : μ {ω | X (t (Fin.last n).castSucc) ω = j (Fin.last n).castSucc} ≠ 0 := by
    rw [hCπ]; exact pi_ne_zero hs hX.irreducible _
  exact ennreal_alg h0 (measure_ne_top _ _) hCne (measure_ne_top _ _) hM

lemma factor [IsProbabilityMeasure μ] (hX : StandingAssumptions μ X) (hs : IsStationary μ X) :
    ∀ (n : ℕ) (t : Fin (n + 1) → ℝ) (j : Fin (n + 1) → 𝒮), StrictMono t →
      μ {ω | ∀ i, X (t i) ω = j i} * ∏ i : Fin n, μ {ω | X 0 ω = j i.castSucc} =
        μ {ω | X 0 ω = j 0} *
          ∏ i : Fin n, D2 μ X (t i.succ - t i.castSucc) (j i.castSucc) (j i.succ) := by
  intro n
  induction n with
  | zero =>
    intro t j _
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    rw [show {ω | ∀ i : Fin (0 + 1), X (t i) ω = j i} = {ω | X (t 0) ω = j 0} from by
      ext ω; exact ⟨fun h => h 0, fun h i => by rw [Fin.fin_one_eq_zero i]; exact h⟩]
    exact stat_one hs _ _
  | succ n ih =>
    intro t j ht
    have ih' := ih (fun i => t i.castSucc) (fun i => j i.castSucc)
      (ht.comp Fin.strictMono_castSucc)
    simp only [Fin.castSucc_zero] at ih'
    have hm := markov_step hX hs n t j ht
    calc μ {ω | ∀ i, X (t i) ω = j i} * ∏ i : Fin (n + 1), μ {ω | X 0 ω = j i.castSucc}
        = (μ {ω | ∀ i, X (t i) ω = j i} * μ {ω | X 0 ω = j (Fin.last n).castSucc}) *
            ∏ i : Fin n, μ {ω | X 0 ω = j i.castSucc.castSucc} := by
          rw [Fin.prod_univ_castSucc]; ring
      _ = (μ {ω | ∀ i : Fin (n + 1), X (t i.castSucc) ω = j i.castSucc} *
            ∏ i : Fin n, μ {ω | X 0 ω = j i.castSucc.castSucc}) *
            D2 μ X (t (Fin.last (n + 1)) - t (Fin.last n).castSucc) (j (Fin.last n).castSucc)
              (j (Fin.last (n + 1))) := by rw [hm]; ring
      _ = μ {ω | X 0 ω = j 0} *
            ∏ i : Fin (n + 1), D2 μ X (t i.succ - t i.castSucc) (j i.castSucc) (j i.succ) := by
          rw [ih', Fin.prod_univ_castSucc]
          simp only [Fin.succ_castSucc, Fin.succ_last]
          ring

/-- Under two-point symmetry, cylinder probabilities at strictly increasing times are
invariant under time reversal. -/
lemma rev_mono [IsProbabilityMeasure μ] (hX : StandingAssumptions μ X) (hs : IsStationary μ X)
    (hD : ∀ h > 0, ∀ a b, D2 μ X h a b = D2 μ X h b a) (n : ℕ) (t : Fin (n + 1) → ℝ)
    (j : Fin (n + 1) → 𝒮) (ht : StrictMono t) (τ : ℝ) :
    μ {ω | ∀ i, X (t i) ω = j i} = μ {ω | ∀ i, X (τ - t i) ω = j i} := by
  have ht' : StrictMono (fun i : Fin (n + 1) => τ - t (Fin.rev i)) := fun a b hab => by
    have := ht (Fin.rev_lt_rev.mpr hab); simp only; linarith
  have hset : {ω | ∀ i, X (τ - t i) ω = j i} =
      {ω | ∀ i, X (τ - t (Fin.rev i)) ω = j (Fin.rev i)} := by
    ext ω; simp only [Set.mem_ofPred_eq]
    exact ⟨fun h i => h _, fun h i => by simpa using h (Fin.rev i)⟩
  rw [hset]
  have h1 := factor hX hs n t j ht
  have h2 := factor hX hs n (fun i => τ - t (Fin.rev i)) (fun i => j (Fin.rev i)) ht'
  simp only [Fin.rev_zero] at h2
  have hperm : ∏ i : Fin (n + 1), μ {ω | X 0 ω = j (Fin.rev i)} =
      ∏ i : Fin (n + 1), μ {ω | X 0 ω = j i} :=
    Fintype.prod_equiv Fin.revPerm _ _ (fun i => rfl)
  have hDprod : ∏ i : Fin n, D2 μ X ((τ - t (Fin.rev i.succ)) - (τ - t (Fin.rev i.castSucc)))
        (j (Fin.rev i.castSucc)) (j (Fin.rev i.succ)) =
      ∏ i : Fin n, D2 μ X (t i.succ - t i.castSucc) (j i.castSucc) (j i.succ) := by
    refine Fintype.prod_equiv Fin.revPerm _ _ (fun i => ?_)
    simp only [Fin.revPerm_apply, Fin.rev_succ, Fin.rev_castSucc]
    have e : τ - t (Fin.rev i).castSucc - (τ - t (Fin.rev i).succ) =
        t (Fin.rev i).succ - t (Fin.rev i).castSucc := by ring
    rw [e, hD _ (sub_pos.mpr (ht Fin.castSucc_lt_succ))]
  have hQ0 : ∏ i : Fin (n + 1), μ {ω | X 0 ω = j i} ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => pi_ne_zero hs hX.irreducible _)
  have hQt : ∏ i : Fin (n + 1), μ {ω | X 0 ω = j i} ≠ ∞ :=
    ENNReal.prod_ne_top (fun i _ => measure_ne_top _ _)
  refine (ENNReal.mul_left_inj hQ0 hQt).mp ?_
  calc μ {ω | ∀ i, X (t i) ω = j i} * ∏ i : Fin (n + 1), μ {ω | X 0 ω = j i}
      = (μ {ω | ∀ i, X (t i) ω = j i} * ∏ i : Fin n, μ {ω | X 0 ω = j i.castSucc}) *
          μ {ω | X 0 ω = j (Fin.last n)} := by rw [Fin.prod_univ_castSucc]; ring
    _ = μ {ω | X 0 ω = j (Fin.last n)} *
          (∏ i : Fin n, D2 μ X ((τ - t (Fin.rev i.succ)) - (τ - t (Fin.rev i.castSucc)))
            (j (Fin.rev i.castSucc)) (j (Fin.rev i.succ))) * μ {ω | X 0 ω = j 0} := by
          rw [h1, ← hDprod]; ring
    _ = (μ {ω | ∀ i, X (τ - t (Fin.rev i)) ω = j (Fin.rev i)} *
          ∏ i : Fin n, μ {ω | X 0 ω = j (Fin.rev i.castSucc)}) *
          μ {ω | X 0 ω = j (Fin.rev (Fin.last n))} := by
          rw [h2, Fin.rev_last]
    _ = μ {ω | ∀ i, X (τ - t (Fin.rev i)) ω = j (Fin.rev i)} *
          ∏ i : Fin (n + 1), μ {ω | X 0 ω = j i} := by
          rw [← hperm, Fin.prod_univ_castSucc (f := fun i => μ {ω | X 0 ω = j (Fin.rev i)})]
          ring

/-- consistent time/state lists can be sorted -/
lemma cyl_sort {n : ℕ} (t : Fin n → ℝ) (j : Fin n → 𝒮)
    (hcons : ∀ i i', t i = t i' → j i = j i') :
    ∃ (m : ℕ) (s : Fin m → ℝ) (g : Fin m → 𝒮), StrictMono s ∧
      ∀ (φ : ℝ → ℝ) (ω : Ω), (∀ i, X (φ (t i)) ω = j i) ↔ (∀ l, X (φ (s l)) ω = g l) := by
  set T := Finset.univ.image t
  have hmem : ∀ l, T.orderEmbOfFin rfl l ∈ T := fun l => Finset.orderEmbOfFin_mem T rfl l
  choose idx hidx using fun l => Finset.mem_image.mp (hmem l)
  refine ⟨T.card, T.orderEmbOfFin rfl, fun l => j (idx l), (T.orderEmbOfFin rfl).strictMono, ?_⟩
  intro φ ω
  constructor
  · intro h l
    rw [← (hidx l).2]
    exact h _
  · intro h i
    have : t i ∈ Set.range (T.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_image_of_mem t (Finset.mem_univ i)
    obtain ⟨l, hl⟩ := this
    rw [← hl, h l]
    exact hcons _ _ ((hidx l).2.trans hl)

theorem rev_of_D [IsProbabilityMeasure μ] (hX : StandingAssumptions μ X) (hs : IsStationary μ X)
    (hD : ∀ h > 0, ∀ a b, D2 μ X h a b = D2 μ X h b a) : IsReversible μ X := by
  intro n t τ j
  unfold cylProb
  by_cases hcons : ∀ i i', t i = t i' → j i = j i'
  · obtain ⟨m, s, g, hsm, hg⟩ := cyl_sort (X := X) (Ω := Ω) t j hcons
    have e1 : {ω | ∀ i, X (t i) ω = j i} = {ω | ∀ l, X (s l) ω = g l} := by
      ext ω; exact hg id ω
    have e2 : {ω | ∀ i, X (τ - t i) ω = j i} = {ω | ∀ l, X (τ - s l) ω = g l} := by
      ext ω; exact hg (fun x => τ - x) ω
    rw [e1, e2]
    cases m with
    | zero => congr 1; ext ω; simp
    | succ m => exact rev_mono hX hs hD m s g hsm τ
  · push Not at hcons
    obtain ⟨i, i', hti, hji⟩ := hcons
    have e1 : {ω | ∀ i, X (t i) ω = j i} = ∅ := by
      ext ω; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h; exact hji ((h i).symm.trans (hti ▸ h i'))
    have e2 : {ω | ∀ i, X (τ - t i) ω = j i} = ∅ := by
      ext ω; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h; exact hji ((h i).symm.trans (hti ▸ h i'))
    rw [e1, e2]


end fdd

section sums

variable {Ω 𝒮 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [Countable 𝒮] {μ : Measure Ω} {X : ℝ → Ω → 𝒮}

lemma row_sum (hX : ∀ t, Measurable (X t)) (h : ℝ) (a : 𝒮) :
    ∑' b, D2 μ X h a b = μ {ω | X 0 ω = a} := by
  unfold D2
  rw [← measure_iUnion]
  · congr 1; ext ω; simp
  · intro b b' hbb'
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨-, h1⟩ ⟨-, h2⟩
    exact hbb' ((show X h ω = b from h1).symm.trans h2)
  · intro b; exact (meas_eq hX 0 a).inter (meas_eq hX h b)

lemma col_sum (hX : ∀ t, Measurable (X t)) (hs : IsStationary μ X) (h : ℝ) (b : 𝒮) :
    ∑' a, D2 μ X h a b = μ {ω | X 0 ω = b} := by
  unfold D2
  rw [← measure_iUnion, ← stat_one hs h b]
  · congr 1; ext ω; simp
  · intro a a' haa'
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨h1, -⟩ ⟨h2, -⟩
    exact haa' ((show X 0 ω = a from h1).symm.trans h2)
  · intro a; exact (meas_eq hX 0 a).inter (meas_eq hX h b)

lemma pi_sum [IsProbabilityMeasure μ] (hX : ∀ t, Measurable (X t)) :
    ∑' a, μ {ω | X 0 ω = a} = 1 := by
  rw [← measure_iUnion, ← measure_univ (μ := μ)]
  · congr 1; ext ω; simp
  · intro a a' haa'
    rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h2
    exact haa' ((show X 0 ω = a from h1).symm.trans h2)
  · intro a; exact meas_eq hX 0 a

/-- If `F j * D h k j = F k * D h j k` for a positive finite `F`, then `F` is constant by the
maximum principle, so the two-point law is symmetric. -/
lemma Dsym_of_F [IsProbabilityMeasure μ] (hX : StandingAssumptions μ X) (hs : IsStationary μ X)
    (F : 𝒮 → ℝ≥0∞) (hF : ∀ j, F j ≠ ∞) (hF0 : ∀ j, F j ≠ 0)
    (hsym : ∀ h > 0, ∀ j k, F j * D2 μ X h k j = F k * D2 μ X h j k) :
    ∀ h > 0, ∀ a b, D2 μ X h a b = D2 μ X h b a := by
  have hle : ∀ j k, j ≠ k → F j ≤ F k := by
    intro j k hjk
    obtain ⟨s, τ, hτ, hpos⟩ := hX.irreducible j k hjk
    have hD : D2 μ X τ j k ≠ 0 := by
      have := stat_two hs 0 τ s j k
      rw [zero_add, add_comm] at this
      unfold D2; rw [← this]; exact hpos
    exact max_principle (fun a => μ {ω | X 0 ω = a}) (D2 μ X τ) F
      (row_sum hX.measurable τ) (col_sum hX.measurable hs τ) (fun _ => measure_ne_top _ _)
      (by rw [pi_sum hX.measurable]; exact ENNReal.one_ne_top) hF (hsym τ hτ) j k hD
  have hconst : ∀ j k, F j = F k := fun j k => by
    by_cases h : j = k
    · rw [h]
    · exact le_antisymm (hle j k h) (hle k j (Ne.symm h))
  intro h hh a b
  have := hsym h hh b a
  rw [hconst b a] at this
  exact (ENNReal.mul_right_inj (hF0 a) (hF a)).mp this

end sums

section paths
/-! ### Deterministic structure of a right-continuous path with finitely many jumps -/

variable {𝒮 : Type*}

/-- `s` is a jump point of the path `x` -/
def IsJump (x : ℝ → 𝒮) (s : ℝ) : Prop := ∀ ε > 0, ∃ u ∈ Set.Ioo (s - ε) (s + ε), x u ≠ x s

lemma const_of_noJump (x : ℝ → 𝒮) (hrc : ∀ s : ℝ, ∃ ε > 0, ∀ u ∈ Set.Ico s (s + ε), x u = x s)
    {u v : ℝ} (huv : u ≤ v) (hno : ∀ p ∈ Set.Ioc u v, ¬ IsJump x p) : x v = x u := by
  let f : Set.Icc u v → 𝒮 := fun p => x p
  have hf : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro p
    rcases eq_or_lt_of_le p.2.1 with hp | hp
    · obtain ⟨ε, hε, hcon⟩ := hrc u
      have hev : ∀ᶠ y : Set.Icc u v in 𝓝 p, (y : ℝ) ∈ Set.Ioo (u - 1) (u + ε) :=
        (continuous_subtype_val.tendsto p).eventually
          (Ioo_mem_nhds (by rw [← hp]; linarith) (by rw [← hp]; linarith))
      filter_upwards [hev] with y hy
      show x y = x p
      rw [hcon y ⟨y.2.1, hy.2⟩]; exact congrArg x hp
    · have hpj := hno p ⟨hp, p.2.2⟩
      simp only [IsJump] at hpj
      push Not at hpj
      obtain ⟨ε, hε, hcon⟩ := hpj
      have hev : ∀ᶠ y : Set.Icc u v in 𝓝 p, (y : ℝ) ∈ Set.Ioo ((p : ℝ) - ε) (p + ε) :=
        (continuous_subtype_val.tendsto p).eventually (Ioo_mem_nhds (by linarith) (by linarith))
      filter_upwards [hev] with y hy
      exact hcon y hy
  have : PreconnectedSpace (Set.Icc u v) := Subtype.preconnectedSpace isPreconnected_Icc
  exact hf.apply_eq_of_preconnectedSpace ⟨v, huv, le_rfl⟩ ⟨u, le_rfl, huv⟩

lemma ceil_eq_succ {s h : ℝ} (hh : 0 < h) {m : ℕ} (h1 : (m : ℝ) * h < s) (h2 : s ≤ ((m : ℝ) + 1) * h) :
    ⌈s / h⌉₊ = m + 1 := by
  rw [Nat.ceil_eq_iff (Nat.succ_ne_zero m)]
  refine ⟨?_, ?_⟩
  · rw [Nat.succ_sub_one, lt_div_iff₀ hh]; exact h1
  · rw [div_le_iff₀ hh]; push_cast; exact h2

open Classical in
lemma path_struct (x : ℝ → 𝒮) (hrc : ∀ s : ℝ, ∃ ε > 0, ∀ u ∈ Set.Ico s (s + ε), x u = x s)
    {t : ℝ} (ht : 0 < t)
    (hfin : {s ∈ Set.Icc 0 t | ∀ ε > 0, ∃ u ∈ Set.Ioo (s - ε) (s + ε), x u ≠ x s}.Finite) :
    ∃ (P : Finset (𝒮 × 𝒮)) (r : ℕ), (∀ p ∈ P, p.1 ≠ p.2) ∧
      (∀ N : ℕ, ((Finset.range N).filter
          (fun m : ℕ => x ((m : ℝ) * (t / N)) ≠ x (((m : ℝ) + 1) * (t / N)))).card ≤ r) ∧
      (∀ᶠ N : ℕ in atTop, ∀ m < N, x ((m : ℝ) * (t / N)) ≠ x (((m : ℝ) + 1) * (t / N)) →
          (x ((m : ℝ) * (t / N)), x (((m : ℝ) + 1) * (t / N))) ∈ P) ∧
      (∀ p ∈ P, ∀ᶠ N : ℕ in atTop, ∃ m < N,
          (x ((m : ℝ) * (t / N)), x (((m : ℝ) + 1) * (t / N))) = p) := by
  classical
  set J := hfin.toFinset with hJ
  have memJ : ∀ s, s ∈ J ↔ (s ∈ Set.Icc 0 t ∧ IsJump x s) := fun s => by
    rw [hJ, Set.Finite.mem_toFinset]; rfl
  set K := insert (0 : ℝ) J with hK
  obtain ⟨δ, hδ, hsep⟩ : ∃ δ > 0, ∀ p ∈ K, ∀ q ∈ K, p ≠ q → δ < |p - q| := by
    set Dset := ((K ×ˢ K).filter (fun pq : ℝ × ℝ => pq.1 ≠ pq.2)).image
      (fun pq => |pq.1 - pq.2|)
    have hpos : ∀ d ∈ Dset, 0 < d := by
      intro d hd
      obtain ⟨pq, hpq, rfl⟩ := Finset.mem_image.mp hd
      exact abs_pos.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hpq).2)
    have hmem : ∀ p ∈ K, ∀ q ∈ K, p ≠ q → |p - q| ∈ Dset := fun p hp q hq hpq =>
      Finset.mem_image.mpr ⟨(p, q), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hq⟩, hpq⟩,
        rfl⟩
    rcases Dset.eq_empty_or_nonempty with he | hne
    · refine ⟨1, one_pos, fun p hp q hq hpq => ?_⟩
      have := hmem p hp q hq hpq
      rw [he] at this; simp at this
    · refine ⟨Dset.min' hne / 2, by linarith [hpos _ (Dset.min'_mem hne)], fun p hp q hq hpq => ?_⟩
      have h1 := Dset.min'_le _ (hmem p hp q hq hpq)
      linarith [hpos _ (Dset.min'_mem hne)]
  have noJ : ∀ s ∈ J, ∀ p, p ∈ Set.Icc 0 t → p ≠ s → |p - s| ≤ δ → ¬ IsJump x p := by
    intro s hs p hp hps hd hj
    have := hsep p (Finset.mem_insert_of_mem ((memJ p).mpr ⟨hp, hj⟩)) s
      (Finset.mem_insert_of_mem hs) hps
    linarith
  have spos : ∀ s ∈ J, 0 < s → δ < s := by
    intro s hs hs0
    have := hsep s (Finset.mem_insert_of_mem hs) 0 (Finset.mem_insert_self _ _) hs0.ne'
    rwa [sub_zero, abs_of_pos hs0] at this
  have step_pair : ∀ h : ℝ, 0 < h → h < δ / 2 → ∀ s ∈ J, 0 < s → ∀ a b : ℝ, a < s → s ≤ b →
      b ≤ t → s - h ≤ a → b ≤ s + h → x a = x (s - δ / 2) ∧ x b = x s := by
    intro h hh hhδ s hs hs0 a b has hsb hbt hsa hbs
    have hδs := spos s hs hs0
    refine ⟨?_, ?_⟩
    · refine const_of_noJump x hrc (by linarith) (fun p hp => noJ s hs p ⟨by linarith [hp.1],
        by linarith [hp.2]⟩ (by linarith [hp.2]) ?_)
      rw [abs_le]; constructor <;> linarith [hp.1, hp.2]
    · refine const_of_noJump x hrc hsb (fun p hp => noJ s hs p ⟨by linarith [hp.1],
        by linarith [hp.2]⟩ (by linarith [hp.1]) ?_)
      rw [abs_le]; constructor <;> linarith [hp.1, hp.2]
  have exists_jump : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ t → x b ≠ x a → ∃ s ∈ J, a < s ∧ s ≤ b := by
    intro a b ha hab hb hne
    by_contra hcon
    push Not at hcon
    apply hne
    refine const_of_noJump x hrc hab (fun p hp hj => ?_)
    have hpJ : p ∈ J := (memJ p).mpr ⟨⟨by linarith [hp.1], hp.2.trans hb⟩, hj⟩
    exact absurd hp.2 (not_le.mpr (hcon p hpJ hp.1))
  -- grid facts
  have grid : ∀ N : ℕ, 1 ≤ N → ∀ m : ℕ, m < N →
      0 ≤ (m : ℝ) * (t / N) ∧ (m : ℝ) * (t / N) ≤ ((m : ℝ) + 1) * (t / N) ∧
        ((m : ℝ) + 1) * (t / N) ≤ t ∧ 0 < t / N := by
    intro N hN m hm
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hh : 0 < t / N := div_pos ht hNpos
    have hmN : (m : ℝ) + 1 ≤ N := by exact_mod_cast hm
    refine ⟨by positivity, by nlinarith, ?_, hh⟩
    calc ((m : ℝ) + 1) * (t / N) ≤ N * (t / N) := by nlinarith
      _ = t := by field_simp
  let P : Finset (𝒮 × 𝒮) :=
    ((J.filter (fun s => 0 < s)).image (fun s => (x (s - δ / 2), x s))).filter
      (fun p => p.1 ≠ p.2)
  have hev : ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ t / N < δ / 2 :=
    (eventually_ge_atTop 1).and
      ((tendsto_const_div_atTop_nhds_zero_nat t).eventually (Iio_mem_nhds (by linarith)))
  refine ⟨P, J.card, fun p hp => (Finset.mem_filter.mp hp).2, ?_, ?_, ?_⟩
  · intro N
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp
    · refine (Finset.card_le_card (t := J.image (fun s => ⌈s / (t / N)⌉₊ - 1)) ?_).trans
        Finset.card_image_le
      intro m hm
      rw [Finset.mem_filter, Finset.mem_range] at hm
      obtain ⟨g0, g1, g2, hh⟩ := grid N hN m hm.1
      obtain ⟨s, hs, hs1, hs2⟩ := exists_jump _ _ g0 g1 g2 (Ne.symm hm.2)
      exact Finset.mem_image.mpr ⟨s, hs, by rw [ceil_eq_succ hh hs1 hs2, Nat.add_sub_cancel]⟩
  · filter_upwards [hev] with N hN
    intro m hm hne
    obtain ⟨g0, g1, g2, hh⟩ := grid N hN.1 m hm
    obtain ⟨s, hs, hs1, hs2⟩ := exists_jump _ _ g0 g1 g2 (Ne.symm hne)
    have hs0 : 0 < s := lt_of_le_of_lt g0 hs1
    obtain ⟨e1, e2⟩ := step_pair _ hh hN.2 s hs hs0 _ _ hs1 hs2 g2 (by nlinarith) (by nlinarith)
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨s, Finset.mem_filter.mpr ⟨hs, hs0⟩, ?_⟩, hne⟩
    rw [e1, e2]
  · intro p hp
    obtain ⟨hp1, -⟩ := Finset.mem_filter.mp hp
    obtain ⟨s, hs', rfl⟩ := Finset.mem_image.mp hp1
    obtain ⟨hs, hs0⟩ := Finset.mem_filter.mp hs'
    have hst : s ≤ t := ((memJ s).mp hs).1.2
    filter_upwards [hev] with N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN.1
    have hh : 0 < t / N := div_pos ht hNpos
    set k := ⌈s / (t / N)⌉₊ with hk
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.ceil_pos.mpr
      (div_pos hs0 hh)))
    have hkN : k ≤ N := by
      rw [hk, Nat.ceil_le]
      rw [div_le_iff₀ hh]
      calc s ≤ t := hst
        _ = N * (t / N) := by field_simp
    have hmk : ((k - 1 : ℕ) : ℝ) + 1 = k := by rw [Nat.cast_sub hk1, Nat.cast_one]; ring
    have hlo : ((k - 1 : ℕ) : ℝ) * (t / N) < s := by
      have := Nat.ceil_lt_add_one (div_pos hs0 hh).le
      rw [← hk] at this
      have h2 : ((k - 1 : ℕ) : ℝ) < s / (t / N) := by linarith
      rwa [lt_div_iff₀ hh] at h2
    have hhi : s ≤ (((k - 1 : ℕ) : ℝ) + 1) * (t / N) := by
      rw [hmk]
      have := Nat.le_ceil (s / (t / N))
      rw [← hk] at this
      rwa [div_le_iff₀ hh] at this
    have hkt : (((k - 1 : ℕ) : ℝ) + 1) * (t / N) ≤ t := by
      rw [hmk]
      calc (k : ℝ) * (t / N) ≤ N * (t / N) := by
            have : (k : ℝ) ≤ N := by exact_mod_cast hkN
            nlinarith
        _ = t := by field_simp
    refine ⟨k - 1, by omega, ?_⟩
    obtain ⟨e1, e2⟩ := step_pair _ hh hN.2 s hs hs0 _ _ hlo hhi hkt (by nlinarith) (by nlinarith)
    rw [e1, e2]

end paths

section positivity

variable {Ω 𝒮 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [Countable 𝒮] {μ : Measure Ω} {X : ℝ → Ω → 𝒮}

/-- Almost surely, a step `a → b` that the skeletons of mesh `t/N` show for all large `N` has a
positive rate. -/
lemma ae_pos_steps [IsProbabilityMeasure μ] (hX : StandingAssumptions μ X) (hs : IsStationary μ X)
    {q : 𝒮 → 𝒮 → ℝ≥0} (hq : IsTransitionRate μ X q) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂μ, ∀ a b : 𝒮, a ≠ b →
      (∀ᶠ N : ℕ in atTop, ∃ m < N, X ((m : ℝ) * (t / N)) ω = a ∧
        X (((m : ℝ) + 1) * (t / N)) ω = b) → 0 < q a b := by
  rw [ae_all_iff]; intro a
  rw [ae_all_iff]; intro b
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ q a b) with hqab | hqab
  swap
  · exact Eventually.of_forall (fun _ _ _ => hqab)
  by_cases hab : a = b
  · exact Eventually.of_forall (fun _ h => absurd hab h)
  set E : ℕ → Set Ω := fun N => ⋃ m ∈ Finset.range N,
    ({ω | X ((m : ℝ) * (t / N)) ω = a} ∩ {ω | X (((m : ℝ) + 1) * (t / N)) ω = b}) with hE
  -- the bound `μ (E N) ≤ g N → 0`
  set g : ℕ → ℝ≥0∞ := fun N =>
    ENNReal.ofReal (t * ((D2 μ X (t / N) a b).toReal / (t / N))) with hg
  have hbound : ∀ N : ℕ, 1 ≤ N → μ (E N) ≤ g N := by
    intro N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    refine (measure_biUnion_finset_le _ _).trans ?_
    have hterm : ∀ m ∈ Finset.range N, μ ({ω | X ((m : ℝ) * (t / N)) ω = a} ∩
        {ω | X (((m : ℝ) + 1) * (t / N)) ω = b}) = D2 μ X (t / N) a b := by
      intro m _
      have := stat_two hs 0 (t / N) ((m : ℝ) * (t / N)) a b
      rw [zero_add, show t / N + (m : ℝ) * (t / N) = ((m : ℝ) + 1) * (t / N) by ring] at this
      exact this
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hg]
    have hfin : D2 μ X (t / N) a b ≠ ∞ := measure_ne_top _ _
    rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    apply le_of_eq; congr 1
    field_simp
  have hlim : Tendsto g atTop (𝓝 0) := by
    have h1 := joint_rate hX hs hq hab
    rw [← hqab, NNReal.coe_zero, mul_zero] at h1
    have h2 : Tendsto (fun N : ℕ => t / N) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_const_div_atTop_nhds_zero_nat t, ?_⟩
      filter_upwards [eventually_ge_atTop 1] with N hN
      exact div_pos ht (by exact_mod_cast hN)
    have h3 := ((h1.comp h2).const_mul t)
    rw [mul_zero] at h3
    have h4 := ENNReal.tendsto_ofReal h3
    rw [ENNReal.ofReal_zero] at h4
    exact h4
  have hnull : μ (⋃ n : ℕ, ⋂ N ≥ n, E N) = 0 := by
    refine measure_iUnion_null (fun n => ?_)
    refine le_antisymm (ge_of_tendsto hlim ?_) zero_le
    filter_upwards [eventually_ge_atTop n, eventually_ge_atTop 1] with M hM hM1
    exact (measure_mono (Set.biInter_subset_of_mem hM)).trans (hbound M hM1)
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) hnull
  simp only [Set.mem_ofPred_eq, Classical.not_imp] at hω
  obtain ⟨-, hev, hneg⟩ := hω
  obtain ⟨n, hn⟩ := eventually_atTop.mp hev
  refine Set.mem_iUnion.mpr ⟨n, Set.mem_iInter₂.mpr (fun N hN => ?_)⟩
  obtain ⟨m, hm, h1, h2⟩ := hn N hN
  exact Set.mem_biUnion (Finset.mem_range.mpr hm) ⟨h1, h2⟩

/-- The positive-rate graph is connected. -/
lemma connected [IsProbabilityMeasure μ] (hX : StandingAssumptions μ X) (hs : IsStationary μ X)
    {q : 𝒮 → 𝒮 → ℝ≥0} (hq : IsTransitionRate μ X q) (a b : 𝒮) :
    Relation.ReflTransGen (fun x y => 0 < q x y) a b := by
  by_cases hab : a = b
  · rw [hab]
  obtain ⟨s, τ, hτ, hpos⟩ := hX.irreducible a b hab
  have hG : μ ({ω | X 0 ω = a} ∩ {ω | X τ ω = b}) ≠ 0 := by
    have := stat_two hs 0 τ s a b
    rw [zero_add, add_comm] at this
    rw [← this]; exact hpos
  obtain ⟨ω, ⟨h0, hτb⟩, hreg, hposω⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hG
      (ae_restrict_of_ae (hX.regular.and (ae_pos_steps hX hs hq hτ)))
  obtain ⟨P, r, hPd, -, hii, hiii⟩ := path_struct (fun u => X u ω) hreg.1 hτ (hreg.2 0 τ)
  have hPpos : ∀ p ∈ P, 0 < q p.1 p.2 := by
    intro p hp
    refine hposω p.1 p.2 (hPd p hp) ?_
    filter_upwards [hiii p hp] with N ⟨m, hm, he⟩
    exact ⟨m, hm, (Prod.ext_iff.mp he).1, (Prod.ext_iff.mp he).2⟩
  obtain ⟨N, hN, hN1⟩ := (hii.and (eventually_ge_atTop 1)).exists
  have key : ∀ m ≤ N, Relation.ReflTransGen (fun x y => 0 < q x y) a
      (X ((m : ℝ) * (τ / N)) ω) := by
    intro m
    induction m with
    | zero =>
      intro _
      have e0 : X (((0 : ℕ) : ℝ) * (τ / N)) ω = a := by simpa using h0
      rw [e0]
    | succ m ih =>
      intro hm
      have ih' := ih (by omega)
      by_cases hst : X ((m : ℝ) * (τ / N)) ω = X (((m : ℝ) + 1) * (τ / N)) ω
      · push_cast; rw [← hst]; exact ih'
      · push_cast
        exact ih'.tail (hPpos _ (hN m (by omega) hst))
  have := key N le_rfl
  have hNpos : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rwa [show (N : ℝ) * (τ / N) = τ by field_simp, hτb] at this

end positivity

section fatou
/-! ### The Fatou skeleton inequality -/

variable {Ω 𝒮 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [Countable 𝒮] {μ : Measure Ω} {X : ℝ → Ω → 𝒮}

open Classical in
/-- one-step reversal ratio `D h b a / D h a b` (`1` on the diagonal) -/
noncomputable def rho (μ : Measure Ω) (X : ℝ → Ω → 𝒮) (h : ℝ) (a b : 𝒮) : ℝ≥0∞ :=
  if a = b then 1 else D2 μ X h b a / D2 μ X h a b

/-- probability of a skeleton path -/
def Pk (μ : Measure Ω) (X : ℝ → Ω → 𝒮) (N : ℕ) (h : ℝ) (γ : Fin (N + 1) → 𝒮) : ℝ≥0∞ :=
  μ {ω | ∀ i : Fin (N + 1), X (((i : ℕ) : ℝ) * h) ω = γ i}

/-- product of the reversal ratios along a skeleton path -/
noncomputable def Phi (μ : Measure Ω) (X : ℝ → Ω → 𝒮) (N : ℕ) (h : ℝ) (γ : Fin (N + 1) → 𝒮) :
    ℝ≥0∞ :=
  ∏ i : Fin N, rho μ X h (γ i.castSucc) (γ i.succ)

lemma path_ratio [IsProbabilityMeasure μ] (hX : StandingAssumptions μ X) (hs : IsStationary μ X)
    (N : ℕ) {h : ℝ} (hh : 0 < h) (γ : Fin (N + 1) → 𝒮) (hP : Pk μ X N h γ ≠ 0) :
    Phi μ X N h γ * Pk μ X N h γ = Pk μ X N h (fun i => γ (Fin.rev i)) := by
  have hπ0 : ∀ a, μ {ω | X 0 ω = a} ≠ 0 := fun a => pi_ne_zero hs hX.irreducible a
  have hπT : ∀ a, μ {ω | X 0 ω = a} ≠ ∞ := fun a => measure_ne_top _ _
  have htm : StrictMono (fun i : Fin (N + 1) => ((i : ℕ) : ℝ) * h) := fun i i' hii =>
    mul_lt_mul_of_pos_right (by exact_mod_cast hii) hh
  have hdiff : ∀ i : Fin N, (((i.succ : ℕ) : ℝ) * h - ((i.castSucc : ℕ) : ℝ) * h) = h := by
    intro i; simp only [Fin.val_succ, Fin.val_castSucc]; push_cast; ring
  have hf := factor hX hs N _ γ htm
  have hr := factor hX hs N _ (fun i => γ (Fin.rev i)) htm
  simp only [hdiff] at hf hr
  simp only [Fin.rev_castSucc, Fin.rev_succ, Fin.rev_zero] at hr
  have e1 : (∏ i : Fin N, μ {ω | X 0 ω = γ (Fin.rev i).succ}) =
      ∏ i : Fin N, μ {ω | X 0 ω = γ i.succ} :=
    Fintype.prod_equiv Fin.revPerm _ _ (fun i => rfl)
  have e2 : (∏ i : Fin N, D2 μ X h (γ (Fin.rev i).succ) (γ (Fin.rev i).castSucc)) =
      ∏ i : Fin N, D2 μ X h (γ i.succ) (γ i.castSucc) :=
    Fintype.prod_equiv Fin.revPerm _ _ (fun i => rfl)
  rw [e1, e2] at hr
  have h1 : (∏ i, μ {ω | X 0 ω = γ i}) =
      μ {ω | X 0 ω = γ 0} * ∏ i : Fin N, μ {ω | X 0 ω = γ i.succ} := Fin.prod_univ_succ _
  have h2 : (∏ i, μ {ω | X 0 ω = γ i}) =
      (∏ i : Fin N, μ {ω | X 0 ω = γ i.castSucc}) * μ {ω | X 0 ω = γ (Fin.last N)} :=
    Fin.prod_univ_castSucc _
  have hπ : μ {ω | X 0 ω = γ 0} * ∏ i : Fin N, μ {ω | X 0 ω = γ i.succ} =
      μ {ω | X 0 ω = γ (Fin.last N)} * ∏ i : Fin N, μ {ω | X 0 ω = γ i.castSucc} :=
    (h1.symm.trans h2).trans (mul_comm _ _)
  have hDf : ∀ i : Fin N, D2 μ X h (γ i.castSucc) (γ i.succ) ≠ 0 := by
    have hne : μ {ω | X 0 ω = γ 0} * ∏ i : Fin N, D2 μ X h (γ i.castSucc) (γ i.succ) ≠ 0 := by
      rw [← hf]
      exact mul_ne_zero hP (Finset.prod_ne_zero_iff.mpr (fun i _ => hπ0 _))
    intro i
    exact Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hne) i (Finset.mem_univ _)
  have hPhi : Phi μ X N h γ * ∏ i : Fin N, D2 μ X h (γ i.castSucc) (γ i.succ) =
      ∏ i : Fin N, D2 μ X h (γ i.succ) (γ i.castSucc) := by
    unfold Phi
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    unfold rho
    split_ifs with he
    · rw [one_mul, he]
    · exact ENNReal.div_mul_cancel (hDf i) (measure_ne_top _ _)
  have hC0 : μ {ω | X 0 ω = γ (Fin.last N)} * ∏ i : Fin N, μ {ω | X 0 ω = γ i.castSucc} ≠ 0 :=
    mul_ne_zero (hπ0 _) (Finset.prod_ne_zero_iff.mpr (fun i _ => hπ0 _))
  have hCT : μ {ω | X 0 ω = γ (Fin.last N)} * ∏ i : Fin N, μ {ω | X 0 ω = γ i.castSucc} ≠ ∞ :=
    ENNReal.mul_ne_top (hπT _) (ENNReal.prod_ne_top (fun i _ => hπT _))
  refine (ENNReal.mul_left_inj hC0 hCT).mp ?_
  have hf' : Pk μ X N h γ * ∏ i : Fin N, μ {ω | X 0 ω = γ i.castSucc} =
      μ {ω | X 0 ω = γ 0} * ∏ i : Fin N, D2 μ X h (γ i.castSucc) (γ i.succ) := hf
  have hr' : Pk μ X N h (fun i => γ (Fin.rev i)) * ∏ i : Fin N, μ {ω | X 0 ω = γ i.succ} =
      μ {ω | X 0 ω = γ (Fin.last N)} * ∏ i : Fin N, D2 μ X h (γ i.succ) (γ i.castSucc) := hr
  calc Phi μ X N h γ * Pk μ X N h γ *
        (μ {ω | X 0 ω = γ (Fin.last N)} * ∏ i : Fin N, μ {ω | X 0 ω = γ i.castSucc})
      = μ {ω | X 0 ω = γ (Fin.last N)} * (Phi μ X N h γ *
          (Pk μ X N h γ * ∏ i : Fin N, μ {ω | X 0 ω = γ i.castSucc})) := by ring
    _ = μ {ω | X 0 ω = γ (Fin.last N)} * μ {ω | X 0 ω = γ 0} *
          (Phi μ X N h γ * ∏ i : Fin N, D2 μ X h (γ i.castSucc) (γ i.succ)) := by
        rw [hf']; ring
    _ = μ {ω | X 0 ω = γ 0} * (μ {ω | X 0 ω = γ (Fin.last N)} *
          ∏ i : Fin N, D2 μ X h (γ i.succ) (γ i.castSucc)) := by rw [hPhi]; ring
    _ = μ {ω | X 0 ω = γ 0} * (Pk μ X N h (fun i => γ (Fin.rev i)) *
          ∏ i : Fin N, μ {ω | X 0 ω = γ i.succ}) := by rw [hr']
    _ = Pk μ X N h (fun i => γ (Fin.rev i)) *
          (μ {ω | X 0 ω = γ (Fin.last N)} * ∏ i : Fin N, μ {ω | X 0 ω = γ i.castSucc}) := by
        rw [← hπ]; ring

lemma lint_paths (hX : ∀ t, Measurable (X t)) {n : ℕ} (s : Fin n → ℝ)
    (G : (Fin n → 𝒮) → ℝ≥0∞) :
    ∫⁻ ω, G (fun i => X (s i) ω) ∂μ = ∑' γ, G γ * μ {ω | ∀ i, X (s i) ω = γ i} := by
  have hS : Measurable (fun ω i => X (s i) ω) := measurable_pi_lambda _ (fun i => hX (s i))
  rw [← lintegral_map (measurable_of_countable G) hS, lintegral_countable']
  refine tsum_congr (fun γ => ?_)
  rw [Measure.map_apply hS (measurableSet_singleton γ)]
  congr 2
  ext ω
  simp [funext_iff]

lemma rho_tendsto [IsProbabilityMeasure μ] (hX : StandingAssumptions μ X) (hs : IsStationary μ X)
    {q : 𝒮 → 𝒮 → ℝ≥0} (hq : IsTransitionRate μ X q) (f : 𝒮 → ℝ) (hf : ∀ a, 0 < f a)
    (hfq : ∀ a b, (μ {ω | X 0 ω = b}).toReal * q b a * f a =
      (μ {ω | X 0 ω = a}).toReal * q a b * f b)
    {a b : 𝒮} (hab : a ≠ b) (hqab : 0 < q a b) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N : ℕ => rho μ X (t / N) a b) atTop (𝓝 (ENNReal.ofReal (f b / f a))) := by
  have hA := joint_rate hX hs hq hab
  have hB := joint_rate hX hs hq (Ne.symm hab)
  have hα : 0 < (μ {ω | X 0 ω = a}).toReal * q a b :=
    mul_pos (pi_toReal_pos hs hX.irreducible a) (by exact_mod_cast hqab)
  have hτ : Tendsto (fun N : ℕ => t / N) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_const_div_atTop_nhds_zero_nat t, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact div_pos ht (by exact_mod_cast hN)
  have hlim : (μ {ω | X 0 ω = b}).toReal * q b a / ((μ {ω | X 0 ω = a}).toReal * q a b) =
      f b / f a := by
    rw [div_eq_div_iff hα.ne' (hf a).ne']
    linarith [hfq a b]
  have hR : Tendsto (fun τ : ℝ => (D2 μ X τ b a).toReal / (D2 μ X τ a b).toReal) (𝓝[>] 0)
      (𝓝 (f b / f a)) := by
    rw [← hlim]
    refine (hB.div hA hα.ne').congr' ?_
    filter_upwards [self_mem_nhdsWithin] with τ hτ'
    exact div_div_div_cancel_right₀ (ne_of_gt hτ') _ _
  have hpos : ∀ᶠ τ in 𝓝[>] (0 : ℝ), 0 < (D2 μ X τ a b).toReal := by
    filter_upwards [hA.eventually (lt_mem_nhds hα), self_mem_nhdsWithin] with τ h1 h2
    exact (div_pos_iff_of_pos_right h2).mp h1
  refine (ENNReal.tendsto_ofReal (hR.comp hτ)).congr' ?_
  filter_upwards [hτ.eventually hpos] with N hN
  simp only [Function.comp_apply, rho, if_neg hab]
  rw [ENNReal.ofReal_div_of_pos hN,
    ENNReal.ofReal_toReal (a := D2 μ X (t / N) b a) (measure_ne_top _ _),
    ENNReal.ofReal_toReal (a := D2 μ X (t / N) a b) (measure_ne_top _ _)]

lemma telescope (f : 𝒮 → ℝ) (hf : ∀ a, 0 < f a) (y : ℕ → 𝒮) (N : ℕ) :
    ∏ m ∈ Finset.range N, ENNReal.ofReal (f (y (m + 1)) / f (y m)) =
      ENNReal.ofReal (f (y N) / f (y 0)) := by
  induction N with
  | zero => simp [div_self (hf (y 0)).ne']
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, ← ENNReal.ofReal_mul (div_pos (hf _) (hf _)).le]
    congr 1
    rw [div_mul_div_comm, mul_comm (f (y n)), mul_div_mul_right _ _ (hf (y n)).ne']

lemma Gpair (f : 𝒮 → ℝ) (hf : ∀ a, 0 < f a) (a b : 𝒮) :
    ENNReal.ofReal (f b / f a) * ENNReal.ofReal (f a / f b) = 1 := by
  rw [← ENNReal.ofReal_mul (div_pos (hf b) (hf a)).le]
  have ha := (hf a).ne'
  have hb := (hf b).ne'
  rw [div_mul_div_comm, mul_comm (f b) (f a), div_self (mul_ne_zero ha hb), ENNReal.ofReal_one]

lemma ae_liminf [IsProbabilityMeasure μ] (hX : StandingAssumptions μ X) (hs : IsStationary μ X)
    {q : 𝒮 → 𝒮 → ℝ≥0} (hq : IsTransitionRate μ X q) (f : 𝒮 → ℝ) (hf : ∀ a, 0 < f a)
    (hfq : ∀ a b, (μ {ω | X 0 ω = b}).toReal * q b a * f a =
      (μ {ω | X 0 ω = a}).toReal * q a b * f b)
    {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂μ, ENNReal.ofReal (f (X t ω) / f (X 0 ω)) ≤
      liminf (fun N : ℕ => ∏ m ∈ Finset.range N,
        rho μ X (t / N) (X ((m : ℝ) * (t / N)) ω) (X (((m : ℝ) + 1) * (t / N)) ω)) atTop := by
  classical
  filter_upwards [hX.regular, ae_pos_steps hX hs hq ht] with ω hreg hpos
  obtain ⟨hrc, hfin⟩ := hreg
  obtain ⟨P, r, hPne, hcard, hev, hreal⟩ := path_struct (fun s => X s ω) hrc ht (hfin 0 t)
  have hqP : ∀ p ∈ P, 0 < q p.1 p.2 := by
    intro p hp
    refine hpos p.1 p.2 (hPne p hp) ((hreal p hp).mono (fun N hN => ?_))
    obtain ⟨m, hm, he⟩ := hN
    subst he
    exact ⟨m, hm, rfl, rfl⟩
  set G : 𝒮 → 𝒮 → ℝ≥0∞ := fun a b => ENNReal.ofReal (f b / f a) with hG
  set c : ℕ → 𝒮 × 𝒮 → ℝ≥0∞ := fun N p => rho μ X (t / N) p.1 p.2 * G p.2 p.1 with hc
  set M : ℕ → ℝ≥0∞ := fun N => ∏ p ∈ P, min 1 (c N p) with hM
  have hGG : ∀ a b, G a b * G b a = 1 := fun a b => Gpair f hf a b
  have hM1 : ∀ N, M N ≤ 1 := fun N => Finset.prod_le_one' (fun p _ => min_le_left _ _)
  have hMp : ∀ N, ∀ p ∈ P, M N ≤ min 1 (c N p) := by
    intro N p hp
    calc M N = min 1 (c N p) * ∏ x ∈ P.erase p, min 1 (c N x) :=
          (Finset.mul_prod_erase P (fun x => min 1 (c N x)) hp).symm
      _ ≤ min 1 (c N p) * 1 :=
          mul_le_mul' le_rfl (Finset.prod_le_one' (fun x _ => min_le_left _ _))
      _ = min 1 (c N p) := mul_one _
  have hlow : ∀ᶠ N : ℕ in atTop, G (X 0 ω) (X t ω) * M N ^ r ≤
      ∏ m ∈ Finset.range N, rho μ X (t / N) (X ((m : ℝ) * (t / N)) ω)
        (X (((m : ℝ) + 1) * (t / N)) ω) := by
    filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1
    set y : ℕ → 𝒮 := fun m => X ((m : ℝ) * (t / N)) ω with hy
    have hy1 : ∀ m : ℕ, X (((m : ℝ) + 1) * (t / N)) ω = y (m + 1) := by
      intro m; simp [hy]
    have hy0 : y 0 = X 0 ω := by simp [hy]
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hN1)
    have hyN : y N = X t ω := by
      simp only [hy]
      rw [show (N : ℝ) * (t / N) = t by field_simp]
    simp only [hy1]
    calc G (X 0 ω) (X t ω) * M N ^ r
        ≤ G (y 0) (y N) * M N ^ ((Finset.range N).filter (fun m => y m ≠ y (m + 1))).card := by
          rw [hy0, hyN]
          refine mul_le_mul' le_rfl (pow_le_pow_right_of_le_one' (hM1 N) ?_)
          have := hcard N
          simp only [hy1] at this
          exact this
      _ = (∏ m ∈ Finset.range N, G (y m) (y (m + 1))) *
            ∏ m ∈ Finset.range N, (if y m = y (m + 1) then 1 else M N) := by
          rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
          congr 1
          exact (telescope f hf y N).symm
      _ = ∏ m ∈ Finset.range N, (G (y m) (y (m + 1)) * if y m = y (m + 1) then 1 else M N) :=
          (Finset.prod_mul_distrib).symm
      _ ≤ ∏ m ∈ Finset.range N, rho μ X (t / N) (y m) (y (m + 1)) := by
          refine Finset.prod_le_prod' (fun m hm => ?_)
          by_cases he : y m = y (m + 1)
          · rw [if_pos he, he, mul_one]
            simp only [hG, rho, if_true, div_self (hf _).ne', ENNReal.ofReal_one, le_refl]
          · rw [if_neg he]
            have hmem : (y m, y (m + 1)) ∈ P := by
              have := hN m (Finset.mem_range.mp hm)
              simp only [hy1] at this
              exact this he
            calc G (y m) (y (m + 1)) * M N ≤ G (y m) (y (m + 1)) * c N (y m, y (m + 1)) :=
                  mul_le_mul' le_rfl ((hMp N _ hmem).trans (min_le_right _ _))
              _ = G (y m) (y (m + 1)) * (rho μ X (t / N) (y m) (y (m + 1)) *
                    G (y (m + 1)) (y m)) := rfl
              _ = rho μ X (t / N) (y m) (y (m + 1)) := by
                  rw [mul_comm, mul_assoc, hGG, mul_one]
  have hc1 : ∀ p ∈ P, Tendsto (fun N => c N p) atTop (𝓝 1) := by
    intro p hp
    have h1 := rho_tendsto hX hs hq f hf hfq (hPne p hp) (hqP p hp) ht
    have h2 := ENNReal.Tendsto.mul_const (b := G p.2 p.1) h1 (Or.inr ENNReal.ofReal_ne_top)
    have h3 : ENNReal.ofReal (f p.2 / f p.1) * G p.2 p.1 = 1 := hGG p.1 p.2
    rw [h3] at h2
    exact h2
  have hMlim : Tendsto M atTop (𝓝 1) := by
    have := ENNReal.tendsto_finsetProd_of_ne_top P (f := fun p N => min 1 (c N p))
      (a := fun _ => 1)
      (fun p hp => by
        simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ≥0∞)) atTop (𝓝 1)).min
          (hc1 p hp))
      (fun _ _ => ENNReal.one_ne_top)
    simpa [hM] using this
  have hlim : Tendsto (fun N => G (X 0 ω) (X t ω) * M N ^ r) atTop
      (𝓝 (G (X 0 ω) (X t ω))) := by
    have h1 : Tendsto (fun N => M N ^ r) atTop (𝓝 1) := by
      have h := ((ENNReal.continuous_pow r).tendsto 1).comp hMlim
      rw [one_pow] at h
      exact h
    simpa using ENNReal.Tendsto.const_mul (a := G (X 0 ω) (X t ω)) h1
      (Or.inr ENNReal.ofReal_ne_top)
  calc G (X 0 ω) (X t ω) = liminf (fun N => G (X 0 ω) (X t ω) * M N ^ r) atTop :=
        hlim.liminf_eq.symm
    _ ≤ _ := liminf_le_liminf hlow

lemma half [IsProbabilityMeasure μ] (hX : StandingAssumptions μ X) (hs : IsStationary μ X)
    {q : 𝒮 → 𝒮 → ℝ≥0} (hq : IsTransitionRate μ X q) (f : 𝒮 → ℝ) (hf : ∀ a, 0 < f a)
    (hfq : ∀ a b, (μ {ω | X 0 ω = b}).toReal * q b a * f a =
      (μ {ω | X 0 ω = a}).toReal * q a b * f b)
    {t : ℝ} (ht : 0 < t) (j k : 𝒮) :
    ENNReal.ofReal (f k / f j) * D2 μ X t j k ≤ D2 μ X t k j := by
  classical
  set E : Set Ω := {ω | X 0 ω = j} ∩ {ω | X t ω = k} with hE
  have hEm : MeasurableSet E := (meas_eq hX.measurable 0 j).inter (meas_eq hX.measurable t k)
  let S : (N : ℕ) → Ω → Fin (N + 1) → 𝒮 := fun N ω i => X (((i : ℕ) : ℝ) * (t / N)) ω
  let G : (N : ℕ) → (Fin (N + 1) → 𝒮) → ℝ≥0∞ := fun N γ =>
    if γ 0 = j ∧ γ (Fin.last N) = k then Phi μ X N (t / N) γ else 0
  have hSm : ∀ N, Measurable (S N) :=
    fun N => measurable_pi_lambda _ (fun i => hX.measurable _)
  have hgm : ∀ N, Measurable (fun ω => G N (S N ω)) :=
    fun N => (measurable_of_countable (G N)).comp (hSm N)
  have hlast : ∀ N : ℕ, 1 ≤ N → ((N : ℕ) : ℝ) * (t / N) = t := by
    intro N hN
    have : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hN)
    field_simp
  have hint : ∀ N : ℕ, 1 ≤ N → ∫⁻ ω, G N (S N ω) ∂μ ≤ D2 μ X t k j := by
    intro N hN
    have hh : 0 < t / N := div_pos ht (by exact_mod_cast hN)
    let H : (Fin (N + 1) → 𝒮) → ℝ≥0∞ := fun γ =>
      if γ (Fin.last N) = j ∧ γ 0 = k then 1 else 0
    let e : (Fin (N + 1) → 𝒮) ≃ (Fin (N + 1) → 𝒮) :=
      ⟨fun γ i => γ (Fin.rev i), fun γ i => γ (Fin.rev i),
        fun γ => by funext i; simp, fun γ => by funext i; simp⟩
    calc ∫⁻ ω, G N (S N ω) ∂μ = ∑' γ, G N γ * Pk μ X N (t / N) γ :=
          lint_paths (μ := μ) hX.measurable (fun i : Fin (N + 1) => ((i : ℕ) : ℝ) * (t / N)) (G N)
      _ ≤ ∑' γ, H (e γ) * Pk μ X N (t / N) (e γ) := by
          refine ENNReal.tsum_le_tsum (fun γ => ?_)
          by_cases hγ : γ 0 = j ∧ γ (Fin.last N) = k
          · have hH : H (e γ) = 1 := by simp [H, e, hγ.1, hγ.2]
            simp only [G, if_pos hγ]
            rw [hH, one_mul]
            by_cases hP : Pk μ X N (t / N) γ = 0
            · rw [hP, mul_zero]; exact zero_le
            · exact (path_ratio hX hs N hh γ hP).le
          · simp only [G, if_neg hγ, zero_mul]; exact zero_le
      _ = ∑' γ, H γ * Pk μ X N (t / N) γ := e.tsum_eq (fun γ => H γ * Pk μ X N (t / N) γ)
      _ = ∫⁻ ω, H (S N ω) ∂μ :=
          (lint_paths (μ := μ) hX.measurable (fun i : Fin (N + 1) => ((i : ℕ) : ℝ) * (t / N)) H).symm
      _ = D2 μ X t k j := by
          have hfun : (fun ω => H (S N ω)) =
              Set.indicator ({ω | X 0 ω = k} ∩ {ω | X t ω = j}) 1 := by
            funext ω
            simp only [H, S, Set.indicator, Set.mem_inter_iff, Set.mem_ofPred_eq, Fin.val_last,
              Fin.val_zero, Nat.cast_zero, zero_mul, hlast N hN, Pi.one_apply]
            by_cases h1 : X 0 ω = k <;> by_cases h2 : X t ω = j <;> simp [h1, h2]
          rw [hfun, lintegral_indicator_one
            ((meas_eq hX.measurable 0 k).inter (meas_eq hX.measurable t j))]
          rfl
  have hpt : ∀ᵐ ω ∂μ, E.indicator (fun _ => ENNReal.ofReal (f k / f j)) ω ≤
      liminf (fun N => G N (S N ω)) atTop := by
    filter_upwards [ae_liminf hX hs hq f hf hfq ht] with ω hω
    by_cases hωE : ω ∈ E
    · rw [Set.indicator_of_mem hωE]
      obtain ⟨h1, h2⟩ := hωE
      have h1' : X 0 ω = j := h1
      have h2' : X t ω = k := h2
      rw [h1', h2'] at hω
      refine hω.trans (le_of_eq (liminf_congr ?_))
      filter_upwards [eventually_ge_atTop 1] with N hN
      simp only [G, S, Fin.val_zero, Fin.val_last, Nat.cast_zero, zero_mul, hlast N hN, h1', h2',
        and_self, if_true, Phi, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
      exact (Fin.prod_univ_eq_prod_range (fun m : ℕ => rho μ X (t / N) (X ((m : ℝ) * (t / N)) ω)
        (X (((m : ℝ) + 1) * (t / N)) ω)) N).symm
    · rw [Set.indicator_of_notMem hωE]; exact zero_le
  calc ENNReal.ofReal (f k / f j) * D2 μ X t j k
      = ∫⁻ ω, E.indicator (fun _ => ENNReal.ofReal (f k / f j)) ω ∂μ := by
        rw [lintegral_indicator_const hEm]; rfl
    _ ≤ ∫⁻ ω, liminf (fun N => G N (S N ω)) atTop ∂μ := lintegral_mono_ae hpt
    _ ≤ liminf (fun N => ∫⁻ ω, G N (S N ω) ∂μ) atTop := lintegral_liminf_le hgm
    _ ≤ liminf (fun _ : ℕ => D2 μ X t k j) atTop := liminf_le_liminf (by
        filter_upwards [eventually_ge_atTop 1] with N hN
        exact hint N hN)
    _ = D2 μ X t k j := liminf_const _

end fatou

end KKCrit

open KellyKolmogorov MeasureTheory NNReal in
theorem solution {Ω 𝒮 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒮]
    [MeasurableSingletonClass 𝒮] [Countable 𝒮] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℝ → Ω → 𝒮) (q : 𝒮 → 𝒮 → ℝ≥0) (hX : StandingAssumptions μ X)
    (hstat : IsStationary μ X) (hq : IsTransitionRate μ X q) :
    IsReversible μ X ↔ KolmogorovCycle q := by
  refine ⟨fun hr => KKCrit.forward hX hstat hq hr, fun hK => ?_⟩
  have hΩ : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  obtain ⟨m, hm0, hm⟩ := KKCrit.exists_db q hK (KKCrit.connected hX hstat hq) (X 0 hΩ.some)
  set f : 𝒮 → ℝ := fun a => (μ {ω | X 0 ω = a}).toReal / m a with hfdef
  have hf : ∀ a, 0 < f a :=
    fun a => div_pos (KKCrit.pi_toReal_pos hstat hX.irreducible a) (hm0 a)
  have hfq : ∀ a b, (μ {ω | X 0 ω = b}).toReal * q b a * f a =
      (μ {ω | X 0 ω = a}).toReal * q a b * f b := by
    intro a b
    have h1 := hm a b
    have ha := (hm0 a).ne'
    have hb := (hm0 b).ne'
    simp only [hfdef]
    rw [mul_div_assoc', mul_div_assoc', div_eq_div_iff ha hb]
    linear_combination (-((μ {ω | X 0 ω = a}).toReal * (μ {ω | X 0 ω = b}).toReal)) * h1
  set F : 𝒮 → ℝ≥0∞ := fun a => ENNReal.ofReal (f a) with hF
  have hle : ∀ t > 0, ∀ j k, F k * KKCrit.D2 μ X t j k ≤ F j * KKCrit.D2 μ X t k j := by
    intro t ht j k
    have h := KKCrit.half hX hstat hq f hf hfq ht j k
    have hj := (hf j).ne'
    have hFk : F k = F j * ENNReal.ofReal (f k / f j) := by
      simp only [hF]
      rw [← ENNReal.ofReal_mul (hf j).le, mul_div_cancel₀ (f k) hj]
    calc F k * KKCrit.D2 μ X t j k
        = F j * (ENNReal.ofReal (f k / f j) * KKCrit.D2 μ X t j k) := by rw [hFk, mul_assoc]
      _ ≤ F j * KKCrit.D2 μ X t k j := mul_le_mul' le_rfl h
  have hsym : ∀ h > 0, ∀ j k, F j * KKCrit.D2 μ X h k j = F k * KKCrit.D2 μ X h j k :=
    fun h hh j k => le_antisymm (hle h hh k j) (hle h hh j k)
  exact KKCrit.rev_of_D hX hstat (KKCrit.Dsym_of_F hX hstat F (fun _ => ENNReal.ofReal_ne_top)
    (fun a => (ENNReal.ofReal_pos.mpr (hf a)).ne') hsym)
