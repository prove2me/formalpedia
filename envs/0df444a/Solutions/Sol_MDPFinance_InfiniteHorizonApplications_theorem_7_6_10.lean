-- Prove2me | solution 1 for MDPFinance.InfiniteHorizonApplications.theorem_7_6_10
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T02:42:48.682977+00:00
-- url     : https://prove2.me/submissions/cbe65e5b-6e32-4c57-b5b2-8cf32ef9d115

import Theorems.Thm_MDPFinance_InfiniteHorizonApplications_proposition_7_6_9

set_option autoImplicit false

open MDPFinance.InfiniteHorizonApplications
open Filter Topology

namespace GittinsReduction

private lemma probability (mn : ℕ × ℕ) : 0 ≤ pMN mn ∧ pMN mn ≤ 1 := by
  unfold pMN
  have hm : (0 : ℝ) ≤ mn.1 := Nat.cast_nonneg _
  have hn : (0 : ℝ) ≤ mn.2 := Nat.cast_nonneg _
  constructor
  · positivity
  · apply (div_le_one (by positivity)).2
    linarith

private lemma reward_range (a : Fin 2) (x : BanditState2) :
    0 ≤ paBandit a x ∧ paBandit a x ≤ 1 := by
  unfold paBandit
  split <;> exact probability _

private lemma mix_range {p l u y z : ℝ} (hp : 0 ≤ p ∧ p ≤ 1)
    (hy : l ≤ y ∧ y ≤ u) (hz : l ≤ z ∧ z ≤ u) :
    l ≤ p * y + (1 - p) * z ∧ p * y + (1 - p) * z ≤ u := by
  constructor
  · nlinarith [mul_nonneg hp.1 (sub_nonneg.mpr hy.1),
      mul_nonneg (sub_nonneg.mpr hp.2) (sub_nonneg.mpr hz.1)]
  · nlinarith [mul_nonneg hp.1 (sub_nonneg.mpr hy.2),
      mul_nonneg (sub_nonneg.mpr hp.2) (sub_nonneg.mpr hz.2)]

private lemma transition_range (a : Fin 2) (v : BanditState2 → ℝ) (l u : ℝ)
    (hv : ∀ x, l ≤ v x ∧ v x ≤ u) (x : BanditState2) :
    l ≤ QaBandit a v x ∧ QaBandit a v x ≤ u := by
  unfold QaBandit Q1Bandit Q2Bandit
  split <;> exact mix_range (probability _) (hv _) (hv _)

private lemma transition_mono (a : Fin 2) {v w : BanditState2 → ℝ}
    (h : ∀ x, v x ≤ w x) (x : BanditState2) : QaBandit a v x ≤ QaBandit a w x := by
  unfold QaBandit Q1Bandit Q2Bandit
  split
  · exact add_le_add (mul_le_mul_of_nonneg_left (h _) (probability _).1)
      (mul_le_mul_of_nonneg_left (h _) (sub_nonneg.mpr (probability _).2))
  · exact add_le_add (mul_le_mul_of_nonneg_left (h _) (probability _).1)
      (mul_le_mul_of_nonneg_left (h _) (sub_nonneg.mpr (probability _).2))

/-- A bounded stopped Bellman fixed point exists for every retirement payment. -/
private lemma stopped_exists {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (K : ℝ) :
    ∃ v : BanditState2 → ℝ, (∃ C : ℝ, ∀ x, |v x| ≤ C) ∧
      ∀ x, v x = max K (max (paBandit 0 x + β * QaBandit 0 v x)
        (paBandit 1 x + β * QaBandit 1 v x)) := by
  classical
  let l := min K 0
  let u := max K (1 / (1 - β))
  have hl : l ≤ 0 := min_le_right _ _
  have hu : 0 ≤ u := (le_of_lt (one_div_pos.mpr (sub_pos.mpr hβ1))).trans (le_max_right _ _)
  have hlu : l ≤ u := hl.trans hu
  have hKu : K ≤ u := le_max_left _ _
  have hlK : l ≤ K := min_le_left _ _
  have hu_step : 1 + β * u ≤ u := by
    have h := le_max_right K (1 / (1 - β))
    have hd : 0 < 1 - β := sub_pos.mpr hβ1
    have : 1 ≤ u * (1 - β) := (div_le_iff₀ hd).mp h
    nlinarith
  let : Fact (l ≤ u) := ⟨hlu⟩
  let T : (BanditState2 → Set.Icc l u) →o (BanditState2 → Set.Icc l u) :=
    { toFun := fun v x =>
        ⟨max K (max (paBandit 0 x + β * QaBandit 0 (fun y => (v y : ℝ)) x)
          (paBandit 1 x + β * QaBandit 1 (fun y => (v y : ℝ)) x)), by
          have hv : ∀ y, l ≤ (v y : ℝ) ∧ (v y : ℝ) ≤ u := fun y => (v y).property
          have h0 := transition_range 0 _ l u hv x
          have h1 := transition_range 1 _ l u hv x
          constructor
          · exact hlK.trans (le_max_left _ _)
          · refine max_le hKu (max_le ?_ ?_)
            · have := mul_le_mul_of_nonneg_left h0.2 hβ0.le
              linarith [(reward_range 0 x).2]
            · have := mul_le_mul_of_nonneg_left h1.2 hβ0.le
              linarith [(reward_range 1 x).2]⟩
      monotone' := by
        intro v w hv x
        change max K _ ≤ max K _
        apply max_le_max_left
        apply max_le_max
        · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
            (transition_mono 0 (fun y => hv y) x) hβ0.le)
        · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
            (transition_mono 1 (fun y => hv y) x) hβ0.le) }
  refine ⟨fun x => (T.lfp x : ℝ), ⟨u - l, ?_⟩, ?_⟩
  · intro x
    apply abs_le.mpr
    rcases (T.lfp x).property with ⟨hx1, hx2⟩
    constructor <;> linarith
  · intro x
    exact (congrArg (fun v : BanditState2 → Set.Icc l u => (v x : ℝ)) T.map_lfp).symm

/-- The stopped family may be chosen to agree with the bandit value below a uniform lower bound. -/
private lemma stopped_family {β : ℝ} (BV : BanditValue β) :
    ∃ (JKS : JointKStoppingValue β) (L : ℝ), ∀ K, K ≤ L → JKS.Jt K = BV.Jinf := by
  classical
  obtain ⟨C, hC⟩ := BV.hJinf_bdd
  choose v hvbdd hvfix using (fun K : ℝ => stopped_exists BV.hβ0 BV.hβ1 K)
  let JKS : JointKStoppingValue β :=
    { hβ0 := BV.hβ0
      hβ1 := BV.hβ1
      Jt := fun K => if K ≤ -C then BV.Jinf else v K
      hJt_bdd := by
        intro K
        by_cases hK : K ≤ -C
        · simpa only [if_pos hK] using BV.hJinf_bdd
        · simpa only [if_neg hK] using hvbdd K
      hJt_fix := by
        intro K x
        by_cases hK : K ≤ -C
        · simp only [if_pos hK]
          have hlow : K ≤ BV.Jinf x := hK.trans (abs_le.mp (hC x)).1
          rw [← BV.hJinf_fix x, max_eq_right hlow]
        · simpa only [if_neg hK] using hvfix K x }
  exact ⟨JKS, -C, fun K hK => by dsimp [JKS]; rw [if_pos hK]⟩

private lemma index_bellman {β : ℝ} (KS : KStoppingValue β pMN) (BV : BanditValue β)
    (f : BanditState2 → Fin 2)
    (hf : ∀ x, f x = if GittinsIndex KS x.1 ≤ GittinsIndex KS x.2 then 1 else 0) :
    ∀ x, BV.Jinf x = paBandit (f x) x + β * QaBandit (f x) BV.Jinf x := by
  classical
  obtain ⟨JKS, L, hL⟩ := stopped_family BV
  intro x
  have h0 : f x = 0 → GittinsIndex KS x.2 ≤ GittinsIndex KS x.1 := by
    intro h
    have h' := hf x
    split_ifs at h' with hc
    · simp [h] at h'
    · exact (lt_of_not_ge hc).le
  have h1 : f x = 1 → GittinsIndex KS x.1 ≤ GittinsIndex KS x.2 := by
    intro h
    have h' := hf x
    split_ifs at h' with hc
    · exact hc
    · simp [h] at h'
  have hmax : max (GittinsIndex KS x.1) (GittinsIndex KS x.2) =
      if f x = 0 then GittinsIndex KS x.1 else GittinsIndex KS x.2 := by
    split_ifs with h
    · exact max_eq_left (h0 h)
    · have hfx : f x = 1 := by omega
      exact max_eq_right (h1 hfx)
  let I := max (GittinsIndex KS x.1) (GittinsIndex KS x.2)
  let K := min L (I - 1)
  have hKL : K ≤ L := min_le_left _ _
  have hKI : K < I := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have h := (proposition_7_6_9 KS JKS x).2.2 (f x) h0 h1 hmax
  simpa only [hL K hKL] using h.2 K hKI

private lemma transition_error (a : Fin 2) (v w : BanditState2 → ℝ) (d : ℝ)
    (h : ∀ x, |v x - w x| ≤ d) (x : BanditState2) :
    |QaBandit a v x - QaBandit a w x| ≤ d := by
  have hm := transition_range a (fun y => v y - w y) (-d) d
    (fun y => abs_le.mp (h y)) x
  have heq : QaBandit a v x - QaBandit a w x =
      QaBandit a (fun y => v y - w y) x := by
    unfold QaBandit Q1Bandit Q2Bandit
    split <;> ring
  rw [heq]
  exact abs_le.mpr hm

/-- Bellman equality gives a geometric error bound for the policy's actual finite-horizon values. -/
private lemma policy_error {β : ℝ} (BV : BanditValue β) (f : BanditState2 → Fin 2)
    (hf : ∀ x, BV.Jinf x = paBandit (f x) x + β * QaBandit (f x) BV.Jinf x)
    (C : ℝ) (hC : ∀ x, |BV.Jinf x| ≤ C) :
    ∀ n x, |banditVpi β f n x - BV.Jinf x| ≤ β ^ n * C := by
  intro n
  induction n with
  | zero => intro x; simpa [banditVpi] using hC x
  | succ n ih =>
    intro x
    rw [banditVpi, hf x]
    have heq : paBandit (f x) x + β * QaBandit (f x) (banditVpi β f n) x -
        (paBandit (f x) x + β * QaBandit (f x) BV.Jinf x) =
        β * (QaBandit (f x) (banditVpi β f n) x - QaBandit (f x) BV.Jinf x) := by ring
    rw [heq, abs_mul, abs_of_pos BV.hβ0]
    have hh := mul_le_mul_of_nonneg_left (transition_error (f x) _ _ _ ih x) BV.hβ0.le
    simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hh

private lemma policy_monotone {β : ℝ} (hβ : 0 ≤ β) (f : BanditState2 → Fin 2) :
    ∀ x, Monotone (fun n => banditVpi β f n x) := by
  have hstep : ∀ n x, banditVpi β f n x ≤ banditVpi β f (n + 1) x := by
    intro n
    induction n with
    | zero =>
      intro x
      simp only [banditVpi]
      have hz : QaBandit (f x) (fun _ => 0) x = 0 := by
        unfold QaBandit Q1Bandit Q2Bandit
        split <;> ring
      rw [hz, mul_zero, add_zero]
      exact (reward_range _ _).1
    | succ n ih =>
      intro x
      simp only [banditVpi]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (transition_mono (f x) ih x) hβ)
  intro x
  exact monotone_nat_of_le_succ (fun n => hstep n x)

private lemma policy_sup {β : ℝ} (BV : BanditValue β) (f : BanditState2 → Fin 2)
    (hf : ∀ x, BV.Jinf x = paBandit (f x) x + β * QaBandit (f x) BV.Jinf x) :
    ∀ x, (⨆ n, banditVpi β f n x) = BV.Jinf x := by
  obtain ⟨C, hC⟩ := BV.hJinf_bdd
  have herr := policy_error BV f hf C hC
  have hpow : Tendsto (fun n : ℕ => β ^ n * C) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one BV.hβ0.le BV.hβ1).mul_const C
  intro x
  have hconv : Tendsto (fun n => banditVpi β f n x) atTop (nhds (BV.Jinf x)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => by simpa [Real.norm_eq_abs] using herr n x) hpow
  have hmono := policy_monotone BV.hβ0.le f x
  have hbdd : BddAbove (Set.range (fun n => banditVpi β f n x)) :=
    ⟨BV.Jinf x, by rintro _ ⟨n, rfl⟩; exact hmono.ge_of_tendsto hconv n⟩
  exact tendsto_nhds_unique (tendsto_atTop_ciSup hmono hbdd) hconv

end GittinsReduction

theorem solution {β : ℝ} (KS : KStoppingValue β pMN) (BV : BanditValue β)
    (fstar : BanditState2 → Fin 2)
    (hfstar : ∀ x : BanditState2, fstar x = if GittinsIndex KS x.1 ≤ GittinsIndex KS x.2
      then 1 else 0) :
    (∀ x, (⨆ n, banditVpi β fstar n x) = BV.Jinf x) ∧
      ∀ x, (if fstar x = 0 then paBandit 0 x + β * QaBandit 0 BV.Jinf x
        else paBandit 1 x + β * QaBandit 1 BV.Jinf x) = BV.Jinf x := by
  have hbell := GittinsReduction.index_bellman KS BV fstar hfstar
  refine ⟨GittinsReduction.policy_sup BV fstar hbell, ?_⟩
  intro x
  rw [hbell x]
  split_ifs with h
  · rw [h]
  · have hfx : fstar x = 1 := by omega
    rw [hfx]
