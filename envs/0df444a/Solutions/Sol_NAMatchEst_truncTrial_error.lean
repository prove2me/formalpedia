-- Prove2me | solution 1 for NAMatchEst.truncTrial_error
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T01:01:06.197603+00:00
-- url     : https://prove2.me/submissions/e0626391-48ce-4604-99dd-35259fd725ec

import Mathlib
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_RandomQueryXOR_uniformOn
import Definitions.Def_ShallowShadows_ShadowNorm_uniformDist
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_NAMatchEst_RandAlg_run
import Definitions.Def_NAMatchEst_RandAlg_prob
import Definitions.Def_NAMatchEst_RandAlg_par
import Definitions.Def_NAMatchEst_RandAlg_guard
import Definitions.Def_NAMatchEst_RandAlg_CostLE
import Definitions.Def_TuranMatching_Clique_Setting
import Definitions.Def_NAMatchEst_AdjList_toGraph
import Definitions.Def_NAMatchEst_C0
import Definitions.Def_NAMatchEst_bernDist
import Definitions.Def_NAMatchEst_largeTrial
import Definitions.Def_NAMatchEst_smallTrial
import Definitions.Def_NAMatchEst_truncTrial
import Theorems.Thm_NAMatchEst_lemma_3_12
import Theorems.Thm_NAMatchEst_lemma_3_13
import Theorems.Thm_NAMatchEst_chernoff_pi


/-! Local toolkit (BEGIN KIT). Inlined into submitted solutions. -/

namespace NAMatchEst.Kit

open WildeQIT

/-- Probability of an event under a finite distribution. -/
noncomputable def pr {Ω : Type} [Fintype Ω] (d : FinDist Ω) (E : Ω → Prop) : ℝ :=
  open Classical in ∑ ω, d.prob ω * if E ω then 1 else 0

/-- `pr` agrees with the explicit weighted sum for any decidability instance. -/
lemma pr_eq_sum {Ω : Type} [Fintype Ω] (d : FinDist Ω) (E : Ω → Prop) [DecidablePred E] :
    pr d E = ∑ ω, d.prob ω * if E ω then 1 else 0 := by
  classical
  unfold pr
  refine Finset.sum_congr rfl fun ω _ => ?_
  congr

lemma pr_congr {Ω : Type} [Fintype Ω] (d : FinDist Ω) {E F : Ω → Prop} (h : ∀ ω, E ω ↔ F ω) :
    pr d E = pr d F := by
  have : E = F := funext fun ω => propext (h ω)
  rw [this]

lemma pr_nonneg {Ω : Type} [Fintype Ω] (d : FinDist Ω) (E : Ω → Prop) : 0 ≤ pr d E := by
  classical
  unfold pr
  exact Finset.sum_nonneg fun ω _ => mul_nonneg (d.nonneg ω) (by split_ifs <;> norm_num)

lemma pr_mono {Ω : Type} [Fintype Ω] (d : FinDist Ω) {E F : Ω → Prop} (h : ∀ ω, E ω → F ω) :
    pr d E ≤ pr d F := by
  classical
  unfold pr
  refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (d.nonneg ω)
  by_cases hE : E ω
  · simp [hE, h ω hE]
  · simp only [hE, if_false]; split_ifs <;> norm_num

lemma pr_true {Ω : Type} [Fintype Ω] (d : FinDist Ω) : pr d (fun _ => True) = 1 := by
  unfold pr; simp only [if_true, mul_one]; exact d.sum_eq_one

lemma pr_le_one {Ω : Type} [Fintype Ω] (d : FinDist Ω) (E : Ω → Prop) : pr d E ≤ 1 :=
  (pr_mono d (fun _ _ => trivial)).trans (pr_true d).le

lemma pr_not {Ω : Type} [Fintype Ω] (d : FinDist Ω) (E : Ω → Prop) :
    pr d (fun ω => ¬ E ω) = 1 - pr d E := by
  classical
  have h : pr d (fun ω => ¬ E ω) + pr d E = 1 := by
    unfold pr
    rw [← Finset.sum_add_distrib]
    calc _ = ∑ ω, d.prob ω := Finset.sum_congr rfl fun ω _ => by by_cases hE : E ω <;> simp [hE]
      _ = 1 := d.sum_eq_one
  linarith

lemma pr_or_le {Ω : Type} [Fintype Ω] (d : FinDist Ω) (E F : Ω → Prop) :
    pr d (fun ω => E ω ∨ F ω) ≤ pr d E + pr d F := by
  classical
  unfold pr
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ω _ => ?_
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (d.nonneg ω)
  by_cases hE : E ω <;> by_cases hF : F ω <;> simp [hE, hF]

lemma pr_and_ge {Ω : Type} [Fintype Ω] (d : FinDist Ω) (E F : Ω → Prop) :
    pr d E + pr d F - 1 ≤ pr d (fun ω => E ω ∧ F ω) := by
  have h1 := pr_or_le d (fun ω => ¬ E ω) (fun ω => ¬ F ω)
  rw [pr_not, pr_not] at h1
  have h2 : pr d (fun ω => ¬E ω ∨ ¬F ω) = 1 - pr d (fun ω => E ω ∧ F ω) := by
    rw [← pr_not]; exact pr_congr d fun ω => by tauto
  linarith

/-- Union bound over a finset of indices. -/
lemma pr_exists_le {Ω ι : Type} [Fintype Ω] (d : FinDist Ω) (s : Finset ι) (E : ι → Ω → Prop) :
    pr d (fun ω => ∃ i ∈ s, E i ω) ≤ ∑ i ∈ s, pr d (E i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pr]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    calc pr d (fun ω => ∃ i ∈ insert a s, E i ω)
        = pr d (fun ω => E a ω ∨ ∃ i ∈ s, E i ω) := pr_congr d fun ω => by simp
      _ ≤ pr d (E a) + pr d (fun ω => ∃ i ∈ s, E i ω) := pr_or_le d _ _
      _ ≤ _ := by linarith

/-- Expectation of a real function. -/
noncomputable def ex {Ω : Type} [Fintype Ω] (d : FinDist Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω, d.prob ω * X ω

/-- Markov's inequality. -/
lemma markov {Ω : Type} [Fintype Ω] (d : FinDist Ω) (X : Ω → ℝ) (hX : ∀ ω, 0 ≤ X ω)
    {a : ℝ} (ha : 0 < a) : pr d (fun ω => a ≤ X ω) ≤ ex d X / a := by
  classical
  rw [le_div_iff₀ ha]
  unfold pr ex
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun ω _ => ?_
  by_cases h : a ≤ X ω
  · simp only [h, if_true, mul_one]
    exact mul_le_mul_of_nonneg_left h (d.nonneg ω)
  · simp only [h, if_false, mul_zero, zero_mul]
    exact mul_nonneg (d.nonneg ω) (hX ω)

/-! ### Product distributions -/

lemma pr_prod {α β : Type} [Fintype α] [Fintype β] (p : FinDist α) (q : FinDist β)
    (E : α × β → Prop) :
    pr (p.prod q) E = ∑ a, p.prob a * pr q (fun b => E (a, b)) := by
  classical
  unfold pr
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [FinDist.prod_prob]

lemma pr_prod' {α β : Type} [Fintype α] [Fintype β] (p : FinDist α) (q : FinDist β)
    (E : α × β → Prop) :
    pr (p.prod q) E = ∑ b, q.prob b * pr p (fun a => E (a, b)) := by
  classical
  unfold pr
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [FinDist.prod_prob]; ring

lemma pr_prod_fst {α β : Type} [Fintype α] [Fintype β] (p : FinDist α) (q : FinDist β)
    (E : α → Prop) : pr (p.prod q) (fun ω => E ω.1) = pr p E := by
  classical
  rw [pr_prod]
  unfold pr
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : E a <;> simp [h, q.sum_eq_one]

lemma pr_prod_snd {α β : Type} [Fintype α] [Fintype β] (p : FinDist α) (q : FinDist β)
    (E : β → Prop) : pr (p.prod q) (fun ω => E ω.2) = pr q E := by
  classical
  rw [pr_prod']
  unfold pr
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : E b <;> simp [h, p.sum_eq_one]

/-- If the conditional probability of `E` given the first coordinate is bounded by `c` on a set of
first coordinates of probability `≥ 1 - δ`, then `P(E) ≤ c + δ`. -/
lemma pr_prod_le_of_cond {α β : Type} [Fintype α] [Fintype β] (p : FinDist α) (q : FinDist β)
    (E : α × β → Prop) (G : α → Prop) (c δ : ℝ) (hG : 1 - δ ≤ pr p G)
    (hc : ∀ a, G a → pr q (fun b => E (a, b)) ≤ c) (hc0 : 0 ≤ c) :
    pr (p.prod q) E ≤ c + δ := by
  classical
  rw [pr_prod]
  have key : ∀ a, p.prob a * pr q (fun b => E (a, b)) ≤
      p.prob a * c + p.prob a * (if G a then 0 else 1) := by
    intro a
    by_cases h : G a
    · simp only [h, if_true, mul_zero, add_zero]
      exact mul_le_mul_of_nonneg_left (hc a h) (p.nonneg a)
    · simp only [h, if_false, mul_one]
      have := pr_le_one q (fun b => E (a, b))
      nlinarith [p.nonneg a]
  calc ∑ a, p.prob a * pr q (fun b => E (a, b))
      ≤ ∑ a, (p.prob a * c + p.prob a * (if G a then 0 else 1)) := Finset.sum_le_sum fun a _ => key a
    _ = c + pr p (fun a => ¬ G a) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, p.sum_eq_one, one_mul]
        congr 1
        unfold pr
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases h : G a <;> simp [h]
    _ ≤ c + δ := by rw [pr_not]; linarith

/-! ### Algorithms -/

lemma prob_eq_pr {n : ℕ} {β : Type} (A : RandAlg n β) (G : AdjList n) (P : β → Prop) :
    A.prob G P = pr A.dist (fun ω => P (A.run G ω)) := rfl

lemma run_par {n : ℕ} {β γ δ : Type} (A : RandAlg n β) (B : RandAlg n γ) (f : β → γ → δ)
    (G : AdjList n) (ω : (A.par B f).Ω) :
    (A.par B f).run G ω = f (A.run G ω.1) (B.run G ω.2) := by
  classical
  simp only [RandAlg.run, RandAlg.par]
  congr 2
  · funext v
    by_cases h : Query.deg v ∈ A.queries ω.1
    · simp [h]
    · simp [h]
  · funext v i
    by_cases h : Query.nbr v i ∈ A.queries ω.1
    · simp [h]
    · simp [h]
  · funext v
    by_cases h : Query.deg v ∈ B.queries ω.2
    · simp [h]
    · simp [h]
  · funext v i
    by_cases h : Query.nbr v i ∈ B.queries ω.2
    · simp [h]
    · simp [h]

lemma par_dist {n : ℕ} {β γ δ : Type} (A : RandAlg n β) (B : RandAlg n γ) (f : β → γ → δ) :
    (A.par B f).dist = A.dist.prod B.dist := rfl

lemma prob_par {n : ℕ} {β γ δ : Type} (A : RandAlg n β) (B : RandAlg n γ) (f : β → γ → δ)
    (G : AdjList n) (P : δ → Prop) :
    (A.par B f).prob G P = pr (A.dist.prod B.dist) (fun ω => P (f (A.run G ω.1) (B.run G ω.2))) := by
  rw [prob_eq_pr]
  exact pr_congr _ fun ω => by rw [run_par]

/-- Union bound for a parallel composition. -/
lemma prob_par_le {n : ℕ} {β γ δ : Type} (A : RandAlg n β) (B : RandAlg n γ) (f : β → γ → δ)
    (G : AdjList n) (P : δ → Prop) (Q₁ : β → Prop) (Q₂ : γ → Prop)
    (h : ∀ a b, P (f a b) → Q₁ a ∨ Q₂ b) :
    (A.par B f).prob G P ≤ A.prob G Q₁ + B.prob G Q₂ := by
  rw [prob_par, prob_eq_pr A, prob_eq_pr B, ← pr_prod_fst A.dist B.dist,
    ← pr_prod_snd A.dist B.dist]
  exact (pr_mono _ fun ω hω => h _ _ hω).trans (pr_or_le _ _ _)

lemma run_guard {n : ℕ} {β : Type} (A : RandAlg n β) (ok : A.Ω → Prop) (b₀ : β) (G : AdjList n)
    (ω : (A.guard ok b₀).Ω) :
    (A.guard ok b₀).run G ω = (open Classical in if ok ω then A.run G ω else b₀) := by
  classical
  simp only [RandAlg.run, RandAlg.guard]
  by_cases h : ok ω
  · simp [h]
  · simp [h]

lemma prob_guard {n : ℕ} {β : Type} (A : RandAlg n β) (ok : A.Ω → Prop) (b₀ : β) (G : AdjList n)
    (P : β → Prop) :
    (A.guard ok b₀).prob G P =
      pr A.dist (fun ω => (open Classical in if ok ω then P (A.run G ω) else P b₀)) := by
  classical
  rw [prob_eq_pr]
  exact pr_congr (A.guard ok b₀).dist fun ω => by
    rw [run_guard]; by_cases h : ok ω <;> simp [h]

lemma costLE_par {n : ℕ} {β γ δ : Type} (A : RandAlg n β) (B : RandAlg n γ) (f : β → γ → δ)
    {a b : ℝ} (hA : A.CostLE a) (hB : B.CostLE b) : (A.par B f).CostLE (a + b) := by
  intro ω
  simp only [RandAlg.par, List.length_append, Nat.cast_add]
  exact add_le_add (hA ω.1) (hB ω.2)

lemma costLE_mono {n : ℕ} {β : Type} (A : RandAlg n β) {a b : ℝ} (hA : A.CostLE a) (hab : a ≤ b) :
    A.CostLE b := fun ω => (hA ω).trans hab

/-! ### Uniform and Bernoulli product laws -/

lemma uniformDist_prob {ι : Type} [Fintype ι] [Nonempty ι] (x : ι) :
    (ShallowShadows.ShadowNorm.uniformDist ι).prob x = 1 / (Fintype.card ι : ℝ) := rfl

/-- The uniform law on `Fin m → Q` is the product of uniform laws. -/
lemma uniformDist_eq_piDist {m : ℕ} {Q : Type} [Fintype Q] [Nonempty Q] (x : Fin m → Q) :
    (ShallowShadows.ShadowNorm.uniformDist (Fin m → Q)).prob x =
      (RandomQueryXOR.piDist fun _ : Fin m => ShallowShadows.ShadowNorm.uniformDist Q).prob x := by
  simp only [uniformDist_prob, RandomQueryXOR.piDist, Fintype.card_fun, Fintype.card_fin,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  rw [one_div_pow]

lemma pr_uniform_eq_pr_pi {m : ℕ} {Q : Type} [Fintype Q] [Nonempty Q] (E : (Fin m → Q) → Prop) :
    pr (ShallowShadows.ShadowNorm.uniformDist (Fin m → Q)) E =
      pr (RandomQueryXOR.piDist fun _ : Fin m => ShallowShadows.ShadowNorm.uniformDist Q) E := by
  classical
  unfold pr
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [uniformDist_eq_piDist]

/-- Marginal of a product distribution: an event depending on one coordinate. -/
lemma pr_piDist_coord {m : ℕ} {Q : Type} [Fintype Q] (p : Fin m → FinDist Q) (i : Fin m)
    (E : Q → Prop) : pr (RandomQueryXOR.piDist p) (fun ω => E (ω i)) = pr (p i) E := by
  classical
  unfold pr
  simp only [RandomQueryXOR.piDist]
  set F : Fin m → Q → ℝ := fun a x =>
    if a = i then (p a).prob x * (if E x then 1 else 0) else (p a).prob x with hF
  have : ∀ ω : Fin m → Q, (∏ a, (p a).prob (ω a)) * (if E (ω i) then (1 : ℝ) else 0) =
      ∏ a, F a (ω a) := by
    intro ω
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [hF, if_true]
    rw [mul_right_comm]
    congr 1
    refine Finset.prod_congr rfl fun a ha => ?_
    rw [if_neg (Finset.ne_of_mem_erase ha)]
  rw [Finset.sum_congr rfl fun ω _ => this ω, ← Fintype.prod_sum F,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  rw [Finset.prod_eq_one, mul_one]
  · simp only [hF, if_true]
  intro a ha
  simp only [hF, if_neg (Finset.ne_of_mem_erase ha)]
  exact (p a).sum_eq_one

end NAMatchEst.Kit

/-! (END KIT) -/



namespace NAMatchEst.AuxTrunc
open NAMatchEst

lemma L_ge_one (n : ℕ) (hn : 2 ≤ n) : 1 ≤ L n := by
  unfold L
  rw [Real.le_log_iff_exp_le (by positivity)]
  have h1 := Real.exp_one_lt_d9
  have h2 : (4 : ℝ) ≤ 2 * n := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  linarith

lemma exp_neg19 (x : ℝ) (hx : 19 ≤ x) : Real.exp (-x) ≤ 1 / 40 := by
  have h := Real.quadratic_le_exp_of_nonneg (by linarith : (0:ℝ) ≤ x)
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
  nlinarith

/-- Cap tail for a Bernoulli sample. -/
lemma cap_tail (n : ℕ) (hn : 2 ≤ n) (p : ℝ) (hp : 0 ≤ p) :
    Kit.pr (bernDist (n := n) p) (fun S =>
      ¬ (((Finset.univ.filter fun v => S v = true).card : ℝ) ≤
        (⌈2 * n * p + 100 * L n⌉₊ : ℝ))) ≤ 1 / 40 := by
  classical
  set pc : ℝ := max 0 (min p 1) with hpc
  have hpc0 : 0 ≤ pc := le_max_left _ _
  have hpcp : pc ≤ p := max_le hp (min_le_left _ _)
  have hL := L_ge_one n hn
  set lam : ℝ := n * pc + 50 * L n with hlam
  set f : Fin n → Bool → ℝ := fun _ b => if b then 1 else 0 with hfdef
  have hf : ∀ v b, 0 ≤ f v b ∧ f v b ≤ 1 := by
    intro v b; simp only [hfdef]; split_ifs <;> norm_num
  set q : Fin n → WildeQIT.FinDist Bool := fun _ =>
    { prob := fun b => if b then max 0 (min p 1) else 1 - max 0 (min p 1)
      nonneg := fun b => by
        have : max 0 (min p 1) ≤ 1 := max_le zero_le_one (min_le_right _ _)
        cases b
        · simp only [Bool.false_eq_true, if_false]; linarith
        · simp only [if_true]; exact le_max_left _ _
      sum_eq_one := by simp } with hq
  have hbern : bernDist (n := n) p = RandomQueryXOR.piDist q := rfl
  have hmean : (∑ v, ∑ b, (q v).prob b * f v b) = n * pc := by
    simp [hq, hfdef, hpc]
  have hH : (∑ v, ∑ b, (q v).prob b * f v b) ≤ lam := by rw [hmean, hlam]; linarith
  have H := (NAMatchEst.chernoff_pi q f hf 0 lam (Real.log 2) (2 * lam)
    (by rw [hmean]; positivity) hH (Real.log_nonneg (by norm_num))).1
  have hsum : ∀ S : Fin n → Bool, ∑ v, f v (S v) =
      ((Finset.univ.filter fun v => S v = true).card : ℝ) := by
    intro S
    rw [Finset.card_filter]; push_cast; rfl
  simp_rw [hsum] at H
  rw [hbern]
  refine le_trans (Kit.pr_mono _ (F := fun S => 2 * lam ≤
      ((Finset.univ.filter fun v => S v = true).card : ℝ)) ?_) ?_
  · intro S hS
    rw [not_le] at hS
    have hc := Nat.le_ceil (2 * n * p + 100 * L n)
    have : 2 * lam ≤ 2 * n * p + 100 * L n := by
      rw [hlam]; nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    linarith
  · rw [Kit.pr_eq_sum]
    refine H.trans ?_
    rw [Real.exp_log (by norm_num : (0:ℝ) < 2)]
    apply le_trans _ (exp_neg19 (lam * (2 * Real.log 2 - 1)) ?_)
    · apply le_of_eq; congr 1; ring
    · have h2 := Real.log_two_gt_d9
      have : 50 ≤ lam := by rw [hlam]; nlinarith
      nlinarith

/-- Generic guard bounds. -/
lemma guard_bounds {n : ℕ} (A : RandAlg n Bool) (ok : A.Ω → Prop) (G : AdjList n) (δ : ℝ)
    (hδ : Kit.pr A.dist (fun ω => ¬ ok ω) ≤ δ) :
    (A.guard ok false).prob G (· = false) ≤ A.prob G (· = false) + δ ∧
      (A.guard ok false).prob G (· = true) ≤ A.prob G (· = true) := by
  classical
  constructor
  · rw [Kit.prob_guard, Kit.prob_eq_pr]
    refine le_trans (Kit.pr_mono _ (F := fun ω => A.run G ω = false ∨ ¬ ok ω) ?_)
      ((Kit.pr_or_le _ _ _).trans (by linarith))
    intro ω h
    by_cases hok : ok ω
    · simp only [hok, if_true] at h; exact Or.inl h
    · exact Or.inr hok
  · rw [Kit.prob_guard, Kit.prob_eq_pr]
    refine Kit.pr_mono _ ?_
    intro ω h
    by_cases hok : ok ω
    · simpa only [hok, if_true] using h
    · simp only [hok, if_false] at h; exact absurd h (by decide)

lemma large_marg1 (n : ℕ) [NeZero n] (α : ℝ) (k : ℕ) (E : (Fin n → Bool) → Prop) :
    Kit.pr (largeTrial n α k).dist (fun ω => E ω.2.2.2.1) =
      Kit.pr (bernDist (n := n) (cc * L n / Real.sqrt (k * α))) E := by
  refine (Kit.pr_prod_snd _ _ (fun x : (degTest n α k).Ω × ((resTest n α k).Ω × (edgeTest n α k).Ω) => E x.2.2.1)).trans ?_
  refine (Kit.pr_prod_snd _ _ (fun x : (resTest n α k).Ω × (edgeTest n α k).Ω => E x.2.1)).trans ?_
  refine (Kit.pr_prod_snd _ _ (fun x : (edgeTest n α k).Ω => E x.1)).trans ?_
  exact Kit.pr_prod_fst _ _ E

lemma large_marg2 (n : ℕ) [NeZero n] (α : ℝ) (k : ℕ) (E : (Fin n → Bool) → Prop) :
    Kit.pr (largeTrial n α k).dist (fun ω => E ω.2.2.2.2.1) =
      Kit.pr (bernDist (n := n) (Real.sqrt (α / k))) E := by
  refine (Kit.pr_prod_snd _ _ (fun x : (degTest n α k).Ω × ((resTest n α k).Ω × (edgeTest n α k).Ω) => E x.2.2.2.1)).trans ?_
  refine (Kit.pr_prod_snd _ _ (fun x : (resTest n α k).Ω × (edgeTest n α k).Ω => E x.2.2.1)).trans ?_
  refine (Kit.pr_prod_snd _ _ (fun x : (edgeTest n α k).Ω => E x.2.1)).trans ?_
  refine (Kit.pr_prod_snd _ _
    (fun x : (Fin n → Bool) × (Fin n → Fin ⌈cc * Delta k α * L n / α⌉₊ → Fin (Delta k α)) =>
      E x.1)).trans ?_
  exact Kit.pr_prod_fst _ _ E

lemma small_marg1 (n : ℕ) [NeZero n] (α : ℝ) (k : ℕ) (E : (Fin n → Bool) → Prop) :
    Kit.pr (smallTrial n α k).dist (fun ω => E ω.2.1) =
      Kit.pr (bernDist (n := n) (cc * L n * Real.sqrt α / k)) E := by
  refine (Kit.pr_prod_snd _ _ (fun x : (smallEdgeTest n α k).Ω => E x.1)).trans ?_
  exact Kit.pr_prod_fst _ _ E

lemma small_marg2 (n : ℕ) [NeZero n] (α : ℝ) (k : ℕ) (E : (Fin n → Bool) → Prop) :
    Kit.pr (smallTrial n α k).dist (fun ω => E ω.2.2) =
      Kit.pr (bernDist (n := n) (1 / Real.sqrt α)) E := by
  refine (Kit.pr_prod_snd _ _ (fun x : (smallEdgeTest n α k).Ω => E x.2)).trans ?_
  exact Kit.pr_prod_snd _ _ E

end NAMatchEst.AuxTrunc

open NAMatchEst NAMatchEst.AuxTrunc in
theorem solution : ∃ N₀ : ℕ, ∀ (n : ℕ) [NeZero n], N₀ ≤ n → ∀ (α : ℝ) (k : ℕ),
    (n : ℝ) ^ ((1 : ℝ) / 3) ≤ α → α ≤ (n : ℝ) ^ ((1 : ℝ) / 2) → α ≤ k → (k : ℝ) ≤ n →
    ∀ G : AdjList n,
      (k ≤ TuranMatching.Clique.matchingNumber G.toGraph →
        (truncTrial n α k).prob G (· = false) ≤ 1 / 5) ∧
      ((TuranMatching.Clique.matchingNumber G.toGraph : ℝ) < k / (C0 * α) →
        (truncTrial n α k).prob G (· = true) ≤ 1 / 5) := by
  obtain ⟨N12, h12⟩ := lemma_3_12
  obtain ⟨N13, h13⟩ := lemma_3_13
  refine ⟨max N12 (max N13 2), ?_⟩
  intro n _ hn α k h1 h2 h3 h4 G
  have hn12 : N12 ≤ n := le_trans (le_max_left _ _) hn
  have hn13 : N13 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn2 : 2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hL0 : 0 ≤ L n := le_trans zero_le_one (L_ge_one n hn2)
  have hcc : (0 : ℝ) ≤ cc := by unfold cc; norm_num
  by_cases hk : α ^ 2 < k
  · obtain ⟨hy, hno⟩ := h12 n hn12 α k h1 h2 h3 h4 hk G
    have hδ : Kit.pr (largeTrial n α k).dist (fun ω =>
        ¬ (((Finset.univ.filter fun v => ω.2.2.2.1 v = true).card : ℝ) ≤
            ⌈2 * n * (cc * L n / Real.sqrt (k * α)) + 100 * L n⌉₊ ∧
          ((Finset.univ.filter fun v => ω.2.2.2.2.1 v = true).card : ℝ) ≤
            ⌈2 * n * Real.sqrt (α / k) + 100 * L n⌉₊)) ≤ 1 / 20 := by
      refine le_trans (Kit.pr_mono _ (F := fun ω =>
        ¬ (((Finset.univ.filter fun v => ω.2.2.2.1 v = true).card : ℝ) ≤
            ⌈2 * n * (cc * L n / Real.sqrt (k * α)) + 100 * L n⌉₊) ∨
        ¬ (((Finset.univ.filter fun v => ω.2.2.2.2.1 v = true).card : ℝ) ≤
            ⌈2 * n * Real.sqrt (α / k) + 100 * L n⌉₊)) (fun ω h => by tauto))
        ((Kit.pr_or_le _ _ _).trans ?_)
      have e1 := cap_tail n hn2 (cc * L n / Real.sqrt (k * α)) (by positivity)
      have e2 := cap_tail n hn2 (Real.sqrt (α / k)) (Real.sqrt_nonneg _)
      rw [large_marg1 n α k (fun S => ¬ (((Finset.univ.filter fun v => S v = true).card : ℝ) ≤
            ⌈2 * n * (cc * L n / Real.sqrt (k * α)) + 100 * L n⌉₊)),
        large_marg2 n α k (fun S => ¬ (((Finset.univ.filter fun v => S v = true).card : ℝ) ≤
            ⌈2 * n * Real.sqrt (α / k) + 100 * L n⌉₊))]
      linarith
    have hg := guard_bounds (largeTrial n α k) _ G _ hδ
    rw [truncTrial, if_pos hk]
    exact ⟨fun h => by linarith [hg.1, hy h], fun h => by linarith [hg.2, hno h]⟩
  · have hk' : (k : ℝ) ≤ α ^ 2 := le_of_not_gt hk
    obtain ⟨hy, hno⟩ := h13 n hn13 α k h1 h2 h3 h4 hk' G
    have hδ : Kit.pr (smallTrial n α k).dist (fun ω =>
        ¬ (((Finset.univ.filter fun v => ω.2.1 v = true).card : ℝ) ≤
            ⌈2 * n * (cc * L n * Real.sqrt α / k) + 100 * L n⌉₊ ∧
          ((Finset.univ.filter fun v => ω.2.2 v = true).card : ℝ) ≤
            ⌈2 * n * (1 / Real.sqrt α) + 100 * L n⌉₊)) ≤ 1 / 20 := by
      refine le_trans (Kit.pr_mono _ (F := fun ω =>
        ¬ (((Finset.univ.filter fun v => ω.2.1 v = true).card : ℝ) ≤
            ⌈2 * n * (cc * L n * Real.sqrt α / k) + 100 * L n⌉₊) ∨
        ¬ (((Finset.univ.filter fun v => ω.2.2 v = true).card : ℝ) ≤
            ⌈2 * n * (1 / Real.sqrt α) + 100 * L n⌉₊)) (fun ω h => by tauto))
        ((Kit.pr_or_le _ _ _).trans ?_)
      have e1 := cap_tail n hn2 (cc * L n * Real.sqrt α / k) (by positivity)
      have e2 := cap_tail n hn2 (1 / Real.sqrt α) (by positivity)
      rw [small_marg1 n α k (fun S => ¬ (((Finset.univ.filter fun v => S v = true).card : ℝ) ≤
            ⌈2 * n * (cc * L n * Real.sqrt α / k) + 100 * L n⌉₊)),
        small_marg2 n α k (fun S => ¬ (((Finset.univ.filter fun v => S v = true).card : ℝ) ≤
            ⌈2 * n * (1 / Real.sqrt α) + 100 * L n⌉₊))]
      linarith
    have hg := guard_bounds (smallTrial n α k) _ G _ hδ
    rw [truncTrial, if_neg hk]
    exact ⟨fun h => by linarith [hg.1, hy h], fun h => by linarith [hg.2, hno h]⟩
