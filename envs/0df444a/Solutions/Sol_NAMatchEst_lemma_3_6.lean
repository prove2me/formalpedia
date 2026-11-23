-- Prove2me | solution 1 for NAMatchEst.lemma_3_6
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T00:38:35.702392+00:00
-- url     : https://prove2.me/submissions/1d730c59-7457-48a9-8e5a-e2b9ead5f979

import Mathlib
import Theorems.Thm_NAMatchEst_chernoff_pi
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
import Definitions.Def_NAMatchEst_AdjList_nbr
import Definitions.Def_NAMatchEst_L
import Definitions.Def_NAMatchEst_RH
import Definitions.Def_NAMatchEst_dHbar
import Definitions.Def_NAMatchEst_U
import Definitions.Def_NAMatchEst_resTest


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



namespace NAMatchEst.Aux36
open Kit

lemma chern {m n : ℕ} [NeZero n] (g : Fin n → ℝ) (hg : ∀ q, 0 ≤ g q ∧ g q ≤ 1)
    (lamL lamH t a : ℝ) (hL : lamL ≤ (m : ℝ) * (∑ q, g q) / n)
    (hH : (m : ℝ) * (∑ q, g q) / n ≤ lamH) (ht : 0 ≤ t) :
    pr (ShallowShadows.ShadowNorm.uniformDist (Fin m → Fin n)) (fun ω => a ≤ ∑ j, g (ω j)) ≤
        Real.exp (lamH * (Real.exp t - 1) - t * a) ∧
    pr (ShallowShadows.ShadowNorm.uniformDist (Fin m → Fin n)) (fun ω => ∑ j, g (ω j) ≤ a) ≤
        Real.exp (lamL * (Real.exp (-t) - 1) + t * a) := by
  classical
  have hmean : ∑ _i : Fin m, ∑ q, (ShallowShadows.ShadowNorm.uniformDist (Fin n)).prob q * g q
      = (m : ℝ) * (∑ q, g q) / n := by
    simp only [uniformDist_prob, Fintype.card_fin, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    ring
  have h := chernoff_pi (fun _ : Fin m => ShallowShadows.ShadowNorm.uniformDist (Fin n))
    (fun _ q => g q) (fun _ q => hg q) lamL lamH t a (hmean ▸ hL) (hmean ▸ hH) ht
  rw [pr_uniform_eq_pr_pi, pr_uniform_eq_pr_pi, pr_eq_sum, pr_eq_sum]
  exact h

lemma lower_tail {m n : ℕ} [NeZero n] (g : Fin n → ℝ) (hg : ∀ q, 0 ≤ g q ∧ g q ≤ 1)
    (lamL : ℝ) (h0 : 0 ≤ lamL) (hL : lamL ≤ (m : ℝ) * (∑ q, g q) / n) :
    pr (ShallowShadows.ShadowNorm.uniformDist (Fin m → Fin n))
      (fun ω => ∑ j, g (ω j) ≤ lamL / 2) ≤ Real.exp (-(3 / 20) * lamL) := by
  have h := (chern g hg lamL _ (Real.log 2) (lamL / 2) hL le_rfl
    (Real.log_nonneg (by norm_num))).2
  refine h.trans (Real.exp_le_exp.mpr ?_)
  rw [Real.exp_neg, Real.exp_log (by norm_num)]
  have := Real.log_two_lt_d9
  nlinarith

lemma upper_tail {m n : ℕ} [NeZero n] (g : Fin n → ℝ) (hg : ∀ q, 0 ≤ g q ∧ g q ≤ 1)
    (lamH a : ℝ) (h0 : 0 ≤ lamH) (hH : (m : ℝ) * (∑ q, g q) / n ≤ lamH) (ha : 4 * lamH ≤ a) :
    pr (ShallowShadows.ShadowNorm.uniformDist (Fin m → Fin n))
      (fun ω => a ≤ ∑ j, g (ω j)) ≤ Real.exp (-(17 / 10) * lamH) := by
  have h := (chern g hg _ lamH (Real.log 2) a le_rfl hH
    (Real.log_nonneg (by norm_num))).1
  refine h.trans (Real.exp_le_exp.mpr ?_)
  rw [Real.exp_log (by norm_num)]
  have := Real.log_two_gt_d9
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith

lemma L_ge_one {n : ℕ} (hn : 2 ≤ n) : 1 ≤ L n := by
  unfold L
  rw [Real.le_log_iff_exp_le (by positivity)]
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

lemma exp_le_npow {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x ≤ -(30 * L n)) :
    Real.exp x ≤ (n : ℝ) ^ (-30 : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.rpow_def_of_pos hn']
  refine Real.exp_le_exp.mpr ?_
  have : Real.log n ≤ L n := by
    unfold L; exact Real.log_le_log hn' (by linarith)
  linarith

lemma alpha_facts {n : ℕ} (hn : 1 ≤ n) {α : ℝ} (h1 : (n : ℝ) ^ ((1 : ℝ) / 3) ≤ α)
    (h2 : α ≤ (n : ℝ) ^ ((1 : ℝ) / 2)) : 1 ≤ α ∧ α ^ 2 ≤ n ∧ (n : ℝ) ≤ α ^ 3 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have ha1 : 1 ≤ α := le_trans (Real.one_le_rpow hn1 (by norm_num)) h1
  refine ⟨ha1, ?_, ?_⟩
  · calc α ^ 2 ≤ ((n : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 := pow_le_pow_left₀ (by linarith) h2 2
      _ = n := by rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]; norm_num
  · calc (n : ℝ) = ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]; norm_num
      _ ≤ α ^ 3 := pow_le_pow_left₀ (by positivity) h1 3



lemma rowNbrs_eq {n : ℕ} (G : AdjList n) (m : Fin n → ℕ → Option (Option (Fin n))) (v : Fin n)
    (D : ℕ) (hm : ∀ i, 1 ≤ i → i ≤ D → m v i = some (G.nbr v i))
    (hD : (G.adj v).length ≤ D) : rowNbrs m v D = (G.adj v).toFinset := by
  classical
  ext u
  simp only [rowNbrs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Icc,
    List.mem_toFinset]
  constructor
  · rintro ⟨i, ⟨hi1, hi2⟩, h⟩
    rw [hm i hi1 hi2] at h
    simp only [Option.some.injEq, AdjList.nbr] at h
    split_ifs at h with hc
    exact List.mem_of_getElem? h
  · intro hu
    obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hu
    refine ⟨idx + 1, ⟨by omega, by omega⟩, ?_⟩
    rw [hm _ (by omega) (by omega)]
    simp [AdjList.nbr, hidx, Nat.succ_le_of_lt hidx]

lemma mem_rowq {n s D : ℕ} (ω : Fin s → Fin n) (j : Fin s) :
    Query.deg (ω j) ∈ (List.ofFn fun j => rowQueries (ω j) D).flatten ∧
    ∀ i, 1 ≤ i → i ≤ D → Query.nbr (ω j) i ∈ (List.ofFn fun j => rowQueries (ω j) D).flatten := by
  constructor
  · exact List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨j, rfl⟩, by simp [rowQueries]⟩
  · intro i h1 h2
    refine List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨j, rfl⟩, ?_⟩
    simp only [rowQueries, List.mem_cons, List.mem_map, List.mem_range]
    right
    exact ⟨i - 1, by omega, by congr 1; omega⟩

lemma len_rowq {n s D : ℕ} (ω : Fin s → Fin n) :
    ((List.ofFn fun j => rowQueries (ω j) D).flatten).length = s * (D + 1) := by
  simp [List.length_flatten, List.sum_ofFn, rowQueries]

noncomputable def Z {n : ℕ} (G : AdjList n) (α : ℝ) (k : ℕ) (H : Finset (Fin n)) (v : Fin n) : ℝ :=
  open Classical in if v ∈ U G α k then (dHbar G H v : ℝ) else 0

lemma mem_U {n : ℕ} (G : AdjList n) (α : ℝ) (k : ℕ) (v : Fin n) :
    v ∈ U G α k ↔ (G.adj v).length < Delta k α := by
  simp [U, V1]

lemma run_resTest (n : ℕ) [NeZero n] (α : ℝ) (k : ℕ) (G : AdjList n)
    (ω : Fin ⌈cc * n * L n / α ^ 2⌉₊ → Fin n) (H : Finset (Fin n)) :
    (resTest n α k).run G ω H = decide ((k : ℝ) * α / 8 ≤ (n : ℝ) / ⌈cc * n * L n / α ^ 2⌉₊ *
        ∑ j, Z G α k H (ω j)) := by
  classical
  simp only [RandAlg.run, resTest]
  congr 3
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨hd, hn⟩ := mem_rowq (D := Delta k α) ω j
  simp only [hd, if_true, Option.mem_def, Option.some.injEq, exists_eq_left']
  unfold Z
  by_cases hU : (G.adj (ω j)).length < Delta k α
  · rw [if_pos hU, if_pos ((mem_U G α k _).mpr hU), rowNbrs_eq G _ _ _ _ hU.le]
    · rfl
    · intro i h1 h2
      simp only [hn i h1 h2, if_true]
  · rw [if_neg hU, if_neg (fun h => hU ((mem_U G α k _).mp h))]

end NAMatchEst.Aux36

open NAMatchEst NAMatchEst.Kit

theorem solution : ∃ D : ℝ, ∃ N₀ : ℕ, ∀ (n : ℕ) [NeZero n], N₀ ≤ n → ∀ (α : ℝ) (k : ℕ),
    (n : ℝ) ^ ((1 : ℝ) / 3) ≤ α → α ≤ (n : ℝ) ^ ((1 : ℝ) / 2) → α ≤ k → (k : ℝ) ≤ n → α ^ 2 < k →
    (∀ (G : AdjList n) (H : Finset (Fin n)), (k : ℝ) * α / 4 ≤ RH G α k H →
      1 - (n : ℝ) ^ (-30 : ℝ) ≤ (resTest n α k).prob G (fun f => f H = true)) ∧
    (∀ (G : AdjList n) (H : Finset (Fin n)), (RH G α k H : ℝ) ≤ k * α / 100 →
      1 - (n : ℝ) ^ (-30 : ℝ) ≤ (resTest n α k).prob G (fun f => f H = false)) ∧
    (resTest n α k).CostLE (D * n * k * L n / α ^ 3) := by
  classical
  refine ⟨3 * (cc + 1), 2, fun n _ hn α k h1 h2 hk hkn _ => ?_⟩
  obtain ⟨hα1, hα2, hα3⟩ := Aux36.alpha_facts (by omega) h1 h2
  have hL1 : 1 ≤ L n := Aux36.L_ge_one hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hk0 : (0 : ℝ) < k := by linarith
  have hα0 : (0 : ℝ) < α := by linarith
  have hcc : cc = 10 ^ 5 := rfl
  set s : ℕ := ⌈cc * n * L n / α ^ 2⌉₊ with hs
  set Δ : ℕ := Delta k α with hΔdef
  have hs1 : cc * n * L n / α ^ 2 ≤ (s : ℝ) := Nat.le_ceil _
  have hs2 : (s : ℝ) < cc * n * L n / α ^ 2 + 1 := Nat.ceil_lt_add_one (by rw [hcc]; positivity)
  have hsα : cc * L n * n ≤ (s : ℝ) * α ^ 2 := by
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < α ^ 2)).mp hs1
    linarith
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le (by rw [hcc]; positivity) hs1
  have hΔle : (Δ : ℝ) ≤ 2 * k / α := Nat.floor_le (by positivity)
  have hΔ2 : 2 ≤ Δ := by
    apply Nat.le_floor
    rw [le_div_iff₀ hα0]; push_cast; linarith
  have hΔ0 : (0 : ℝ) < Δ := by exact_mod_cast (show 0 < Δ by omega)
  have hΔα : (Δ : ℝ) * α ≤ 2 * k := by
    have := (le_div_iff₀ hα0).mp hΔle; linarith
  -- key lower bound: 2 s k α ≥ cc L n Δ
  have hkey : cc * L n * n * Δ ≤ 2 * (s : ℝ) * k * α := by
    have e1 : cc * L n * n * Δ ≤ (s : ℝ) * α ^ 2 * Δ := mul_le_mul_of_nonneg_right hsα hΔ0.le
    have e2 : (s : ℝ) * α ^ 2 * Δ ≤ 2 * (s : ℝ) * k * α := by
      have := mul_le_mul_of_nonneg_left hΔα (by positivity : (0 : ℝ) ≤ s * α)
      nlinarith
    linarith
  have hg : ∀ (G : AdjList n) (H : Finset (Fin n)) (q : Fin n),
      0 ≤ Aux36.Z G α k H q / Δ ∧ Aux36.Z G α k H q / Δ ≤ 1 := by
    intro G H q
    unfold Aux36.Z
    split_ifs with hq
    · refine ⟨by positivity, ?_⟩
      rw [div_le_one hΔ0]
      have h3 := (Aux36.mem_U G α k q).mp hq
      have h4 : dHbar G H q ≤ (G.adj q).length :=
        (Finset.card_le_card Finset.sdiff_subset).trans (List.toFinset_card_le _)
      exact_mod_cast (h4.trans h3.le)
    · simp
  have hsum : ∀ (G : AdjList n) (H : Finset (Fin n)),
      ∑ q, Aux36.Z G α k H q / Δ = (RH G α k H : ℝ) / Δ := by
    intro G H
    rw [← Finset.sum_div]
    congr 1
    simp only [Aux36.Z, RH]
    rw [← Finset.sum_filter]
    push_cast
    simp
  -- the acceptance event in normalized form
  have hacc : ∀ (G : AdjList n) (H : Finset (Fin n)) (ω : Fin s → Fin n),
      ((k : ℝ) * α / 8 ≤ (n : ℝ) / s * ∑ j, Aux36.Z G α k H (ω j)) ↔
      (s : ℝ) * k * α / (8 * n * Δ) ≤ ∑ j, Aux36.Z G α k H (ω j) / Δ := by
    intro G H ω
    rw [← Finset.sum_div]
    set S := ∑ j, Aux36.Z G α k H (ω j)
    have e1 : (n : ℝ) / s * S = (n * Δ / s) * (S / Δ) := by field_simp
    have e2 : (k : ℝ) * α / 8 = (n * Δ / s) * ((s : ℝ) * k * α / (8 * n * Δ)) := by field_simp
    rw [e1, e2]
    exact mul_le_mul_iff_of_pos_left (by positivity)
  have hprob : ∀ (G : AdjList n) (H : Finset (Fin n)) (P : Bool → Prop),
      (resTest n α k).prob G (fun f => P (f H)) =
      pr (ShallowShadows.ShadowNorm.uniformDist (Fin s → Fin n))
        (fun ω => P (decide ((s : ℝ) * k * α / (8 * n * Δ) ≤
          ∑ j, Aux36.Z G α k H (ω j) / Δ))) := by
    intro G H P
    rw [prob_eq_pr]
    show pr (ShallowShadows.ShadowNorm.uniformDist (Fin s → Fin n)) _ = _
    refine pr_congr _ fun ω => ?_
    rw [Aux36.run_resTest n α k G ω H]
    rw [decide_eq_decide.mpr (hacc G H ω)]
  refine ⟨fun G H hR => ?_, fun G H hR => ?_, fun (ω : Fin s → Fin n) => ?_⟩
  · -- yes case: lower tail
    rw [hprob G H (· = true)]
    set lam : ℝ := (s : ℝ) * k * α / (4 * n * Δ) with hlam
    have hlam0 : 0 ≤ lam := by positivity
    have hmean : lam ≤ (s : ℝ) * (∑ q, Aux36.Z G α k H q / Δ) / n := by
      rw [hsum, hlam]
      rw [show (s : ℝ) * ((RH G α k H : ℝ) / Δ) / n = (s : ℝ) * RH G α k H / (n * Δ) by
        field_simp]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h8 : (0 : ℝ) ≤ 4 * RH G α k H - k * α := by linarith
      nlinarith [mul_nonneg (mul_nonneg hs0.le h8) (mul_pos hn0 hΔ0).le]
    have ht := Aux36.lower_tail (m := s) _ (hg G H) lam hlam0 hmean
    have hlamL : cc * L n / 8 ≤ lam := by
      rw [hlam, le_div_iff₀ (by positivity)]; nlinarith
    have hle : pr (ShallowShadows.ShadowNorm.uniformDist (Fin s → Fin n))
        (fun ω => ¬ (decide ((s : ℝ) * k * α / (8 * n * Δ) ≤
          ∑ j, Aux36.Z G α k H (ω j) / Δ) = true)) ≤ (n : ℝ) ^ (-30 : ℝ) := by
      refine le_trans (pr_mono _ fun ω hω => ?_)
        (ht.trans (Aux36.exp_le_npow (n := n) (by omega) ?_))
      · simp only [decide_eq_true_iff, not_le] at hω
        apply le_of_lt; convert hω using 1; rw [hlam]; field_simp; ring
      · rw [hcc] at hlamL; norm_num at hlamL; linarith
    rw [pr_not] at hle
    linarith
  · -- no case: upper tail
    rw [hprob G H (· = false)]
    set lam : ℝ := (s : ℝ) * k * α / (100 * n * Δ) with hlam
    have hlam0 : 0 ≤ lam := by positivity
    have hmean : (s : ℝ) * (∑ q, Aux36.Z G α k H q / Δ) / n ≤ lam := by
      rw [hsum, hlam]
      rw [show (s : ℝ) * ((RH G α k H : ℝ) / Δ) / n = (s : ℝ) * RH G α k H / (n * Δ) by
        field_simp]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h8 : (0 : ℝ) ≤ k * α - 100 * RH G α k H := by linarith
      nlinarith [mul_nonneg (mul_nonneg hs0.le h8) (mul_pos hn0 hΔ0).le]
    have h125 : (s : ℝ) * k * α / (8 * n * Δ) = 25 / 2 * lam := by
      rw [hlam]; field_simp; ring
    have ht := Aux36.upper_tail (m := s) _ (hg G H) lam ((s : ℝ) * k * α / (8 * n * Δ)) hlam0 hmean
      (by rw [h125]; linarith)
    have hlamL : cc * L n / 200 ≤ lam := by
      rw [hlam, le_div_iff₀ (by positivity)]; nlinarith
    have hle : pr (ShallowShadows.ShadowNorm.uniformDist (Fin s → Fin n))
        (fun ω => ¬ (decide ((s : ℝ) * k * α / (8 * n * Δ) ≤
          ∑ j, Aux36.Z G α k H (ω j) / Δ) = false)) ≤ (n : ℝ) ^ (-30 : ℝ) := by
      refine le_trans (pr_mono _ fun ω hω => ?_)
        (ht.trans (Aux36.exp_le_npow (n := n) (by omega) ?_))
      · simpa using hω
      · rw [hcc] at hlamL; norm_num at hlamL; linarith
    rw [pr_not] at hle
    linarith
  · -- cost
    show (((List.ofFn fun j => rowQueries (ω j) Δ).flatten).length : ℝ) ≤ _
    rw [Aux36.len_rowq]
    push_cast
    have hA : (s : ℝ) ≤ (cc + 1) * (n * L n / α ^ 2) := by
      have h1' : 1 ≤ (n : ℝ) * L n / α ^ 2 := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      have : cc * n * L n / α ^ 2 = cc * (n * L n / α ^ 2) := by ring
      nlinarith
    have hB : (Δ : ℝ) + 1 ≤ 3 * (k / α) := by
      have : 1 ≤ (k : ℝ) / α := by rw [le_div_iff₀ hα0]; linarith
      have : 2 * (k : ℝ) / α = 2 * (k / α) := by ring
      linarith
    calc (s : ℝ) * (Δ + 1) ≤ ((cc + 1) * (n * L n / α ^ 2)) * (3 * (k / α)) :=
          mul_le_mul hA hB (by positivity) (by rw [hcc]; positivity)
      _ = 3 * (cc + 1) * n * k * L n / α ^ 3 := by field_simp
