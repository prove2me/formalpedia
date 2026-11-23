-- Prove2me | solution 1 for NAMatchEst.lemma_3_11
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T00:39:03.169794+00:00
-- url     : https://prove2.me/submissions/a526038b-3045-4322-9b53-21b58c7640e5

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
import Definitions.Def_NAMatchEst_V1
import Definitions.Def_NAMatchEst_U
import Definitions.Def_NAMatchEst_dU
import Definitions.Def_NAMatchEst_V1H
import Definitions.Def_NAMatchEst_pilot


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



namespace NAMatchEst.Aux311
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

lemma mem_U {n : ℕ} (G : AdjList n) (α : ℝ) (k : ℕ) (v : Fin n) :
    v ∈ U G α k ↔ (G.adj v).length < Delta k α := by
  simp [U, V1]


/-- The pilot count `X_v`. -/
noncomputable def Xc {n s : ℕ} (G : AdjList n) (α : ℝ) (k : ℕ) (v : Fin n) (ω : Fin s → Fin n) :
    ℕ :=
  open Classical in (Finset.univ.filter fun j => ω j ∈ U G α k ∧ v ∈ G.adj (ω j)).card

/-- Indicator whose sum over the draws is `X_v`. -/
noncomputable def gX {n : ℕ} (G : AdjList n) (α : ℝ) (k : ℕ) (v : Fin n) (q : Fin n) : ℝ :=
  open Classical in if q ∈ U G α k ∧ v ∈ G.adj q then 1 else 0

lemma run_pilot (n : ℕ) [NeZero n] (α : ℝ) (k : ℕ) (G : AdjList n)
    (ω : Fin ⌈n * L n / α ^ 2⌉₊ → Fin n) :
    (pilot n α k).run G ω = Finset.univ.filter fun v => ⌈128 * L n⌉₊ ≤ Xc G α k v ω := by
  classical
  simp only [RandAlg.run, pilot]
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Xc]
  rw [Finset.filter_congr (q := fun j => ω j ∈ U G α k ∧ v ∈ G.adj (ω j)) (fun j _ => ?_)]
  · convert Iff.rfl; simp
  obtain ⟨hd, hn⟩ := mem_rowq (D := Delta k α) ω j
  simp only [hd, if_true, Option.mem_def, Option.some.injEq, exists_eq_left', mem_U]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [rowNbrs_eq G _ _ _ (fun i h1 h2 => by simp only [hn i h1 h2, if_true]) h1.le] at h2
    exact List.mem_toFinset.mp h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [rowNbrs_eq G _ _ _ (fun i h1 h2 => by simp only [hn i h1 h2, if_true]) h1.le]
    exact List.mem_toFinset.mpr h2

lemma Xc_eq_sum {n s : ℕ} (G : AdjList n) (α : ℝ) (k : ℕ) (v : Fin n) (ω : Fin s → Fin n) :
    (Xc G α k v ω : ℝ) = ∑ j, gX G α k v (ω j) := by
  classical
  unfold Xc gX
  rw [Finset.natCast_card_filter]

lemma sum_gX {n : ℕ} (G : AdjList n) (α : ℝ) (k : ℕ) (v : Fin n) :
    ∑ q, gX G α k v q = (dU G α k v : ℝ) := by
  classical
  unfold gX dU
  rw [Finset.sum_boole]
  congr 2
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter, List.mem_toFinset]
  rw [G.symm v q]
  tauto

lemma gX_mem {n : ℕ} (G : AdjList n) (α : ℝ) (k : ℕ) (v q : Fin n) :
    0 ≤ gX G α k v q ∧ gX G α k v q ≤ 1 := by
  unfold gX; split_ifs <;> norm_num

lemma sum_Xc_le {n s : ℕ} (G : AdjList n) (α : ℝ) (k : ℕ) (ω : Fin s → Fin n) :
    ∑ v, Xc G α k v ω ≤ s * Delta k α := by
  classical
  unfold Xc
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  calc ∑ j, ∑ v, (if ω j ∈ U G α k ∧ v ∈ G.adj (ω j) then 1 else 0)
      ≤ ∑ _j : Fin s, Delta k α := Finset.sum_le_sum fun j _ => by
        rw [← Finset.card_filter]
        by_cases hU : ω j ∈ U G α k
        · calc _ ≤ (G.adj (ω j)).toFinset.card :=
                Finset.card_le_card fun v hv => by simp at hv ⊢; exact hv.2
            _ ≤ (G.adj (ω j)).length := List.toFinset_card_le _
            _ ≤ Delta k α := ((mem_U G α k _).mp hU).le
        · simp [hU]
    _ = s * Delta k α := by simp

lemma pr_false {Ω : Type} [Fintype Ω] (d : WildeQIT.FinDist Ω) : pr d (fun _ => False) = 0 := by
  unfold pr; simp

lemma union_bound_val {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * (2 * Real.exp (-(31 * L n))) ≤ (n : ℝ) ^ (-30 : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have e : Real.exp (-(31 * L n)) = (2 * (n : ℝ))⁻¹ * Real.exp (-(30 * L n)) := by
    rw [show -(31 * L n) = -L n + -(30 * L n) by ring, Real.exp_add, Real.exp_neg]
    unfold L; rw [Real.exp_log (by positivity)]
  rw [e]
  have : (n : ℝ) * (2 * ((2 * (n : ℝ))⁻¹ * Real.exp (-(30 * L n)))) = Real.exp (-(30 * L n)) := by
    field_simp
  rw [this]
  exact exp_le_npow hn le_rfl

end NAMatchEst.Aux311

open NAMatchEst NAMatchEst.Kit

theorem solution : ∃ D : ℝ, ∃ N₀ : ℕ, ∀ (n : ℕ) [NeZero n], N₀ ≤ n → ∀ (α : ℝ) (k : ℕ),
    (n : ℝ) ^ ((1 : ℝ) / 3) ≤ α → α ≤ (n : ℝ) ^ ((1 : ℝ) / 2) → α ≤ k → (k : ℝ) ≤ n → α ^ 2 < k →
    (pilot n α k).CostLE (D * n * k * L n / α ^ 3) ∧
    ∀ G : AdjList n,
      (∀ ω, (((pilot n α k).run G ω).card : ℝ) ≤ k / 32) ∧
      1 - (n : ℝ) ^ (-30 : ℝ) ≤ (pilot n α k).prob G (fun H =>
        V1H G α k ⊆ H ∧ H ⊆ Finset.univ.filter (fun v => 16 * α ^ 2 < (dU G α k v : ℝ)) ∧
          Finset.univ.filter (fun v => 16 * α ^ 2 < (dU G α k v : ℝ)) ⊆ V1 G α k) ∧
      1 - (n : ℝ) ^ (-30 : ℝ) ≤ (pilot n α k).prob G (fun H => V1H G α k ⊆ H ∧ H ⊆ V1 G α k) := by
  classical
  refine ⟨6, 2, fun n _ hn α k h1 h2 hk hkn _ => ?_⟩
  obtain ⟨hα1, hα2, hα3⟩ := Aux311.alpha_facts (by omega) h1 h2
  have hL1 : 1 ≤ L n := Aux311.L_ge_one hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hk0 : (0 : ℝ) < k := by linarith
  have hα0 : (0 : ℝ) < α := by linarith
  set s : ℕ := ⌈n * L n / α ^ 2⌉₊ with hs
  set Δ : ℕ := Delta k α with hΔdef
  set T : ℕ := ⌈128 * L n⌉₊ with hT
  have hs1 : n * L n / α ^ 2 ≤ (s : ℝ) := Nat.le_ceil _
  have hs2 : (s : ℝ) < n * L n / α ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hsα : L n * n ≤ (s : ℝ) * α ^ 2 := by
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < α ^ 2)).mp hs1
    linarith
  have hs0 : (0 : ℝ) ≤ s := by positivity
  have hT1 : 128 * L n ≤ (T : ℝ) := Nat.le_ceil _
  have hT2 : (T : ℝ) < 128 * L n + 1 := Nat.ceil_lt_add_one (by positivity)
  have hΔle : (Δ : ℝ) ≤ 2 * k / α := Nat.floor_le (by positivity)
  have hΔα : (Δ : ℝ) * α ≤ 2 * k := by
    have := (le_div_iff₀ hα0).mp hΔle; linarith
  have hnL : 1 ≤ (n : ℝ) * L n / α ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  -- deterministic inclusion
  have hdet : ∀ G : AdjList n,
      Finset.univ.filter (fun v => 16 * α ^ 2 < (dU G α k v : ℝ)) ⊆ V1 G α k := by
    intro G v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simp only [V1, Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hlt
    push Not at hlt
    have hd : dU G α k v ≤ (G.adj v).length :=
      (Finset.card_le_card Finset.inter_subset_left).trans (List.toFinset_card_le _)
    have hd' : (dU G α k v : ℝ) < Δ := by exact_mod_cast (lt_of_le_of_lt hd hlt)
    have h3 : (Δ : ℝ) * α ≤ 2 * n := by linarith
    have h4 : (dU G α k v : ℝ) * α ≤ 16 * α ^ 2 * α := by nlinarith
    nlinarith
  refine ⟨fun (ω : Fin s → Fin n) => ?_, fun G => ?_⟩
  · -- cost
    show (((List.ofFn fun j => rowQueries (ω j) Δ).flatten).length : ℝ) ≤ _
    rw [Aux311.len_rowq]
    push_cast
    have hA : (s : ℝ) ≤ 2 * (n * L n / α ^ 2) := by linarith
    have hB : (Δ : ℝ) + 1 ≤ 3 * (k / α) := by
      have : 1 ≤ (k : ℝ) / α := by rw [le_div_iff₀ hα0]; linarith
      have : 2 * (k : ℝ) / α = 2 * (k / α) := by ring
      linarith
    calc (s : ℝ) * (Δ + 1) ≤ (2 * (n * L n / α ^ 2)) * (3 * (k / α)) :=
          mul_le_mul hA hB (by positivity) (by positivity)
      _ = 6 * n * k * L n / α ^ 3 := by field_simp; ring
  -- the good event
  set Good : (Fin s → Fin n) → Prop := fun ω => ∀ v,
    (512 * α ^ 2 ≤ (dU G α k v : ℝ) → T ≤ Aux311.Xc G α k v ω) ∧
    ((dU G α k v : ℝ) ≤ 16 * α ^ 2 → Aux311.Xc G α k v ω < T) with hGood
  have hgood : 1 - (n : ℝ) ^ (-30 : ℝ) ≤ pr (ShallowShadows.ShadowNorm.uniformDist (Fin s → Fin n))
      Good := by
    have hbad : pr (ShallowShadows.ShadowNorm.uniformDist (Fin s → Fin n)) (fun ω => ¬ Good ω)
        ≤ (n : ℝ) ^ (-30 : ℝ) := by
      have hsub := pr_exists_le (ShallowShadows.ShadowNorm.uniformDist (Fin s → Fin n))
        Finset.univ (fun v ω => (512 * α ^ 2 ≤ (dU G α k v : ℝ) ∧ Aux311.Xc G α k v ω < T) ∨
          ((dU G α k v : ℝ) ≤ 16 * α ^ 2 ∧ T ≤ Aux311.Xc G α k v ω))
      have hper : ∀ v : Fin n, pr (ShallowShadows.ShadowNorm.uniformDist (Fin s → Fin n))
          (fun ω => (512 * α ^ 2 ≤ (dU G α k v : ℝ) ∧ Aux311.Xc G α k v ω < T) ∨
            ((dU G α k v : ℝ) ≤ 16 * α ^ 2 ∧ T ≤ Aux311.Xc G α k v ω)) ≤
          2 * Real.exp (-(31 * L n)) := by
        intro v
        refine (pr_or_le _ _ _).trans ?_
        rw [two_mul]
        apply add_le_add
        · by_cases hv : 512 * α ^ 2 ≤ (dU G α k v : ℝ)
          · have hmean : 512 * L n ≤ (s : ℝ) * (∑ q, Aux311.gX G α k v q) / n := by
              rw [Aux311.sum_gX, le_div_iff₀ hn0]
              nlinarith
            have ht := Aux311.lower_tail (m := s) _ (Aux311.gX_mem G α k v) (512 * L n)
              (by positivity) hmean
            refine le_trans (pr_mono _ fun ω hω => ?_) (ht.trans (Real.exp_le_exp.mpr ?_))
            · have h5 := hω.2
              have h6 : (Aux311.Xc G α k v ω : ℝ) < T := by exact_mod_cast h5
              rw [Aux311.Xc_eq_sum] at h6
              linarith
            · linarith
          · refine le_trans (pr_mono _ fun ω hω => ?_) ((Aux311.pr_false _).le.trans (Real.exp_pos _).le)
            exact hv hω.1
        · by_cases hv : (dU G α k v : ℝ) ≤ 16 * α ^ 2
          · have hmean : (s : ℝ) * (∑ q, Aux311.gX G α k v q) / n ≤ 32 * L n := by
              rw [Aux311.sum_gX, div_le_iff₀ hn0]
              have e1 : (s : ℝ) * dU G α k v ≤ s * (16 * α ^ 2) :=
                mul_le_mul_of_nonneg_left hv hs0
              have e2 : (s : ℝ) * (16 * α ^ 2) ≤ (n * L n / α ^ 2 + 1) * (16 * α ^ 2) :=
                mul_le_mul_of_nonneg_right hs2.le (by positivity)
              have e3 : (n * L n / α ^ 2 + 1) * (16 * α ^ 2) = 16 * n * L n + 16 * α ^ 2 := by
                field_simp
              nlinarith
            have ht := Aux311.upper_tail (m := s) _ (Aux311.gX_mem G α k v) (32 * L n) (T : ℝ)
              (by positivity) hmean (by linarith)
            refine le_trans (pr_mono _ fun ω hω => ?_) (ht.trans (Real.exp_le_exp.mpr ?_))
            · have h6 : (T : ℝ) ≤ Aux311.Xc G α k v ω := by exact_mod_cast hω.2
              rw [Aux311.Xc_eq_sum] at h6
              exact h6
            · linarith
          · refine le_trans (pr_mono _ fun ω hω => ?_) ((Aux311.pr_false _).le.trans (Real.exp_pos _).le)
            exact hv hω.1
      refine le_trans (pr_mono _ fun ω hω => ?_) (hsub.trans ?_)
      · simp only [hGood, not_forall] at hω
        obtain ⟨v, hv⟩ := hω
        refine ⟨v, Finset.mem_univ _, ?_⟩
        by_cases ha : 512 * α ^ 2 ≤ (dU G α k v : ℝ)
        · by_cases hb : T ≤ Aux311.Xc G α k v ω
          · right
            have : ¬ ((dU G α k v : ℝ) ≤ 16 * α ^ 2 → Aux311.Xc G α k v ω < T) := by
              intro h; exact hv ⟨fun _ => hb, h⟩
            push Not at this
            exact ⟨this.1, this.2⟩
          · left; exact ⟨ha, by omega⟩
        · right
          have : ¬ ((dU G α k v : ℝ) ≤ 16 * α ^ 2 → Aux311.Xc G α k v ω < T) := by
            intro h; exact hv ⟨fun h' => absurd h' ha, h⟩
          push Not at this
          exact ⟨this.1, this.2⟩
      · calc ∑ v : Fin n, pr (ShallowShadows.ShadowNorm.uniformDist (Fin s → Fin n))
              (fun ω => (512 * α ^ 2 ≤ (dU G α k v : ℝ) ∧ Aux311.Xc G α k v ω < T) ∨
                ((dU G α k v : ℝ) ≤ 16 * α ^ 2 ∧ T ≤ Aux311.Xc G α k v ω))
            ≤ ∑ _v : Fin n, 2 * Real.exp (-(31 * L n)) := Finset.sum_le_sum fun v _ => hper v
          _ = (n : ℝ) * (2 * Real.exp (-(31 * L n))) := by simp
          _ ≤ _ := Aux311.union_bound_val (by omega)
    rw [pr_not] at hbad
    linarith
  have hprob : ∀ P : Finset (Fin n) → Prop,
      (∀ ω, Good ω → P (Finset.univ.filter fun v => T ≤ Aux311.Xc G α k v ω)) →
      1 - (n : ℝ) ^ (-30 : ℝ) ≤ (pilot n α k).prob G P := by
    intro P hP
    rw [prob_eq_pr]
    show _ ≤ pr (ShallowShadows.ShadowNorm.uniformDist (Fin s → Fin n)) _
    refine hgood.trans (pr_mono _ fun ω hω => ?_)
    rw [Aux311.run_pilot n α k G ω]
    exact hP ω hω
  have hsand : ∀ ω, Good ω →
      V1H G α k ⊆ (Finset.univ.filter fun v => T ≤ Aux311.Xc G α k v ω) ∧
      (Finset.univ.filter fun v => T ≤ Aux311.Xc G α k v ω) ⊆
        Finset.univ.filter (fun v => 16 * α ^ 2 < (dU G α k v : ℝ)) := by
    intro ω hω
    constructor
    · intro v hv
      simp only [V1H, Finset.mem_filter] at hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hω v).1 hv.2
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      by_contra hc
      push Not at hc
      have := (hω v).2 hc
      omega
  refine ⟨fun ω => ?_, hprob _ fun ω hω => ⟨(hsand ω hω).1, (hsand ω hω).2, hdet G⟩,
    hprob _ fun ω hω => ⟨(hsand ω hω).1, (hsand ω hω).2.trans (hdet G)⟩⟩
  -- size bound
  rw [Aux311.run_pilot n α k G ω]
  set Hs := Finset.univ.filter fun v => T ≤ Aux311.Xc G α k v ω
  have hnat : Hs.card * T ≤ s * Δ := by
    calc Hs.card * T = Hs.card • T := by rw [smul_eq_mul]
      _ ≤ ∑ v ∈ Hs, Aux311.Xc G α k v ω := Finset.card_nsmul_le_sum _ _ _ fun v hv => by
          simp only [Hs, Finset.mem_filter] at hv; exact hv.2
      _ ≤ ∑ v, Aux311.Xc G α k v ω := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ ≤ s * Δ := Aux311.sum_Xc_le G α k ω
  have hreal : (Hs.card : ℝ) * T ≤ s * Δ := by exact_mod_cast hnat
  have hc0 : (0 : ℝ) ≤ Hs.card := by positivity
  have h128 : (Hs.card : ℝ) * (128 * L n) ≤ s * Δ :=
    le_trans (mul_le_mul_of_nonneg_left hT1 hc0) hreal
  have hsΔ : (s : ℝ) * Δ ≤ 4 * L n * k := by
    have e1 : (s : ℝ) ≤ 2 * L n * α - 1 + 1 := by
      have : n * L n / α ^ 2 ≤ L n * α := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      nlinarith
    have e2 : (s : ℝ) * Δ * α ≤ 2 * L n * α * (2 * k) := by
      have : (s : ℝ) * (Δ * α) ≤ (2 * L n * α) * (2 * k) :=
        mul_le_mul (by linarith) hΔα (by positivity) (by positivity)
      linarith
    have e3 : (s : ℝ) * Δ * α ≤ (4 * L n * k) * α := by linarith
    exact le_of_mul_le_mul_right e3 hα0
  rw [le_div_iff₀ (by norm_num)]
  have : (Hs.card : ℝ) * 32 * (4 * L n) ≤ k * (4 * L n) := by linarith
  exact le_of_mul_le_mul_right this (by positivity)
