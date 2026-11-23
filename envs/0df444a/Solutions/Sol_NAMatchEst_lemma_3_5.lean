-- Prove2me | solution 1 for NAMatchEst.lemma_3_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T00:38:08.544101+00:00
-- url     : https://prove2.me/submissions/5e876be9-bc35-476b-81df-7a660c1b43af

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
import Definitions.Def_NAMatchEst_Query
import Definitions.Def_NAMatchEst_L
import Definitions.Def_NAMatchEst_V1
import Definitions.Def_NAMatchEst_degTest


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



namespace NAMatchEst.Aux35
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


noncomputable def gV1 {n : ℕ} (G : AdjList n) (α : ℝ) (k : ℕ) (v : Fin n) : ℝ :=
  open Classical in if v ∈ V1 G α k then 1 else 0

lemma run_degTest (n : ℕ) [NeZero n] (α : ℝ) (k : ℕ) (G : AdjList n)
    (ω : Fin ⌈cc * n * L n / k⌉₊ → Fin n) :
    (degTest n α k).run G ω = decide (((⌈cc * n * L n / k⌉₊ : ℝ) * k / (16 * n)) ≤
      ∑ j, gV1 G α k (ω j)) := by
  classical
  simp only [RandAlg.run, degTest]
  have hm : ∀ j, Query.deg (ω j) ∈ List.ofFn (fun j => Query.deg (ω j)) :=
    fun j => List.mem_ofFn.mpr ⟨j, rfl⟩
  simp only [hm, if_true, Option.mem_def, Option.some.injEq, exists_eq_left']
  rw [Finset.natCast_card_filter]
  congr
  funext j
  simp [gV1, V1]

end NAMatchEst.Aux35

open NAMatchEst NAMatchEst.Kit

theorem solution : ∃ D : ℝ, ∃ N₀ : ℕ, ∀ (n : ℕ) [NeZero n], N₀ ≤ n → ∀ (α : ℝ) (k : ℕ),
    (n : ℝ) ^ ((1 : ℝ) / 3) ≤ α → α ≤ (n : ℝ) ^ ((1 : ℝ) / 2) → α ≤ k → (k : ℝ) ≤ n →
    (∀ G : AdjList n, (k : ℝ) / 8 ≤ (V1 G α k).card →
      1 - (n : ℝ) ^ (-30 : ℝ) ≤ (degTest n α k).prob G (· = true)) ∧
    (∀ G : AdjList n, ((V1 G α k).card : ℝ) ≤ k / 100 →
      1 - (n : ℝ) ^ (-30 : ℝ) ≤ (degTest n α k).prob G (· = false)) ∧
    (degTest n α k).CostLE (D * n * L n / k) ∧
    ∀ ω, ∀ q ∈ (degTest n α k).queries ω, ∃ v, q = Query.deg v := by
  classical
  refine ⟨cc + 1, 2, fun n _ hn α k h1 h2 hk hkn => ?_⟩
  obtain ⟨hα1, hα2, hα3⟩ := Aux35.alpha_facts (by omega) h1 h2
  have hL1 : 1 ≤ L n := Aux35.L_ge_one hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hk0 : (0 : ℝ) < k := by linarith
  have hcc : cc = 10 ^ 5 := rfl
  set s : ℕ := ⌈cc * n * L n / k⌉₊ with hs
  have hs1 : cc * n * L n / k ≤ (s : ℝ) := Nat.le_ceil _
  have hs2 : (s : ℝ) < cc * n * L n / k + 1 := Nat.ceil_lt_add_one (by rw [hcc]; positivity)
  have hsk : cc * L n ≤ (s : ℝ) * k / n := by
    rw [le_div_iff₀ hn0]
    have := (div_le_iff₀ hk0).mp hs1
    linarith
  have hsum : ∀ G : AdjList n, ∑ q, Aux35.gV1 G α k q = ((V1 G α k).card : ℝ) := by
    intro G
    simp only [Aux35.gV1]
    rw [Finset.sum_boole]
    simp
  have hg : ∀ G : AdjList n, ∀ q, 0 ≤ Aux35.gV1 G α k q ∧ Aux35.gV1 G α k q ≤ 1 := by
    intro G q; unfold Aux35.gV1; split_ifs <;> norm_num
  have hprob : ∀ (G : AdjList n) (P : Bool → Prop), (degTest n α k).prob G P =
      pr (ShallowShadows.ShadowNorm.uniformDist (Fin s → Fin n))
        (fun ω => P (decide (((s : ℝ) * k / (16 * n)) ≤ ∑ j, Aux35.gV1 G α k (ω j)))) := by
    intro G P
    rw [prob_eq_pr]
    show pr (ShallowShadows.ShadowNorm.uniformDist (Fin s → Fin n)) _ = _
    refine pr_congr _ fun ω => ?_
    rw [Aux35.run_degTest n α k G ω]
  refine ⟨fun G hV => ?_, fun G hV => ?_, fun ω => ?_, fun ω q hq => ?_⟩
  · -- yes case: lower tail
    rw [hprob]
    set lam : ℝ := (s : ℝ) * k / (8 * n) with hlam
    have hlam0 : 0 ≤ lam := by positivity
    have hmean : lam ≤ (s : ℝ) * (∑ q, Aux35.gV1 G α k q) / n := by
      rw [hsum, hlam, div_le_div_iff₀ (by positivity) hn0]
      have : (0 : ℝ) ≤ s := by positivity
      have h8 : (0 : ℝ) ≤ 8 * (V1 G α k).card - k := by linarith
      nlinarith [mul_nonneg (mul_nonneg this h8) hn0.le]
    have ht := Aux35.lower_tail (m := s) _ (hg G) lam hlam0 hmean
    have hle : pr (ShallowShadows.ShadowNorm.uniformDist (Fin s → Fin n))
        (fun ω => ¬ (decide (((s : ℝ) * k / (16 * n)) ≤ ∑ j, Aux35.gV1 G α k (ω j)) = true)) ≤
        (n : ℝ) ^ (-30 : ℝ) := by
      refine le_trans (pr_mono _ fun ω hω => ?_) (ht.trans (Aux35.exp_le_npow (n := n) (by omega) ?_))
      · simp only [decide_eq_true_iff, not_le] at hω
        rw [hlam]; apply le_of_lt; convert hω using 1; ring
      · have : lam = (s : ℝ) * k / n / 8 := by rw [hlam]; field_simp
        rw [this]; rw [hcc] at hsk; nlinarith
    rw [pr_not] at hle
    linarith
  · -- no case: upper tail
    rw [hprob]
    set lam : ℝ := (s : ℝ) * k / (100 * n) with hlam
    have hlam0 : 0 ≤ lam := by positivity
    have hmean : (s : ℝ) * (∑ q, Aux35.gV1 G α k q) / n ≤ lam := by
      rw [hsum, hlam, div_le_div_iff₀ hn0 (by positivity)]
      have : (0 : ℝ) ≤ s := by positivity
      have h8 : (0 : ℝ) ≤ k - 100 * (V1 G α k).card := by linarith
      nlinarith [mul_nonneg (mul_nonneg this h8) hn0.le]
    have h625 : (s : ℝ) * k / (16 * n) = 25 / 4 * lam := by rw [hlam]; field_simp; ring
    have ht := Aux35.upper_tail (m := s) _ (hg G) lam ((s : ℝ) * k / (16 * n)) hlam0 hmean
      (by rw [h625]; linarith)
    have hle : pr (ShallowShadows.ShadowNorm.uniformDist (Fin s → Fin n))
        (fun ω => ¬ (decide (((s : ℝ) * k / (16 * n)) ≤ ∑ j, Aux35.gV1 G α k (ω j)) = false)) ≤
        (n : ℝ) ^ (-30 : ℝ) := by
      refine le_trans (pr_mono _ fun ω hω => ?_) (ht.trans (Aux35.exp_le_npow (n := n) (by omega) ?_))
      · simpa using hω
      · have : lam = (s : ℝ) * k / n / 100 := by rw [hlam]; field_simp
        rw [this]; rw [hcc] at hsk; nlinarith
    rw [pr_not] at hle
    linarith
  · -- cost
    show ((List.ofFn fun j => Query.deg (ω j)).length : ℝ) ≤ _
    rw [List.length_ofFn]
    have h1' : 1 ≤ (n : ℝ) * L n / k := by
      rw [le_div_iff₀ hk0]; nlinarith
    calc (s : ℝ) ≤ cc * n * L n / k + 1 := hs2.le
      _ ≤ cc * (n * L n / k) + n * L n / k := by
          have : cc * n * L n / k = cc * (n * L n / k) := by ring
          linarith
      _ = (cc + 1) * n * L n / k := by ring
  · -- all queries are degree queries
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
    exact ⟨_, rfl⟩
