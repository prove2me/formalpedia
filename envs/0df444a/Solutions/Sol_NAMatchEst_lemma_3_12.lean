-- Prove2me | solution 1 for NAMatchEst.lemma_3_12
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T00:55:35.612204+00:00
-- url     : https://prove2.me/submissions/3b0f8e0d-86c4-4c8f-93f2-32d57f20b2e2

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
import Definitions.Def_NAMatchEst_largeTrial
import Theorems.Thm_NAMatchEst_lemma_3_3
import Theorems.Thm_NAMatchEst_lemma_3_4
import Theorems.Thm_NAMatchEst_lemma_3_5
import Theorems.Thm_NAMatchEst_lemma_3_6
import Theorems.Thm_NAMatchEst_lemma_3_8
import Theorems.Thm_NAMatchEst_lemma_3_9
import Theorems.Thm_NAMatchEst_lemma_3_11


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



namespace NAMatchEst.AuxE12
open NAMatchEst

/-- The probability of an event of the large trial, written on the product seed space. -/
lemma largeTrial_prob (n : ℕ) [NeZero n] (α : ℝ) (k : ℕ) (G : AdjList n) (P : Bool → Prop) :
    (largeTrial n α k).prob G P =
      Kit.pr ((pilot n α k).dist.prod ((degTest n α k).dist.prod
        ((resTest n α k).dist.prod (edgeTest n α k).dist)))
        (fun ω => P ((degTest n α k).run G ω.2.1 ||
          (resTest n α k).run G ω.2.2.1 ((pilot n α k).run G ω.1) ||
          (open Classical in decide (cc * L n / 4 ≤
            ((((edgeTest n α k).run G ω.2.2.2) ((pilot n α k).run G ω.1)).ZE : ℝ))))) := by
  unfold largeTrial
  rw [Kit.prob_par]
  refine Kit.pr_congr _ fun ω => ?_
  rw [Kit.run_par, Kit.run_par]

lemma deg_pr {n : ℕ} [NeZero n] {α : ℝ} {k : ℕ} {β : Type} [Fintype β]
    (q : WildeQIT.FinDist β) (G : AdjList n) (b : Bool) :
    Kit.pr ((degTest n α k).dist.prod q) (fun ω => (degTest n α k).run G ω.1 = b) =
      (degTest n α k).prob G (· = b) :=
  Kit.pr_prod_fst _ _ (fun x => (degTest n α k).run G x = b)

lemma pr_snd_fst {β γ δ : Type} [Fintype β] [Fintype γ] [Fintype δ] (p : WildeQIT.FinDist β)
    (r : WildeQIT.FinDist γ) (q : WildeQIT.FinDist δ) (E : γ → Prop) :
    Kit.pr (p.prod (r.prod q)) (fun ω => E ω.2.1) = Kit.pr r E := by
  rw [Kit.pr_prod_snd p (r.prod q) (fun y => E y.1), Kit.pr_prod_fst]

lemma pr_snd_snd {β γ δ : Type} [Fintype β] [Fintype γ] [Fintype δ] (p : WildeQIT.FinDist β)
    (r : WildeQIT.FinDist γ) (q : WildeQIT.FinDist δ) (E : δ → Prop) :
    Kit.pr (p.prod (r.prod q)) (fun ω => E ω.2.2) = Kit.pr q E := by
  rw [Kit.pr_prod_snd p (r.prod q) (fun y => E y.2), Kit.pr_prod_snd]

lemma res_pr {n : ℕ} [NeZero n] {α : ℝ} {k : ℕ} {β γ : Type} [Fintype β] [Fintype γ]
    (p : WildeQIT.FinDist β) (q : WildeQIT.FinDist γ) (G : AdjList n) (H : Finset (Fin n))
    (b : Bool) :
    Kit.pr (p.prod ((resTest n α k).dist.prod q)) (fun ω => (resTest n α k).run G ω.2.1 H = b) =
      (resTest n α k).prob G (fun f => f H = b) := by
  exact pr_snd_fst p (resTest n α k).dist q (fun x => (resTest n α k).run G x H = b)

lemma edge_pr {n : ℕ} [NeZero n] {α : ℝ} {k : ℕ} {β γ : Type} [Fintype β] [Fintype γ]
    (p : WildeQIT.FinDist β) (q : WildeQIT.FinDist γ) (G : AdjList n) (H : Finset (Fin n))
    (E : EdgeStats n → Prop) :
    Kit.pr (p.prod (q.prod (edgeTest n α k).dist)) (fun ω => E ((edgeTest n α k).run G ω.2.2 H)) =
      (edgeTest n α k).prob G (fun o => E (o H)) := by
  exact pr_snd_snd p q (edgeTest n α k).dist (fun x => E ((edgeTest n α k).run G x H))

/-- The seed law of the three tests run after the pilot. -/
noncomputable abbrev Qd (n : ℕ) [NeZero n] (α : ℝ) (k : ℕ) :=
  (degTest n α k).dist.prod ((resTest n α k).dist.prod (edgeTest n α k).dist)

lemma prob_compl {n : ℕ} {β : Type} (A : RandAlg n β) (G : AdjList n) (P : β → Prop) :
    A.prob G (fun x => ¬ P x) = 1 - A.prob G P := by
  rw [Kit.prob_eq_pr, Kit.prob_eq_pr, Kit.pr_not]

lemma rpow_small (n : ℕ) (hn : 100 ≤ n) : (n : ℝ) ^ (-30 : ℝ) ≤ 1 / 100 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have h1 : (n : ℝ) ^ (-30 : ℝ) ≤ (n : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  rw [Real.rpow_neg_one] at h1
  have h2 : (n : ℝ)⁻¹ ≤ 1 / 100 := by
    rw [inv_eq_one_div]
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    exact_mod_cast hn
  linarith

end NAMatchEst.AuxE12

open NAMatchEst NAMatchEst.AuxE12 in
theorem solution : ∃ N₀ : ℕ, ∀ (n : ℕ) [NeZero n], N₀ ≤ n → ∀ (α : ℝ) (k : ℕ),
    (n : ℝ) ^ ((1 : ℝ) / 3) ≤ α → α ≤ (n : ℝ) ^ ((1 : ℝ) / 2) → α ≤ k → (k : ℝ) ≤ n → α ^ 2 < k →
    ∀ G : AdjList n,
      (k ≤ TuranMatching.Clique.matchingNumber G.toGraph → (largeTrial n α k).prob G (· = false) ≤ 1 / 10) ∧
      ((TuranMatching.Clique.matchingNumber G.toGraph : ℝ) < k / (C0 * α) →
        (largeTrial n α k).prob G (· = true) ≤ 1 / 10) := by
  obtain ⟨D5, N5, h5⟩ := lemma_3_5
  obtain ⟨D6, N6, h6⟩ := lemma_3_6
  obtain ⟨N8, h8⟩ := lemma_3_8
  obtain ⟨N9, h9⟩ := lemma_3_9
  obtain ⟨D11, N11, h11⟩ := lemma_3_11
  refine ⟨max 100 (max N5 (max N6 (max N8 (max N9 N11)))), ?_⟩
  intro n _ hn α k h13 h12 hαk hkn hlarge G
  have hn100 : 100 ≤ n := le_of_max_le_left hn
  have hn' := le_of_max_le_right hn
  have hN5 : N5 ≤ n := le_of_max_le_left hn'
  have hn'' := le_of_max_le_right hn'
  have hN6 : N6 ≤ n := le_of_max_le_left hn''
  have hn''' := le_of_max_le_right hn''
  have hN8 : N8 ≤ n := le_of_max_le_left hn'''
  have hn'''' := le_of_max_le_right hn'''
  have hN9 : N9 ≤ n := le_of_max_le_left hn''''
  have hN11 : N11 ≤ n := le_of_max_le_right hn''''
  obtain ⟨h5yes, h5no, -, -⟩ := h5 n hN5 α k h13 h12 hαk hkn
  obtain ⟨h6yes, h6no, -⟩ := h6 n hN6 α k h13 h12 hαk hkn hlarge
  obtain ⟨-, h11G⟩ := h11 n hN11 α k h13 h12 hαk hkn hlarge
  obtain ⟨-, -, hpil⟩ := h11G G
  have heps := rpow_small n hn100
  have heps0 : 0 ≤ (n : ℝ) ^ (-30 : ℝ) := by positivity
  set ε := (n : ℝ) ^ (-30 : ℝ) with hε
  have hpil' : 1 - ε ≤ Kit.pr (pilot n α k).dist
      (fun a => V1H G α k ⊆ (pilot n α k).run G a ∧ (pilot n α k).run G a ⊆ V1 G α k) := hpil
  constructor
  · -- yes case
    intro hμ
    rw [largeTrial_prob]
    refine (Kit.pr_prod_le_of_cond _ (Qd n α k) _ _ (2 * ε) ε hpil' ?_ (by positivity)).trans
      (by linarith)
    rintro a ⟨-, hHV1⟩
    set H := (pilot n α k).run G a with hH
    rcases lemma_3_4 n α k h13 h12 hαk hkn hlarge G H hμ hHV1 with hV | hR | hM
    · -- degree test rejects with small probability
      have hd := h5yes G hV
      calc _ ≤ Kit.pr (Qd n α k) (fun b => (degTest n α k).run G b.1 = false) := by
            refine Kit.pr_mono _ fun b hb => ?_
            simp only [Bool.or_eq_false_iff] at hb
            exact hb.1.1
        _ = (degTest n α k).prob G (· = false) := deg_pr _ G false
        _ = 1 - (degTest n α k).prob G (· = true) := by
            rw [← prob_compl]; congr 1; funext x; simp
        _ ≤ 2 * ε := by linarith
    · have hd := h6yes G H hR
      calc _ ≤ Kit.pr (Qd n α k) (fun b => (resTest n α k).run G b.2.1 H = false) := by
            refine Kit.pr_mono _ fun b hb => ?_
            simp only [Bool.or_eq_false_iff] at hb
            exact hb.1.2
        _ = (resTest n α k).prob G (fun f => f H = false) := res_pr _ _ G H false
        _ = 1 - (resTest n α k).prob G (fun f => f H = true) := by
            rw [← prob_compl (resTest n α k) G (fun f => f H = true)]; congr 1; funext x; simp
        _ ≤ 2 * ε := by linarith
    · have hd := h8 n hN8 α k h13 h12 hαk hkn hlarge G H hM
      calc _ ≤ Kit.pr (Qd n α k) (fun b => ¬ (cc * L n / 4 ≤ (((edgeTest n α k).run G b.2.2 H).ZE : ℝ))) := by
            refine Kit.pr_mono _ fun b hb => ?_
            simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hb
            exact hb.2
        _ = (edgeTest n α k).prob G (fun o => ¬ (cc * L n / 4 ≤ ((o H).ZE : ℝ))) :=
            edge_pr _ _ G H (fun o => ¬ (cc * L n / 4 ≤ (o.ZE : ℝ)))
        _ = 1 - (edgeTest n α k).prob G (fun o => cc * L n / 4 ≤ ((o H).ZE : ℝ)) :=
            prob_compl _ _ _
        _ ≤ 2 * ε := by linarith
  · -- no case
    intro hμ
    rw [largeTrial_prob]
    have hC0 : (64 : ℝ) / C0 ≤ 1 / 10000 := by unfold C0; norm_num
    refine (Kit.pr_prod_le_of_cond _ (Qd n α k) _ _ (64 / C0 + 3 * ε) ε hpil' ?_
      (by unfold C0; positivity)).trans (by linarith)
    rintro a ⟨hV1H, hHV1⟩
    set H := (pilot n α k).run G a with hH
    obtain ⟨hV, hR⟩ := lemma_3_3 n α k h13 h12 hαk hkn hlarge G H hV1H hHV1 hμ
    have hd := h5no G hV
    have hr := h6no G H hR.le
    have he := h9 n hN9 α k h13 h12 hαk hkn hlarge G H hHV1 hμ
    have hd' : (degTest n α k).prob G (· = true) ≤ ε := by
      have : (degTest n α k).prob G (· = true) = 1 - (degTest n α k).prob G (· = false) := by
        rw [← prob_compl]; congr 1; funext x; simp
      linarith
    have hr' : (resTest n α k).prob G (fun f => f H = true) ≤ ε := by
      have : (resTest n α k).prob G (fun f => f H = true) =
          1 - (resTest n α k).prob G (fun f => f H = false) := by
        rw [← prob_compl (resTest n α k) G (fun f => f H = false)]; congr 1; funext x; simp
      linarith
    calc _ ≤ Kit.pr (Qd n α k) (fun b => (degTest n α k).run G b.1 = true ∨
            ((resTest n α k).run G b.2.1 H = true ∨
              cc * L n / 4 ≤ (((edgeTest n α k).run G b.2.2 H).ZE : ℝ))) := by
          refine Kit.pr_mono _ fun b hb => ?_
          simp only [Bool.or_eq_true, decide_eq_true_eq] at hb
          tauto
      _ ≤ Kit.pr (Qd n α k) (fun b => (degTest n α k).run G b.1 = true) +
          (Kit.pr (Qd n α k) (fun b => (resTest n α k).run G b.2.1 H = true) +
            Kit.pr (Qd n α k) (fun b => cc * L n / 4 ≤ (((edgeTest n α k).run G b.2.2 H).ZE : ℝ))) := by
          refine (Kit.pr_or_le _ _ _).trans ?_
          have := Kit.pr_or_le (Qd n α k)
            (fun b => (resTest n α k).run G b.2.1 H = true)
            (fun b => cc * L n / 4 ≤ (((edgeTest n α k).run G b.2.2 H).ZE : ℝ))
          linarith
      _ = (degTest n α k).prob G (· = true) + ((resTest n α k).prob G (fun f => f H = true) +
            (edgeTest n α k).prob G (fun o => cc * L n / 4 ≤ ((o H).ZE : ℝ))) := by
          rw [deg_pr _ G true, res_pr _ _ G H true,
            edge_pr _ _ G H (fun o => cc * L n / 4 ≤ (o.ZE : ℝ))]
      _ ≤ 64 / C0 + 3 * ε := by linarith
