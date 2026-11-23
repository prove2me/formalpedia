-- Prove2me | solution 1 for NAMatchEst.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T00:55:38.206675+00:00
-- url     : https://prove2.me/submissions/627e9b9f-87c3-4b09-8f5a-1980e830da31

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_AdjList_toGraph
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_NAMatchEst_RandAlg_prob
import Definitions.Def_NAMatchEst_RandAlg_CostLE
import Definitions.Def_NAMatchEst_L
import Definitions.Def_NAMatchEst_C0
import Theorems.Thm_NAMatchEst_lemma_3_1
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_RandomQueryXOR_uniformOn
import Definitions.Def_ShallowShadows_ShadowNorm_uniformDist
import Definitions.Def_NAMatchEst_RandAlg_run
import Definitions.Def_NAMatchEst_RandAlg_par
import Definitions.Def_NAMatchEst_RandAlg_guard


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



/-! Local toolkit part 2 (BEGIN KIT2): families of independent algorithms. -/

namespace NAMatchEst.Kit

open WildeQIT

/-- Product of a dependent family of finite distributions. -/
noncomputable def dpi {m : ℕ} {Q : Fin m → Type} [∀ i, Fintype (Q i)] (p : ∀ i, FinDist (Q i)) :
    FinDist (∀ i, Q i) where
  prob ω := ∏ i, (p i).prob (ω i)
  nonneg ω := Finset.prod_nonneg fun i _ => (p i).nonneg (ω i)
  sum_eq_one := by
    rw [← Fintype.prod_sum (fun i x => (p i).prob x)]
    exact Finset.prod_eq_one fun i _ => (p i).sum_eq_one

lemma pr_dpi_forall {m : ℕ} {Q : Fin m → Type} [∀ i, Fintype (Q i)] (p : ∀ i, FinDist (Q i))
    (E : ∀ i, Q i → Prop) :
    pr (dpi p) (fun ω => ∀ i, E i (ω i)) = ∏ i, pr (p i) (E i) := by
  classical
  unfold pr
  simp only [dpi]
  refine (Finset.sum_congr rfl fun ω _ => ?_).trans
    (Fintype.prod_sum (fun i x => (p i).prob x * if E i x then (1:ℝ) else 0)).symm
  beta_reduce
  rw [Finset.prod_mul_distrib]
  congr 1
  by_cases h : ∀ i, E i (ω i)
  · rw [if_pos h, Finset.prod_eq_one]; intro i _; rw [if_pos (h i)]
  · rw [if_neg h]; push Not at h; obtain ⟨i, hi⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)).symm

lemma pr_dpi_coord {m : ℕ} {Q : Fin m → Type} [∀ i, Fintype (Q i)] (p : ∀ i, FinDist (Q i))
    (j : Fin m) (E : Q j → Prop) : pr (dpi p) (fun ω => E (ω j)) = pr (p j) E := by
  classical
  let E' : ∀ i, Q i → Prop := fun i x => ∀ h : i = j, E (cast (congrArg Q h) x)
  have h1 : pr (dpi p) (fun ω => E (ω j)) = pr (dpi p) (fun ω => ∀ i, E' i (ω i)) := by
    refine pr_congr _ fun ω => ⟨fun h i hi => ?_, fun h => h j rfl⟩
    subst hi; exact h
  rw [h1, pr_dpi_forall, Finset.prod_eq_single j]
  · exact pr_congr _ fun x => ⟨fun h => h rfl, fun h _ => h⟩
  · intro i _ hij
    rw [show E' i = fun _ => True from funext fun x => propext ⟨fun _ => trivial,
      fun _ h => absurd h hij⟩]
    exact pr_true _
  · intro h; exact absurd (Finset.mem_univ j) h

/-- Independent parallel composition of a finite family of algorithms. -/
noncomputable def piAlg {n m : ℕ} {β : Type} (B : Fin m → RandAlg n β) : RandAlg n (Fin m → β) where
  Ω := ∀ j, (B j).Ω
  dist := dpi fun j => (B j).dist
  queries ω := (List.ofFn fun j => (B j).queries (ω j)).flatten
  output ω d m' := fun j => (B j).output (ω j)
      (fun v => if Query.deg v ∈ (B j).queries (ω j) then d v else none)
      (fun v i => if Query.nbr v i ∈ (B j).queries (ω j) then m' v i else none)

lemma mem_piAlg_queries {n m : ℕ} {β : Type} (B : Fin m → RandAlg n β) (ω : (piAlg B).Ω)
    (j : Fin m) {q : Query n} (hq : q ∈ (B j).queries (ω j)) : q ∈ (piAlg B).queries ω := by
  simp only [piAlg]
  exact List.mem_flatten.2 ⟨_, List.mem_ofFn.2 ⟨j, rfl⟩, hq⟩

lemma run_piAlg {n m : ℕ} {β : Type} (B : Fin m → RandAlg n β) (G : AdjList n)
    (ω : (piAlg B).Ω) : (piAlg B).run G ω = fun j => (B j).run G (ω j) := by
  classical
  funext j
  simp only [RandAlg.run]
  change (B j).output (ω j) _ _ = _
  congr 1
  · funext v
    by_cases h : Query.deg v ∈ (B j).queries (ω j)
    · simp [h, mem_piAlg_queries B ω j h]
    · simp [h]
  · funext v i
    by_cases h : Query.nbr v i ∈ (B j).queries (ω j)
    · simp [h, mem_piAlg_queries B ω j h]
    · simp [h]

lemma piAlg_dist {n m : ℕ} {β : Type} (B : Fin m → RandAlg n β) :
    (piAlg B).dist = dpi fun j => (B j).dist := rfl

lemma costLE_piAlg {n m : ℕ} {β : Type} (B : Fin m → RandAlg n β) (c : Fin m → ℝ)
    (hc : ∀ j, (B j).CostLE (c j)) : (piAlg B).CostLE (∑ j, c j) := by
  intro ω
  simp only [piAlg, List.length_flatten, List.map_ofFn]
  rw [List.sum_ofFn]
  push_cast
  exact Finset.sum_le_sum fun j _ => hc j (ω j)

/-- Union bound over the components of a family. -/
lemma prob_piAlg_exists_le {n m : ℕ} {β : Type} (B : Fin m → RandAlg n β) (G : AdjList n)
    (bad : Fin m → β → Prop) :
    (piAlg B).prob G (fun b => ∃ j, bad j (b j)) ≤ ∑ j, (B j).prob G (bad j) := by
  rw [prob_eq_pr]
  calc pr (piAlg B).dist (fun ω => ∃ j, bad j ((piAlg B).run G ω j))
      = pr (dpi fun j => (B j).dist) (fun ω => ∃ j ∈ Finset.univ, bad j ((B j).run G (ω j))) :=
        pr_congr _ fun ω => by rw [run_piAlg]; simp
    _ ≤ ∑ j, pr (dpi fun j => (B j).dist) (fun ω => bad j ((B j).run G (ω j))) :=
        pr_exists_le _ _ _
    _ = ∑ j, (B j).prob G (bad j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [pr_dpi_coord (fun j => (B j).dist) j (fun x => bad j ((B j).run G x)), prob_eq_pr]

/-- Post-processing of the output. -/
def mapOut {n : ℕ} {β γ : Type} (A : RandAlg n β) (f : β → γ) : RandAlg n γ where
  Ω := A.Ω
  dist := A.dist
  queries := A.queries
  output ω d m := f (A.output ω d m)

lemma prob_mapOut {n : ℕ} {β γ : Type} (A : RandAlg n β) (f : β → γ) (G : AdjList n)
    (P : γ → Prop) : (mapOut A f).prob G P = A.prob G (fun b => P (f b)) := rfl

lemma costLE_mapOut {n : ℕ} {β γ : Type} (A : RandAlg n β) (f : β → γ) {c : ℝ}
    (h : A.CostLE c) : (mapOut A f).CostLE c := h

/-- An algorithm with no queries and a constant output. -/
noncomputable def constAlg (n : ℕ) {β : Type} (b : β) : RandAlg n β where
  Ω := Unit
  dist := ⟨fun _ => 1, fun _ => zero_le_one, by simp⟩
  queries _ := []
  output _ _ _ := b

lemma run_constAlg (n : ℕ) {β : Type} (b : β) (G : AdjList n) (ω : (constAlg n b).Ω) :
    (constAlg n b).run G ω = b := rfl

lemma costLE_constAlg (n : ℕ) {β : Type} (b : β) : (constAlg n b).CostLE 0 := by
  intro ω; simp [constAlg]

end NAMatchEst.Kit

/-! (END KIT2) -/



namespace NAMatchEst.AuxT3

open NAMatchEst NAMatchEst.Kit

/-- The matching number is at most the number of vertices. -/
lemma matchingNumber_le (n : ℕ) (G : SimpleGraph (Fin n)) :
    TuranMatching.Clique.matchingNumber G ≤ n := by
  unfold TuranMatching.Clique.matchingNumber
  apply csSup_le
  · exact ⟨_, ⊥, by simp [SimpleGraph.Subgraph.IsMatching], rfl⟩
  · rintro m ⟨M, hM, rfl⟩
    have h1 : M.edgeSet.ncard ≤ M.verts.ncard := by
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      exact Nat.card_le_card_of_surjective _ (SimpleGraph.Subgraph.IsMatching.toEdge.surjective hM)
    have h2 : M.verts.ncard ≤ n := by
      calc M.verts.ncard ≤ (Set.univ : Set (Fin n)).ncard := Set.ncard_le_ncard (Set.subset_univ _)
        _ = n := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
    omega

end NAMatchEst.AuxT3

open NAMatchEst NAMatchEst.Kit NAMatchEst.AuxT3

theorem solution : ∃ C : ℝ, 1 ≤ C ∧ ∃ D : ℝ, ∀ (n : ℕ) (α : ℝ),
    (n : ℝ) ^ ((1 : ℝ) / 3) ≤ α → α ≤ (n : ℝ) ^ ((1 : ℝ) / 2) →
    ∃ A : RandAlg n ℝ,
      A.CostLE (D * (n : ℝ) ^ ((3 : ℝ) / 2) / α ^ ((3 : ℝ) / 2) * L n ^ 3) ∧
      ∀ G : AdjList n, 1 ≤ TuranMatching.Clique.matchingNumber G.toGraph →
        1 - (n : ℝ) ^ (-10 : ℝ) ≤ A.prob G (fun muhat =>
          (TuranMatching.Clique.matchingNumber G.toGraph : ℝ) / (C * α) ≤ muhat ∧
            muhat ≤ (TuranMatching.Clique.matchingNumber G.toGraph : ℝ)) := by
  classical
  obtain ⟨D1, hD1⟩ := lemma_3_1
  set D1' := max D1 0 with hD1'
  have hC0 : (C0 : ℝ) = 2 ^ 20 := rfl
  refine ⟨2 * C0, by rw [hC0]; norm_num, 2 * D1', ?_⟩
  intro n α h13 h12
  -- degenerate case n = 0
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    refine ⟨constAlg 0 (1 : ℝ), ?_, ?_⟩
    · refine costLE_mono _ (costLE_constAlg 0 _) (le_of_eq ?_)
      simp [Real.zero_rpow (by norm_num : (3:ℝ)/2 ≠ 0)]
    · intro G hG
      have := matchingNumber_le 0 G.toGraph
      omega
  -- main case n ≥ 1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
  have hα1 : 1 ≤ α := by
    refine le_trans ?_ h13
    exact Real.one_le_rpow hn1 (by norm_num)
  have hαpos : 0 < α := by linarith
  have hsqrt : α ≤ Real.sqrt n := by rwa [Real.sqrt_eq_rpow]
  have hαn : α ≤ n := by
    refine hsqrt.trans ?_
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  set k0 : ℕ := ⌈α⌉₊ with hk0
  have hk0α : α ≤ k0 := Nat.le_ceil α
  have hk0lt : (k0 : ℝ) < α + 1 := Nat.ceil_lt_add_one hαpos.le
  set m : ℕ := Nat.log 2 n + 1 with hm
  let kk : Fin m → ℕ := fun j => k0 * 2 ^ (j : ℕ)
  have hkkα : ∀ j, α ≤ (kk j : ℝ) := by
    intro j
    refine hk0α.trans ?_
    have : (k0 : ℝ) ≤ k0 * 2 ^ (j : ℕ) := by
      have : (1 : ℝ) ≤ 2 ^ (j : ℕ) := one_le_pow₀ (by norm_num)
      have : (0 : ℝ) ≤ k0 := by positivity
      nlinarith
    simpa [kk] using this
  -- the testers
  let B : Fin m → RandAlg n Bool := fun j =>
    if h : (kk j : ℝ) ≤ n then Classical.choose (hD1 n α (kk j) h13 h12 (hkkα j) h)
    else constAlg n false
  have hBspec : ∀ j (h : (kk j : ℝ) ≤ n), B j = Classical.choose (hD1 n α (kk j) h13 h12 (hkkα j) h) :=
    fun j h => by simp only [B, dif_pos h]
  have hBfalse : ∀ j, ¬ (kk j : ℝ) ≤ n → B j = constAlg n false :=
    fun j h => by simp only [B, dif_neg h]
  -- output map
  let kstar : (Fin m → Bool) → ℕ := fun b => (Finset.univ.filter fun j => b j = true).sup kk
  let est : (Fin m → Bool) → ℝ := fun b => max 1 ((kstar b : ℝ) / (C0 * α))
  have hC0α : 1 ≤ (C0 : ℝ) * α := by
    rw [hC0]; nlinarith
  set Y : ℝ := (n : ℝ) ^ ((3 : ℝ) / 2) / α ^ ((3 : ℝ) / 2) with hY
  have hYnn : 0 ≤ Y := by positivity
  have hLnn : 0 ≤ L n := by
    unfold L; exact Real.log_nonneg (by linarith)
  have hX : ∀ j : Fin m, (kk j : ℝ) ≤ n → (if (kk j : ℝ) ≤ α ^ 2 then (n : ℝ) / Real.sqrt α
      else n * Real.sqrt (kk j) / α ^ ((3 : ℝ) / 2)) ≤ Y := by
    intro j hkn
    have hα32 : α ^ ((3 : ℝ) / 2) = α * Real.sqrt α := by
      rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hαpos, Real.rpow_one,
        Real.sqrt_eq_rpow]
    have hn32 : (n : ℝ) ^ ((3 : ℝ) / 2) = n * Real.sqrt n := by
      rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one,
        Real.sqrt_eq_rpow]
    have hsa : 0 < Real.sqrt α := Real.sqrt_pos.2 hαpos
    rw [hY, hα32, hn32]
    split_ifs with hk
    · rw [div_le_div_iff₀ hsa (by positivity)]
      have := mul_le_mul_of_nonneg_left hsqrt (by positivity : (0:ℝ) ≤ n * Real.sqrt α)
      nlinarith
    · rw [div_le_div_iff_of_pos_right (by positivity)]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hkn) (by positivity)
  have hBcost : ∀ j, (B j).CostLE (D1' * L n ^ 2 * Y) := by
    intro j
    by_cases hkn : (kk j : ℝ) ≤ n
    · rw [hBspec j hkn]
      have hc := (Classical.choose_spec (hD1 n α (kk j) h13 h12 (hkkα j) hkn)).1
      refine costLE_mono _ hc ?_
      have hXj := hX j hkn
      have hX0 : 0 ≤ (if (kk j : ℝ) ≤ α ^ 2 then (n : ℝ) / Real.sqrt α
          else n * Real.sqrt (kk j) / α ^ ((3 : ℝ) / 2)) := by split_ifs <;> positivity
      calc D1 * L n ^ 2 * _ ≤ D1' * L n ^ 2 * _ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) hX0
        _ ≤ D1' * L n ^ 2 * Y :=
            mul_le_mul_of_nonneg_left hXj (mul_nonneg (le_max_right _ _) (by positivity))
    · rw [hBfalse j hkn]
      exact costLE_mono _ (costLE_constAlg n false)
        (mul_nonneg (mul_nonneg (le_max_right _ _) (by positivity)) hYnn)
  have hm2L : (m : ℝ) ≤ 2 * L n := by
    have hpow : ((2 : ℕ) : ℝ) ^ (Nat.log 2 n) ≤ n := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : n ≠ 0)
    have hlog : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
      have := Real.log_le_log (by positivity) hpow
      rwa [Real.log_pow, Nat.cast_ofNat] at this
    have hL : L n = Real.log 2 + Real.log n := by
      unfold L; rw [Real.log_mul (by norm_num) (by linarith)]
    have h2 : (1 : ℝ) / 2 < Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have : (m : ℝ) * Real.log 2 ≤ L n := by
      rw [hm, hL]; push_cast; nlinarith
    nlinarith
  refine ⟨mapOut (piAlg B) est, ?_, ?_⟩
  · -- cost
    refine costLE_mapOut _ _ (costLE_mono _ (costLE_piAlg B (fun _ => D1' * L n ^ 2 * Y)
      (fun j => hBcost j)) ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : 0 ≤ D1' * L n ^ 2 * Y := mul_nonneg (mul_nonneg (le_max_right _ _) (by positivity)) hYnn
    calc (m : ℝ) * (D1' * L n ^ 2 * Y) ≤ (2 * L n) * (D1' * L n ^ 2 * Y) :=
          mul_le_mul_of_nonneg_right hm2L this
      _ = 2 * D1' * (n : ℝ) ^ ((3 : ℝ) / 2) / α ^ ((3 : ℝ) / 2) * L n ^ 3 := by
          rw [hY]; ring
  · -- correctness
    intro G hG
    set μ := TuranMatching.Clique.matchingNumber G.toGraph with hμ
    have hμn : μ ≤ n := matchingNumber_le n G.toGraph
    let good : (Fin m → Bool) → Prop := fun b => ∀ j, ((kk j ≤ μ) → b j = true) ∧
      ((μ : ℝ) < kk j / (C0 * α) → b j = false) ∧ (¬ (kk j : ℝ) ≤ n → b j = false)
    let bad : Fin m → Bool → Prop := fun j x => ¬ (((kk j ≤ μ) → x = true) ∧
      ((μ : ℝ) < kk j / (C0 * α) → x = false) ∧ (¬ (kk j : ℝ) ≤ n → x = false))
    -- deterministic part
    have hdet : ∀ b, good b → (μ : ℝ) / (2 * C0 * α) ≤ est b ∧ est b ≤ μ := by
      intro b hb
      have hμ1 : (1 : ℝ) ≤ μ := by exact_mod_cast hG
      constructor
      · by_cases hsmall : μ < k0
        · have : (μ : ℝ) < 2 * α := by
            have : (μ : ℝ) + 1 ≤ k0 := by exact_mod_cast hsmall
            linarith
          have h1 : (μ : ℝ) / (2 * C0 * α) ≤ 1 := by
            rw [div_le_one (by rw [hC0]; positivity)]
            rw [hC0]; nlinarith
          exact h1.trans (le_max_left _ _)
        · push Not at hsmall
          have hk0pos : 0 < k0 := Nat.lt_of_lt_of_le (Nat.ceil_pos.2 hαpos) le_rfl
          set j1 := Nat.log 2 (μ / k0) with hj1
          have hq : μ / k0 ≠ 0 := (Nat.div_pos hsmall hk0pos).ne'
          have h2le : 2 ^ j1 ≤ μ / k0 := Nat.pow_log_le_self 2 hq
          have hlt : μ / k0 < 2 ^ (j1 + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
          have hkkle : k0 * 2 ^ j1 ≤ μ := (Nat.mul_le_mul_left k0 h2le).trans (Nat.mul_div_le μ k0)
          have hμlt : μ < 2 * (k0 * 2 ^ j1) := by
            have h1 := Nat.lt_mul_div_succ μ hk0pos
            have h2 : k0 * (μ / k0 + 1) ≤ k0 * 2 ^ (j1 + 1) := Nat.mul_le_mul_left k0 (by omega)
            rw [pow_succ] at h2
            linarith
          have hj1m : j1 < m := by
            have : 2 ^ j1 ≤ n := h2le.trans ((Nat.div_le_self μ k0).trans hμn)
            have := Nat.le_log_of_pow_le (by norm_num) this
            omega
          let J : Fin m := ⟨j1, hj1m⟩
          have hbJ : b J = true := (hb J).1 hkkle
          have hle : kk J ≤ kstar b := Finset.le_sup (f := kk) (by simp [hbJ])
          have hμle : (μ : ℝ) ≤ 2 * kstar b := by
            have : μ ≤ 2 * kstar b := by
              have : kk J = k0 * 2 ^ j1 := rfl
              omega
            exact_mod_cast this
          have hpos : 0 < (C0 : ℝ) * α := by linarith
          calc (μ : ℝ) / (2 * C0 * α) ≤ (2 * kstar b) / (2 * C0 * α) :=
                div_le_div_of_nonneg_right hμle (by linarith)
            _ = (kstar b : ℝ) / (C0 * α) := by field_simp
            _ ≤ est b := le_max_right _ _
      · refine max_le hμ1 ?_
        by_cases hne : (Finset.univ.filter fun j => b j = true).Nonempty
        · obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup _ hne kk
          have hbj : b j = true := by simpa using hj
          have hkn : (kk j : ℝ) ≤ n := by
            by_contra h
            have := (hb j).2.2 h
            rw [hbj] at this; exact absurd this (by decide)
          have hno : ¬ (μ : ℝ) < kk j / (C0 * α) := fun h => by
            have := (hb j).2.1 h
            rw [hbj] at this; exact absurd this (by decide)
          push Not at hno
          have : kstar b = kk j := hjeq
          rw [this]; exact hno
        · rw [Finset.not_nonempty_iff_eq_empty] at hne
          have : kstar b = 0 := by simp only [kstar, hne, Finset.sup_empty]; rfl
          rw [this]; simp only [Nat.cast_zero, zero_div]; positivity
    -- probabilistic part
    have hn20 : (0 : ℝ) ≤ (n : ℝ) ^ (-20 : ℝ) := Real.rpow_nonneg (by linarith) _
    have hpr0' : ∀ (A : RandAlg n Bool) (P : Bool → Prop), (∀ ω, ¬ P (A.run G ω)) → A.prob G P = 0 := by
      intro A P hP
      rw [prob_eq_pr]
      have := pr_not A.dist (fun _ => True)
      rw [pr_true] at this
      rw [pr_congr A.dist (fun ω => by simp [hP ω] : ∀ ω, P (A.run G ω) ↔ ¬ True), this]; ring
    have hpr0 : ∀ (A : RandAlg n Bool) (P : Bool → Prop), (∀ x, ¬ P x) → A.prob G P = 0 :=
      fun A P hP => hpr0' A P fun ω => hP _
    have hj : ∀ j, (B j).prob G (bad j) ≤ (n : ℝ) ^ (-20 : ℝ) := by
      intro j
      by_cases hkn : (kk j : ℝ) ≤ n
      · have hspec := (Classical.choose_spec (hD1 n α (kk j) h13 h12 (hkkα j) hkn)).2 G
        rw [hBspec j hkn]
        set A := Classical.choose (hD1 n α (kk j) h13 h12 (hkkα j) hkn)
        by_cases hyes : kk j ≤ μ
        · have hno : ¬ (μ : ℝ) < kk j / (C0 * α) := by
            push Not
            calc (kk j : ℝ) / (C0 * α) ≤ kk j := div_le_self (by positivity) hC0α
              _ ≤ μ := by exact_mod_cast hyes
          have h1 := hspec.1 hyes
          have : A.prob G (bad j) ≤ A.prob G (fun x => ¬ (x = true)) := by
            rw [prob_eq_pr, prob_eq_pr]
            exact pr_mono _ fun ω h hx => h ⟨fun _ => hx, fun h' => absurd h' hno, fun h' => absurd hkn h'⟩
          have e1 : A.prob G (fun x => ¬ (x = true)) = 1 - A.prob G (fun x => x = true) := by
            rw [prob_eq_pr, prob_eq_pr, pr_not]
          linarith
        · by_cases hnoc : (μ : ℝ) < kk j / (C0 * α)
          · have h2 := hspec.2 hnoc
            have : A.prob G (bad j) ≤ A.prob G (fun x => ¬ (x = false)) := by
              rw [prob_eq_pr, prob_eq_pr]
              exact pr_mono _ fun ω h hx => h ⟨fun h' => absurd h' hyes, fun _ => hx, fun h' => absurd hkn h'⟩
            have e1 : A.prob G (fun x => ¬ (x = false)) = 1 - A.prob G (fun x => x = false) := by
              rw [prob_eq_pr, prob_eq_pr, pr_not]
            linarith
          · rw [hpr0 A (bad j) (fun x hx => hx ⟨fun h' => absurd h' hyes, fun h' => absurd h' hnoc,
              fun h' => absurd hkn h'⟩)]
            exact hn20
      · rw [hBfalse j hkn]
        refine (le_of_eq (hpr0' _ _ ?_)).trans hn20
        intro ω hx
        rw [run_constAlg] at hx
        apply hx
        refine ⟨fun h' => absurd (by exact_mod_cast (h'.trans hμn) : (kk j : ℝ) ≤ n) hkn,
          fun _ => rfl, fun _ => rfl⟩
    have hmn : (m : ℝ) * (n : ℝ) ^ (-20 : ℝ) ≤ (n : ℝ) ^ (-10 : ℝ) := by
      have hlog : Nat.log 2 n < n :=
        lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_log_le_self 2 (by omega))
      have hmn' : (m : ℝ) ≤ n := by exact_mod_cast (by omega : m ≤ n)
      have hnpos' : (0 : ℝ) < n := by linarith
      calc (m : ℝ) * (n : ℝ) ^ (-20 : ℝ) ≤ n * (n : ℝ) ^ (-20 : ℝ) :=
            mul_le_mul_of_nonneg_right hmn' hn20
        _ = (n : ℝ) ^ (-19 : ℝ) := by
            rw [show (-19 : ℝ) = 1 + -20 by norm_num, Real.rpow_add hnpos', Real.rpow_one]
        _ ≤ (n : ℝ) ^ (-10 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
    have hunion := prob_piAlg_exists_le B G bad
    have hsum : ∑ j, (B j).prob G (bad j) ≤ m * (n : ℝ) ^ (-20 : ℝ) := by
      calc ∑ j, (B j).prob G (bad j) ≤ ∑ _j : Fin m, (n : ℝ) ^ (-20 : ℝ) :=
            Finset.sum_le_sum fun j _ => hj j
        _ = m * (n : ℝ) ^ (-20 : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [prob_mapOut]
    have hmono : (piAlg B).prob G (fun b => ¬ ∃ j, bad j (b j)) ≤
        (piAlg B).prob G (fun b => (μ : ℝ) / (2 * C0 * α * 1) ≤ est b ∧ est b ≤ μ) := by
      rw [prob_eq_pr, prob_eq_pr]
      refine pr_mono _ fun ω h => ?_
      have hg : good ((piAlg B).run G ω) := by
        intro j; by_contra hc; exact h ⟨j, hc⟩
      have := hdet _ hg
      rw [mul_one]; exact this
    have hnot : (piAlg B).prob G (fun b => ¬ ∃ j, bad j (b j)) =
        1 - (piAlg B).prob G (fun b => ∃ j, bad j (b j)) := by
      rw [prob_eq_pr, prob_eq_pr, pr_not]
    have hfin : 1 - (n : ℝ) ^ (-10 : ℝ) ≤
        (piAlg B).prob G (fun b => (μ : ℝ) / (2 * C0 * α * 1) ≤ est b ∧ est b ≤ μ) := by
      linarith
    simpa [mul_assoc] using hfin
