-- Prove2me | solution 1 for NAMatchEst.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T01:05:23.53849+00:00
-- url     : https://prove2.me/submissions/fd8074dd-57aa-4a23-a15e-34d6264eacde

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_AdjList_toGraph
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_NAMatchEst_RandAlg_prob
import Definitions.Def_NAMatchEst_RandAlg_CostLE
import Definitions.Def_NAMatchEst_C0
import Definitions.Def_NAMatchEst_L
import Theorems.Thm_NAMatchEst_truncTrial_error
import Theorems.Thm_NAMatchEst_lemma_3_14
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



namespace NAMatchEst.AuxL31

open NAMatchEst NAMatchEst.Kit WildeQIT

/-! ### Exact algorithm for small `n` -/

lemma nbr_succ {n : ℕ} (G : AdjList n) (v : Fin n) (j : ℕ) :
    G.nbr v (j + 1) = (G.adj v)[j]? := by
  unfold AdjList.nbr
  split_ifs with h
  · simp
  · rw [List.getElem?_eq_none]; omega

lemma adj_length_le {n : ℕ} (G : AdjList n) (v : Fin n) : (G.adj v).length ≤ n := by
  have := (G.nodup v).length_le_card
  simpa using this

lemma adjList_ext {n : ℕ} {G G' : AdjList n} (h : G.adj = G'.adj) : G = G' := by
  cases G; cases G'; cases h; rfl

lemma eq_of_nbr_agree {n : ℕ} (G G' : AdjList n)
    (h : ∀ v (i : ℕ), 1 ≤ i → i ≤ n → G.nbr v i = G'.nbr v i) : G = G' := by
  apply adjList_ext
  funext v
  apply List.ext_getElem?
  intro j
  by_cases hj : j < n
  · rw [← nbr_succ, ← nbr_succ]; exact h v (j + 1) (by omega) (by omega)
  · have h1 := adj_length_le G v
    have h2 := adj_length_le G' v
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- Queries all `nbr(v, i)` for `1 ≤ i ≤ n` and decides `k ≤ μ(G)` exactly. -/
noncomputable def exactAlg (n k : ℕ) : RandAlg n Bool where
  Ω := Unit
  dist := ⟨fun _ => 1, fun _ => zero_le_one, by simp⟩
  queries _ := (List.finRange n ×ˢ List.range n).map (fun p => Query.nbr p.1 (p.2 + 1))
  output _ _ m := open Classical in
    decide (∃ G' : AdjList n, (∀ v (i : ℕ), 1 ≤ i → i ≤ n → m v i = some (G'.nbr v i)) ∧
      k ≤ TuranMatching.Clique.matchingNumber G'.toGraph)

lemma exactAlg_length (n k : ℕ) (ω : (exactAlg n k).Ω) :
    ((exactAlg n k).queries ω).length = n * n := by
  simp [exactAlg, List.length_product]

lemma run_exactAlg (n k : ℕ) (G : AdjList n) (ω : (exactAlg n k).Ω) :
    (exactAlg n k).run G ω =
      (open Classical in decide (k ≤ TuranMatching.Clique.matchingNumber G.toGraph)) := by
  classical
  have hmem : ∀ v (i : ℕ), 1 ≤ i → i ≤ n → Query.nbr v i ∈ (exactAlg n k).queries ω := by
    intro v i h1 h2
    simp only [exactAlg, List.mem_map, List.mem_product, List.mem_finRange, List.mem_range,
      true_and, Prod.exists]
    exact ⟨v, i - 1, by omega, by congr 1; omega⟩
  simp only [RandAlg.run]
  change decide _ = decide _
  congr 1
  apply propext
  constructor
  · rintro ⟨G', hG', hk⟩
    have : G = G' := eq_of_nbr_agree G G' fun v i h1 h2 => by
      have := hG' v i h1 h2
      beta_reduce at this
      rw [if_pos (hmem v i h1 h2)] at this
      exact Option.some_injective _ this
    subst this; exact hk
  · intro hk
    exact ⟨G, fun v i h1 h2 => by beta_reduce; rw [if_pos (hmem v i h1 h2)], hk⟩

/-! ### Amplification -/

lemma amplify {n T : ℕ} {β : Type} (B : RandAlg n β) (G : AdjList n) (bad : β → Prop) [DecidablePred bad]
    (q : ℝ) (hq : B.prob G bad ≤ q) (hq1 : q ≤ 1) :
    (piAlg (fun _ : Fin T => B)).prob G
        (fun b => T ≤ 2 * (Finset.univ.filter (fun j => bad (b j))).card) ≤
      2 ^ T * q ^ ((T + 1) / 2) := by
  classical
  set m := (T + 1) / 2 with hm
  set q' := B.prob G bad with hq'
  have hq'0 : 0 ≤ q' := by rw [hq', prob_eq_pr]; exact pr_nonneg _ _
  rw [prob_eq_pr]
  calc pr (piAlg fun _ : Fin T => B).dist
        (fun ω => T ≤ 2 * (Finset.univ.filter
          (fun j => bad ((piAlg fun _ : Fin T => B).run G ω j))).card)
      ≤ pr (dpi fun _ : Fin T => B.dist) (fun ω => ∃ S ∈ (Finset.univ : Finset (Fin T)).powerset,
          T ≤ 2 * S.card ∧ ∀ j, (j ∈ S → bad (B.run G (ω j)))) := by
        refine pr_mono _ fun ω hω => ?_
        rw [run_piAlg] at hω
        refine ⟨_, Finset.mem_powerset.2 (Finset.subset_univ _), hω, fun j hj => ?_⟩
        exact (Finset.mem_filter.1 hj).2
    _ ≤ ∑ S ∈ (Finset.univ : Finset (Fin T)).powerset, pr (dpi fun _ : Fin T => B.dist)
          (fun ω => T ≤ 2 * S.card ∧ ∀ j, (j ∈ S → bad (B.run G (ω j)))) := pr_exists_le _ _ _
    _ ≤ ∑ _S ∈ (Finset.univ : Finset (Fin T)).powerset, q ^ m := by
        refine Finset.sum_le_sum fun S _ => ?_
        by_cases hS : T ≤ 2 * S.card
        · have hmS : m ≤ S.card := by omega
          calc _ = pr (dpi fun _ : Fin T => B.dist)
                (fun ω => ∀ j, (fun j x => j ∈ S → bad (B.run G x)) j (ω j)) :=
                  pr_congr _ fun ω => by simp [hS]
            _ = ∏ j : Fin T, pr B.dist (fun x => j ∈ S → bad (B.run G x)) :=
                  pr_dpi_forall (fun _ : Fin T => B.dist) (fun j x => j ∈ S → bad (B.run G x))
            _ = ∏ j : Fin T, if j ∈ S then q' else 1 := by
                refine Finset.prod_congr rfl fun j _ => ?_
                by_cases hj : j ∈ S
                · simp only [hj, if_true, true_imp_iff, hq', prob_eq_pr]
                · simp only [hj, if_false, false_imp_iff]; exact pr_true _
            _ = q' ^ S.card := by rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
            _ ≤ q' ^ m := pow_le_pow_of_le_one hq'0 (hq.trans hq1) hmS
            _ ≤ q ^ m := pow_le_pow_left₀ hq'0 hq m
        · calc _ = pr (dpi fun _ : Fin T => B.dist) (fun _ => False) :=
                  pr_congr _ fun ω => by simp [hS]
            _ = 0 := by simp [pr]
            _ ≤ q ^ m := pow_nonneg (hq'0.trans hq) m
    _ = 2 ^ T * q ^ m := by
        rw [Finset.sum_const, Finset.card_powerset, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]; push_cast; ring

lemma one_sub_le_of_bad {n : ℕ} {β : Type} (R : RandAlg n β) (G : AdjList n) (Q Bd : β → Prop)
    (h : ∀ b, ¬ Q b → Bd b) {ε : ℝ} (hε : R.prob G Bd ≤ ε) : 1 - ε ≤ R.prob G Q := by
  rw [prob_eq_pr] at hε ⊢
  have h1 := pr_not R.dist (fun ω => Q (R.run G ω))
  have h2 : pr R.dist (fun ω => ¬ Q (R.run G ω)) ≤ pr R.dist (fun ω => Bd (R.run G ω)) :=
    pr_mono _ fun ω hω => h _ hω
  linarith

/-- `2^T (1/5)^⌈T/2⌉ ≤ n^{-20}` for `T ≥ 200 L`. -/
lemma tail_bound (n T : ℕ) (hn : 1 ≤ n) (hT : 200 * L n ≤ T) :
    (2 : ℝ) ^ T * (1 / 5) ^ ((T + 1) / 2) ≤ (n : ℝ) ^ (-20 : ℝ) := by
  set m := (T + 1) / 2 with hm
  have hTm : T ≤ 2 * m := by omega
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 200 * L n ≤ 2 * (m : ℝ) := hT.trans (by exact_mod_cast hTm)
  have h45 : (4 / 5 : ℝ) ≤ Real.exp (-1 / 5) := by
    have := Real.add_one_le_exp (-1 / 5 : ℝ); linarith
  calc (2 : ℝ) ^ T * (1 / 5) ^ m ≤ 2 ^ (2 * m) * (1 / 5) ^ m := by
        gcongr; norm_num
    _ = (4 / 5 : ℝ) ^ m := by rw [pow_mul, ← mul_pow]; norm_num
    _ ≤ Real.exp (-1 / 5) ^ m := by gcongr
    _ = Real.exp (m * (-1 / 5)) := by rw [Real.exp_nat_mul]
    _ ≤ Real.exp (Real.log n * (-20)) := by
        apply Real.exp_le_exp.2
        have : Real.log n ≤ L n := by
          unfold L; exact Real.log_le_log (by linarith) (by linarith)
        nlinarith
    _ = (n : ℝ) ^ (-20 : ℝ) := by rw [Real.rpow_def_of_pos (by linarith)]

end NAMatchEst.AuxL31

namespace NAMatchEst.AuxL31

open NAMatchEst NAMatchEst.Kit

/-- The size factor of the cost bound is at least `1`. -/
lemma one_le_X (n : ℕ) (α : ℝ) (k : ℕ) (hn : 1 ≤ n)
    (h13 : (n : ℝ) ^ ((1 : ℝ) / 3) ≤ α) (_h12 : α ≤ (n : ℝ) ^ ((1 : ℝ) / 2)) (hαk : α ≤ k)
    (hkn : (k : ℝ) ≤ n) :
    1 ≤ (if (k : ℝ) ≤ α ^ 2 then n / Real.sqrt α else n * Real.sqrt k / α ^ ((3 : ℝ) / 2)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hα1 : 1 ≤ α := le_trans (Real.one_le_rpow hn' (by norm_num)) h13
  have hk1 : (1 : ℝ) ≤ k := hα1.trans hαk
  have hsq : (n : ℝ) ^ ((1 : ℝ) / 2) ≤ n := by
    calc (n : ℝ) ^ ((1 : ℝ) / 2) ≤ (n : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hn' (by norm_num)
      _ = n := Real.rpow_one _
  have hsα : Real.sqrt α ≤ α := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hsα0 : 0 < Real.sqrt α := Real.sqrt_pos.2 (by linarith)
  split_ifs with hk
  · rw [le_div_iff₀ hsα0]; linarith
  · push Not at hk
    have hsk : Real.sqrt k ≤ k := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    have hsk0 : 0 ≤ Real.sqrt k := Real.sqrt_nonneg _
    have hkk : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt (by linarith)
    have h32 : α ^ ((3 : ℝ) / 2) ≤ α ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hα1 (by norm_num)
    rw [Real.rpow_two] at h32
    have hpos : 0 < α ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos (by linarith) _
    rw [le_div_iff₀ hpos]
    nlinarith

end NAMatchEst.AuxL31

open NAMatchEst NAMatchEst.Kit NAMatchEst.AuxL31

theorem solution : ∃ D : ℝ, ∀ (n : ℕ) (α : ℝ) (k : ℕ),
    (n : ℝ) ^ ((1 : ℝ) / 3) ≤ α → α ≤ (n : ℝ) ^ ((1 : ℝ) / 2) → α ≤ k → (k : ℝ) ≤ n →
    ∃ A : RandAlg n Bool,
      A.CostLE (D * L n ^ 2 *
        (if (k : ℝ) ≤ α ^ 2 then n / Real.sqrt α else n * Real.sqrt k / α ^ ((3 : ℝ) / 2))) ∧
      ∀ G : AdjList n,
        (k ≤ TuranMatching.Clique.matchingNumber G.toGraph → 1 - (n : ℝ) ^ (-20 : ℝ) ≤ A.prob G (· = true)) ∧
        ((TuranMatching.Clique.matchingNumber G.toGraph : ℝ) < k / (C0 * α) →
          1 - (n : ℝ) ^ (-20 : ℝ) ≤ A.prob G (· = false)) := by
  classical
  obtain ⟨N₁, h₁⟩ := truncTrial_error
  obtain ⟨D₁₄, N₂, h₂⟩ := lemma_3_14
  set N₀ := max (max N₁ N₂) 2 with hN₀
  set D' := max D₁₄ 0 with hD'
  have hD'0 : 0 ≤ D' := le_max_right _ _
  refine ⟨max (3 * (N₀ : ℝ) ^ 2) (201 * D'), ?_⟩
  intro n α k h13 h12 hαk hkn
  set X := (if (k : ℝ) ≤ α ^ 2 then n / Real.sqrt α else n * Real.sqrt k / α ^ ((3 : ℝ) / 2))
    with hX
  have hC0 : (C0 : ℝ) = 2 ^ 20 := rfl
  by_cases hn : n < N₀
  · -- small `n`: exact algorithm
    refine ⟨exactAlg n k, ?_, fun G => ⟨fun hk => ?_, fun hk => ?_⟩⟩
    · intro ω
      rw [exactAlg_length]
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0; simp [L]
      · have hX1 := one_le_X n α k hpos h13 h12 hαk hkn
        have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hpos
        have hL : Real.log 2 ≤ L n := Real.log_le_log (by norm_num) (by linarith)
        have hL2 : (1 : ℝ) / 3 ≤ L n ^ 2 := by
          have := Real.log_two_gt_d9; nlinarith
        have hnN : (n : ℝ) ≤ N₀ := by exact_mod_cast hn.le
        calc ((n * n : ℕ) : ℝ) = (n : ℝ) * n := by push_cast; ring
          _ ≤ 3 * (N₀ : ℝ) ^ 2 * (1 / 3) * 1 := by nlinarith
          _ ≤ max (3 * (N₀ : ℝ) ^ 2) (201 * D') * L n ^ 2 * X := by
              gcongr
              exact le_max_left _ _
    · have h1 : ∀ ω, (exactAlg n k).run G ω = true := fun ω => by
        rw [run_exactAlg]; simpa using hk
      rw [prob_eq_pr, pr_congr _ (fun ω => iff_true_intro (h1 ω)), pr_true]
      have : (0 : ℝ) ≤ (n : ℝ) ^ (-20 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      linarith
    · have hnk : ¬ k ≤ TuranMatching.Clique.matchingNumber G.toGraph := by
        intro hk'
        have hk'' : (k : ℝ) ≤ TuranMatching.Clique.matchingNumber G.toGraph := by
          exact_mod_cast hk'
        rcases Nat.eq_zero_or_pos k with h0 | hpos
        · subst h0; simp at hk; linarith [hk, (Nat.cast_nonneg _ :
            (0:ℝ) ≤ TuranMatching.Clique.matchingNumber G.toGraph)]
        · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hpos
          have hn' : (1 : ℝ) ≤ n := hk1.trans hkn
          have hα1 : 1 ≤ α := le_trans (Real.one_le_rpow hn' (by norm_num)) h13
          have : (k : ℝ) / (C0 * α) ≤ k :=
            div_le_self (by positivity) (by rw [hC0]; nlinarith)
          linarith
      have h1 : ∀ ω, (exactAlg n k).run G ω = false := fun ω => by
        rw [run_exactAlg]; simpa using hnk
      rw [prob_eq_pr, pr_congr _ (fun ω => iff_true_intro (h1 ω)), pr_true]
      have : (0 : ℝ) ≤ (n : ℝ) ^ (-20 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      linarith
  · -- large `n`: majority vote over `T` independent truncated trials
    push Not at hn
    have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
    have hN1 : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hN2 : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have : NeZero n := ⟨by omega⟩
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hL1 : 1 ≤ L n := by
      unfold L
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9; linarith
    have hX1 := one_le_X n α k (by omega) h13 h12 hαk hkn
    set T := ⌈200 * L n⌉₊ with hT
    have hTle : (T : ℝ) ≤ 201 * L n := by
      have := Nat.ceil_lt_add_one (show 0 ≤ 200 * L n by linarith); linarith
    have hTge : 200 * L n ≤ T := Nat.le_ceil _
    set P := piAlg (fun _ : Fin T => truncTrial n α k) with hP
    refine ⟨mapOut P (fun b => decide (T < 2 * (Finset.univ.filter (fun j => b j = true)).card)),
      ?_, fun G => ⟨fun hk => ?_, fun hk => ?_⟩⟩
    · apply costLE_mapOut
      have hc : ∀ j : Fin T, (truncTrial n α k).CostLE (D' * L n * X) := fun _ =>
        costLE_mono _ (h₂ n hN2 α k h13 h12 hαk hkn) (by
          have : 0 ≤ L n * X := by nlinarith
          rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) this)
      refine costLE_mono _ (costLE_piAlg _ _ hc) ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc (T : ℝ) * (D' * L n * X) ≤ (201 * L n) * (D' * L n * X) := by
            gcongr
        _ = (201 * D') * L n ^ 2 * X := by ring
        _ ≤ max (3 * (N₀ : ℝ) ^ 2) (201 * D') * L n ^ 2 * X := by
            gcongr; exact le_max_right _ _
    · have he := (h₁ n hN1 α k h13 h12 hαk hkn G).1 hk
      rw [prob_mapOut]
      refine one_sub_le_of_bad P G _
        (fun b => T ≤ 2 * (Finset.univ.filter (fun j => b j = false)).card) (fun b hb => ?_) ?_
      · simp only [decide_eq_true_eq, not_lt] at hb
        have := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin T))) (fun j => b j = true)
        simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at this
        omega
      · exact (amplify _ G (fun x => x = false) (1 / 5) he (by norm_num)).trans
          (tail_bound n T (by omega) hTge)
    · have he := (h₁ n hN1 α k h13 h12 hαk hkn G).2 hk
      rw [prob_mapOut]
      refine one_sub_le_of_bad P G _
        (fun b => T ≤ 2 * (Finset.univ.filter (fun j => b j = true)).card) (fun b hb => ?_) ?_
      · simp only [decide_eq_false_iff_not, not_not] at hb
        omega
      · exact (amplify _ G (fun x => x = true) (1 / 5) he (by norm_num)).trans
          (tail_bound n T (by omega) hTge)
