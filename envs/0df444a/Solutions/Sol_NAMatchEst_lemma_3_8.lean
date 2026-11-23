-- Prove2me | solution 1 for NAMatchEst.lemma_3_8
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T00:47:54.811997+00:00
-- url     : https://prove2.me/submissions/01e19162-7a32-402b-946d-09e0c5064d89

import Mathlib
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_AdjList_toGraph
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_NAMatchEst_RandAlg_run
import Definitions.Def_NAMatchEst_RandAlg_prob
import Definitions.Def_NAMatchEst_cc
import Definitions.Def_NAMatchEst_L
import Definitions.Def_NAMatchEst_W3
import Definitions.Def_NAMatchEst_W4
import Definitions.Def_NAMatchEst_bernDist
import Definitions.Def_NAMatchEst_EdgeStats
import Definitions.Def_NAMatchEst_edgeTest
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_RandomQueryXOR_uniformOn
import Definitions.Def_ShallowShadows_ShadowNorm_uniformDist
import Definitions.Def_NAMatchEst_RandAlg_par
import Definitions.Def_NAMatchEst_RandAlg_guard
import Definitions.Def_NAMatchEst_RandAlg_CostLE
import Theorems.Thm_NAMatchEst_lemma_3_7
import Theorems.Thm_NAMatchEst_pair_count_lower_tail


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



namespace NAMatchEst.AuxE38
open NAMatchEst

/-- the number of draws. -/
noncomputable abbrev rr (n : ℕ) (α : ℝ) (k : ℕ) : ℕ := ⌈cc * Delta k α * L n / α⌉₊

def Ycnt {n R D : ℕ} (G : AdjList n) (H : Finset (Fin n)) (v : Fin n) (pos : Fin R → Fin D) : ℕ :=
  open Classical in
  (Finset.univ.filter fun j => ∃ u, G.nbr v ((pos j : ℕ) + 1) = some u ∧ u ∉ H).card

variable {n : ℕ} {α : ℝ} {k : ℕ}

lemma omega_eq : (edgeTest n α k).Ω = ((Fin n → Bool) × (Fin n → Bool) ×
      (Fin n → Fin (rr n α k) → Fin (Delta k α))) := rfl

lemma deg_mem_of_SL (ω : (edgeTest n α k).Ω) (v : Fin n) (h : ω.1 v = true) :
    Query.deg v ∈ (edgeTest n α k).queries ω := by
  simp only [edgeTest, List.mem_flatMap, List.mem_finRange, true_and]
  exact ⟨v, by simp [h, rowQueries]⟩

lemma deg_mem_of_SR (ω : (edgeTest n α k).Ω) (v : Fin n) (h : ω.2.1 v = true) :
    Query.deg v ∈ (edgeTest n α k).queries ω := by
  simp only [edgeTest, List.mem_flatMap, List.mem_finRange, true_and]
  exact ⟨v, by simp [h]⟩

lemma nbr_mem_of_SL (ω : (edgeTest n α k).Ω) (v : Fin n) (h : ω.1 v = true) (i : ℕ)
    (hi1 : 1 ≤ i) (hi2 : i ≤ Delta k α) :
    Query.nbr v i ∈ (edgeTest n α k).queries ω := by
  simp only [edgeTest, List.mem_flatMap, List.mem_finRange, true_and]
  refine ⟨v, ?_⟩
  simp only [h, if_true, List.mem_append, rowQueries, List.mem_cons, List.mem_map, List.mem_range]
  left; right
  exact ⟨i - 1, by omega, by congr 1; omega⟩

lemma nbr_mem_of_SR (ω : (edgeTest n α k).Ω) (v : Fin n) (h : ω.2.1 v = true) (j) :
    Query.nbr v ((ω.2.2 v j : ℕ) + 1) ∈ (edgeTest n α k).queries ω := by
  simp only [edgeTest, List.mem_flatMap, List.mem_finRange, true_and]
  refine ⟨v, ?_⟩
  simp only [h, if_true, List.mem_append, List.mem_cons, List.mem_ofFn]
  right; right
  exact ⟨j, rfl⟩



/-- degree answers -/
noncomputable def dA (G : AdjList n) (ω : (edgeTest n α k).Ω) : Fin n → Option ℕ :=
  fun v => if Query.deg v ∈ (edgeTest n α k).queries ω then some (G.adj v).length else none

/-- neighbour answers -/
noncomputable def mA (G : AdjList n) (ω : (edgeTest n α k).Ω) : Fin n → ℕ → Option (Option (Fin n)) :=
  fun v i => if Query.nbr v i ∈ (edgeTest n α k).queries ω then some (G.nbr v i) else none

lemma run_eq (G : AdjList n) (ω : (edgeTest n α k).Ω) :
    (edgeTest n α k).run G ω = (edgeTest n α k).output ω (dA G ω) (mA G ω) := rfl

lemma out_SL (ω : (edgeTest n α k).Ω) d m H (v : Fin n) :
    v ∈ ((edgeTest n α k).output ω d m H).SL ↔ ω.1 v = true := by
  simp [edgeTest]

lemma out_SR (ω : (edgeTest n α k).Ω) d m H (v : Fin n) :
    v ∈ ((edgeTest n α k).output ω d m H).SR ↔ ω.2.1 v = true := by
  simp [edgeTest]

lemma out_SL3 (ω : (edgeTest n α k).Ω) d m H (v : Fin n) :
    v ∈ ((edgeTest n α k).output ω d m H).SL3 ↔ ω.1 v = true ∧ (∃ x ∈ d v, x < Delta k α) ∧
      ((rowNbrs m v (Delta k α) \ H).card : ℝ) < 2 * α := by
  simp [edgeTest]

lemma out_SR3 (ω : (edgeTest n α k).Ω) d m H (v : Fin n) :
    v ∈ ((edgeTest n α k).output ω d m H).SR3 ↔ ω.2.1 v = true ∧ (∃ x ∈ d v, x < Delta k α) ∧
      (Delta k α : ℝ) / (rr n α k) * ((Finset.univ.filter fun j =>
        ∃ u, m v ((ω.2.2 v j : ℕ) + 1) = some (some u) ∧ u ∉ H).card : ℝ) < 2 * α := by
  classical
  simp [edgeTest]

lemma out_ZE (ω : (edgeTest n α k).Ω) d m H :
    ((edgeTest n α k).output ω d m H).ZE = (((edgeTest n α k).output ω d m H).SL3 ×ˢ
      ((edgeTest n α k).output ω d m H).SR3 |>.filter fun p => p.2 ∈ rowNbrs m p.1 (Delta k α)).card := by
  simp [edgeTest]


lemma dA_of (G : AdjList n) (ω : (edgeTest n α k).Ω) (v : Fin n)
    (h : ω.1 v = true ∨ ω.2.1 v = true) : dA G ω v = some (G.adj v).length := by
  unfold dA
  rcases h with h | h
  · rw [if_pos (deg_mem_of_SL ω v h)]
  · rw [if_pos (deg_mem_of_SR ω v h)]

lemma mA_some (G : AdjList n) (ω : (edgeTest n α k).Ω) (v : Fin n) (i : ℕ) (u : Fin n)
    (h : mA G ω v i = some (some u)) : G.nbr v i = some u := by
  unfold mA at h
  split_ifs at h with h1
  · exact Option.some_injective _ h

lemma nbr_some_mem (G : AdjList n) (v : Fin n) (i : ℕ) (u : Fin n) (h : G.nbr v i = some u) :
    u ∈ G.adj v := by
  unfold AdjList.nbr at h
  split_ifs at h with h1
  exact List.mem_of_getElem? h

lemma rowNbrs_sub (G : AdjList n) (ω : (edgeTest n α k).Ω) (v u : Fin n) (D : ℕ)
    (h : u ∈ rowNbrs (mA G ω) v D) : u ∈ G.adj v := by
  unfold rowNbrs at h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
  obtain ⟨i, -, hi⟩ := h
  exact nbr_some_mem G v i u (mA_some G ω v i u hi)

lemma rowNbrs_of_SL (G : AdjList n) (ω : (edgeTest n α k).Ω) (v u : Fin n) (hv : ω.1 v = true)
    (hlen : (G.adj v).length < Delta k α) (hu : u ∈ G.adj v) :
    u ∈ rowNbrs (mA G ω) v (Delta k α) := by
  unfold rowNbrs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Icc]
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
  refine ⟨i + 1, ⟨by omega, by omega⟩, ?_⟩
  unfold mA
  rw [if_pos (nbr_mem_of_SL ω v hv (i + 1) (by omega) (by omega))]
  unfold AdjList.nbr
  rw [if_pos ⟨by omega, by omega⟩]
  simp [List.getElem?_eq_getElem hi]

lemma rowNbrs_eq (G : AdjList n) (ω : (edgeTest n α k).Ω) (v : Fin n) (hv : ω.1 v = true)
    (hlen : (G.adj v).length < Delta k α) :
    rowNbrs (mA G ω) v (Delta k α) = (G.adj v).toFinset := by
  ext u
  rw [List.mem_toFinset]
  exact ⟨rowNbrs_sub G ω v u _, rowNbrs_of_SL G ω v u hv hlen⟩

variable (G : AdjList n) (H : Finset (Fin n)) (ω : (edgeTest n α k).Ω)

lemma mem_SL (v : Fin n) : v ∈ ((edgeTest n α k).run G ω H).SL ↔ ω.1 v = true := by
  rw [run_eq]; exact out_SL ω _ _ H v

lemma mem_SR (v : Fin n) : v ∈ ((edgeTest n α k).run G ω H).SR ↔ ω.2.1 v = true := by
  rw [run_eq]; exact out_SR ω _ _ H v

lemma mem_SL3 (v : Fin n) :
    v ∈ ((edgeTest n α k).run G ω H).SL3 ↔
      ω.1 v = true ∧ (G.adj v).length < Delta k α ∧ (dHbar G H v : ℝ) < 2 * α := by
  rw [run_eq, out_SL3]
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [dA_of G ω v (Or.inl h1)] at h2
    obtain ⟨x, hx, hxl⟩ := h2
    rw [Option.mem_def, Option.some_inj] at hx
    subst hx
    rw [rowNbrs_eq G ω v h1 hxl] at h3
    exact ⟨h1, hxl, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ⟨_, by rw [dA_of G ω v (Or.inl h1)]; rfl, h2⟩, ?_⟩
    rw [rowNbrs_eq G ω v h1 h2]
    exact h3

lemma mem_SR3 (v : Fin n) :
    v ∈ ((edgeTest n α k).run G ω H).SR3 ↔
      ω.2.1 v = true ∧ (G.adj v).length < Delta k α ∧
        (Delta k α : ℝ) / (rr n α k) * (Ycnt G H v (ω.2.2 v) : ℝ) < 2 * α := by
  rw [run_eq, out_SR3]
  have hY : ∀ h1 : ω.2.1 v = true, ((Finset.univ.filter fun j =>
        ∃ u, mA G ω v ((ω.2.2 v j : ℕ) + 1) = some (some u) ∧ u ∉ H).card) =
        Ycnt G H v (ω.2.2 v) := by
    intro h1
    classical
    unfold Ycnt
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold mA
    rw [if_pos (nbr_mem_of_SR ω v h1 j)]
    simp
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [dA_of G ω v (Or.inr h1)] at h2
    obtain ⟨x, hx, hxl⟩ := h2
    rw [Option.mem_def, Option.some_inj] at hx
    subst hx
    rw [hY h1] at h3
    exact ⟨h1, hxl, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ⟨_, by rw [dA_of G ω v (Or.inr h1)]; rfl, h2⟩, ?_⟩
    rw [hY h1]
    exact h3

lemma ZE_eq :
    ((edgeTest n α k).run G ω H).ZE = (((edgeTest n α k).run G ω H).SL3 ×ˢ
      ((edgeTest n α k).run G ω H).SR3 |>.filter fun p => G.toGraph.Adj p.1 p.2).card := by
  classical
  rw [run_eq, out_ZE]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, rowNbrs_sub G ω p.1 p.2 _ h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have := (mem_SL3 G H ω p.1).1 (by rw [run_eq]; exact h1.1)
    exact rowNbrs_of_SL G ω p.1 p.2 this.1 this.2.1 h2


lemma pr_pos (v : Fin n) [Nonempty (Fin (Delta k α))]
    (E : (Fin (rr n α k) → Fin (Delta k α)) → Prop) :
    Kit.pr (edgeTest n α k).dist (fun ω => E (ω.2.2 v)) =
      Kit.pr (RandomQueryXOR.piDist fun _ : Fin (rr n α k) =>
        ShallowShadows.ShadowNorm.uniformDist (Fin (Delta k α))) E := by
  refine (Kit.pr_prod_snd _ _ (fun b : (Fin n → Bool) × (Fin n → Fin (rr n α k) → Fin (Delta k α)) =>
    E (b.2 v))).trans ?_
  refine (Kit.pr_prod_snd _ _ (fun b : Fin n → Fin (rr n α k) → Fin (Delta k α) => E (b v))).trans ?_
  rw [Kit.pr_uniform_eq_pr_pi (m := n) (Q := Fin (rr n α k) → Fin (Delta k α))]
  rw [Kit.pr_piDist_coord (fun _ : Fin n =>
    ShallowShadows.ShadowNorm.uniformDist (Fin (rr n α k) → Fin (Delta k α))) v E]
  exact Kit.pr_uniform_eq_pr_pi E

lemma pr_false {Ω : Type} [Fintype Ω] (d : WildeQIT.FinDist Ω) : Kit.pr d (fun _ => False) = 0 := by
  unfold Kit.pr; simp

lemma mem_U (G : AdjList n) (v : Fin n) : v ∈ U G α k ↔ (G.adj v).length < Delta k α := by
  simp [U, V1]

lemma mem_W3 (G : AdjList n) (H : Finset (Fin n)) (v : Fin n) :
    v ∈ W3 G α k H ↔ (G.adj v).length < Delta k α ∧ (dHbar G H v : ℝ) < α := by
  simp [W3, U, V1]

lemma mem_W4 (G : AdjList n) (H : Finset (Fin n)) (v : Fin n) :
    v ∈ W4 G α k H ↔ (G.adj v).length < Delta k α ∧ (dHbar G H v : ℝ) < 4 * α := by
  simp [W4, U, V1]

lemma final_arith (n : ℕ) (hn : (1 : ℝ) ≤ n) :
    (n : ℝ) * Real.exp (-31 * L n) ≤ (n : ℝ) ^ (-30 : ℝ) := by
  have h2n : (0 : ℝ) < 2 * n := by linarith
  have he : Real.exp (-31 * L n) = ((2 * (n : ℝ)) ^ 31)⁻¹ := by
    rw [neg_mul, Real.exp_neg, show (31 : ℝ) = ((31 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, L,
      Real.exp_log h2n]
  rw [he, Real.rpow_neg (by linarith), show (30 : ℝ) = ((30 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  have hn0 : (0 : ℝ) < n := by linarith
  rw [mul_pow, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
  rw [show (n : ℝ) ^ 31 = n * n ^ 30 by ring]
  field_simp
  have : (1 : ℝ) ≤ 2 ^ 31 := by norm_num
  nlinarith [pow_pos hn0 30]

lemma exp_bound (X Lv : ℝ) (hL : 0 ≤ Lv) (hX : cc * Lv ≤ X) (c : ℝ) (hc : 0.38 ≤ c) :
    Real.exp (-c * X) ≤ Real.exp (-31 * Lv) := by
  apply Real.exp_le_exp.2
  have hcc : cc = 100000 := by norm_num [cc]
  rw [hcc] at hX
  have hX0 : 0 ≤ X := by nlinarith
  nlinarith

end NAMatchEst.AuxE38

namespace NAMatchEst.AuxE38
open NAMatchEst

/-- Basic parameter facts. -/
lemma params (n : ℕ) [NeZero n] (α : ℝ) (k : ℕ)
    (h13 : (n : ℝ) ^ ((1 : ℝ) / 3) ≤ α) (hα2 : α ^ 2 < k) :
    (1 : ℝ) ≤ n ∧ 1 ≤ α ∧ 0 < L n ∧ 2 ≤ Delta k α ∧ 0 < rr n α k ∧
      cc * L n ≤ (rr n α k : ℝ) * α / Delta k α := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  have hα : 1 ≤ α := le_trans (Real.one_le_rpow hn (by norm_num)) h13
  have hL : 0 < L n := Real.log_pos (by linarith)
  have hΔ : 2 ≤ Delta k α := by
    unfold Delta
    apply Nat.le_floor
    rw [le_div_iff₀ (by linarith)]
    push_cast
    nlinarith
  have hΔr : (2 : ℝ) ≤ Delta k α := by exact_mod_cast hΔ
  have hcc : (0 : ℝ) < cc := by norm_num [cc]
  have hx : 0 < cc * Delta k α * L n / α := by positivity
  have hR := Nat.le_ceil (cc * Delta k α * L n / α)
  refine ⟨hn, hα, hL, hΔ, Nat.ceil_pos.2 hx, ?_⟩
  rw [le_div_iff₀ (by linarith)]
  rw [div_le_iff₀ (by linarith)] at hR
  change cc * Delta k α * L n ≤ (rr n α k : ℝ) * α at hR
  linarith

end NAMatchEst.AuxE38

namespace NAMatchEst.AuxE38
open NAMatchEst

lemma asymp (n : ℕ) (hn : (10 : ℝ) ^ 42 ≤ n) : cc * L n ≤ (n : ℝ) ^ ((1 : ℝ) / 3) := by
  have hn0 : (0 : ℝ) ≤ n := by positivity
  set y := (n : ℝ) ^ ((1 : ℝ) / 6) with hy
  have hy2 : (n : ℝ) ^ ((1 : ℝ) / 3) = y * y := by
    rw [hy, ← Real.rpow_add' hn0 (by norm_num)]; norm_num
  have hy7 : (10 : ℝ) ^ 7 ≤ y := by
    have h1 : ((10 : ℝ) ^ 42) ^ ((1 : ℝ) / 6) = 10 ^ 7 := by
      rw [show ((10 : ℝ) ^ 42) = ((10 : ℝ) ^ 7) ^ (6 : ℕ) by norm_num,
        show ((1 : ℝ) / 6) = ((6 : ℕ) : ℝ)⁻¹ by norm_num]
      exact Real.pow_rpow_inv_natCast (by positivity) (by norm_num)
    rw [← h1]
    exact Real.rpow_le_rpow (by positivity) hn (by norm_num)
  have hlog : Real.log n ≤ 6 * y := by
    have := Real.log_le_rpow_div hn0 (show (0 : ℝ) < 1 / 6 by norm_num)
    rw [hy]; linarith [show (n : ℝ) ^ ((1 : ℝ) / 6) / (1 / 6) = 6 * (n : ℝ) ^ ((1 : ℝ) / 6) by ring]
  have hn1 : (2 : ℝ) ≤ n := le_trans (by norm_num) hn
  have hL : L n ≤ 2 * Real.log n := by
    unfold L
    rw [Real.log_mul (by norm_num) (by linarith)]
    have : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn1
    linarith
  rw [hy2]
  have hcc : cc = 100000 := by norm_num [cc]
  rw [hcc]
  nlinarith



lemma pLpR {n : ℕ} {α : ℝ} {k : ℕ} (hk : (0 : ℝ) < k) (hα : 0 < α) :
    cc * L n / Real.sqrt (k * α) * Real.sqrt (α / k) = cc * L n / k := by
  rw [Real.sqrt_mul hk.le, Real.sqrt_div hα.le]
  have h1 := Real.sqrt_pos.2 hk
  have h2 := Real.sqrt_pos.2 hα
  field_simp
  rw [Real.sq_sqrt hk.le]

lemma pr_two {n : ℕ} {α : ℝ} {k : ℕ} (Q : (Fin n → Bool) × (Fin n → Bool) → Prop) :
    Kit.pr (edgeTest n α k).dist (fun ω => Q (ω.1, ω.2.1)) =
      Kit.pr ((bernDist (n := n) (cc * L n / Real.sqrt (k * α))).prod
        (bernDist (n := n) (Real.sqrt (α / k)))) Q := by
  refine (Kit.pr_prod _ _ _).trans ?_
  rw [Kit.pr_prod]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  exact Kit.pr_prod_fst _ _ (fun s : Fin n → Bool => Q (a, s))

lemma final_arith2 (n : ℕ) (hn : (1 : ℝ) ≤ n) :
    2 * Real.exp (-31 * L n) ≤ (n : ℝ) ^ (-30 : ℝ) := by
  have h := final_arith n hn
  have hn0 : (0 : ℝ) < n := by linarith
  have he : Real.exp (-31 * L n) = ((2 * (n : ℝ)) ^ 31)⁻¹ := by
    rw [neg_mul, Real.exp_neg, show (31 : ℝ) = ((31 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, L,
      Real.exp_log (by linarith)]
  rw [he, Real.rpow_neg (by linarith), show (30 : ℝ) = ((30 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, mul_pow, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
  rw [show (n : ℝ) ^ 31 = n * n ^ 30 by ring]
  field_simp
  have : (1 : ℝ) ≤ n ^ 30 := one_le_pow₀ hn
  nlinarith [pow_pos hn0 30]

end NAMatchEst.AuxE38

namespace NAMatchEst.AuxE38
open NAMatchEst

lemma pairs_of_matching {n : ℕ} (G : AdjList n) (M : G.toGraph.Subgraph) (hM : M.IsMatching)
    (S : Finset (Fin n)) (hS : M.verts ⊆ ↑S) :
    ∃ (m : ℕ) (a b : Fin m → Fin n), Function.Injective a ∧ Function.Injective b ∧
      (∀ i, G.toGraph.Adj (a i) (b i) ∧ a i ∈ S ∧ b i ∈ S) ∧ 2 * M.edgeSet.ncard = m := by
  classical
  let P := (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => M.Adj p.1 p.2)
  let e := P.equivFin.symm
  have hP : ∀ i, M.Adj (e i).1.1 (e i).1.2 := fun i => (Finset.mem_filter.1 (e i).2).2
  refine ⟨P.card, fun i => (e i).1.1, fun i => (e i).1.2, ?_, ?_, fun i => ?_, ?_⟩
  · intro i j h
    apply e.injective
    apply Subtype.ext
    refine Prod.ext h ?_
    have hj := hP j
    simp only at h
    rw [← h] at hj
    exact hM.eq_of_adj_left (hP i) hj
  · intro i j h
    apply e.injective
    apply Subtype.ext
    refine Prod.ext ?_ h
    have hj := hP j
    simp only at h
    rw [← h] at hj
    exact hM.eq_of_adj_right (hP i) hj
  · exact ⟨M.adj_sub (hP i), hS (M.edge_vert (hP i)), hS (M.edge_vert (M.adj_symm (hP i)))⟩
  · have h1 : P.card = ∑ u, M.spanningCoe.degree u := by
      simp only [P, Finset.card_filter, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter,
        Finset.card_filter]
      simp
    rw [h1, SimpleGraph.sum_degrees_eq_twice_card_edges, ← SimpleGraph.Subgraph.edgeSet_spanningCoe,
      ← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]

end NAMatchEst.AuxE38

open NAMatchEst NAMatchEst.AuxE38 in
theorem solution : ∃ N₀ : ℕ, ∀ (n : ℕ) [NeZero n], N₀ ≤ n → ∀ (α : ℝ) (k : ℕ),
    (n : ℝ) ^ ((1 : ℝ) / 3) ≤ α → α ≤ (n : ℝ) ^ ((1 : ℝ) / 2) → α ≤ k → (k : ℝ) ≤ n → α ^ 2 < k →
    ∀ (G : AdjList n) (H : Finset (Fin n)),
      (∃ M : G.toGraph.Subgraph, M.IsMatching ∧ M.verts ⊆ ↑(W3 G α k H) ∧
        (k : ℝ) / 2 ≤ M.edgeSet.ncard) →
      1 - 2 * (n : ℝ) ^ (-30 : ℝ) ≤
        (edgeTest n α k).prob G (fun o => cc * L n / 4 ≤ ((o H).ZE : ℝ)) := by
  obtain ⟨N7, h7⟩ := lemma_3_7
  refine ⟨max N7 (10 ^ 42), fun n _ hN α k h13 h12 hαk hkn hα2 G H hMex => ?_⟩
  obtain ⟨hn, hα, hL, -, -, -⟩ := params n α k h13 hα2
  obtain ⟨hE7, hdet⟩ := h7 n (le_of_max_le_left hN) α k h13 h12 hαk hkn hα2 G H
  have hn42 : (10 : ℝ) ^ 42 ≤ n := by exact_mod_cast le_of_max_le_right hN
  have hasy := asymp n hn42
  obtain ⟨M, hM, hMW, hMk⟩ := hMex
  obtain ⟨m, a, b, ha, hb, hab, hm⟩ := pairs_of_matching G M hM _ hMW
  have hmk : (k : ℝ) ≤ m := by
    have : (m : ℝ) = 2 * M.edgeSet.ncard := by rw [← hm]; push_cast; ring
    linarith
  have hk : (0 : ℝ) < k := by nlinarith
  have hcc : (0 : ℝ) < cc := by norm_num [cc]
  set pL := cc * L n / Real.sqrt (k * α) with hpL
  set pR := Real.sqrt (α / k) with hpR
  have hαk1 : α / k ≤ 1 := (div_le_one hk).2 hαk
  have hαk0 : 0 ≤ α / k := by positivity
  have hpR0 : 0 ≤ pR := Real.sqrt_nonneg _
  have hpR1 : pR ≤ 1 := Real.sqrt_le_one.mpr hαk1
  have hsq : α ≤ Real.sqrt (k * α) := by
    rw [Real.le_sqrt (by linarith) (by positivity)]; nlinarith
  have hpL0 : 0 ≤ pL := by positivity
  have hpL1 : pL ≤ 1 := by
    rw [hpL, div_le_one (by linarith)]; linarith
  have hprod : pL * pR = cc * L n / k := pLpR hk (by linarith)
  have hmLR : cc * L n ≤ m * pL * pR := by
    rw [mul_assoc, hprod, mul_div_assoc']
    rw [le_div_iff₀ hk]
    nlinarith [mul_le_mul_of_nonneg_left hmk (le_of_lt (mul_pos hcc hL))]
  have hmR : α ≤ m * pR := by
    have h1 : α / k ≤ pR := by
      rw [hpR, Real.le_sqrt hαk0 hαk0]; nlinarith
    have h2 : α ≤ k * pR := by rwa [div_le_iff₀ hk, mul_comm] at h1
    nlinarith
  -- the pair-count tail
  have hpair := pair_count_lower_tail (n := n) pL pR ⟨hpL0, hpL1⟩ ⟨hpR0, hpR1⟩ a b ha hb
  rw [← Kit.pr_eq_sum, ← pr_two (α := α) (k := k)] at hpair
  have hcc31 : 31 * L n ≤ cc * L n / 14 := by
    rw [le_div_iff₀ (by norm_num)]; norm_num [cc]; nlinarith
  have hpair2 : Kit.pr (edgeTest n α k).dist (fun ω =>
      (((Finset.univ.filter fun i => ω.1 (a i) = true ∧ ω.2.1 (b i) = true).card : ℕ) : ℝ) ≤
        m * pL * pR / 4) ≤ (n : ℝ) ^ (-30 : ℝ) - (n : ℝ) ^ (-30 : ℝ) + 2 * Real.exp (-31 * L n) := by
    refine hpair.trans ?_
    have e1 : Real.exp (-(m * pR) / 7) ≤ Real.exp (-31 * L n) := by
      apply Real.exp_le_exp.2
      rw [neg_div]
      linarith
    have e2 : Real.exp (-(m * pL * pR) / 14) ≤ Real.exp (-31 * L n) := by
      apply Real.exp_le_exp.2
      rw [neg_div]
      have : cc * L n / 14 ≤ m * pL * pR / 14 := by linarith
      linarith
    linarith
  have hfa := final_arith2 n hn
  rw [Kit.prob_eq_pr] at hE7 ⊢
  have hnot7 := Kit.pr_not (edgeTest n α k).dist (fun ω =>
      ((edgeTest n α k).run G ω H).SR ∩ W3 G α k H ⊆ ((edgeTest n α k).run G ω H).SR3 ∧
      ((edgeTest n α k).run G ω H).SR3 ⊆ ((edgeTest n α k).run G ω H).SR ∩ W4 G α k H)
  have hbad : Kit.pr (edgeTest n α k).dist
      (fun ω => ¬ (cc * L n / 4 ≤ (((edgeTest n α k).run G ω H).ZE : ℝ))) ≤
      2 * (n : ℝ) ^ (-30 : ℝ) := by
    calc _ ≤ Kit.pr (edgeTest n α k).dist (fun ω => ¬ (
        ((edgeTest n α k).run G ω H).SR ∩ W3 G α k H ⊆ ((edgeTest n α k).run G ω H).SR3 ∧
        ((edgeTest n α k).run G ω H).SR3 ⊆ ((edgeTest n α k).run G ω H).SR ∩ W4 G α k H) ∨
          (((Finset.univ.filter fun i => ω.1 (a i) = true ∧ ω.2.1 (b i) = true).card : ℕ) : ℝ) ≤
            m * pL * pR / 4) := by
          refine Kit.pr_mono _ fun ω hω => ?_
          by_cases hE : ((edgeTest n α k).run G ω H).SR ∩ W3 G α k H ⊆
              ((edgeTest n α k).run G ω H).SR3 ∧
              ((edgeTest n α k).run G ω H).SR3 ⊆ ((edgeTest n α k).run G ω H).SR ∩ W4 G α k H
          · right
            have hle : (Finset.univ.filter fun i => ω.1 (a i) = true ∧ ω.2.1 (b i) = true).card ≤
                ((edgeTest n α k).run G ω H).ZE := by
              rw [ZE_eq]
              refine Finset.card_le_card_of_injOn (fun i => (a i, b i)) ?_ ?_
              · intro i hi
                simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi
                simp only [Finset.coe_filter, Finset.mem_product, Set.mem_ofPred_eq]
                obtain ⟨hadj, haW, hbW⟩ := hab i
                refine ⟨⟨(hdet ω).1 ?_, hE.1 ?_⟩, hadj⟩
                · rw [Finset.mem_inter, mem_SL]; exact ⟨hi.1, haW⟩
                · rw [Finset.mem_inter, mem_SR]; exact ⟨hi.2, hbW⟩
              · intro i _ j _ hij
                exact ha (Prod.ext_iff.1 hij).1
            have hle' : (((Finset.univ.filter fun i => ω.1 (a i) = true ∧
                ω.2.1 (b i) = true).card : ℕ) : ℝ) ≤ ((edgeTest n α k).run G ω H).ZE := by
              exact_mod_cast hle
            have : cc * L n / 4 ≤ m * pL * pR / 4 := by linarith
            linarith [lt_of_not_ge hω]
          · left; exact hE
      _ ≤ _ := Kit.pr_or_le _ _ _
      _ ≤ (n : ℝ) ^ (-30 : ℝ) + (2 * Real.exp (-31 * L n)) := by
          refine add_le_add ?_ (by linarith)
          rw [hnot7]; linarith
      _ ≤ _ := by linarith
  rw [Kit.pr_not] at hbad
  linarith
