-- Prove2me | solution 1 for NAMatchEst.lemma_3_13
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T00:55:37.200717+00:00
-- url     : https://prove2.me/submissions/3fb8b07e-367c-46c1-8fe1-c4df6dd74b78

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
import Definitions.Def_NAMatchEst_AdjList_nbr
import Definitions.Def_NAMatchEst_C0
import Definitions.Def_NAMatchEst_U
import Definitions.Def_NAMatchEst_V1
import Definitions.Def_NAMatchEst_smallTrial
import Theorems.Thm_NAMatchEst_lemma_3_5
import Theorems.Thm_NAMatchEst_observation_3_2
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



namespace NAMatchEst.AuxE13
open NAMatchEst

lemma pr_false {Ω : Type} [Fintype Ω] (d : WildeQIT.FinDist Ω) : Kit.pr d (fun _ => False) = 0 := by
  unfold Kit.pr; simp

lemma pr_prod_and {α β : Type} [Fintype α] [Fintype β] (p : WildeQIT.FinDist α)
    (q : WildeQIT.FinDist β) (A : α → Prop) (B : β → Prop) :
    Kit.pr (p.prod q) (fun ω => A ω.1 ∧ B ω.2) = Kit.pr p A * Kit.pr q B := by
  classical
  rw [Kit.pr_prod]
  have : ∀ a, p.prob a * Kit.pr q (fun b => A a ∧ B b) =
      (p.prob a * if A a then 1 else 0) * Kit.pr q B := by
    intro a
    by_cases h : A a
    · simp only [h, true_and, if_true, mul_one]
    · simp only [h, false_and, if_false, mul_zero, zero_mul, pr_false]
  rw [Finset.sum_congr rfl fun a _ => this a, ← Finset.sum_mul, Kit.pr_eq_sum p A]

lemma pr_bern (n : ℕ) (p : ℝ) (u : Fin n) :
    Kit.pr (bernDist (n := n) p) (fun ω => ω u = true) = max 0 (min p 1) := by
  classical
  unfold bernDist
  refine (Kit.pr_piDist_coord _ u (fun x => x = true)).trans ?_
  rw [Kit.pr_eq_sum]
  simp

lemma ex_count {Ω ι : Type} [Fintype Ω] (d : WildeQIT.FinDist Ω) (P : Finset ι)
    (E : ι → Ω → Prop) [∀ i, DecidablePred (E i)] :
    Kit.ex d (fun ω => ((P.filter (fun i => E i ω)).card : ℝ)) = ∑ i ∈ P, Kit.pr d (E i) := by
  unfold Kit.ex
  simp_rw [Finset.card_filter]
  push_cast
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Kit.pr_eq_sum]

lemma exists_max_matching {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = TuranMatching.Clique.matchingNumber G := by
  have hne : {m | ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = m}.Nonempty :=
    ⟨_, ⊥, fun v hv => by simp at hv, rfl⟩
  have hbdd : BddAbove {m | ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = m} := by
    refine ⟨G.edgeSet.ncard, ?_⟩
    rintro m ⟨M, -, rfl⟩
    exact Set.ncard_le_ncard M.edgeSet_subset (Set.toFinite _)
  exact Nat.sSup_mem hne hbdd

/-- The matching partner of a vertex. -/
noncomputable def partner {V : Type} {G : SimpleGraph V} (M : G.Subgraph) (hM : M.IsMatching)
    (v : V) : V :=
  open Classical in if h : v ∈ M.verts then (hM h).exists.choose else v

lemma partner_adj {V : Type} {G : SimpleGraph V} (M : G.Subgraph) (hM : M.IsMatching) {v : V}
    (h : v ∈ M.verts) : M.Adj v (partner M hM v) := by
  unfold partner; rw [dif_pos h]; exact (hM h).exists.choose_spec

lemma partner_inj {V : Type} {G : SimpleGraph V} (M : G.Subgraph) (hM : M.IsMatching) {x y : V}
    (hx : x ∈ M.verts) (hy : y ∈ M.verts) (hxy : partner M hM x = partner M hM y) : x = y := by
  have h1 := partner_adj M hM hx
  have h2 := partner_adj M hM hy
  rw [hxy] at h1
  have hp : partner M hM y ∈ M.verts := M.edge_vert h2.symm
  exact (hM hp).unique h1.symm h2.symm

lemma eventually_cL : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → cc * L n ≤ (n : ℝ) ^ ((1 : ℝ) / 6) := by
  have hcc : (0:ℝ) < cc := by unfold cc; norm_num
  have h := (isLittleO_log_rpow_atTop (r := 1/6) (by norm_num)).bound
    (c := 1 / (2 * cc)) (by positivity)
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp h
  refine ⟨⌈X⌉₊ + 1, fun n hn => ?_⟩
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hx : X ≤ 2 * n := by
    have : ((⌈X⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    have := Nat.le_ceil X
    push_cast at *
    linarith
  have h1 := hX (2 * n) hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith)),
    abs_of_nonneg (by positivity)] at h1
  have h2 : (2 * (n:ℝ)) ^ ((1:ℝ)/6) ≤ 2 * (n:ℝ) ^ ((1:ℝ)/6) := by
    rw [Real.mul_rpow (by norm_num) (by positivity)]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc (2:ℝ) ^ ((1:ℝ)/6) ≤ 2 ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  unfold L
  calc cc * Real.log (2 * n) ≤ cc * (1 / (2 * cc) * (2 * n) ^ ((1:ℝ)/6)) :=
        mul_le_mul_of_nonneg_left h1 hcc.le
    _ ≤ cc * (1 / (2 * cc) * (2 * (n:ℝ) ^ ((1:ℝ)/6))) := by gcongr
    _ = _ := by field_simp

lemma mem_U {n : ℕ} (G : AdjList n) (α : ℝ) (k : ℕ) (v : Fin n) :
    v ∈ U G α k ↔ (G.adj v).length < Delta k α := by
  simp [U, V1]

lemma nbr_mem {n : ℕ} (G : AdjList n) (v : Fin n) (i : ℕ) (u : Fin n) (h : G.nbr v i = some u) :
    u ∈ G.adj v := by
  unfold AdjList.nbr at h
  split_ifs at h
  exact List.mem_of_getElem? h

lemma mem_ite_some {p : Prop} [Decidable p] {x y : ℕ} (h : x ∈ (if p then some y else none)) :
    y = x := by
  by_cases hp : p
  · rw [if_pos hp] at h; exact Option.some_injective _ h
  · rw [if_neg hp] at h; cases h

lemma ite_some_eq {β : Type} {p : Prop} [Decidable p] {x y : β}
    (h : (if p then some y else none) = some x) : y = x := by
  by_cases hp : p
  · rw [if_pos hp] at h; exact Option.some_injective _ h
  · rw [if_neg hp] at h; cases h

lemma ite_some_of {β : Type} {p : Prop} [Decidable p] {y : β} (hp : p) :
    (if p then some y else none) = some y := by
  rw [if_pos hp]

/-- Ordered adjacent pairs inside `U`. -/
noncomputable def Pset {n : ℕ} (G : AdjList n) (α : ℝ) (k : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.1 ∈ U G α k ∧ p.2 ∈ U G α k ∧ G.toGraph.Adj p.1 p.2

lemma q_degL {n : ℕ} (α : ℝ) (k : ℕ) (ω : (Fin n → Bool) × (Fin n → Bool)) (v : Fin n)
    (hv : ω.1 v = true) : Query.deg v ∈ (smallEdgeTest n α k).queries ω := by
  simp only [smallEdgeTest]
  exact List.mem_flatMap.mpr ⟨v, List.mem_finRange _, by simp [hv, rowQueries]⟩

lemma q_degR {n : ℕ} (α : ℝ) (k : ℕ) (ω : (Fin n → Bool) × (Fin n → Bool)) (v : Fin n)
    (hv : ω.2 v = true) : Query.deg v ∈ (smallEdgeTest n α k).queries ω := by
  simp only [smallEdgeTest]
  exact List.mem_flatMap.mpr ⟨v, List.mem_finRange _, by simp [hv]⟩

lemma q_nbrL {n : ℕ} (α : ℝ) (k : ℕ) (ω : (Fin n → Bool) × (Fin n → Bool)) (v : Fin n)
    (hv : ω.1 v = true) (t : ℕ) (ht : t < Delta k α) :
    Query.nbr v (t + 1) ∈ (smallEdgeTest n α k).queries ω := by
  simp only [smallEdgeTest]
  refine List.mem_flatMap.mpr ⟨v, List.mem_finRange _, ?_⟩
  simp only [hv, if_true, rowQueries, List.mem_append, List.mem_cons, List.mem_map,
    List.mem_range]
  left; right
  exact ⟨t, ht, rfl⟩

lemma sedge_true {n : ℕ} (α : ℝ) (k : ℕ) (G : AdjList n) (ω : (Fin n → Bool) × (Fin n → Bool))
    (h : (smallEdgeTest n α k).run G ω = true) :
    cc * L n / 4 ≤
      (((Pset G α k).filter (fun p => ω.1 p.1 = true ∧ ω.2 p.2 = true)).card : ℝ) := by
  classical
  unfold RandAlg.run at h
  generalize (smallEdgeTest n α k).queries ω = Q at h
  simp only [smallEdgeTest, decide_eq_true_eq] at h
  refine h.trans ?_
  exact_mod_cast Finset.card_le_card (by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp
    obtain ⟨⟨⟨h1, x1, hx1, hx1'⟩, ⟨h2, x2, hx2, hx2'⟩⟩, h3⟩ := hp
    simp only [Pset, Finset.mem_filter, Finset.mem_univ, true_and, mem_U]
    refine ⟨⟨?_, ?_, ?_⟩, h1, h2⟩
    · have := mem_ite_some hx1; omega
    · have := mem_ite_some hx2; omega
    · simp only [rowNbrs, Finset.mem_filter, Finset.mem_univ, true_and] at h3
      obtain ⟨i, -, hi⟩ := h3
      exact nbr_mem G _ _ _ (ite_some_eq hi))

lemma sedge_false {n m : ℕ} (α : ℝ) (k : ℕ) (G : AdjList n) (a b : Fin m → Fin n)
    (ha : Function.Injective a)
    (hU : ∀ i, (G.adj (a i)).length < Delta k α) (hUb : ∀ i, (G.adj (b i)).length < Delta k α)
    (hadj : ∀ i, b i ∈ G.adj (a i)) (ω : (Fin n → Bool) × (Fin n → Bool))
    (h : (smallEdgeTest n α k).run G ω = false) :
    ((Finset.univ.filter fun i => ω.1 (a i) = true ∧ ω.2 (b i) = true).card : ℝ) <
      cc * L n / 4 := by
  classical
  unfold RandAlg.run at h
  have hL1 := q_degL α k ω
  have hR1 := q_degR α k ω
  have hN1 := q_nbrL α k ω
  generalize (smallEdgeTest n α k).queries ω = Q at h hL1 hR1 hN1
  simp only [smallEdgeTest, decide_eq_false_iff_not, not_le] at h
  refine lt_of_le_of_lt ?_ h
  refine Nat.cast_le.mpr (Finset.card_le_card_of_injOn (fun i => (a i, b i)) ?_ ?_)
  · intro i hi
    simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨h1, h2⟩ := hi
    obtain ⟨t, ht⟩ := List.mem_iff_getElem?.mp (hadj i)
    have htl : t < (G.adj (a i)).length := (List.getElem?_eq_some_iff.mp ht).1
    have hUi := hU i
    simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
      true_and]
    refine ⟨⟨⟨h1, (G.adj (a i)).length, ?_, hUi⟩, ⟨h2, (G.adj (b i)).length, ?_, hUb i⟩⟩, ?_⟩
    · rw [ite_some_of (hL1 _ h1)]; rfl
    · rw [ite_some_of (hR1 _ h2)]; rfl
    · simp only [rowNbrs, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨t + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      rw [ite_some_of (hN1 _ h1 t (by omega))]
      unfold AdjList.nbr
      rw [if_pos ⟨by omega, by omega⟩]
      simpa using ht
  · intro i _ j _ hij
    simp only [Prod.mk.injEq] at hij
    exact ha hij.1

lemma half_card {n : ℕ} (G : AdjList n) (α : ℝ) (k : ℕ) (C : Finset (Fin n)) :
    ((C ×ˢ Finset.univ).filter
      (fun p : Fin n × Fin n => p.1 ∈ U G α k ∧ G.toGraph.Adj p.1 p.2)).card ≤
      C.card * Delta k α := by
  classical
  rw [Finset.card_filter, Finset.sum_product]
  calc ∑ u ∈ C, ∑ v, (if u ∈ U G α k ∧ G.toGraph.Adj u v then 1 else 0)
        ≤ ∑ _u ∈ C, Delta k α := by
        refine Finset.sum_le_sum fun u _ => ?_
        rw [← Finset.card_filter]
        by_cases hu : u ∈ U G α k
        · have hsub : (Finset.univ.filter fun v => u ∈ U G α k ∧ G.toGraph.Adj u v) ⊆
              (G.adj u).toFinset := by
            intro v hv
            exact List.mem_toFinset.mpr (Finset.mem_filter.mp hv).2.2
          calc _ ≤ (G.adj u).toFinset.card := Finset.card_le_card hsub
            _ ≤ (G.adj u).length := List.toFinset_card_le _
            _ ≤ Delta k α := ((mem_U G α k u).mp hu).le
        · simp [hu]
    _ = C.card * Delta k α := by rw [Finset.sum_const, smul_eq_mul]

lemma Pset_card {n : ℕ} (G : AdjList n) (α : ℝ) (k : ℕ) (C : Finset (Fin n))
    (hcover : ∀ u v, G.toGraph.Adj u v → u ∈ C ∨ v ∈ C) :
    (Pset G α k).card ≤ 2 * (C.card * Delta k α) := by
  classical
  set A := (C ×ˢ Finset.univ).filter
    (fun p : Fin n × Fin n => p.1 ∈ U G α k ∧ G.toGraph.Adj p.1 p.2) with hA
  have hsub : Pset G α k ⊆ A ∪ A.image Prod.swap := by
    intro p hp
    simp only [Pset, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨h1, h2, h3⟩ := hp
    rcases hcover _ _ h3 with h | h
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩, h1, h3⟩)
    · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p.swap, ?_, by simp⟩)
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩, h2, h3.symm⟩
  have h1 : A.card ≤ C.card * Delta k α := half_card G α k C
  calc _ ≤ (A ∪ A.image Prod.swap).card := Finset.card_le_card hsub
    _ ≤ A.card + (A.image Prod.swap).card := Finset.card_union_le _ _
    _ ≤ A.card + A.card := Nat.add_le_add_left (Finset.card_image_le (s := A) (f := Prod.swap)) _
    _ ≤ _ := by omega

lemma L_ge_one (n : ℕ) (hn : 2 ≤ n) : 1 ≤ L n := by
  unfold L
  rw [Real.le_log_iff_exp_le (by positivity)]
  have h1 := Real.exp_one_lt_d9
  have h2 : (4 : ℝ) ≤ 2 * n := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  linarith

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

lemma exp_small (x c : ℝ) (hc : 0 < c) (hx : 20 * c ≤ x) : Real.exp (-x / c) ≤ 1 / 20 := by
  have h1 : 20 ≤ x / c := (le_div_iff₀ hc).mpr (by linarith)
  have h2 := Real.add_one_le_exp (x / c)
  rw [neg_div, Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
  linarith

lemma arith_no (P C0 cL k α : ℝ) (hP : P ≤ 2 * ((2 * k / (C0 * α)) * (2 * k / α)))
    (hC0 : 0 < C0) (hk0 : 0 < k) (hα : 0 < α) (hsmall : k ≤ α ^ 2) (hcL : 0 < cL) :
    P * (cL / k) / (cL / 4) ≤ 32 / C0 := by
  have e0 : P * (cL / k) / (cL / 4) = 4 * P / k := by field_simp
  rw [e0, div_le_div_iff₀ hk0 hC0]
  have hα2 : 0 < α ^ 2 := by positivity
  have e1 : 2 * ((2 * k / (C0 * α)) * (2 * k / α)) * C0 = 8 * k * (k / α ^ 2) := by
    field_simp; ring
  have e2 : k / α ^ 2 ≤ 1 := by rw [div_le_one hα2]; exact hsmall
  have h1 := mul_le_mul_of_nonneg_right hP hC0.le
  rw [e1] at h1
  have h2 : 8 * k * (k / α ^ 2) ≤ 8 * k := by nlinarith
  linarith

lemma clamp_le (p : ℝ) (hp : 0 ≤ p) : max 0 (min p 1) ≤ p := max_le hp (min_le_left _ _)

lemma deg_false_eq {n : ℕ} [NeZero n] (α : ℝ) (k : ℕ) (G : AdjList n) :
    (degTest n α k).prob G (· = false) = 1 - (degTest n α k).prob G (· = true) := by
  rw [Kit.prob_eq_pr, Kit.prob_eq_pr, ← Kit.pr_not]
  exact Kit.pr_congr _ fun x => by simp

end NAMatchEst.AuxE13

open NAMatchEst NAMatchEst.AuxE13 in
theorem solution : ∃ N₀ : ℕ, ∀ (n : ℕ) [NeZero n], N₀ ≤ n → ∀ (α : ℝ) (k : ℕ),
    (n : ℝ) ^ ((1 : ℝ) / 3) ≤ α → α ≤ (n : ℝ) ^ ((1 : ℝ) / 2) → α ≤ k → (k : ℝ) ≤ n → (k : ℝ) ≤ α ^ 2 →
    ∀ G : AdjList n,
      (k ≤ TuranMatching.Clique.matchingNumber G.toGraph → (smallTrial n α k).prob G (· = false) ≤ 1 / 10) ∧
      ((TuranMatching.Clique.matchingNumber G.toGraph : ℝ) < k / (C0 * α) →
        (smallTrial n α k).prob G (· = true) ≤ 1 / 10) := by
  classical
  obtain ⟨D5, N5, h5⟩ := lemma_3_5
  obtain ⟨Nl, hNl⟩ := eventually_cL
  refine ⟨max 100 (max N5 Nl), ?_⟩
  intro n _ hn α k h13 h12 hαk hkn hsmall G
  have hn100 : 100 ≤ n := le_of_max_le_left hn
  have hN5 : N5 ≤ n := le_of_max_le_left (le_of_max_le_right hn)
  have hNl' : Nl ≤ n := le_of_max_le_right (le_of_max_le_right hn)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : (0 : ℝ) < n := by linarith
  have hL1 : 1 ≤ L n := L_ge_one n (by omega)
  have hcc : cc = 10 ^ 5 := rfl
  have hc0 : 0 < cc := by rw [hcc]; norm_num
  have hcL : 0 < cc * L n := by positivity
  have hα1 : 1 ≤ α := le_trans (Real.one_le_rpow hn1 (by norm_num)) h13
  have hα0 : 0 ≤ α := by linarith
  have hk0 : (0 : ℝ) < k := by linarith
  have hsa1 : 1 ≤ Real.sqrt α := Real.one_le_sqrt.mpr hα1
  have hsa0 : 0 < Real.sqrt α := by linarith
  have hsaa : Real.sqrt α * Real.sqrt α = α := Real.mul_self_sqrt hα0
  have hsa6 : (n : ℝ) ^ ((1 : ℝ) / 6) ≤ Real.sqrt α := by
    have h := Real.sqrt_le_sqrt h13
    rwa [Real.sqrt_eq_rpow, ← Real.rpow_mul hn0.le, show (1 / 3 : ℝ) * (1 / 2) = 1 / 6 by norm_num]
      at h
  have hcLa : cc * L n ≤ Real.sqrt α := (hNl n hNl').trans hsa6
  have hpL0 : 0 ≤ cc * L n * Real.sqrt α / k := by positivity
  have hpL1 : cc * L n * Real.sqrt α / k ≤ 1 := by
    rw [div_le_one hk0]
    calc cc * L n * Real.sqrt α ≤ Real.sqrt α * Real.sqrt α :=
          mul_le_mul_of_nonneg_right hcLa hsa0.le
      _ = α := hsaa
      _ ≤ k := hαk
  have hpR0 : 0 ≤ 1 / Real.sqrt α := by positivity
  have hpR1 : 1 / Real.sqrt α ≤ 1 := by rw [div_le_one hsa0]; exact hsa1
  have hpLR : cc * L n * Real.sqrt α / k * (1 / Real.sqrt α) = cc * L n / k := by
    field_simp
  obtain ⟨h5yes, h5no, -, -⟩ := h5 n hN5 α k h13 h12 hαk hkn
  have heps := rpow_small n hn100
  obtain ⟨M, hM, hMcard⟩ := exists_max_matching G.toGraph
  obtain ⟨hcover, hverts, hno, -⟩ := observation_3_2 n α k h13 h12 hαk hkn G M hM hMcard
  set μ := TuranMatching.Clique.matchingNumber G.toGraph with hμdef
  set Mv := M.verts.toFinset with hMv
  have hMvcard : Mv.card = 2 * μ := by rw [hMv, ← Set.ncard_eq_toFinset_card', hverts]
  constructor
  · -- yes case
    intro hμ
    rw [smallTrial, Kit.prob_par]
    by_cases hV : (k : ℝ) / 8 ≤ (V1 G α k).card
    · have hd := h5yes G hV
      calc _ ≤ Kit.pr ((degTest n α k).dist.prod (smallEdgeTest n α k).dist)
            (fun ω => (degTest n α k).run G ω.1 = false) := by
            refine Kit.pr_mono _ fun ω hω => ?_
            simp only [Bool.or_eq_false_iff] at hω
            exact hω.1
        _ = (degTest n α k).prob G (· = false) :=
            Kit.pr_prod_fst _ _ (fun x => (degTest n α k).run G x = false)
        _ ≤ 1 / 10 := by rw [deg_false_eq]; linarith
    · push Not at hV
      set W := Mv.filter (fun v => v ∈ U G α k ∧ partner M hM v ∈ U G α k) with hW
      have hWMv : ∀ v ∈ W, v ∈ M.verts := fun v hv =>
        Set.mem_toFinset.mp (Finset.mem_filter.mp hv).1
      have hWcard : (k : ℝ) ≤ W.card := by
        have hsub : Mv ⊆ W ∪ (Mv.filter (fun v => v ∈ V1 G α k) ∪
            Mv.filter (fun v => partner M hM v ∈ V1 G α k)) := by
          intro v hv
          by_cases h1 : v ∈ V1 G α k
          · exact Finset.mem_union_right _ (Finset.mem_union_left _
              (Finset.mem_filter.mpr ⟨hv, h1⟩))
          by_cases h2 : partner M hM v ∈ V1 G α k
          · exact Finset.mem_union_right _ (Finset.mem_union_right _
              (Finset.mem_filter.mpr ⟨hv, h2⟩))
          exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hv, by simp [U, h1], by simp [U, h2]⟩)
        have hA : (Mv.filter (fun v => v ∈ V1 G α k)).card ≤ (V1 G α k).card :=
          Finset.card_le_card (fun v hv => (Finset.mem_filter.mp hv).2)
        have hB : (Mv.filter (fun v => partner M hM v ∈ V1 G α k)).card ≤ (V1 G α k).card := by
          refine Finset.card_le_card_of_injOn (partner M hM)
            (fun v hv => (Finset.mem_filter.mp (Finset.mem_coe.mp hv)).2) ?_
          intro x hx y hy hxy
          exact partner_inj M hM
            (Set.mem_toFinset.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).1)
            (Set.mem_toFinset.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).1) hxy
        have h1 := Finset.card_le_card hsub
        have h2 := Finset.card_union_le W (Mv.filter (fun v => v ∈ V1 G α k) ∪
            Mv.filter (fun v => partner M hM v ∈ V1 G α k))
        have h3 := Finset.card_union_le (Mv.filter (fun v => v ∈ V1 G α k))
            (Mv.filter (fun v => partner M hM v ∈ V1 G α k))
        have h4 : Mv.card ≤ W.card + 2 * (V1 G α k).card := by omega
        have h5 : ((Mv.card : ℕ) : ℝ) ≤ W.card + 2 * (V1 G α k).card := by exact_mod_cast h4
        rw [hMvcard] at h5
        have h6 : (k : ℝ) ≤ μ := by exact_mod_cast hμ
        push_cast at h5
        linarith
      -- the pairs
      set e := W.equivFin with he
      let a' : Fin W.card → Fin n := fun i => (e.symm i : Fin n)
      have haW : ∀ i, a' i ∈ W := fun i => (e.symm i).2
      have ha' : Function.Injective a' := fun i j h => e.symm.injective (Subtype.ext h)
      let b' : Fin W.card → Fin n := fun i => partner M hM (a' i)
      have hb' : Function.Injective b' := fun i j h =>
        ha' (partner_inj M hM (hWMv _ (haW i)) (hWMv _ (haW j)) h)
      have hU' : ∀ i, (G.adj (a' i)).length < Delta k α := fun i =>
        (mem_U G α k _).mp (Finset.mem_filter.mp (haW i)).2.1
      have hUb' : ∀ i, (G.adj (b' i)).length < Delta k α := fun i =>
        (mem_U G α k _).mp (Finset.mem_filter.mp (haW i)).2.2
      have hadj' : ∀ i, b' i ∈ G.adj (a' i) := fun i =>
        M.adj_sub (partner_adj M hM (hWMv _ (haW i)))
      have hpair := pair_count_lower_tail (n := n) (cc * L n * Real.sqrt α / k)
        (1 / Real.sqrt α) ⟨hpL0, hpL1⟩ ⟨hpR0, hpR1⟩ a' b' ha' hb'
      rw [← Kit.pr_eq_sum] at hpair
      have hm1 : cc * L n ≤ (W.card : ℝ) * (cc * L n * Real.sqrt α / k) * (1 / Real.sqrt α) := by
        rw [mul_assoc, hpLR, mul_div_assoc', le_div_iff₀ hk0]
        nlinarith
      have hm2 : (W.card : ℝ) * (cc * L n * Real.sqrt α / k) * (1 / Real.sqrt α) ≤
          W.card * (1 / Real.sqrt α) := by
        apply mul_le_mul_of_nonneg_right _ hpR0
        exact mul_le_of_le_one_right (Nat.cast_nonneg _) hpL1
      have hcL20 : 20 * 14 ≤ cc * L n := by rw [hcc]; nlinarith
      have hE1 := exp_small ((W.card : ℝ) * (1 / Real.sqrt α)) 7 (by norm_num) (by linarith)
      have hE2 := exp_small ((W.card : ℝ) * (cc * L n * Real.sqrt α / k) * (1 / Real.sqrt α)) 14
        (by norm_num) (by linarith)
      calc _ ≤ Kit.pr ((degTest n α k).dist.prod (smallEdgeTest n α k).dist)
            (fun ω => (smallEdgeTest n α k).run G ω.2 = false) := by
            refine Kit.pr_mono _ fun ω hω => ?_
            simp only [Bool.or_eq_false_iff] at hω
            exact hω.2
        _ = Kit.pr (smallEdgeTest n α k).dist (fun x => (smallEdgeTest n α k).run G x = false) :=
            Kit.pr_prod_snd _ _ (fun x => (smallEdgeTest n α k).run G x = false)
        _ ≤ Kit.pr ((bernDist (n := n) (cc * L n * Real.sqrt α / k)).prod
              (bernDist (n := n) (1 / Real.sqrt α)))
            (fun ω => ((Finset.univ.filter fun i => ω.1 (a' i) = true ∧ ω.2 (b' i) = true).card : ℝ)
              ≤ W.card * (cc * L n * Real.sqrt α / k) * (1 / Real.sqrt α) / 4) := by
            refine Kit.pr_mono _ fun x hx => ?_
            have := sedge_false α k G a' b' ha' hU' hUb' hadj' x hx
            linarith
        _ ≤ _ := hpair
        _ ≤ 1 / 20 + 1 / 20 := add_le_add hE1 hE2
        _ ≤ 1 / 10 := by norm_num
  · -- no case
    intro hμ
    obtain ⟨-, hV1card, hk100⟩ := hno hμ
    rw [smallTrial]
    refine (Kit.prob_par_le _ _ _ G (· = true) (· = true) (· = true) ?_).trans ?_
    · intro x y h
      simpa using h
    have hd : (degTest n α k).prob G (· = true) ≤ (n : ℝ) ^ (-30 : ℝ) := by
      have := h5no G (by linarith)
      have h2 := deg_false_eq α k G
      linarith
    have hP := Pset_card G α k Mv (fun u v h => by
      rcases hcover u v h with h' | h'
      · exact Or.inl (Set.mem_toFinset.mpr h')
      · exact Or.inr (Set.mem_toFinset.mpr h'))
    have hΔ : ((Delta k α : ℕ) : ℝ) ≤ 2 * k / α := Nat.floor_le (by positivity)
    have hC0 : (0 : ℝ) < C0 := by unfold C0; norm_num
    have hMvR : (Mv.card : ℝ) ≤ 2 * k / (C0 * α) := by
      rw [hMvcard]; push_cast
      have : (μ : ℝ) * 2 ≤ k / (C0 * α) * 2 := by linarith
      calc (2 : ℝ) * μ ≤ k / (C0 * α) * 2 := by linarith
        _ = 2 * k / (C0 * α) := by ring
    have hPR : ((Pset G α k).card : ℝ) ≤ 2 * ((2 * k / (C0 * α)) * (2 * k / α)) := by
      have : ((Pset G α k).card : ℝ) ≤ 2 * ((Mv.card : ℝ) * (Delta k α : ℕ)) := by
        exact_mod_cast hP
      refine this.trans ?_
      gcongr
    have he : (smallEdgeTest n α k).prob G (· = true) ≤ 32 / C0 := by
      rw [Kit.prob_eq_pr]
      change Kit.pr ((bernDist (n := n) (cc * L n * Real.sqrt α / k)).prod
        (bernDist (n := n) (1 / Real.sqrt α)))
        (fun ω : (Fin n → Bool) × (Fin n → Bool) => (smallEdgeTest n α k).run G ω = true) ≤ _
      have hc4 : 0 < cc * L n / 4 := by positivity
      have hex : Kit.ex ((bernDist (n := n) (cc * L n * Real.sqrt α / k)).prod
          (bernDist (n := n) (1 / Real.sqrt α)))
          (fun x : (Fin n → Bool) × (Fin n → Bool) =>
            (((Pset G α k).filter (fun p => x.1 p.1 = true ∧ x.2 p.2 = true)).card : ℝ)) ≤
          ((Pset G α k).card : ℝ) * (cc * L n / k) := by
        rw [ex_count]
        have : ∀ p ∈ Pset G α k, Kit.pr ((bernDist (n := n) (cc * L n * Real.sqrt α / k)).prod
          (bernDist (n := n) (1 / Real.sqrt α)))
            (fun x : (Fin n → Bool) × (Fin n → Bool) => x.1 p.1 = true ∧ x.2 p.2 = true) ≤
            cc * L n / k := by
          intro p _
          have h1 := pr_prod_and (bernDist (n := n) (cc * L n * Real.sqrt α / k))
            (bernDist (n := n) (1 / Real.sqrt α)) (fun s => s p.1 = true) (fun s => s p.2 = true)
          rw [pr_bern, pr_bern] at h1
          refine (le_of_eq h1).trans ?_
          rw [← hpLR]
          exact mul_le_mul (clamp_le _ hpL0) (clamp_le _ hpR0) (le_max_left _ _) hpL0
        calc _ ≤ ∑ _p ∈ Pset G α k, cc * L n / k := Finset.sum_le_sum this
          _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
      calc _ ≤ Kit.pr ((bernDist (n := n) (cc * L n * Real.sqrt α / k)).prod
          (bernDist (n := n) (1 / Real.sqrt α)))
            (fun x : (Fin n → Bool) × (Fin n → Bool) => cc * L n / 4 ≤
              (((Pset G α k).filter (fun p => x.1 p.1 = true ∧ x.2 p.2 = true)).card : ℝ)) :=
            Kit.pr_mono _ fun x hx => sedge_true α k G x hx
        _ ≤ _ := Kit.markov _ _ (fun _ => Nat.cast_nonneg _) hc4
        _ ≤ ((Pset G α k).card : ℝ) * (cc * L n / k) / (cc * L n / 4) :=
            div_le_div_of_nonneg_right hex hc4.le
        _ ≤ 32 / C0 := arith_no _ _ _ _ _ hPR hC0 hk0 (by linarith) hsmall hcL
    have hC : (32 : ℝ) / C0 ≤ 1 / 10000 := by unfold C0; norm_num
    exact le_trans (add_le_add hd he) (by linarith only [hC, heps])
