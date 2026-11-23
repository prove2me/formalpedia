-- Prove2me | solution 1 for NAMatchEst.lemma_3_14
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T00:55:37.703025+00:00
-- url     : https://prove2.me/submissions/ecec5e89-a5b8-4e7b-be33-710710323576

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
import Definitions.Def_NAMatchEst_L
import Definitions.Def_NAMatchEst_truncTrial


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



namespace NAMatchEst.AuxE14
open NAMatchEst

lemma len_row {n : ℕ} (v : Fin n) (D : ℕ) : (rowQueries v D).length = D + 1 := by
  simp [rowQueries]

lemma len_pilot (n : ℕ) [NeZero n] (α : ℝ) (k : ℕ) (ω : (pilot n α k).Ω) :
    ((pilot n α k).queries ω).length = ⌈n * L n / α ^ 2⌉₊ * (Delta k α + 1) := by
  simp [pilot, List.length_flatten, len_row, List.sum_ofFn]

lemma len_deg (n : ℕ) [NeZero n] (α : ℝ) (k : ℕ) (ω : (degTest n α k).Ω) :
    ((degTest n α k).queries ω).length = ⌈cc * n * L n / k⌉₊ := by
  simp [degTest]

lemma len_res (n : ℕ) [NeZero n] (α : ℝ) (k : ℕ) (ω : (resTest n α k).Ω) :
    ((resTest n α k).queries ω).length = ⌈cc * n * L n / α ^ 2⌉₊ * (Delta k α + 1) := by
  simp [resTest, List.length_flatten, len_row, List.sum_ofFn]

lemma len_edge (n : ℕ) (α : ℝ) (k : ℕ) (ω : (edgeTest n α k).Ω) :
    (((edgeTest n α k).queries ω).length : ℝ) =
      ((Finset.univ.filter fun v => ω.1 v = true).card : ℝ) * (Delta k α + 1) +
      ((Finset.univ.filter fun v => ω.2.1 v = true).card : ℝ) *
        (1 + ⌈cc * Delta k α * L n / α⌉₊) := by
  simp only [edgeTest, List.length_flatMap, List.length_append]
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  push_cast
  rw [Finset.sum_add_distrib, Finset.card_filter, Finset.card_filter]
  push_cast
  rw [Finset.sum_mul, Finset.sum_mul]
  congr 1 <;> refine Finset.sum_congr rfl fun v _ => ?_ <;> split_ifs <;> simp [len_row]; ring

lemma len_sedge (n : ℕ) (α : ℝ) (k : ℕ) (ω : (smallEdgeTest n α k).Ω) :
    (((smallEdgeTest n α k).queries ω).length : ℝ) =
      ((Finset.univ.filter fun v => ω.1 v = true).card : ℝ) * (Delta k α + 1) +
      ((Finset.univ.filter fun v => ω.2 v = true).card : ℝ) := by
  simp only [smallEdgeTest, List.length_flatMap, List.length_append]
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  push_cast
  rw [Finset.sum_add_distrib, Finset.card_filter, Finset.card_filter]
  push_cast
  rw [Finset.sum_mul]
  congr 1 <;> refine Finset.sum_congr rfl fun v _ => ?_ <;> split_ifs <;> simp [len_row]


lemma large_real (n L a s Δ s0 sD sM SL SR r : ℝ) (ha : 1 ≤ a) (hL : 1 ≤ L) (hs : 0 ≤ s)
    (has : a ^ 4 < s ^ 2) (hsn : s ^ 2 ≤ n) (han : a ^ 4 ≤ n) (hna : n ≤ a ^ 6)
    (hLs : L * s ≤ 3 * n) (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ 2 * s ^ 2 / a ^ 2)
    (hs0 : s0 ≤ n * L / a ^ 4 + 1) (hsD : sD ≤ cc * n * L / s ^ 2 + 1)
    (hsM : sM ≤ cc * n * L / a ^ 4 + 1)
    (hSL : SL ≤ 2 * n * (cc * L / (s * a)) + 100 * L + 1)
    (hSR : SR ≤ 2 * n * (a / s) + 100 * L + 1)
    (hr0 : 0 ≤ r) (hr : r ≤ cc * Δ * L / a ^ 2 + 1) :
    s0 * (Δ + 1) + (sD + (sM * (Δ + 1) + (SL * (Δ + 1) + SR * (1 + r)))) ≤
      10 ^ 8 * L * (n * s / a ^ 3) := by
  have hcc : cc = 10 ^ 5 := rfl
  have hc0 : 0 < cc := by rw [hcc]; norm_num
  have ha0 : 0 < a := by linarith
  have hL0 : 0 < L := by linarith
  have ha2 : 1 ≤ a ^ 2 := one_le_pow₀ ha
  have ha3 : 1 ≤ a ^ 3 := one_le_pow₀ ha
  have ha4 : 1 ≤ a ^ 4 := one_le_pow₀ ha
  have ha2s : a ^ 2 < s := by
    have : (a ^ 2) ^ 2 < s ^ 2 := by rw [← pow_mul]; exact has
    exact lt_of_pow_lt_pow_left₀ 2 hs this
  have hs1 : 1 ≤ s := by linarith
  have hs0' : 0 < s := by linarith
  have has' : a ≤ s := by nlinarith only [ha2s, ha]
  have hsa3 : s ≤ a ^ 3 := by
    have : s ^ 2 ≤ (a ^ 3) ^ 2 := by
      calc s ^ 2 ≤ n := hsn
        _ ≤ a ^ 6 := hna
        _ = (a ^ 3) ^ 2 := by ring
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) this
  have ha24 : a ^ 2 ≤ a ^ 4 := pow_le_pow_right₀ ha (by norm_num)
  have ha34 : a ^ 3 ≤ a ^ 4 := pow_le_pow_right₀ ha (by norm_num)
  have haa2 : a ≤ a ^ 2 := by nlinarith only [ha]
  have ha2n : a ^ 2 ≤ n := by linarith
  have hn0 : 0 < n := by linarith
  have hsan : s * a ≤ n := by
    have h1 : (s * a) ^ 2 ≤ n ^ 2 := by
      rw [mul_pow]; nlinarith only [hsn, ha2n, ha2, sq_nonneg s]
    exact le_of_pow_le_pow_left₀ (by norm_num) hn0.le h1
  have ha3n : a ^ 3 ≤ n := by nlinarith only [ha3, ha, hna, han, ha4]
  obtain ⟨B, hB'⟩ : ∃ B, B = L * n * s / a ^ 3 := ⟨_, rfl⟩
  have hBpos : 0 ≤ B := by rw [hB']; positivity
  -- basic facts
  have P1 : n * L / a ^ 4 ≤ B := by
    rw [hB', div_le_div_iff₀ (by positivity) (by positivity)]
    have : a ^ 3 ≤ a ^ 4 * s := ha34.trans (le_mul_of_one_le_right (by positivity) hs1)
    have h := mul_le_mul_of_nonneg_left this (mul_pos hn0 hL0).le
    linarith
  have P4 : 1 ≤ B := by
    rw [hB', le_div_iff₀ (by positivity)]
    have h1 : n ≤ n * s := le_mul_of_one_le_right hn0.le hs1
    have h2 : n * s ≤ L * (n * s) := le_mul_of_one_le_left (by positivity) hL
    linarith [show L * (n * s) = L * n * s by ring]
  have PΔ : 2 * s ^ 2 / a ^ 2 ≤ 2 * B := by
    rw [hB', mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : s * a ≤ L * n := by nlinarith only [hsan, hL, hn0]
    have h := mul_le_mul_of_nonneg_right h1 (by positivity : (0:ℝ) ≤ s * a ^ 2)
    linarith
  have P3 : n * L / a ^ 4 * (2 * s ^ 2 / a ^ 2) ≤ 2 * B := by
    rw [hB', div_mul_div_comm, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have : n * L * (2 * s ^ 2) * a ^ 3 = (2 * n * L * s) * (s * a ^ 3) := by ring
    have h2 : 2 * (L * n * s) * (a ^ 4 * a ^ 2) = (2 * n * L * s) * (a ^ 3 * a ^ 3) := by ring
    rw [this, h2]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_right hsa3 (by positivity)
  have P5 : cc * n * L / s ^ 2 ≤ cc * B := by
    rw [hB', mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : a ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ ha0.le has' 3
    have : cc * n * L * a ^ 3 = (cc * n * L) * a ^ 3 := by ring
    have h2 : cc * (L * n * s) * s ^ 2 = (cc * n * L) * s ^ 3 := by ring
    rw [this, h2]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  have PL : L ≤ B := by
    rw [hB', le_div_iff₀ (by positivity)]
    have : L * a ^ 3 ≤ L * (n * s) := mul_le_mul_of_nonneg_left
      (by nlinarith only [ha3n, hs1, hn0]) hL0.le
    linarith
  -- pilot and res
  have hpil : s0 * (Δ + 1) ≤ 6 * B := by
    have h1 : s0 * (Δ + 1) ≤ (n * L / a ^ 4 + 1) * (Δ + 1) :=
      mul_le_mul_of_nonneg_right hs0 (by linarith)
    have h2 : n * L / a ^ 4 * Δ ≤ n * L / a ^ 4 * (2 * s ^ 2 / a ^ 2) :=
      mul_le_mul_of_nonneg_left hΔ (by positivity)
    linarith
  have hres : sM * (Δ + 1) ≤ 6 * cc * B := by
    have h1 : sM * (Δ + 1) ≤ (cc * (n * L / a ^ 4) + 1) * (Δ + 1) := by
      rw [show cc * (n * L / a ^ 4) = cc * n * L / a ^ 4 by ring]
      exact mul_le_mul_of_nonneg_right hsM (by linarith)
    have h2 : n * L / a ^ 4 * Δ ≤ n * L / a ^ 4 * (2 * s ^ 2 / a ^ 2) :=
      mul_le_mul_of_nonneg_left hΔ (by positivity)
    have hc1 : 1 ≤ cc := by rw [hcc]; norm_num
    have e : (cc * (n * L / a ^ 4) + 1) * (Δ + 1) =
      cc * (n * L / a ^ 4 * Δ) + cc * (n * L / a ^ 4) + Δ + 1 := by ring
    rw [e] at h1
    have h3 := mul_le_mul_of_nonneg_left (h2.trans P3) hc0.le
    have h4 := mul_le_mul_of_nonneg_left P1 hc0.le
    have h5 := mul_le_mul_of_nonneg_right hc1 hBpos
    nlinarith only [h1, h3, h4, h5, PΔ, P4, hΔ]
  have hdeg : sD ≤ (cc + 1) * B := by linarith
  -- left sample
  have hSLb : SL * (Δ + 1) ≤ (6 * cc + 303) * B := by
    obtain ⟨x, hx⟩ : ∃ x, x = 2 * n * (cc * L / (s * a)) := ⟨_, rfl⟩
    rw [← hx] at hSL
    have hx0 : 0 ≤ x := by rw [hx]; positivity
    have Px : x ≤ 2 * cc * B := by
      rw [hx, hB', mul_div_assoc', mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      have : 2 * n * (cc * L) * a ^ 3 = (2 * cc * n * L) * a ^ 3 := by ring
      have h2 : 2 * cc * (L * n * s) * (s * a) = (2 * cc * n * L) * (s ^ 2 * a) := by ring
      rw [this, h2]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : a ^ 2 ≤ s ^ 2 := by nlinarith only [ha2s, ha2]
      have h := mul_le_mul_of_nonneg_right this ha0.le
      linarith
    have PxΔ : x * (2 * s ^ 2 / a ^ 2) ≤ 4 * cc * B := by
      rw [hx, hB']
      apply le_of_eq
      field_simp; ring
    have PLΔ : L * (2 * s ^ 2 / a ^ 2) ≤ 2 * B := by
      rw [hB', mul_div_assoc', mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      have : L * (2 * s ^ 2) * a ^ 3 = (2 * L * s * a ^ 2) * (s * a) := by ring
      have h2 : 2 * (L * n * s) * a ^ 2 = (2 * L * s * a ^ 2) * n := by ring
      rw [this, h2]
      exact mul_le_mul_of_nonneg_left hsan (by positivity)
    have e1 : SL * (Δ + 1) ≤ (x + 100 * L + 1) * (Δ + 1) :=
      mul_le_mul_of_nonneg_right hSL (by linarith)
    have e2 : (x + 100 * L + 1) * Δ ≤ (x + 100 * L + 1) * (2 * s ^ 2 / a ^ 2) :=
      mul_le_mul_of_nonneg_left hΔ (by positivity)
    have e3 : (x + 100 * L + 1) * (2 * s ^ 2 / a ^ 2) =
      x * (2 * s ^ 2 / a ^ 2) + 100 * (L * (2 * s ^ 2 / a ^ 2)) + 2 * s ^ 2 / a ^ 2 := by ring
    have e4 : (x + 100 * L + 1) * (Δ + 1) = (x + 100 * L + 1) * Δ + (x + 100 * L + 1) := by ring
    linarith
  -- right sample
  have hSRb : SR * (1 + r) ≤ (4 * cc + 202 * 3 * cc + 2 + 202 + 101 + 4) * B := by
    obtain ⟨y, hy⟩ : ∃ y, y = 2 * n * (a / s) := ⟨_, rfl⟩
    rw [← hy] at hSR
    have hy0 : 0 ≤ y := by rw [hy]; positivity
    obtain ⟨r', hr'⟩ : ∃ r', r' = 2 * cc * s ^ 2 * L / a ^ 4 := ⟨_, rfl⟩
    have hr'0 : 0 ≤ r' := by rw [hr']; positivity
    have hrr : r ≤ r' + 1 := by
      have : cc * Δ * L / a ^ 2 ≤ r' := by
        rw [hr']
        calc cc * Δ * L / a ^ 2 ≤ cc * (2 * s ^ 2 / a ^ 2) * L / a ^ 2 := by
              apply div_le_div_of_nonneg_right _ (by positivity)
              apply mul_le_mul_of_nonneg_right _ hL0.le
              exact mul_le_mul_of_nonneg_left hΔ hc0.le
          _ = 2 * cc * s ^ 2 * L / a ^ 4 := by field_simp
      linarith
    have Pyr : y * r' ≤ 4 * cc * B := by
      rw [hy, hr', hB']
      apply le_of_eq
      field_simp; ring
    have Py : y ≤ 2 * B := by
      rw [hy, hB', mul_div_assoc', mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      have : 2 * n * a * a ^ 3 = (2 * n) * a ^ 4 := by ring
      have h2 : 2 * (L * n * s) * s = (2 * n) * (L * s ^ 2) := by ring
      rw [this, h2]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith only [has, hL, sq_nonneg s]
    have PLr : L * r' ≤ 2 * 3 * cc * B := by
      rw [hr', hB', mul_div_assoc', mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      have : L * (2 * cc * s ^ 2 * L) * a ^ 3 = (2 * cc * s * L * a ^ 2) * ((L * s) * a) := by ring
      have h2 : 2 * 3 * cc * (L * n * s) * a ^ 4 =
        (2 * cc * s * L * a ^ 2) * (3 * n * a ^ 2) := by ring
      rw [this, h2]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have h3 : L * s * a ≤ 3 * n * a := mul_le_mul_of_nonneg_right hLs ha0.le
      have h4 : 3 * n * a ≤ 3 * n * a ^ 2 := mul_le_mul_of_nonneg_left haa2 (by positivity)
      linarith
    have e1 : SR * (1 + r) ≤ (y + 100 * L + 1) * (1 + r) :=
      mul_le_mul_of_nonneg_right hSR (by linarith)
    have e2 : (y + 100 * L + 1) * (1 + r) ≤ (y + 100 * L + 1) * (2 + r') :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e3 : (y + 100 * L + 1) * (2 + r') = 2 * y + y * r' + 200 * L + 100 * (L * r') + 2 + r' := by
      ring
    have hr'B : r' ≤ 2 * 3 * cc * B := by nlinarith only [PLr, hL, hr'0]
    nlinarith only [e1, e2, e3, hr'B, PLr, Pyr, Py, PL, P4, hc0]
  have : s0 * (Δ + 1) + (sD + (sM * (Δ + 1) + (SL * (Δ + 1) + SR * (1 + r)))) ≤
      (6 + (cc + 1) + 6 * cc + (6 * cc + 303) + (4 * cc + 202 * 3 * cc + 2 + 202 + 101 + 4)) * B := by
    linarith
  calc _ ≤ _ := this
    _ ≤ 10 ^ 8 * B := by apply mul_le_mul_of_nonneg_right _ hBpos; rw [hcc]; norm_num
    _ = _ := by rw [hB']; ring


lemma small_real (n L a s Δ sD SL SR : ℝ) (ha : 1 ≤ a) (hL : 1 ≤ L) (hs : 0 ≤ s)
    (has : a ^ 2 ≤ s ^ 2) (hsn : s ^ 2 ≤ n) (han : a ^ 4 ≤ n)
    (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ 2 * s ^ 2 / a ^ 2)
    (hsD : sD ≤ cc * n * L / s ^ 2 + 1)
    (hSL : SL ≤ 2 * n * (cc * L * a / s ^ 2) + 100 * L + 1)
    (hSR : SR ≤ 2 * n * (1 / a) + 100 * L + 1) :
    sD + (SL * (Δ + 1) + SR) ≤ 10 ^ 8 * L * (n / a) := by
  have hcc : cc = 10 ^ 5 := rfl
  have hc0 : 0 < cc := by rw [hcc]; norm_num
  have ha0 : 0 < a := by linarith
  have hL0 : 0 < L := by linarith
  have ha2 : 1 ≤ a ^ 2 := one_le_pow₀ ha
  have ha24 : a ^ 2 ≤ a ^ 4 := pow_le_pow_right₀ ha (by norm_num)
  have haa2 : a ≤ a ^ 2 := by nlinarith only [ha]
  have hs2 : 0 < s ^ 2 := by linarith
  have hsne : s ≠ 0 := by rintro rfl; simp at hs2
  have han' : a ≤ n := by linarith
  have hn0 : 0 < n := by linarith
  obtain ⟨B, hB'⟩ : ∃ B, B = L * n / a := ⟨_, rfl⟩
  have hBpos : 0 ≤ B := by rw [hB']; positivity
  have P4 : 1 ≤ B := by
    rw [hB', le_div_iff₀ ha0]
    have : n ≤ L * n := le_mul_of_one_le_left hn0.le hL
    linarith
  have PL : L ≤ B := by
    rw [hB', le_div_iff₀ ha0]
    have : L * a ≤ L * n := mul_le_mul_of_nonneg_left han' hL0.le
    linarith
  have P5 : cc * n * L / s ^ 2 ≤ cc * B := by
    rw [hB', mul_div_assoc', div_le_div_iff₀ hs2 ha0]
    have : cc * n * L * a = (cc * n * L) * a := by ring
    have h2 : cc * (L * n) * s ^ 2 = (cc * n * L) * s ^ 2 := by ring
    rw [this, h2]
    exact mul_le_mul_of_nonneg_left (haa2.trans has) (by positivity)
  have Px : 2 * n * (cc * L * a / s ^ 2) ≤ 2 * cc * B := by
    rw [hB', mul_div_assoc', mul_div_assoc', div_le_div_iff₀ hs2 ha0]
    have : 2 * n * (cc * L * a) * a = (2 * cc * n * L) * a ^ 2 := by ring
    have h2 : 2 * cc * (L * n) * s ^ 2 = (2 * cc * n * L) * s ^ 2 := by ring
    rw [this, h2]
    exact mul_le_mul_of_nonneg_left has (by positivity)
  have PxΔ : 2 * n * (cc * L * a / s ^ 2) * (2 * s ^ 2 / a ^ 2) ≤ 4 * cc * B := by
    rw [hB']
    apply le_of_eq
    field_simp; ring
  have PLΔ : L * (2 * s ^ 2 / a ^ 2) ≤ 2 * B := by
    rw [hB', mul_div_assoc', mul_div_assoc', div_le_div_iff₀ (by positivity) ha0]
    have : L * (2 * s ^ 2) * a = (2 * L * a) * s ^ 2 := by ring
    have h2 : 2 * (L * n) * a ^ 2 = (2 * L * a) * (n * a) := by ring
    rw [this, h2]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : n ≤ n * a := le_mul_of_one_le_right hn0.le ha
    linarith
  have Py : 2 * n * (1 / a) ≤ 2 * B := by
    rw [hB', mul_one_div, mul_div_assoc', div_le_div_iff₀ ha0 ha0]
    have : 2 * n * a ≤ 2 * (L * n) * a := by
      have : n ≤ L * n := le_mul_of_one_le_left hn0.le hL
      nlinarith only [this, ha0]
    linarith
  have hΔB : 2 * s ^ 2 / a ^ 2 ≤ 2 * B := by
    have := PLΔ
    have h2 : 2 * s ^ 2 / a ^ 2 ≤ L * (2 * s ^ 2 / a ^ 2) :=
      le_mul_of_one_le_left (by positivity) hL
    linarith
  obtain ⟨x, hx⟩ : ∃ x, x = 2 * n * (cc * L * a / s ^ 2) := ⟨_, rfl⟩
  rw [← hx] at hSL Px PxΔ
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have e1 : SL * (Δ + 1) ≤ (x + 100 * L + 1) * (Δ + 1) := by
    have : 0 ≤ Δ + 1 := by linarith
    by_cases h : 0 ≤ SL
    · exact mul_le_mul_of_nonneg_right hSL this
    · nlinarith
  have e2 : (x + 100 * L + 1) * Δ ≤ (x + 100 * L + 1) * (2 * s ^ 2 / a ^ 2) :=
    mul_le_mul_of_nonneg_left hΔ (by positivity)
  have e3 : (x + 100 * L + 1) * (2 * s ^ 2 / a ^ 2) =
    x * (2 * s ^ 2 / a ^ 2) + 100 * (L * (2 * s ^ 2 / a ^ 2)) + 2 * s ^ 2 / a ^ 2 := by ring
  have e4 : (x + 100 * L + 1) * (Δ + 1) = (x + 100 * L + 1) * Δ + (x + 100 * L + 1) := by ring
  have : sD + (SL * (Δ + 1) + SR) ≤ (cc + 1 + (4 * cc + 200 + 2 + 2 * cc + 101) + 103) * B := by
    linarith
  calc _ ≤ _ := this
    _ ≤ 10 ^ 8 * B := by apply mul_le_mul_of_nonneg_right _ hBpos; rw [hcc]; norm_num
    _ = _ := by rw [hB']; ring

lemma L_ge_one (n : ℕ) (hn : 2 ≤ n) : 1 ≤ L n := by
  unfold L
  rw [Real.le_log_iff_exp_le (by positivity)]
  have h1 := Real.exp_one_lt_d9
  have h2 : (4 : ℝ) ≤ 2 * n := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  linarith

lemma L_le (n : ℕ) (hn : 1 ≤ n) : L n ≤ 3 * Real.sqrt n := by
  unfold L
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : Real.log (2 * n) = 2 * Real.log (Real.sqrt (2 * n)) := by
    rw [Real.log_sqrt (by positivity)]; ring
  have h3 : Real.log (Real.sqrt (2 * n)) ≤ Real.sqrt (2 * n) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h4 : Real.sqrt (2 * n) = Real.sqrt 2 * Real.sqrt n := Real.sqrt_mul (by norm_num) _
  have h5 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h6 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  nlinarith

end NAMatchEst.AuxE14

open NAMatchEst NAMatchEst.AuxE14 in
theorem solution : ∃ D : ℝ, ∃ N₀ : ℕ, ∀ (n : ℕ) [NeZero n], N₀ ≤ n → ∀ (α : ℝ) (k : ℕ),
    (n : ℝ) ^ ((1 : ℝ) / 3) ≤ α → α ≤ (n : ℝ) ^ ((1 : ℝ) / 2) → α ≤ k → (k : ℝ) ≤ n →
    (truncTrial n α k).CostLE (D * L n *
      (if (k : ℝ) ≤ α ^ 2 then n / Real.sqrt α else n * Real.sqrt k / α ^ ((3 : ℝ) / 2))) := by
  refine ⟨10 ^ 8, 2, ?_⟩
  intro n _ hn α k h13 h12 hαk hkn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : (0 : ℝ) < n := by linarith
  have hL1 : 1 ≤ L n := L_ge_one n hn
  have hL0 : 0 ≤ L n := by linarith
  have hα1 : 1 ≤ α := le_trans (Real.one_le_rpow hn1 (by norm_num)) h13
  have hα0 : 0 ≤ α := by linarith
  -- α² ≤ n ≤ α³
  have hα2n : α ^ 2 ≤ n := by
    have : α ^ 2 ≤ ((n : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 := pow_le_pow_left₀ hα0 h12 2
    have e : ((n : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = n := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; norm_num
    rwa [e] at this
  have hnα3 : (n : ℝ) ≤ α ^ 3 := by
    have : ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 ≤ α ^ 3 :=
      pow_le_pow_left₀ (by positivity) h13 3
    have e : ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = n := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; norm_num
    rwa [e] at this
  set a := Real.sqrt α with ha_def
  set s := Real.sqrt (k : ℝ) with hs_def
  have hαa : α = a ^ 2 := (Real.sq_sqrt hα0).symm
  have hks : (k : ℝ) = s ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg k)).symm
  have ha1 : 1 ≤ a := Real.one_le_sqrt.mpr hα1
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hLs : L n * s ≤ 3 * n := by
    have h1 := L_le n (by omega)
    have h2 : s ≤ Real.sqrt n := Real.sqrt_le_sqrt hkn
    have h3 : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
    have h4 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
    calc L n * s ≤ (3 * Real.sqrt n) * Real.sqrt n := mul_le_mul h1 h2 hs0 (by positivity)
      _ = 3 * n := by rw [mul_assoc, h3]
  have hΔ : ((Delta k α : ℕ) : ℝ) ≤ 2 * s ^ 2 / a ^ 2 := by
    rw [← hks, ← hαa]; exact Nat.floor_le (by positivity)
  have hΔ0 : (0 : ℝ) ≤ (Delta k α : ℕ) := Nat.cast_nonneg _
  have han : a ^ 4 ≤ n := by
    rw [show a ^ 4 = (a ^ 2) ^ 2 by ring, ← hαa]; exact hα2n
  have hna : (n : ℝ) ≤ a ^ 6 := by
    rw [show a ^ 6 = (a ^ 2) ^ 3 by ring, ← hαa]; exact hnα3
  have hceil : ∀ x : ℝ, 0 ≤ x → ((⌈x⌉₊ : ℕ) : ℝ) ≤ x + 1 := fun x hx =>
    (Nat.ceil_lt_add_one hx).le
  have hsD : ((⌈cc * n * L n / k⌉₊ : ℕ) : ℝ) ≤ cc * n * L n / s ^ 2 + 1 := by
    rw [← hks]; exact hceil _ (by unfold cc; positivity)
  by_cases hsm : (k : ℝ) ≤ α ^ 2
  · -- small case
    rw [if_pos hsm]
    have hlarge : ¬ α ^ 2 < k := not_lt.mpr hsm
    intro ω
    revert ω
    rw [truncTrial, if_neg hlarge]
    intro ω
    simp only [RandAlg.guard]
    split_ifs with hok
    · obtain ⟨h1, h2⟩ := hok
      simp only [smallTrial, RandAlg.par, List.length_append]
      push_cast
      rw [len_deg, len_sedge]
      have hSL : ((Finset.univ.filter fun v => ω.2.1 v = true).card : ℝ) ≤
          2 * n * (cc * L n * a / s ^ 2) + 100 * L n + 1 := by
        refine h1.trans ?_
        rw [← hks]; exact hceil _ (by unfold cc; positivity)
      have hSR : ((Finset.univ.filter fun v => ω.2.2 v = true).card : ℝ) ≤
          2 * n * (1 / a) + 100 * L n + 1 := h2.trans (hceil _ (by positivity))
      have := small_real n (L n) a s _ _ _ _ ha1 hL1 hs0
        (by rw [← hks, ← hαa]; exact hαk) (by rw [← hks]; exact hkn) han hΔ0 hΔ hsD hSL hSR
      linarith
    · simp only [List.length_nil, Nat.cast_zero]
      have : 0 < a := by linarith
      positivity
  · -- large case
    rw [if_neg hsm]
    have hlarge : α ^ 2 < k := lt_of_not_ge hsm
    have hpow : α ^ ((3 : ℝ) / 2) = a ^ 3 := by
      rw [ha_def, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hα0]; norm_num
    rw [hpow]
    intro ω
    revert ω
    rw [truncTrial, if_pos hlarge]
    intro ω
    simp only [RandAlg.guard]
    split_ifs with hok
    · obtain ⟨h1, h2⟩ := hok
      simp only [largeTrial, RandAlg.par, List.length_append]
      push_cast
      rw [len_pilot, len_deg, len_res, len_edge]
      push_cast
      have hsa : Real.sqrt (k * α) = s * a := Real.sqrt_mul (Nat.cast_nonneg k) α
      have hsa' : Real.sqrt (α / k) = a / s := Real.sqrt_div' α (Nat.cast_nonneg k)
      have hSL : ((Finset.univ.filter fun v => ω.2.2.2.1 v = true).card : ℝ) ≤
          2 * n * (cc * L n / (s * a)) + 100 * L n + 1 := by
        refine h1.trans ?_
        rw [← hsa]; exact hceil _ (by unfold cc; positivity)
      have hSR : ((Finset.univ.filter fun v => ω.2.2.2.2.1 v = true).card : ℝ) ≤
          2 * n * (a / s) + 100 * L n + 1 := by
        refine h2.trans ?_
        rw [← hsa']; exact hceil _ (by positivity)
      have hs0' : ((⌈n * L n / α ^ 2⌉₊ : ℕ) : ℝ) ≤ n * L n / a ^ 4 + 1 := by
        rw [show a ^ 4 = (a ^ 2) ^ 2 by ring, ← hαa]; exact hceil _ (by positivity)
      have hsM : ((⌈cc * n * L n / α ^ 2⌉₊ : ℕ) : ℝ) ≤ cc * n * L n / a ^ 4 + 1 := by
        rw [show a ^ 4 = (a ^ 2) ^ 2 by ring, ← hαa]; exact hceil _ (by unfold cc; positivity)
      have hr : ((⌈cc * (Delta k α : ℕ) * L n / α⌉₊ : ℕ) : ℝ) ≤
          cc * (Delta k α : ℕ) * L n / a ^ 2 + 1 := by
        rw [← hαa]; exact hceil _ (by unfold cc; positivity)
      have := large_real n (L n) a s _ _ _ _ _ _ _ ha1 hL1 hs0
        (by rw [show a ^ 4 = (a ^ 2) ^ 2 by ring, ← hαa, ← hks]; exact hlarge)
        (by rw [← hks]; exact hkn) han hna hLs hΔ0 hΔ hs0' hsD
        hsM hSL hSR
        (Nat.cast_nonneg _) hr
      linarith
    · simp only [List.length_nil, Nat.cast_zero]
      have : 0 < a := by linarith
      positivity
