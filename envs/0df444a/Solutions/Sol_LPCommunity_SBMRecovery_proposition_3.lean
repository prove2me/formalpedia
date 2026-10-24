-- Prove2me | solution 1 for LPCommunity.SBMRecovery.proposition_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T10:50:04.181881+00:00
-- url     : https://prove2.me/submissions/1a205da1-5f1c-4552-a3e0-791882807c14
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_LPCommunity_MinBisect_Setting
import Definitions.Def_LPCommunity_SBMRecovery_Factors
import Theorems.Thm_LPCommunity_SBMRecovery_proposition_5

open Finset Filter Topology
open scoped Classical

namespace LP5Deg

open LPCommunity.SBMRecovery

/-- graphs on `Fin n` are the same as Boolean functions on the pairs `i < j`. -/
noncomputable def graphEquiv (n : ℕ) :
    SimpleGraph (Fin n) ≃ ({p : Fin n × Fin n // p ∈ pairs n} → Bool) where
  toFun G := fun p => decide (G.Adj p.1.1 p.1.2)
  invFun g :=
    { Adj := fun i j => (∃ h : (i, j) ∈ pairs n, g ⟨(i, j), h⟩ = true) ∨
          (∃ h : (j, i) ∈ pairs n, g ⟨(j, i), h⟩ = true)
      symm := ⟨fun _ _ h => Or.symm h⟩
      loopless := ⟨fun i h => by
        rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [pairs] at h⟩ }
  left_inv G := by
    ext i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · have h1 : (i, j) ∈ pairs n := by simp [pairs, hij]
      have h2 : (j, i) ∉ pairs n := by simp [pairs, hij.le]
      constructor
      · rintro (⟨h, hg⟩ | ⟨h, hg⟩)
        · simpa using hg
        · exact absurd h h2
      · intro hG; exact Or.inl ⟨h1, by simpa using hG⟩
    · simp [pairs]
    · have h1 : (j, i) ∈ pairs n := by simp [pairs, hij]
      have h2 : (i, j) ∉ pairs n := by simp [pairs, hij.le]
      constructor
      · rintro (⟨h, hg⟩ | ⟨h, hg⟩)
        · exact absurd h h2
        · simpa [G.adj_comm] using hg
      · intro hG; exact Or.inr ⟨h1, by simpa [G.adj_comm] using hG⟩
  right_inv g := by
    funext ⟨⟨i, j⟩, h⟩
    have hij : i < j := by simpa [pairs] using h
    have h2 : (j, i) ∉ pairs n := by simp [pairs, hij.le]
    simp only
    cases hg : g ⟨(i, j), h⟩
    · simp only [decide_eq_false_iff_not]
      rintro (⟨h', hg'⟩ | ⟨h', _⟩)
      · rw [hg] at hg'; exact Bool.false_ne_true hg'
      · exact h2 h'
    · simp only [decide_eq_true_eq]
      exact Or.inl ⟨h, hg⟩

lemma edgeWeight_sum {n : ℕ} (r : Fin n → Fin n → ℝ) :
    ∑ G : SimpleGraph (Fin n), edgeWeight G r = 1 := by
  set f : {p : Fin n × Fin n // p ∈ pairs n} → Bool → ℝ :=
    fun p b => if b then clamp01 (r p.1.1 p.1.2) else 1 - clamp01 (r p.1.1 p.1.2) with hf
  have h1 : ∏ i, ∑ b ∈ (univ : Finset Bool), f i b = 1 := by
    apply Finset.prod_eq_one
    intro i _
    simp [hf]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ] at h1
  rw [← h1]
  refine Fintype.sum_equiv (graphEquiv n) _ _ (fun G => ?_)
  unfold edgeWeight
  rw [← Finset.prod_coe_sort]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  simp [hf, graphEquiv]

lemma edgeWeight_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) (r : Fin n → Fin n → ℝ) :
    0 ≤ edgeWeight G r := by
  unfold edgeWeight
  apply Finset.prod_nonneg
  intro p _
  have h0 : 0 ≤ clamp01 (r p.1 p.2) := le_max_left _ _
  have h1 : clamp01 (r p.1 p.2) ≤ 1 := max_le zero_le_one (min_le_left _ _)
  split_ifs <;> linarith


lemma bisections_nonempty (m : ℕ) : (bisections (2 * m)).Nonempty := by
  obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (univ : Finset (Fin (2 * m))))
    (n := m) (by simp; omega)
  exact ⟨S, by simp [bisections, LPCommunity.MinBisect.IsBisection, hS]⟩

lemma sbmProb_true (m : ℕ) (p q : ℝ) :
    sbmProb (2 * m) p q (fun _ _ => True) = 1 := by
  unfold sbmProb
  simp only [if_true, mul_one, edgeWeight_sum, Finset.sum_const, nsmul_eq_mul]
  have : ((bisections (2 * m)).card : ℝ) ≠ 0 := by
    exact_mod_cast (bisections_nonempty m).card_pos.ne'
  field_simp

lemma sbmProb_mono {n : ℕ} (p q : ℝ) (E F : Finset (Fin n) → SimpleGraph (Fin n) → Prop)
    (h : ∀ V1 ∈ bisections n, ∀ G, E V1 G → F V1 G) :
    sbmProb n p q E ≤ sbmProb n p q F := by
  unfold sbmProb
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro V1 hV1
  apply Finset.sum_le_sum
  intro G _
  apply mul_le_mul_of_nonneg_left _ (edgeWeight_nonneg _ _)
  by_cases hE : E V1 G
  · simp [hE, h V1 hV1 G hE]
  · simp only [hE, if_false]; split_ifs <;> norm_num

lemma sbmProb_le_one (m : ℕ) (p q : ℝ) (E : Finset (Fin (2 * m)) → SimpleGraph (Fin (2 * m)) → Prop) :
    sbmProb (2 * m) p q E ≤ 1 := by
  rw [← sbmProb_true m p q]
  exact sbmProb_mono p q _ _ (fun _ _ _ _ => trivial)

lemma sbmProb_or_le {n : ℕ} (p q : ℝ) (E F : Finset (Fin n) → SimpleGraph (Fin n) → Prop) :
    sbmProb n p q (fun V G => E V G ∨ F V G) ≤ sbmProb n p q E + sbmProb n p q F := by
  unfold sbmProb
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro V1 _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro G _
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (edgeWeight_nonneg _ _)
  split_ifs <;> simp_all

lemma sbmProb_compl {n : ℕ} (p q : ℝ) (E : Finset (Fin n) → SimpleGraph (Fin n) → Prop) :
    sbmProb n p q E + sbmProb n p q (fun V G => ¬ E V G) = sbmProb n p q (fun _ _ => True) := by
  unfold sbmProb
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun V1 _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun G _ => ?_)
  by_cases h : E V1 G <;> simp [h]

lemma tendsto_and {p q : ℕ → ℝ}
    (E F : (m : ℕ) → Finset (Fin (2 * m)) → SimpleGraph (Fin (2 * m)) → Prop)
    (hE : Filter.Tendsto (fun m => sbmProb (2 * m) (p m) (q m) (E m)) Filter.atTop (nhds 1))
    (hF : Filter.Tendsto (fun m => sbmProb (2 * m) (p m) (q m) (F m)) Filter.atTop (nhds 1)) :
    Filter.Tendsto (fun m => sbmProb (2 * m) (p m) (q m) (fun V G => E m V G ∧ F m V G))
      Filter.atTop (nhds 1) := by
  have key : ∀ m, sbmProb (2 * m) (p m) (q m) (E m) + sbmProb (2 * m) (p m) (q m) (F m) - 1 ≤
      sbmProb (2 * m) (p m) (q m) (fun V G => E m V G ∧ F m V G) := by
    intro m
    have h1 := sbmProb_compl (p m) (q m) (E m)
    have h2 := sbmProb_compl (p m) (q m) (F m)
    have h3 := sbmProb_compl (p m) (q m) (fun V G => E m V G ∧ F m V G)
    have h4 := sbmProb_or_le (p m) (q m) (fun V G => ¬ E m V G) (fun V G => ¬ F m V G)
    have h5 : sbmProb (2 * m) (p m) (q m) (fun V G => ¬ (E m V G ∧ F m V G)) ≤
        sbmProb (2 * m) (p m) (q m) (fun V G => ¬ E m V G ∨ ¬ F m V G) :=
      sbmProb_mono _ _ _ _ (fun V _ G h => by tauto)
    rw [sbmProb_true] at h1 h2 h3
    linarith
  have hlow : Filter.Tendsto (fun m => sbmProb (2 * m) (p m) (q m) (E m) +
      sbmProb (2 * m) (p m) (q m) (F m) - 1) Filter.atTop (nhds 1) := by
    have := (hE.add hF).sub_const 1
    norm_num at this
    exact this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds key
    (fun m => sbmProb_le_one m _ _ _)

lemma tendsto_of_imp {p q : ℕ → ℝ}
    (E F : (m : ℕ) → Finset (Fin (2 * m)) → SimpleGraph (Fin (2 * m)) → Prop)
    (hE : Filter.Tendsto (fun m => sbmProb (2 * m) (p m) (q m) (E m)) Filter.atTop (nhds 1))
    (hEF : ∀ᶠ m in Filter.atTop, ∀ V1 ∈ bisections (2 * m), ∀ G, E m V1 G → F m V1 G) :
    Filter.Tendsto (fun m => sbmProb (2 * m) (p m) (q m) (F m)) Filter.atTop (nhds 1) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hE tendsto_const_nhds ?_
    (Filter.Eventually.of_forall (fun m => sbmProb_le_one m _ _ _))
  filter_upwards [hEF] with m hm
  exact sbmProb_mono _ _ _ _ hm


section WSec
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def W (a : ι → ℝ) (x : ι → Bool) : ℝ := ∏ i, if x i then a i else 1 - a i

lemma sum_W_mul_prod (a : ι → ℝ) (φ : ι → Bool → ℝ) :
    ∑ x : ι → Bool, W a x * ∏ i, φ i (x i) =
      ∏ i, (a i * φ i true + (1 - a i) * φ i false) := by
  have h := Finset.prod_univ_sum (fun _ : ι => (univ : Finset Bool))
    (fun i b => (if b then a i else 1 - a i) * φ i b)
  rw [Fintype.piFinset_univ] at h
  simp only [W, ← Finset.prod_mul_distrib]
  rw [← h]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp [Fintype.sum_bool]


end WSec

/-- the edge probabilities of `r`, clamped, as a function on pairs. -/
noncomputable def aR {n : ℕ} (r : Fin n → Fin n → ℝ) : {p : Fin n × Fin n // p ∈ pairs n} → ℝ :=
  fun p => clamp01 (r p.1.1 p.1.2)

lemma edgeWeight_eq {n : ℕ} (G : SimpleGraph (Fin n)) (r : Fin n → Fin n → ℝ) :
    edgeWeight G r = W (aR r) (graphEquiv n G) := by
  unfold edgeWeight W
  rw [← Finset.prod_coe_sort]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  simp [aR, graphEquiv]

lemma sum_graph {n : ℕ} (r : Fin n → Fin n → ℝ) (f : SimpleGraph (Fin n) → ℝ) :
    ∑ G, edgeWeight G r * f G = ∑ x, W (aR r) x * f ((graphEquiv n).symm x) := by
  rw [← (graphEquiv n).symm.sum_comp]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [edgeWeight_eq, Equiv.apply_symm_apply]

lemma clamp01_nonneg (x : ℝ) : 0 ≤ clamp01 x := le_max_left _ _
lemma clamp01_le_one (x : ℝ) : clamp01 x ≤ 1 := max_le zero_le_one (min_le_left _ _)

/-- the pairs `i < j` containing `v`. -/
noncomputable def star {n : ℕ} (v : Fin n) : Finset (Fin n × Fin n) :=
  (pairs n).filter (fun p => p.1 = v ∨ p.2 = v)

lemma star_prod {M : Type*} [CommMonoid M] {n : ℕ} (v : Fin n) (g : Fin n → Fin n → M)
    (hg : ∀ i j, g i j = g j i) :
    ∏ p ∈ star v, g p.1 p.2 = ∏ u ∈ univ.erase v, g v u := by
  refine Finset.prod_nbij' (fun p => if p.1 = v then p.2 else p.1)
    (fun u => if v < u then (v, u) else (u, v)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hp
    simp only [star, pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    obtain ⟨hlt, h | h⟩ := hp
    · subst h; simp only [if_true]; exact hlt.ne'
    · subst h; simp only [if_neg hlt.ne]; exact hlt.ne
  · intro u hu
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hu
    simp only [star, pairs, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with h
    · exact ⟨h, Or.inl rfl⟩
    · exact ⟨lt_of_le_of_ne (not_lt.1 h) hu, Or.inr rfl⟩
  · rintro ⟨a, b⟩ hp
    simp only [star, pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hlt, h | h⟩ := hp
    · subst h; simp [hlt]
    · subst h; simp [hlt.ne, not_lt.2 hlt.le]
  · intro u hu
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hu
    by_cases h : v < u
    · simp [h]
    · simp [h, hu]
  · rintro ⟨a, b⟩ hp
    simp only [star, pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hlt, h | h⟩ := hp
    · subst h; simp
    · subst h; simp [hlt.ne, hg]

lemma exp_degree {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) (s : ℝ) :
    Real.exp (s * G.degree v) =
      ∏ p ∈ star v, Real.exp (s * (if G.Adj p.1 p.2 then 1 else 0)) := by
  rw [star_prod v (fun i j => Real.exp (s * (if G.Adj i j then 1 else 0)))
    (fun i j => by simp only [G.adj_comm])]
  rw [← Real.exp_sum, ← Finset.mul_sum]
  congr 2
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter,
    Finset.card_filter]
  push_cast
  rw [Finset.sum_erase (f := fun i => if G.Adj v i then (1:ℝ) else 0) univ (by simp)]

lemma mgf_degree {n : ℕ} (r : Fin n → Fin n → ℝ) (hr : ∀ i j, r i j = r j i) (v : Fin n) (s : ℝ) :
    ∑ G : SimpleGraph (Fin n), edgeWeight G r * Real.exp (s * G.degree v) =
      ∏ u ∈ univ.erase v, (clamp01 (r v u) * Real.exp s + (1 - clamp01 (r v u))) := by
  rw [sum_graph r (fun G => Real.exp (s * G.degree v))]
  set φ : {p : Fin n × Fin n // p ∈ pairs n} → Bool → ℝ := fun p b =>
    if p.1.1 = v ∨ p.1.2 = v then Real.exp (s * (if b then 1 else 0)) else 1 with hφ
  have hx : ∀ x : {p : Fin n × Fin n // p ∈ pairs n} → Bool,
      Real.exp (s * ((graphEquiv n).symm x).degree v) = ∏ p, φ p (x p) := by
    intro x
    rw [exp_degree, star, Finset.prod_filter, ← Finset.prod_coe_sort]
    refine Finset.prod_congr rfl (fun p _ => ?_)
    have hxp : decide (((graphEquiv n).symm x).Adj p.1.1 p.1.2) = x p :=
      congrFun ((graphEquiv n).apply_symm_apply x) p
    simp only [hφ]
    split_ifs with h1 h2 h3 h3 <;> simp_all
  simp_rw [hx]
  rw [sum_W_mul_prod]
  rw [← star_prod v (fun i j => clamp01 (r i j) * Real.exp s + (1 - clamp01 (r i j)))
    (fun i j => by rw [hr])]
  rw [star, Finset.prod_filter, ← Finset.prod_coe_sort (pairs n)]
  refine Fintype.prod_congr _ _ (fun p => ?_)
  simp only [hφ, aR]
  split_ifs <;> simp_all

lemma mgf_degree_le {n : ℕ} (r : Fin n → Fin n → ℝ) (hr : ∀ i j, r i j = r j i) (v : Fin n)
    (s : ℝ) (hs : |s| ≤ 1) :
    ∑ G : SimpleGraph (Fin n), edgeWeight G r * Real.exp (s * G.degree v) ≤
      Real.exp ((s + s ^ 2) * ∑ u ∈ univ.erase v, clamp01 (r v u)) := by
  rw [mgf_degree r hr v s, Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro u _
    have := clamp01_nonneg (r v u); have := clamp01_le_one (r v u)
    have := Real.exp_pos s
    nlinarith
  · intro u _
    have h1 := clamp01_nonneg (r v u)
    have hb := Real.abs_exp_sub_one_sub_id_le hs
    have hb' : Real.exp s - 1 ≤ s + s ^ 2 := by
      have := (abs_le.1 hb).2; linarith
    calc clamp01 (r v u) * Real.exp s + (1 - clamp01 (r v u))
        = clamp01 (r v u) * (Real.exp s - 1) + 1 := by ring
      _ ≤ clamp01 (r v u) * (s + s ^ 2) + 1 := by nlinarith
      _ ≤ Real.exp (clamp01 (r v u) * (s + s ^ 2)) := by
          have := Real.add_one_le_exp (clamp01 (r v u) * (s + s ^ 2)); linarith
      _ = Real.exp ((s + s ^ 2) * clamp01 (r v u)) := by ring_nf

/-- Chernoff tail for one degree, both directions: `σ = 1` upper, `σ = -1` lower. -/
lemma degree_tail {n : ℕ} (r : Fin n → Fin n → ℝ) (hr : ∀ i j, r i j = r j i) (v : Fin n)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (t M : ℝ) (ht : 0 ≤ t) (hM : 0 < M) (htM : t ≤ 2 * M)
    (hμM : ∑ u ∈ univ.erase v, clamp01 (r v u) ≤ M) :
    ∑ G : SimpleGraph (Fin n), edgeWeight G r *
      (if σ * ((G.degree v : ℝ) - ∑ u ∈ univ.erase v, clamp01 (r v u)) ≥ t then 1 else 0) ≤
      Real.exp (- t ^ 2 / (4 * M)) := by
  have hμ0 : 0 ≤ ∑ u ∈ univ.erase v, clamp01 (r v u) :=
    Finset.sum_nonneg (fun u _ => clamp01_nonneg _)
  have hmgf := mgf_degree_le r hr v
  generalize hμ : ∑ u ∈ univ.erase v, clamp01 (r v u) = μ at hμM hμ0 hmgf ⊢
  set l := t / (2 * M) with hl
  have hl0 : 0 ≤ l := by positivity
  have hl1 : l ≤ 1 := by rw [hl, div_le_one (by positivity)]; exact htM
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with h | h <;> simp [h]
  have hs : |σ * l| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hl0]
    rcases hσ with h | h <;> simp [h, hl1]
  have step1 : ∀ G : SimpleGraph (Fin n),
      (if σ * ((G.degree v : ℝ) - μ) ≥ t then (1:ℝ) else 0) ≤
        Real.exp (- (σ * l) * μ - l * t) * Real.exp ((σ * l) * G.degree v) := by
    intro G
    rw [← Real.exp_add]
    split_ifs with h
    · apply Real.one_le_exp
      nlinarith
    · exact (Real.exp_pos _).le
  calc ∑ G : SimpleGraph (Fin n), edgeWeight G r *
        (if σ * ((G.degree v : ℝ) - μ) ≥ t then 1 else 0)
      ≤ ∑ G : SimpleGraph (Fin n), edgeWeight G r *
        (Real.exp (- (σ * l) * μ - l * t) * Real.exp ((σ * l) * G.degree v)) := by
        apply Finset.sum_le_sum
        intro G _
        exact mul_le_mul_of_nonneg_left (step1 G) (edgeWeight_nonneg _ _)
    _ = Real.exp (- (σ * l) * μ - l * t) *
        ∑ G : SimpleGraph (Fin n), edgeWeight G r * Real.exp ((σ * l) * G.degree v) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun G _ => by ring)
    _ ≤ Real.exp (- (σ * l) * μ - l * t) * Real.exp ((σ * l + (σ * l) ^ 2) * μ) :=
        mul_le_mul_of_nonneg_left (hmgf _ hs) (Real.exp_pos _).le
    _ = Real.exp (- l * t + l ^ 2 * μ) := by
        rw [← Real.exp_add]; congr 1
        have : (σ * l) ^ 2 = l ^ 2 := by rw [mul_pow, hσ2, one_mul]
        rw [this]; ring
    _ ≤ Real.exp (- t ^ 2 / (4 * M)) := by
        apply Real.exp_le_exp.2
        have h1 : l ^ 2 * μ ≤ l ^ 2 * M := mul_le_mul_of_nonneg_left hμM (by positivity)
        have h2 : - l * t + l ^ 2 * M = - t ^ 2 / (4 * M) := by
          rw [hl]; field_simp; ring
        linarith

/-- union bound over the vertices. -/
lemma sum_exists_le {n : ℕ} (r : Fin n → Fin n → ℝ) (B : Fin n → SimpleGraph (Fin n) → Prop) :
    ∑ G : SimpleGraph (Fin n), edgeWeight G r * (if ∃ v, B v G then 1 else 0) ≤
      ∑ v, ∑ G : SimpleGraph (Fin n), edgeWeight G r * (if B v G then 1 else 0) := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro G _
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (edgeWeight_nonneg _ _)
  split_ifs with h
  · obtain ⟨v, hv⟩ := h
    calc (1:ℝ) = if B v G then 1 else 0 := by simp [hv]
      _ ≤ ∑ v, (if B v G then (1:ℝ) else 0) :=
        Finset.single_le_sum (f := fun v => if B v G then (1:ℝ) else 0)
          (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ v)
  · exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)

lemma sum_compl {n : ℕ} (r : Fin n → Fin n → ℝ) (E : SimpleGraph (Fin n) → Prop) :
    ∑ G : SimpleGraph (Fin n), edgeWeight G r * (if E G then 1 else 0) =
      1 - ∑ G : SimpleGraph (Fin n), edgeWeight G r * (if ¬ E G then 1 else 0) := by
  rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  calc ∑ G : SimpleGraph (Fin n), (edgeWeight G r * (if E G then 1 else 0) +
        edgeWeight G r * (if ¬ E G then 1 else 0)) = ∑ G : SimpleGraph (Fin n), edgeWeight G r :=
        Finset.sum_congr rfl (fun G _ => by by_cases h : E G <;> simp [h])
    _ = 1 := edgeWeight_sum r

lemma exp_neg_two_log (m : ℕ) (hm : 1 ≤ m) :
    Real.exp (- (2 * Real.log m)) = 1 / ((m : ℝ) * m) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  rw [Real.exp_neg, two_mul, Real.exp_add, Real.exp_log hm0, one_div]


lemma sqrt_small (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, Real.sqrt (m * Real.log m) ≤ δ * m := by
  have h1 := Real.isLittleO_log_id_atTop.bound (pow_pos hδ 2)
  have h2 := tendsto_natCast_atTop_atTop.eventually h1
  filter_upwards [h2] with m hm
  simp only [Real.norm_eq_abs, id] at hm
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  rw [abs_of_nonneg hm0] at hm
  have hlog : Real.log m ≤ δ ^ 2 * m := le_trans (le_abs_self _) hm
  have hml : (m : ℝ) * Real.log m ≤ m * (δ ^ 2 * m) := mul_le_mul_of_nonneg_left hlog hm0
  calc Real.sqrt (m * Real.log m) ≤ Real.sqrt ((δ * m) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = δ * m := Real.sqrt_sq (by positivity)

lemma log_ge_one {n : ℕ} (hn : 3 ≤ n) : 1 ≤ Real.log n := by
  have hn' : (3:ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith


lemma dMax_le {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) (X : ℝ)
    (h : ∀ v, (G.degree v : ℝ) ≤ X) : (dMax G : ℝ) ≤ X := by
  unfold dMax
  have hne : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, mem_univ _⟩
  obtain ⟨v, _, hv⟩ := Finset.exists_mem_eq_sup univ hne (fun v => G.degree v)
  rw [hv]
  exact h v

lemma mu_cross {m : ℕ} (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (V1 : Finset (Fin (2 * m)))
    (hV1 : V1.card = m) (v : Fin (2 * m)) :
    ∑ u ∈ univ.erase v, clamp01
      ((fun i j => if LPCommunity.MinBisect.sameSide V1 i j then (0:ℝ) else q) v u) = q * m := by
  have hc0 : clamp01 0 = 0 := by unfold clamp01; simp
  have hcq : clamp01 q = q := by
    unfold clamp01; rw [min_eq_right hq1.le, max_eq_right hq0.le]
  have h1 : ∀ u, clamp01 (if LPCommunity.MinBisect.sameSide V1 v u then (0:ℝ) else q) =
      if ¬ LPCommunity.MinBisect.sameSide V1 v u then q else 0 := by
    intro u; split_ifs <;> simp_all
  simp only [h1]
  rw [Finset.sum_erase (f := fun u => if ¬ LPCommunity.MinBisect.sameSide V1 v u then q else 0) univ
    (by simp [LPCommunity.MinBisect.sameSide])]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  by_cases hv : v ∈ V1
  · have : univ.filter (fun u => ¬ LPCommunity.MinBisect.sameSide V1 v u) = V1ᶜ := by
      ext u; simp [LPCommunity.MinBisect.sameSide, hv]
    rw [this, Finset.card_compl, Fintype.card_fin]
    push_cast [show m ≤ 2 * m by omega, hV1]
    ring
  · have : univ.filter (fun u => ¬ LPCommunity.MinBisect.sameSide V1 v u) = V1 := by
      ext u; simp [LPCommunity.MinBisect.sameSide, hv]
    rw [this, hV1]


open LPCommunity.MinBisect

/-- the bipartite complement of `G` with respect to the partition `V1, V1ᶜ`. -/
def bcompl {n : ℕ} (V1 : Finset (Fin n)) (G : SimpleGraph (Fin n)) : SimpleGraph (Fin n) where
  Adj i j := ¬ sameSide V1 i j ∧ ¬ G.Adj i j
  symm := ⟨fun i j h => ⟨fun h' => h.1 (Iff.symm h'), fun h' => h.2 h'.symm⟩⟩
  loopless := ⟨fun i h => h.1 Iff.rfl⟩

/-- the number of edges of `G` between `A` and `B`, as a double sum. -/
noncomputable def Xr {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)) : ℝ :=
  ∑ i ∈ A, ∑ j ∈ B, if G.Adj i j then 1 else 0

lemma Xr_le {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)) :
    Xr G A B ≤ (A.card : ℝ) * B.card := by
  unfold Xr
  have : ∀ i ∈ A, ∑ j ∈ B, (if G.Adj i j then (1:ℝ) else 0) ≤ B.card := by
    intro i _
    calc ∑ j ∈ B, (if G.Adj i j then (1:ℝ) else 0) ≤ ∑ j ∈ B, (1:ℝ) :=
          Finset.sum_le_sum (fun j _ => by split_ifs <;> norm_num)
      _ = B.card := by simp
  calc ∑ i ∈ A, ∑ j ∈ B, (if G.Adj i j then (1:ℝ) else 0) ≤ ∑ i ∈ A, (B.card : ℝ) :=
        Finset.sum_le_sum this
    _ = (A.card : ℝ) * B.card := by simp

lemma Xr_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)) : 0 ≤ Xr G A B :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num))

lemma Xr_split_left {n : ℕ} (G : SimpleGraph (Fin n)) (A U B : Finset (Fin n)) :
    Xr G A B = Xr G (A ∩ U) B + Xr G (A \ U) B := by
  unfold Xr
  rw [Finset.sum_inter_add_sum_sdiff]

lemma Xr_split_right {n : ℕ} (G : SimpleGraph (Fin n)) (A B U : Finset (Fin n)) :
    Xr G A B = Xr G A (B ∩ U) + Xr G A (B \ U) := by
  unfold Xr
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_inter_add_sum_sdiff]

/-- degree as a sum over the other side, for a graph with only crossing edges. -/
lemma degree_eq_side {n : ℕ} (V1 : Finset (Fin n)) (G : SimpleGraph (Fin n))
    (hG : ∀ i j, G.Adj i j → ¬ sameSide V1 i j) (v : Fin n) :
    (G.degree v : ℝ) = ∑ u ∈ (if v ∈ V1 then V1ᶜ else V1), if G.Adj v u then 1 else 0 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter,
    Finset.card_filter]
  push_cast
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro u _ hu
  rw [if_neg]
  intro hadj
  apply hG v u hadj
  unfold sameSide
  split_ifs at hu with hv
  · simp only [Finset.mem_compl, not_not] at hu
    exact iff_of_true hv hu
  · exact iff_of_false hv hu

lemma sum_degree_left {n : ℕ} (V1 : Finset (Fin n)) (G : SimpleGraph (Fin n))
    (hG : ∀ i j, G.Adj i j → ¬ sameSide V1 i j) (A : Finset (Fin n)) (hA : A ⊆ V1) :
    ∑ v ∈ A, (G.degree v : ℝ) = Xr G A V1ᶜ := by
  unfold Xr
  refine Finset.sum_congr rfl (fun v hv => ?_)
  rw [degree_eq_side V1 G hG v, if_pos (hA hv)]

lemma sum_degree_right {n : ℕ} (V1 : Finset (Fin n)) (G : SimpleGraph (Fin n))
    (hG : ∀ i j, G.Adj i j → ¬ sameSide V1 i j) (B : Finset (Fin n)) (hB : B ⊆ V1ᶜ) :
    ∑ v ∈ B, (G.degree v : ℝ) = Xr G V1 B := by
  unfold Xr
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  have hv' : v ∉ V1 := Finset.mem_compl.1 (hB hv)
  rw [degree_eq_side V1 G hG v, if_neg hv']
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [G.adj_comm]

/-- edge count inside `U` of a graph with only crossing edges. -/
lemma edgeCount_cross {n : ℕ} (V1 : Finset (Fin n)) (K : SimpleGraph (Fin n))
    (hK : ∀ i j, K.Adj i j → ¬ sameSide V1 i j) (U : Finset (Fin n)) :
    (edgeCount K U U : ℝ) = Xr K (V1 ∩ U) (V1ᶜ ∩ U) := by
  unfold Xr edgeCount
  have : ∑ i ∈ V1 ∩ U, ∑ j ∈ V1ᶜ ∩ U, (if K.Adj i j then (1:ℝ) else 0) =
      (((V1 ∩ U) ×ˢ (V1ᶜ ∩ U)).filter (fun ij => K.Adj ij.1 ij.2)).card := by
    rw [Finset.card_filter, ← Finset.sum_product']
    push_cast; rfl
  rw [this]
  norm_cast
  symm
  refine Finset.card_bij (fun ij _ => s(ij.1, ij.2)) ?_ ?_ ?_
  · rintro ⟨i, j⟩ hij
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_inter, Finset.mem_compl] at hij
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact ⟨hij.2, i, hij.1.1.2, j, hij.1.2.2, rfl⟩
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_inter, Finset.mem_compl] at hij hij'
    simp only [Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [h1, h2]
    · exfalso; rw [h1] at hij; exact hij'.1.2.1 hij.1.1.1
  · intro e he
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
    obtain ⟨he, u, hu, u', hu', rfl⟩ := he
    rw [SimpleGraph.mem_edgeSet] at he
    have hs := hK u u' he
    unfold sameSide at hs
    by_cases huV : u ∈ V1
    · have hu'V : u' ∉ V1 := fun h => hs (iff_of_true huV h)
      refine ⟨(u, u'), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_inter, Finset.mem_compl]
      exact ⟨⟨⟨huV, hu⟩, hu'V, hu'⟩, he⟩
    · have hu'V : u' ∈ V1 := by
        by_contra h; exact hs (iff_of_false huV h)
      refine ⟨(u', u), ?_, Sym2.eq_swap⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_inter, Finset.mem_compl]
      exact ⟨⟨⟨hu'V, hu'⟩, huV, hu⟩, he.symm⟩

lemma Xr_bcompl {n : ℕ} (V1 : Finset (Fin n)) (G : SimpleGraph (Fin n)) (A B : Finset (Fin n))
    (hA : A ⊆ V1) (hB : B ⊆ V1ᶜ) :
    Xr (bcompl V1 G) A B = (A.card : ℝ) * B.card - Xr G A B := by
  unfold Xr
  have : ∀ i ∈ A, ∀ j ∈ B, (if (bcompl V1 G).Adj i j then (1:ℝ) else 0) =
      1 - (if G.Adj i j then 1 else 0) := by
    intro i hi j hj
    have hs : ¬ sameSide V1 i j := fun h =>
      Finset.mem_compl.1 (hB hj) (h.1 (hA hi))
    by_cases hg : G.Adj i j
    · rw [if_neg (fun h => h.2 hg), if_pos hg]; ring
    · rw [if_pos ⟨hs, hg⟩, if_neg hg]; ring
  rw [Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => this i hi j hj))]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]

lemma det3 {m : ℕ} (V1 : Finset (Fin (2 * m))) (hV1 : V1.card = m) (G : SimpleGraph (Fin (2 * m)))
    (hG : ∀ i j, G.Adj i j → ¬ sameSide V1 i j) (d : ℕ) (hdm : d ≤ m)
    (hdeg : ∀ v, G.degree v ≤ d)
    (hcond : ∀ A ⊆ V1, ∀ B ⊆ V1ᶜ, A.card + B.card < m →
      Xr G (V1 \ A) (V1ᶜ \ B) ≤ (A.card : ℝ) * B.card + d * ((m : ℝ) - A.card - B.card)) :
    ∃ H : SimpleGraph (Fin (2 * m)), G ≤ H ∧ (∀ i j, H.Adj i j → ¬ sameSide V1 i j) ∧
      ∀ v, H.degree v = d := by
  have hV1c : V1ᶜ.card = m := by
    rw [Finset.card_compl, Fintype.card_fin]; omega
  set K := bcompl V1 G with hKdef
  have hKc : ∀ i j, K.Adj i j → ¬ sameSide V1 i j := fun i j h => h.1
  have hbip : ∃ A : Finset (Fin (2 * m)), ∀ u v, K.Adj u v → (u ∈ A ↔ v ∉ A) := by
    refine ⟨V1, fun u v h => ?_⟩
    have := h.1
    unfold sameSide at this
    tauto
  set b : Fin (2 * m) → ℕ := fun v => d - G.degree v with hb
  have hbr : ∀ v, (b v : ℝ) = d - G.degree v := fun v => by
    rw [hb]; push_cast [hdeg v]; ring
  have hfac : LPCommunity.SBMRecovery.HasFactor K b := by
    refine (LPCommunity.SBMRecovery.proposition_5 K hbip b).2 (fun U => ?_)
    set A := V1 ∩ U with hA
    set B := V1ᶜ ∩ U with hB
    have hAV : A ⊆ V1 := Finset.inter_subset_left
    have hBV : B ⊆ V1ᶜ := Finset.inter_subset_left
    have hW1 : V1 \ A = V1 \ U := by
      ext x; simp [hA]
    have hW2 : V1ᶜ \ B = V1ᶜ \ U := by
      ext x; simp [hB]
    -- left-hand side
    rw [edgeCount_cross V1 K hKc U, Xr_bcompl V1 G A B hAV hBV]
    -- b(U)
    have hU : ∑ v ∈ U, (b v : ℝ) = d * (A.card + B.card) - (Xr G A V1ᶜ + Xr G V1 B) := by
      have hsplit : ∑ v ∈ U, (b v : ℝ) = ∑ v ∈ A, (b v : ℝ) + ∑ v ∈ B, (b v : ℝ) := by
        rw [← Finset.sum_inter_add_sum_sdiff U V1]
        congr 1
        · rw [Finset.inter_comm]
        · apply Finset.sum_congr _ (fun _ _ => rfl)
          ext x; simp [hB, and_comm]
      rw [hsplit]
      simp only [hbr, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      rw [sum_degree_left V1 G hG A hAV, sum_degree_right V1 G hG B hBV]
      ring
    have hV : ∑ v, (b v : ℝ) = d * (2 * m) - 2 * Xr G V1 V1ᶜ := by
      have hsplit : ∑ v, (b v : ℝ) = ∑ v ∈ V1, (b v : ℝ) + ∑ v ∈ V1ᶜ, (b v : ℝ) := by
        rw [Finset.sum_add_sum_compl]
      rw [hsplit]
      simp only [hbr, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hV1, hV1c]
      rw [sum_degree_left V1 G hG V1 (subset_refl _),
        sum_degree_right V1 G hG V1ᶜ (subset_refl _)]
      ring
    rw [hU, hV]
    -- splits
    set W1 := V1 \ U with hW1d
    set W2 := V1ᶜ \ U with hW2d
    have e1 : Xr G A V1ᶜ = Xr G A B + Xr G A W2 := Xr_split_right G A V1ᶜ U
    have e2 : Xr G V1 B = Xr G A B + Xr G W1 B := Xr_split_left G V1 U B
    have e3 : Xr G V1 V1ᶜ = Xr G A V1ᶜ + Xr G W1 V1ᶜ := Xr_split_left G V1 U V1ᶜ
    have e4 : Xr G W1 V1ᶜ = Xr G W1 B + Xr G W1 W2 := Xr_split_right G W1 V1ᶜ U
    have cW1 : (W1.card : ℝ) = m - A.card := by
      have := (Finset.card_sdiff_add_card_inter V1 U).trans hV1
      have h2 : ((V1 \ U).card : ℝ) + (V1 ∩ U).card = m := by exact_mod_cast this
      rw [hW1d, hA]; linarith
    have cW2 : (W2.card : ℝ) = m - B.card := by
      have := (Finset.card_sdiff_add_card_inter V1ᶜ U).trans hV1c
      have h2 : ((V1ᶜ \ U).card : ℝ) + (V1ᶜ ∩ U).card = m := by exact_mod_cast this
      rw [hW2d, hB]; linarith
    have key : Xr G W1 W2 ≤ (A.card : ℝ) * B.card + d * ((m : ℝ) - A.card - B.card) := by
      by_cases hab : A.card + B.card < m
      · have := hcond A hAV B hBV hab
        rw [hW1, hW2] at this
        exact this
      · push Not at hab
        have hab' : (m : ℝ) ≤ A.card + B.card := by exact_mod_cast hab
        have hdm' : (d : ℝ) ≤ m := by exact_mod_cast hdm
        have h1 := Xr_le G W1 W2
        rw [cW1, cW2] at h1
        nlinarith
    have hnn := Xr_nonneg G W1 W2
    linarith
  obtain ⟨F, hFK, hFdeg⟩ := hfac
  refine ⟨G ⊔ F, le_sup_left, ?_, ?_⟩
  · intro i j h
    rcases h with h | h
    · exact hG i j h
    · exact (hFK h).1
  · intro v
    have hdisj : Disjoint (G.neighborFinset v) (F.neighborFinset v) := by
      rw [Finset.disjoint_left]
      intro u hu hu'
      rw [SimpleGraph.mem_neighborFinset] at hu hu'
      exact (hFK hu').2 hu
    have key : (G.neighborFinset v ∪ F.neighborFinset v).card = d := by
      rw [Finset.card_union_of_disjoint hdisj, SimpleGraph.card_neighborFinset_eq_degree,
        SimpleGraph.card_neighborFinset_eq_degree, hFdeg v]
      have := hdeg v
      simp only [hb]
      omega
    rw [← key, ← SimpleGraph.card_neighborFinset_eq_degree]
    congr 1
    ext u
    simp [SimpleGraph.mem_neighborFinset]

/-- the pairs `i < j` with one end in `W1` and the other in `W2`. -/
noncomputable def Spair {n : ℕ} (W1 W2 : Finset (Fin n)) : Finset (Fin n × Fin n) :=
  (pairs n).filter (fun p => (p.1 ∈ W1 ∧ p.2 ∈ W2) ∨ (p.1 ∈ W2 ∧ p.2 ∈ W1))

lemma Spair_sub {n : ℕ} (W1 W2 : Finset (Fin n)) : Spair W1 W2 ⊆ pairs n :=
  Finset.filter_subset _ _

lemma sum_to_Spair {n : ℕ} (W1 W2 : Finset (Fin n)) (hd : Disjoint W1 W2)
    (f : Fin n → Fin n → ℝ) (hf : ∀ i j, f i j = f j i) :
    ∑ i ∈ W1, ∑ j ∈ W2, f i j = ∑ p ∈ Spair W1 W2, f p.1 p.2 := by
  rw [← Finset.sum_product' (f := f)]
  refine Finset.sum_nbij' (fun ij => if ij.1 < ij.2 then ij else (ij.2, ij.1))
    (fun p => if p.1 ∈ W1 then p else (p.2, p.1)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ h
    simp only [Finset.mem_coe, Finset.mem_product] at h
    have hij : i ≠ j := fun e => Finset.disjoint_left.1 hd h.1 (e ▸ h.2)
    simp only [Finset.mem_coe, Spair, pairs, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with hlt
    · exact ⟨hlt, Or.inl h⟩
    · exact ⟨lt_of_le_of_ne (not_lt.1 hlt) hij.symm, Or.inr ⟨h.2, h.1⟩⟩
  · rintro ⟨i, j⟩ h
    simp only [Finset.mem_coe, Spair, pairs, Finset.mem_filter, Finset.mem_univ, true_and] at h
    simp only [Finset.mem_coe, Finset.mem_product]
    split_ifs with h1
    · rcases h.2 with h2 | h2
      · exact h2
      · exact absurd h1 (Finset.disjoint_right.1 hd h2.1)
    · rcases h.2 with h2 | h2
      · exact absurd h2.1 h1
      · exact ⟨h2.2, h2.1⟩
  · rintro ⟨i, j⟩ h
    simp only [Finset.mem_coe, Finset.mem_product] at h
    by_cases hlt : i < j
    · simp [hlt, h.1]
    · have : j ∉ W1 := fun hj => Finset.disjoint_left.1 hd hj h.2
      simp [hlt, this]
  · rintro ⟨i, j⟩ h
    simp only [Finset.mem_coe, Spair, pairs, Finset.mem_filter, Finset.mem_univ, true_and] at h
    by_cases h1 : i ∈ W1
    · simp [h1, h.1]
    · simp [h1, not_lt.2 h.1.le]
  · rintro ⟨i, j⟩ _
    by_cases hlt : i < j
    · simp [hlt]
    · simp [hlt, hf]

lemma mgf_set {n : ℕ} (r : Fin n → Fin n → ℝ) (S : Finset (Fin n × Fin n)) (hS : S ⊆ pairs n)
    (s : ℝ) :
    ∑ G : SimpleGraph (Fin n), edgeWeight G r *
      Real.exp (s * ∑ p ∈ S, (if G.Adj p.1 p.2 then (1:ℝ) else 0)) =
      ∏ p ∈ S, (clamp01 (r p.1 p.2) * Real.exp s + (1 - clamp01 (r p.1 p.2))) := by
  rw [sum_graph r (fun G => Real.exp (s * ∑ p ∈ S, (if G.Adj p.1 p.2 then (1:ℝ) else 0)))]
  have hSf : (pairs n).filter (fun p => p ∈ S) = S := by
    rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hS]
  set φ : {p : Fin n × Fin n // p ∈ pairs n} → Bool → ℝ := fun p b =>
    if p.1 ∈ S then Real.exp (s * (if b then 1 else 0)) else 1 with hφ
  have hx : ∀ x : {p : Fin n × Fin n // p ∈ pairs n} → Bool,
      Real.exp (s * ∑ p ∈ S, (if ((graphEquiv n).symm x).Adj p.1 p.2 then (1:ℝ) else 0)) =
        ∏ p, φ p (x p) := by
    intro x
    rw [Finset.mul_sum, Real.exp_sum]
    conv_lhs => rw [← hSf]
    rw [Finset.prod_filter, ← Finset.prod_coe_sort (pairs n)]
    refine Fintype.prod_congr _ _ (fun p => ?_)
    have hxp : decide (((graphEquiv n).symm x).Adj p.1.1 p.1.2) = x p :=
      congrFun ((graphEquiv n).apply_symm_apply x) p
    simp only [hφ]
    split_ifs <;> simp_all
  simp_rw [hx]
  rw [sum_W_mul_prod]
  conv_rhs => rw [← hSf]
  rw [Finset.prod_filter, ← Finset.prod_coe_sort (pairs n)]
  refine Fintype.prod_congr _ _ (fun p => ?_)
  simp only [hφ, aR]
  split_ifs <;> simp_all

lemma set_tail {n : ℕ} (r : Fin n → Fin n → ℝ) (S : Finset (Fin n × Fin n)) (hS : S ⊆ pairs n)
    (T M : ℝ) (hT : 0 ≤ T) (hM : 0 < M) (hTM : T ≤ 2 * M)
    (hμM : ∑ p ∈ S, clamp01 (r p.1 p.2) ≤ M) :
    ∑ G : SimpleGraph (Fin n), edgeWeight G r *
      (if ∑ p ∈ S, (if G.Adj p.1 p.2 then (1:ℝ) else 0) ≥ ∑ p ∈ S, clamp01 (r p.1 p.2) + T
        then 1 else 0) ≤ Real.exp (- T ^ 2 / (4 * M)) := by
  have hμ0 : 0 ≤ ∑ p ∈ S, clamp01 (r p.1 p.2) := Finset.sum_nonneg (fun _ _ => clamp01_nonneg _)
  have hmgf : ∀ l : ℝ, |l| ≤ 1 → ∑ G : SimpleGraph (Fin n), edgeWeight G r *
      Real.exp (l * ∑ p ∈ S, (if G.Adj p.1 p.2 then (1:ℝ) else 0)) ≤
      Real.exp ((l + l ^ 2) * ∑ p ∈ S, clamp01 (r p.1 p.2)) := by
    intro l hl
    rw [mgf_set r S hS l, Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p _
      have := clamp01_nonneg (r p.1 p.2); have := clamp01_le_one (r p.1 p.2)
      have := Real.exp_pos l
      nlinarith
    · intro p _
      have h1 := clamp01_nonneg (r p.1 p.2)
      have hb := Real.abs_exp_sub_one_sub_id_le hl
      have hb' : Real.exp l - 1 ≤ l + l ^ 2 := by
        have := (abs_le.1 hb).2; linarith
      calc clamp01 (r p.1 p.2) * Real.exp l + (1 - clamp01 (r p.1 p.2))
          = clamp01 (r p.1 p.2) * (Real.exp l - 1) + 1 := by ring
        _ ≤ clamp01 (r p.1 p.2) * (l + l ^ 2) + 1 := by nlinarith
        _ ≤ Real.exp (clamp01 (r p.1 p.2) * (l + l ^ 2)) := by
            have := Real.add_one_le_exp (clamp01 (r p.1 p.2) * (l + l ^ 2)); linarith
        _ = Real.exp ((l + l ^ 2) * clamp01 (r p.1 p.2)) := by ring_nf
  generalize hμ : ∑ p ∈ S, clamp01 (r p.1 p.2) = μ at hμM hμ0 hmgf ⊢
  set l := T / (2 * M) with hl
  have hl0 : 0 ≤ l := by positivity
  have hl1 : l ≤ 1 := by rw [hl, div_le_one (by positivity)]; exact hTM
  have hs : |l| ≤ 1 := by rw [abs_of_nonneg hl0]; exact hl1
  have step1 : ∀ G : SimpleGraph (Fin n),
      (if ∑ p ∈ S, (if G.Adj p.1 p.2 then (1:ℝ) else 0) ≥ μ + T then (1:ℝ) else 0) ≤
        Real.exp (- l * μ - l * T) *
          Real.exp (l * ∑ p ∈ S, (if G.Adj p.1 p.2 then (1:ℝ) else 0)) := by
    intro G
    rw [← Real.exp_add]
    split_ifs with h
    · apply Real.one_le_exp
      nlinarith
    · exact (Real.exp_pos _).le
  calc ∑ G : SimpleGraph (Fin n), edgeWeight G r *
        (if ∑ p ∈ S, (if G.Adj p.1 p.2 then (1:ℝ) else 0) ≥ μ + T then 1 else 0)
      ≤ ∑ G : SimpleGraph (Fin n), edgeWeight G r * (Real.exp (- l * μ - l * T) *
          Real.exp (l * ∑ p ∈ S, (if G.Adj p.1 p.2 then (1:ℝ) else 0))) := by
        apply Finset.sum_le_sum
        intro G _
        exact mul_le_mul_of_nonneg_left (step1 G) (edgeWeight_nonneg _ _)
    _ = Real.exp (- l * μ - l * T) * ∑ G : SimpleGraph (Fin n), edgeWeight G r *
          Real.exp (l * ∑ p ∈ S, (if G.Adj p.1 p.2 then (1:ℝ) else 0)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun G _ => by ring)
    _ ≤ Real.exp (- l * μ - l * T) * Real.exp ((l + l ^ 2) * μ) :=
        mul_le_mul_of_nonneg_left (hmgf _ hs) (Real.exp_pos _).le
    _ = Real.exp (- l * T + l ^ 2 * μ) := by
        rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (- T ^ 2 / (4 * M)) := by
        apply Real.exp_le_exp.2
        have h1 : l ^ 2 * μ ≤ l ^ 2 * M := mul_le_mul_of_nonneg_left hμM (by positivity)
        have h2 : - l * T + l ^ 2 * M = - T ^ 2 / (4 * M) := by
          rw [hl]; field_simp; ring
        linarith

/-- the SBM edge probabilities with `p = 0`. -/
noncomputable def r0 {n : ℕ} (V1 : Finset (Fin n)) (q : ℝ) : Fin n → Fin n → ℝ :=
  fun i j => if sameSide V1 i j then (0:ℝ) else q

lemma r0_symm {n : ℕ} (V1 : Finset (Fin n)) (q : ℝ) (i j : Fin n) : r0 V1 q i j = r0 V1 q j i := by
  unfold r0 sameSide
  by_cases h : i ∈ V1 <;> by_cases h' : j ∈ V1 <;> simp [h, h']

/-- tail bound for the number of edges between `W1 ⊆ V1` and `W2 ⊆ V1ᶜ`. -/
lemma tailAB {n : ℕ} (V1 : Finset (Fin n)) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (W1 W2 : Finset (Fin n)) (h1 : W1 ⊆ V1) (h2 : W2 ⊆ V1ᶜ) (R : ℝ)
    (hN : 0 < (W1.card : ℝ) * W2.card) (hR : q * (W1.card * W2.card) ≤ R) :
    ∑ G : SimpleGraph (Fin n), edgeWeight G (r0 V1 q) * (if Xr G W1 W2 > R then 1 else 0) ≤
      Real.exp (- (R - q * (W1.card * W2.card)) ^ 2 / (4 * (W1.card * W2.card))) := by
  set N : ℝ := (W1.card : ℝ) * W2.card with hNdef
  have hd : Disjoint W1 W2 := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact Finset.mem_compl.1 (h2 hx') (h1 hx)
  have hcq : clamp01 q = q := by
    unfold clamp01; rw [min_eq_right hq1.le, max_eq_right hq0.le]
  have hX : ∀ G : SimpleGraph (Fin n), Xr G W1 W2 =
      ∑ p ∈ Spair W1 W2, (if G.Adj p.1 p.2 then (1:ℝ) else 0) := by
    intro G
    unfold Xr
    exact sum_to_Spair W1 W2 hd (fun i j => if G.Adj i j then 1 else 0)
      (fun i j => by simp only [G.adj_comm])
  have hμ : ∑ p ∈ Spair W1 W2, clamp01 (r0 V1 q p.1 p.2) = q * N := by
    have := sum_to_Spair W1 W2 hd (fun i j => clamp01 (r0 V1 q i j))
      (fun i j => by rw [r0_symm])
    rw [← this]
    have : ∀ i ∈ W1, ∀ j ∈ W2, clamp01 (r0 V1 q i j) = q := by
      intro i hi j hj
      have hs : ¬ sameSide V1 i j := fun h => Finset.mem_compl.1 (h2 hj) (h.1 (h1 hi))
      simp only [r0, if_neg hs, hcq]
    rw [Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => this i hi j hj))]
    simp [hNdef]; ring
  have hXle : ∀ G : SimpleGraph (Fin n), Xr G W1 W2 ≤ N := fun G => Xr_le G W1 W2
  by_cases hbig : R - q * N ≤ 2 * N
  · calc ∑ G : SimpleGraph (Fin n), edgeWeight G (r0 V1 q) * (if Xr G W1 W2 > R then 1 else 0)
        ≤ ∑ G : SimpleGraph (Fin n), edgeWeight G (r0 V1 q) *
          (if ∑ p ∈ Spair W1 W2, (if G.Adj p.1 p.2 then (1:ℝ) else 0) ≥
            ∑ p ∈ Spair W1 W2, clamp01 (r0 V1 q p.1 p.2) + (R - q * N) then 1 else 0) := by
          apply Finset.sum_le_sum
          intro G _
          apply mul_le_mul_of_nonneg_left _ (edgeWeight_nonneg _ _)
          by_cases h : Xr G W1 W2 > R
          · rw [if_pos h, if_pos]
            rw [hμ, ← hX]; linarith
          · rw [if_neg h]; split_ifs <;> norm_num
      _ ≤ Real.exp (- (R - q * N) ^ 2 / (4 * N)) :=
          set_tail (r0 V1 q) (Spair W1 W2) (Spair_sub W1 W2) (R - q * N) N (by linarith) hN hbig
            (by rw [hμ]; nlinarith)
  · have : ∀ G : SimpleGraph (Fin n), ¬ (Xr G W1 W2 > R) := by
      intro G h
      have := hXle G
      nlinarith
    calc ∑ G : SimpleGraph (Fin n), edgeWeight G (r0 V1 q) * (if Xr G W1 W2 > R then 1 else 0)
        = 0 := Finset.sum_eq_zero (fun G _ => by rw [if_neg (this G)]; ring)
      _ ≤ _ := (Real.exp_pos _).le

lemma log_small (c : ℝ) (hc : 0 < c) : ∀ᶠ m : ℕ in atTop, Real.log m ≤ c * m := by
  have h1 := Real.isLittleO_log_id_atTop.bound hc
  have h2 := tendsto_natCast_atTop_atTop.eventually h1
  filter_upwards [h2] with m hm
  simp only [Real.norm_eq_abs, id] at hm
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  rw [abs_of_nonneg hm0] at hm
  exact le_trans (le_abs_self _) hm

lemma pow_eq_exp (m k : ℕ) (hm : 1 ≤ m) : ((m : ℝ) ^ k) = Real.exp (k * Real.log m) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  rw [Real.exp_nat_mul, Real.exp_log hm0]

/-- the key estimate of p. 23, for `a ≤ b`. -/
lemma term_bound_le (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (m : ℕ) (hm3 : 3 ≤ m)
    (hlogm : 256 * Real.log m ≤ (1 - q) ^ 2 * m) (d : ℝ)
    (hd : q * m + 32 * Real.sqrt (m * Real.log m) - 1 ≤ d) (a b : ℕ) (hab : a + b < m)
    (hle : a ≤ b) :
    (m.choose a : ℝ) * m.choose b *
      Real.exp (- ((a : ℝ) * b + d * ((m : ℝ) - a - b) - q * (((m : ℝ) - a) * ((m : ℝ) - b))) ^ 2
        / (4 * (((m : ℝ) - a) * ((m : ℝ) - b)))) ≤ Real.exp (- (6 * Real.log m)) := by
  have hM : (3:ℝ) ≤ m := by exact_mod_cast hm3
  have hlog := log_ge_one hm3
  set s := Real.sqrt (m * Real.log m) with hsdef
  have hs1 : 1 ≤ s := Real.one_le_sqrt.2 (by nlinarith)
  have hsq : s ^ 2 = m * Real.log m := Real.sq_sqrt (by nlinarith)
  have hab' : (a : ℝ) + b + 1 ≤ m := by exact_mod_cast hab
  have ha0 : (0:ℝ) ≤ a := Nat.cast_nonneg a
  have hb0 : (0:ℝ) ≤ b := Nat.cast_nonneg b
  have hle' : (a : ℝ) ≤ b := by exact_mod_cast hle
  set M : ℝ := (m : ℝ) with hMdef
  set A : ℝ := (a : ℝ) with hAdef
  set B : ℝ := (b : ℝ) with hBdef
  set N := (M - A) * (M - B) with hN
  set T := A * B + d * (M - A - B) - q * N with hT
  have hNid : N = A * B + M * (M - A - B) := by rw [hN]; ring
  have hTid : T = (1 - q) * (A * B) + (d - q * M) * (M - A - B) := by rw [hT, hNid]; ring
  have hdq : 16 * s ≤ d - q * M := by linarith
  have hMAB : 1 ≤ M - A - B := by linarith
  have hlogM0 : 0 ≤ Real.log M := by linarith
  have hq1' : 0 ≤ 1 - q := by linarith
  have hT1 : (1 - q) * (A * B) + 16 * s * (M - A - B) ≤ T := by
    rw [hTid]
    have : 16 * s * (M - A - B) ≤ (d - q * M) * (M - A - B) :=
      mul_le_mul_of_nonneg_right hdq (by linarith)
    linarith
  have hAB0 : 0 ≤ A * B := mul_nonneg ha0 hb0
  have hp1 : 0 ≤ (1 - q) * (A * B) := mul_nonneg hq1' hAB0
  have hp2 : 0 ≤ 16 * s * (M - A - B) := by
    have : 0 ≤ M - A - B := by linarith
    positivity
  have hT0 : 0 ≤ T := by linarith
  have hNpos : 0 < N := by rw [hN]; apply mul_pos <;> linarith
  have hM0 : 0 < M := by linarith
  -- the claim T² M ≥ 64 log M · N²
  have claim : 64 * Real.log M * N ^ 2 ≤ T ^ 2 * M := by
    by_cases hc : N ≤ 2 * (A * B)
    · have h1 : (1 - q) * N / 2 ≤ T := by
        have := mul_le_mul_of_nonneg_left hc hq1'
        linarith
      have h2 : ((1 - q) * N / 2) ^ 2 ≤ T ^ 2 := by
        apply pow_le_pow_left₀ (by positivity) h1
      have h3 : 64 * Real.log M * N ^ 2 ≤ ((1 - q) * N / 2) ^ 2 * M := by
        have : 64 * Real.log M ≤ (1 - q) ^ 2 * M / 4 := by linarith
        have hN2 : 0 ≤ N ^ 2 := sq_nonneg N
        calc 64 * Real.log M * N ^ 2 ≤ (1 - q) ^ 2 * M / 4 * N ^ 2 :=
              mul_le_mul_of_nonneg_right this hN2
          _ = ((1 - q) * N / 2) ^ 2 * M := by ring
      have h4 := mul_le_mul_of_nonneg_right h2 hM0.le
      linarith
    · push Not at hc
      have h1 : N ≤ 2 * (M * (M - A - B)) := by
        have := hNid; linarith
      have h16 : 16 * s * (M - A - B) ≤ T := by linarith
      have h2 : 8 * s * N ≤ T * M := by
        have e1 := mul_le_mul_of_nonneg_right h16 hM0.le
        have e2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 8 * s)
        have e3 : 16 * s * (M - A - B) * M = 8 * s * (2 * (M * (M - A - B))) := by ring
        linarith
      have h3 : (8 * s * N) ^ 2 ≤ (T * M) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h2 2
      have h4 : (8 * s * N) ^ 2 = 64 * Real.log M * N ^ 2 * M := by
        rw [mul_pow, mul_pow, hsq]; ring
      have h5 : (T * M) ^ 2 = T ^ 2 * M * M := by ring
      rw [h4, h5] at h3
      exact le_of_mul_le_mul_right h3 hM0
  -- k = m - b
  have hk : ((m - b : ℕ) : ℝ) = M - B := by
    rw [Nat.cast_sub (by omega)]
  have hNk : M / 2 * (M - B) ≤ N := by
    rw [hN]
    have : M / 2 ≤ M - A := by linarith
    exact mul_le_mul_of_nonneg_right this (by linarith)
  have hexp : 8 * (M - B) * Real.log M ≤ T ^ 2 / (4 * N) := by
    rw [le_div_iff₀ (by positivity)]
    have h6 : (M - B) * M ≤ 2 * N := by
      have := hNk; nlinarith
    have h7 := mul_le_mul_of_nonneg_left h6 (by positivity : (0:ℝ) ≤ 32 * Real.log M * N)
    have h8 : 8 * (M - B) * Real.log M * (4 * N) * M ≤ T ^ 2 * M := by
      have e1 : 8 * (M - B) * Real.log M * (4 * N) * M = 32 * Real.log M * N * ((M - B) * M) := by
        ring
      have e2 : 32 * Real.log M * N * (2 * N) = 64 * Real.log M * N ^ 2 := by ring
      linarith
    exact le_of_mul_le_mul_right h8 hM0
  -- binomials
  have hm1 : 1 ≤ m := by omega
  have hch : (m.choose a : ℝ) * m.choose b ≤ Real.exp ((2 * (m - b : ℕ) : ℕ) * Real.log M) := by
    rw [← pow_eq_exp m _ hm1]
    have h1 : m.choose b = m.choose (m - b) := (Nat.choose_symm (by omega)).symm
    have h2 : (m.choose a : ℝ) ≤ (m : ℝ) ^ (m - b) := by
      have := Nat.choose_le_pow m a
      have h3 : (m : ℝ) ^ a ≤ (m : ℝ) ^ (m - b) :=
        pow_le_pow_right₀ (by exact_mod_cast hm1) (by omega)
      calc (m.choose a : ℝ) ≤ (m : ℝ) ^ a := by exact_mod_cast this
        _ ≤ _ := h3
    have h4 : (m.choose b : ℝ) ≤ (m : ℝ) ^ (m - b) := by
      rw [h1]; exact_mod_cast Nat.choose_le_pow m (m - b)
    calc (m.choose a : ℝ) * m.choose b ≤ (m : ℝ) ^ (m - b) * (m : ℝ) ^ (m - b) :=
          mul_le_mul h2 h4 (by positivity) (by positivity)
      _ = (m : ℝ) ^ (2 * (m - b)) := by rw [← pow_add]; ring_nf
  calc (m.choose a : ℝ) * m.choose b * Real.exp (- T ^ 2 / (4 * N))
      ≤ Real.exp ((2 * (m - b : ℕ) : ℕ) * Real.log M) * Real.exp (- (8 * (M - B) * Real.log M)) := by
        apply mul_le_mul hch _ (Real.exp_pos _).le (Real.exp_pos _).le
        apply Real.exp_le_exp.2
        rw [neg_div]
        linarith
    _ = Real.exp (- (6 * (M - B) * Real.log M)) := by
        rw [← Real.exp_add]
        congr 1
        push_cast [Nat.cast_sub (show b ≤ m by omega)]
        ring
    _ ≤ Real.exp (- (6 * Real.log M)) := by
        apply Real.exp_le_exp.2
        have : 0 ≤ (M - B - 1) * Real.log M := mul_nonneg (by linarith) hlogM0
        linarith

lemma term_bound (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (m : ℕ) (hm3 : 3 ≤ m)
    (hlogm : 256 * Real.log m ≤ (1 - q) ^ 2 * m) (d : ℝ)
    (hd : q * m + 32 * Real.sqrt (m * Real.log m) - 1 ≤ d) (a b : ℕ) (hab : a + b < m) :
    (m.choose a : ℝ) * m.choose b *
      Real.exp (- ((a : ℝ) * b + d * ((m : ℝ) - a - b) - q * (((m : ℝ) - a) * ((m : ℝ) - b))) ^ 2
        / (4 * (((m : ℝ) - a) * ((m : ℝ) - b)))) ≤ Real.exp (- (6 * Real.log m)) := by
  rcases le_total a b with h | h
  · exact term_bound_le q hq0 hq1 m hm3 hlogm d hd a b hab h
  · have := term_bound_le q hq0 hq1 m hm3 hlogm d hd b a (by omega) h
    have e1 : (b : ℝ) * a + d * ((m : ℝ) - b - a) - q * (((m : ℝ) - b) * ((m : ℝ) - a)) =
        (a : ℝ) * b + d * ((m : ℝ) - a - b) - q * (((m : ℝ) - a) * ((m : ℝ) - b)) := by ring
    have e2 : ((m : ℝ) - b) * ((m : ℝ) - a) = ((m : ℝ) - a) * ((m : ℝ) - b) := by ring
    rw [e1, e2, mul_comm (m.choose b : ℝ)] at this
    exact this

lemma weight_cross {n : ℕ} (V1 : Finset (Fin n)) (q : ℝ) (G : SimpleGraph (Fin n))
    (hw : edgeWeight G (r0 V1 q) ≠ 0) : ∀ i j, G.Adj i j → ¬ sameSide V1 i j := by
  intro i j hadj hs
  apply hw
  have hc0 : clamp01 0 = 0 := by unfold clamp01; simp
  unfold edgeWeight
  rcases lt_trichotomy i j with hij | rfl | hij
  · apply Finset.prod_eq_zero (i := (i, j)) (by simp [pairs, hij])
    simp [hadj, r0, hs, hc0]
  · exact absurd hadj (G.loopless.irrefl i)
  · apply Finset.prod_eq_zero (i := (j, i)) (by simp [pairs, hij])
    have hs' : sameSide V1 j i := Iff.symm hs
    simp [hadj.symm, r0, hs', hc0]

lemma ind_nonneg (P : Prop) [Decidable P] : (0:ℝ) ≤ if P then 1 else 0 := by split_ifs <;> norm_num

lemma poly_bound (m : ℕ) (hm : 3 ≤ m) :
    ((m : ℝ) + 1) ^ 2 * Real.exp (- (6 * Real.log m)) ≤ 4 / m := by
  have hm0 : (0:ℝ) < m := by
    have : (3:ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hm1 : (1:ℝ) ≤ m := by
    have : (3:ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have h6 : Real.exp (6 * Real.log m) = (m : ℝ) ^ 6 := by
    have := pow_eq_exp m 6 (by omega)
    push_cast at this
    rw [this]
  rw [Real.exp_neg, h6, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) hm0]
  have h1 : ((m : ℝ) + 1) ^ 2 ≤ 4 * (m : ℝ) ^ 2 := by nlinarith
  have h2 : (m : ℝ) ^ 3 ≤ (m : ℝ) ^ 5 := pow_le_pow_right₀ hm1 (by norm_num)
  have e : 4 * (m : ℝ) ^ 6 = 4 * (m : ℝ) ^ 5 * m := by ring
  have h3 : ((m : ℝ) + 1) ^ 2 * m ≤ 4 * (m : ℝ) ^ 2 * m := mul_le_mul_of_nonneg_right h1 hm0.le
  have h4 : 4 * (m : ℝ) ^ 2 * m = 4 * (m : ℝ) ^ 3 := by ring
  nlinarith

set_option maxHeartbeats 2000000 in
lemma inner_bound (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (m : ℕ) (hm3 : 3 ≤ m)
    (hlogm : 256 * Real.log m ≤ (1 - q) ^ 2 * m)
    (hsd : Real.sqrt (m * Real.log m) ≤ q / 16 * m)
    (hdm : Real.sqrt (m * Real.log m) ≤ (1 - q) / 32 * m)
    (V1 : Finset (Fin (2 * m))) (hV1 : V1.card = m) :
    ∑ G : SimpleGraph (Fin (2 * m)), edgeWeight G (r0 V1 q) *
      (if ¬ (∃ H : SimpleGraph (Fin (2 * m)), G ≤ H ∧
          (∀ i j, H.Adj i j → ¬ LPCommunity.MinBisect.sameSide V1 i j) ∧
          ∀ v, (H.degree v : ℤ) = ⌊q * m + 32 * Real.sqrt (m * Real.log m)⌋) then 1 else 0)
      ≤ 6 / m := by
  have hM : (3:ℝ) ≤ m := by exact_mod_cast hm3
  have hlog := log_ge_one hm3
  have hV1c : V1ᶜ.card = m := by
    rw [Finset.card_compl, Fintype.card_fin]; omega
  set s := Real.sqrt (m * Real.log m) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s ^ 2 = m * Real.log m := Real.sq_sqrt (by nlinarith)
  set D : ℤ := ⌊q * m + 32 * s⌋ with hDdef
  have hD0 : 0 ≤ D := Int.floor_nonneg.2 (by positivity)
  set d : ℕ := D.toNat with hddef
  have hdD : (d : ℤ) = D := Int.toNat_of_nonneg hD0
  have hdR : (d : ℝ) = (D : ℝ) := by exact_mod_cast hdD
  have hdlow : q * m + 32 * s - 1 ≤ (d : ℝ) := by
    rw [hdR]; exact (Int.sub_one_lt_floor _).le
  have hdup : (d : ℝ) ≤ q * m + 32 * s := by rw [hdR]; exact Int.floor_le _
  have hdm' : d ≤ m := by
    have : (d : ℝ) ≤ m := by nlinarith
    exact_mod_cast this
  set r := r0 V1 q with hr
  have hμ : ∀ v, ∑ u ∈ univ.erase v, clamp01 (r v u) = q * m := fun v =>
    mu_cross q hq0 hq1 V1 hV1 v
  -- the bad events
  set R : ℕ → ℕ → ℝ := fun a b => (a : ℝ) * b + d * ((m : ℝ) - a - b) with hRdef
  set g : ℕ → ℕ → ℝ := fun a b => if a + b < m then
      Real.exp (- (R a b - q * (((m : ℝ) - a) * ((m : ℝ) - b))) ^ 2 /
        (4 * (((m : ℝ) - a) * ((m : ℝ) - b)))) else 0 with hgdef
  have step1 : ∀ G : SimpleGraph (Fin (2 * m)), edgeWeight G r *
      (if ¬ (∃ H : SimpleGraph (Fin (2 * m)), G ≤ H ∧
          (∀ i j, H.Adj i j → ¬ LPCommunity.MinBisect.sameSide V1 i j) ∧
          ∀ v, (H.degree v : ℤ) = D) then 1 else 0) ≤
      edgeWeight G r * (if ∃ v, (1:ℝ) * ((G.degree v : ℝ) - ∑ u ∈ univ.erase v, clamp01 (r v u))
          ≥ 32 * s then 1 else 0) +
      ∑ A ∈ V1.powerset, ∑ B ∈ V1ᶜ.powerset, edgeWeight G r *
        (if A.card + B.card < m ∧ Xr G (V1 \ A) (V1ᶜ \ B) > R A.card B.card then 1 else 0) := by
    intro G
    have hw0 := edgeWeight_nonneg G r
    have hRHS0 : 0 ≤ ∑ A ∈ V1.powerset, ∑ B ∈ V1ᶜ.powerset, edgeWeight G r *
        (if A.card + B.card < m ∧ Xr G (V1 \ A) (V1ᶜ \ B) > R A.card B.card then (1:ℝ) else 0) :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => mul_nonneg hw0 (ind_nonneg _)))
    have hdeg0 := mul_nonneg hw0 (ind_nonneg (∃ v, (1:ℝ) * ((G.degree v : ℝ) -
        ∑ u ∈ univ.erase v, clamp01 (r v u)) ≥ 32 * s))
    by_cases hw : edgeWeight G r = 0
    · simp [hw]
    by_cases hE : ∃ H : SimpleGraph (Fin (2 * m)), G ≤ H ∧
          (∀ i j, H.Adj i j → ¬ LPCommunity.MinBisect.sameSide V1 i j) ∧
          ∀ v, (H.degree v : ℤ) = D
    · rw [if_neg (not_not.2 hE), mul_zero]; linarith
    rw [if_pos hE, mul_one]
    have hG := weight_cross V1 q G hw
    by_cases hdb : ∃ v, (1:ℝ) * ((G.degree v : ℝ) - ∑ u ∈ univ.erase v, clamp01 (r v u)) ≥ 32 * s
    · rw [if_pos hdb, mul_one]; linarith
    -- degrees are fine, so some condition fails
    have hdeg : ∀ v, G.degree v ≤ d := by
      intro v
      by_contra hv
      push Not at hv
      apply hdb
      refine ⟨v, ?_⟩
      rw [hμ v]
      have : (d : ℝ) + 1 ≤ G.degree v := by exact_mod_cast hv
      have h2 := (Int.lt_floor_add_one (q * m + 32 * s))
      have : (D : ℝ) + 1 ≤ G.degree v := by rw [← hdR]; exact this
      linarith
    have hcb : ∃ A ∈ V1.powerset, ∃ B ∈ V1ᶜ.powerset, A.card + B.card < m ∧
        Xr G (V1 \ A) (V1ᶜ \ B) > R A.card B.card := by
      by_contra hc
      push Not at hc
      apply hE
      obtain ⟨H, h1, h2, h3⟩ := det3 V1 hV1 G hG d hdm' hdeg (fun A hA B hB hab =>
        hc A (Finset.mem_powerset.2 hA) B (Finset.mem_powerset.2 hB) hab)
      exact ⟨H, h1, h2, fun v => by rw [h3 v, hdD]⟩
    obtain ⟨A, hA, B, hB, hAB⟩ := hcb
    have : edgeWeight G r ≤ ∑ A ∈ V1.powerset, ∑ B ∈ V1ᶜ.powerset, edgeWeight G r *
        (if A.card + B.card < m ∧ Xr G (V1 \ A) (V1ᶜ \ B) > R A.card B.card then (1:ℝ) else 0) := by
      calc edgeWeight G r = edgeWeight G r *
            (if A.card + B.card < m ∧ Xr G (V1 \ A) (V1ᶜ \ B) > R A.card B.card then (1:ℝ) else 0) := by
            rw [if_pos hAB, mul_one]
        _ ≤ ∑ B' ∈ V1ᶜ.powerset, edgeWeight G r *
            (if A.card + B'.card < m ∧ Xr G (V1 \ A) (V1ᶜ \ B') > R A.card B'.card then (1:ℝ) else 0) :=
            Finset.single_le_sum (f := fun B' => edgeWeight G r *
              (if A.card + B'.card < m ∧ Xr G (V1 \ A) (V1ᶜ \ B') > R A.card B'.card then (1:ℝ) else 0))
              (fun _ _ => mul_nonneg hw0 (ind_nonneg _)) hB
        _ ≤ _ := Finset.single_le_sum (f := fun A' => ∑ B' ∈ V1ᶜ.powerset, edgeWeight G r *
              (if A'.card + B'.card < m ∧ Xr G (V1 \ A') (V1ᶜ \ B') > R A'.card B'.card then (1:ℝ) else 0))
              (fun _ _ => Finset.sum_nonneg (fun _ _ => mul_nonneg hw0 (ind_nonneg _))) hA
    linarith
  -- degree part
  have hdegpart : ∑ G : SimpleGraph (Fin (2 * m)), edgeWeight G r *
      (if ∃ v, (1:ℝ) * ((G.degree v : ℝ) - ∑ u ∈ univ.erase v, clamp01 (r v u)) ≥ 32 * s
        then 1 else 0) ≤ 2 / m := by
    have hM0 : 0 < q * m := by positivity
    calc _ ≤ ∑ v : Fin (2 * m), ∑ G : SimpleGraph (Fin (2 * m)), edgeWeight G r *
          (if (1:ℝ) * ((G.degree v : ℝ) - ∑ u ∈ univ.erase v, clamp01 (r v u)) ≥ 32 * s
            then 1 else 0) :=
          sum_exists_le _ (fun v G =>
            (1:ℝ) * ((G.degree v : ℝ) - ∑ u ∈ univ.erase v, clamp01 (r v u)) ≥ 32 * s)
      _ ≤ ∑ v : Fin (2 * m), Real.exp (- (32 * s) ^ 2 / (4 * (q * m))) := by
          apply Finset.sum_le_sum
          intro v _
          exact degree_tail r (r0_symm V1 q) v 1 (Or.inl rfl) (32 * s) (q * m) (by positivity) hM0
            (by nlinarith) (le_of_eq (hμ v))
      _ ≤ ∑ v : Fin (2 * m), Real.exp (- (2 * Real.log m)) := by
          apply Finset.sum_le_sum
          intro v _
          apply Real.exp_le_exp.2
          have h5 : 2 * Real.log m ≤ (32 * s) ^ 2 / (4 * (q * m)) := by
            rw [le_div_iff₀ (by positivity)]
            have : (32 * s) ^ 2 = 1024 * (m * Real.log m) := by rw [mul_pow, hsq]; ring
            rw [this]
            have hlog0 : 0 ≤ Real.log m := by linarith
            have : q * m * Real.log m ≤ m * Real.log m := by
              have := mul_le_mul_of_nonneg_right hq1.le (by positivity : (0:ℝ) ≤ m * Real.log m)
              nlinarith
            nlinarith
          rw [neg_div]
          linarith
      _ = 2 / m := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            exp_neg_two_log m (by omega)]
          have : (m:ℝ) ≠ 0 := by positivity
          push_cast
          field_simp
  -- condition part
  have hABpart : ∀ A ∈ V1.powerset, ∀ B ∈ V1ᶜ.powerset,
      ∑ G : SimpleGraph (Fin (2 * m)), edgeWeight G r *
        (if A.card + B.card < m ∧ Xr G (V1 \ A) (V1ᶜ \ B) > R A.card B.card then 1 else 0)
        ≤ g A.card B.card := by
    intro A hA B hB
    rw [Finset.mem_powerset] at hA hB
    by_cases hab : A.card + B.card < m
    · simp only [hgdef, if_pos hab]
      have c1 : ((V1 \ A).card : ℝ) = (m : ℝ) - A.card := by
        have := Finset.card_sdiff_add_card_eq_card hA
        rw [hV1] at this
        have : ((V1 \ A).card : ℝ) + A.card = m := by exact_mod_cast this
        linarith
      have c2 : ((V1ᶜ \ B).card : ℝ) = (m : ℝ) - B.card := by
        have := Finset.card_sdiff_add_card_eq_card hB
        rw [hV1c] at this
        have : ((V1ᶜ \ B).card : ℝ) + B.card = m := by exact_mod_cast this
        linarith
      have hab' : (A.card : ℝ) + B.card + 1 ≤ m := by exact_mod_cast hab
      have hN : 0 < ((V1 \ A).card : ℝ) * (V1ᶜ \ B).card := by
        rw [c1, c2]; apply mul_pos <;> linarith
      have hRq : q * (((V1 \ A).card : ℝ) * (V1ᶜ \ B).card) ≤ R A.card B.card := by
        rw [c1, c2]
        simp only [hRdef]
        have hdq : q * m ≤ (d : ℝ) := by nlinarith
        have h0 : (0:ℝ) ≤ A.card := Nat.cast_nonneg _
        have h0' : (0:ℝ) ≤ B.card := Nat.cast_nonneg _
        have : q * (((m:ℝ) - A.card) * ((m:ℝ) - B.card)) =
            q * (A.card * B.card) + q * m * ((m:ℝ) - A.card - B.card) := by ring
        rw [this]
        have e1 : q * m * ((m:ℝ) - A.card - B.card) ≤ d * ((m:ℝ) - A.card - B.card) :=
          mul_le_mul_of_nonneg_right hdq (by linarith)
        have e2 : q * (A.card * B.card) ≤ (A.card : ℝ) * B.card := by
          have : (0:ℝ) ≤ A.card * B.card := by positivity
          nlinarith
        linarith
      have := tailAB V1 q hq0 hq1 (V1 \ A) (V1ᶜ \ B) Finset.sdiff_subset Finset.sdiff_subset
        (R A.card B.card) hN hRq
      rw [c1, c2] at this
      calc _ ≤ ∑ G : SimpleGraph (Fin (2 * m)), edgeWeight G (r0 V1 q) *
            (if Xr G (V1 \ A) (V1ᶜ \ B) > R A.card B.card then 1 else 0) := by
            apply Finset.sum_le_sum
            intro G _
            apply mul_le_mul_of_nonneg_left _ (edgeWeight_nonneg _ _)
            by_cases h : Xr G (V1 \ A) (V1ᶜ \ B) > R A.card B.card
            · rw [if_pos ⟨hab, h⟩, if_pos h]
            · rw [if_neg (fun h' => h h'.2)]; exact ind_nonneg _
        _ ≤ _ := this
    · simp only [hgdef, if_neg hab]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro G _
      rw [if_neg (fun h => hab h.1), mul_zero]
  -- the combinatorial sum
  have hgsum : ∑ A ∈ V1.powerset, ∑ B ∈ V1ᶜ.powerset, g A.card B.card ≤ 4 / m := by
    have e1 : ∀ A : Finset (Fin (2 * m)), ∑ B ∈ V1ᶜ.powerset, g A.card B.card =
        ∑ b ∈ range (m + 1), (m.choose b : ℝ) * g A.card b := by
      intro A
      rw [Finset.sum_powerset_apply_card (f := fun b => g A.card b), hV1c]
      simp only [nsmul_eq_mul]
    simp_rw [e1]
    rw [Finset.sum_powerset_apply_card (f := fun a => ∑ b ∈ range (m + 1), (m.choose b : ℝ) * g a b),
      hV1]
    simp only [nsmul_eq_mul, Finset.mul_sum]
    have hterm : ∀ a ∈ range (m + 1), ∀ b ∈ range (m + 1),
        (m.choose a : ℝ) * ((m.choose b : ℝ) * g a b) ≤ Real.exp (- (6 * Real.log m)) := by
      intro a _ b _
      simp only [hgdef]
      split_ifs with hab
      · have := term_bound q hq0 hq1 m hm3 hlogm d hdlow a b hab
        simp only [hRdef]
        rw [← mul_assoc]
        exact this
      · rw [mul_zero, mul_zero]; exact (Real.exp_pos _).le
    calc ∑ a ∈ range (m + 1), ∑ b ∈ range (m + 1), (m.choose a : ℝ) * ((m.choose b : ℝ) * g a b)
        ≤ ∑ a ∈ range (m + 1), ∑ b ∈ range (m + 1), Real.exp (- (6 * Real.log m)) :=
          Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => hterm a ha b hb))
      _ = ((m : ℝ) + 1) ^ 2 * Real.exp (- (6 * Real.log m)) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast; ring
      _ ≤ 4 / m := poly_bound m hm3
  -- assemble
  have hfinal : ∑ G : SimpleGraph (Fin (2 * m)), edgeWeight G r *
      (if ¬ (∃ H : SimpleGraph (Fin (2 * m)), G ≤ H ∧
          (∀ i j, H.Adj i j → ¬ LPCommunity.MinBisect.sameSide V1 i j) ∧
          ∀ v, (H.degree v : ℤ) = D) then 1 else 0) ≤ 6 / m := by
    calc _ ≤ ∑ G : SimpleGraph (Fin (2 * m)), (edgeWeight G r *
          (if ∃ v, (1:ℝ) * ((G.degree v : ℝ) - ∑ u ∈ univ.erase v, clamp01 (r v u)) ≥ 32 * s
            then 1 else 0) +
          ∑ A ∈ V1.powerset, ∑ B ∈ V1ᶜ.powerset, edgeWeight G r *
          (if A.card + B.card < m ∧ Xr G (V1 \ A) (V1ᶜ \ B) > R A.card B.card then 1 else 0)) :=
          Finset.sum_le_sum (fun G _ => step1 G)
      _ = ∑ G : SimpleGraph (Fin (2 * m)), edgeWeight G r *
          (if ∃ v, (1:ℝ) * ((G.degree v : ℝ) - ∑ u ∈ univ.erase v, clamp01 (r v u)) ≥ 32 * s
            then 1 else 0) +
          ∑ A ∈ V1.powerset, ∑ B ∈ V1ᶜ.powerset, ∑ G : SimpleGraph (Fin (2 * m)), edgeWeight G r *
          (if A.card + B.card < m ∧ Xr G (V1 \ A) (V1ᶜ \ B) > R A.card B.card then 1 else 0) := by
          rw [Finset.sum_add_distrib, add_right_inj, Finset.sum_comm]
          exact Finset.sum_congr rfl (fun A _ => Finset.sum_comm)
      _ ≤ 2 / m + 4 / m := by
          refine add_le_add hdegpart (le_trans ?_ hgsum)
          exact Finset.sum_le_sum (fun A hA => Finset.sum_le_sum (fun B hB => hABpart A hA B hB))
      _ = 6 / m := by ring
  exact hfinal

end LP5Deg

open LP5Deg LPCommunity.SBMRecovery in
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 0 < q → q < 1 →
      Tendsto (fun m : ℕ => sbmProb (2 * m) 0 q (fun V1 G =>
        ∃ H : SimpleGraph (Fin (2 * m)), G ≤ H ∧ (∀ i j, H.Adj i j → ¬ LPCommunity.MinBisect.sameSide V1 i j) ∧
          ∀ v, (H.degree v : ℤ) = ⌊q * m + C * Real.sqrt (m * Real.log m)⌋)) atTop (𝓝 1) := by
  refine ⟨32, by norm_num, fun q hq0 hq1 => ?_⟩
  have hbad : ∀ᶠ m : ℕ in atTop, sbmProb (2 * m) 0 q (fun V1 G =>
      ¬ ∃ H : SimpleGraph (Fin (2 * m)), G ≤ H ∧
        (∀ i j, H.Adj i j → ¬ LPCommunity.MinBisect.sameSide V1 i j) ∧
          ∀ v, (H.degree v : ℤ) = ⌊q * m + 32 * Real.sqrt (m * Real.log m)⌋) ≤ 6 / m := by
    filter_upwards [eventually_ge_atTop 3, log_small ((1 - q) ^ 2 / 256) (by
        have : 0 < 1 - q := by linarith
        positivity),
      sqrt_small (q / 16) (by positivity),
      sqrt_small ((1 - q) / 32) (by have : 0 < 1 - q := by linarith
                                    positivity)] with m hm3 hlog hsd hdm
    have hlogm : 256 * Real.log m ≤ (1 - q) ^ 2 * m := by linarith
    unfold sbmProb
    have hcard : (0:ℝ) < (bisections (2 * m)).card := by
      exact_mod_cast (bisections_nonempty m).card_pos
    calc _ ≤ (1 / ((bisections (2 * m)).card : ℝ)) * ∑ V1 ∈ bisections (2 * m), (6 / (m:ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          apply Finset.sum_le_sum
          intro V1 hV1
          have hc : V1.card = m := by
            unfold bisections at hV1
            rw [Finset.mem_filter] at hV1
            have h2 := hV1.2
            unfold LPCommunity.MinBisect.IsBisection at h2
            omega
          refine le_trans (le_of_eq ?_) (inner_bound q hq0 hq1 m hm3 hlogm hsd hdm V1 hc)
          refine Finset.sum_congr rfl (fun G _ => ?_)
          congr 1
          by_cases hE : ∃ H : SimpleGraph (Fin (2 * m)), G ≤ H ∧
            (∀ i j, H.Adj i j → ¬ LPCommunity.MinBisect.sameSide V1 i j) ∧
              ∀ v, (H.degree v : ℤ) = ⌊q * m + 32 * Real.sqrt (m * Real.log m)⌋
          · rw [if_neg (not_not.2 hE), if_neg (not_not.2 hE)]
          · rw [if_pos hE, if_pos hE]
      _ = 6 / (m:ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          field_simp
  have hlow : Tendsto (fun m : ℕ => 1 - 6 / (m:ℝ)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub (tendsto_const_div_atTop_nhds_zero_nat 6)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [hbad] with m hm
    have h := sbmProb_compl (n := 2 * m) 0 q (fun V1 G =>
      ∃ H : SimpleGraph (Fin (2 * m)), G ≤ H ∧
        (∀ i j, H.Adj i j → ¬ LPCommunity.MinBisect.sameSide V1 i j) ∧
          ∀ v, (H.degree v : ℤ) = ⌊q * m + 32 * Real.sqrt (m * Real.log m)⌋)
    rw [sbmProb_true] at h
    linarith
  · exact Filter.Eventually.of_forall (fun m => sbmProb_le_one m _ _ _)
