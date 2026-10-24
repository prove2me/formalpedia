-- Prove2me | solution 1 for LPCommunity.SBMRecovery.proposition_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T11:16:52.656218+00:00
-- url     : https://prove2.me/submissions/b140aa1b-b41b-47a4-8ddb-7860014bd2dc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_LPCommunity_MinBisect_Setting
import Definitions.Def_LPCommunity_SBMRecovery_Factors
import Theorems.Thm_LPCommunity_SBMRecovery_proposition_7
import Theorems.Thm_LPCommunity_SBMRecovery_proposition_8
import Theorems.Thm_LPCommunity_SBMRecovery_proposition_9

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


lemma edgeCount_disj {n : ℕ} (G : SimpleGraph (Fin n)) (S T : Finset (Fin n)) (hd : Disjoint S T) :
    (edgeCount G S T : ℝ) = Xr G S T := by
  unfold Xr edgeCount
  have : ∑ i ∈ S, ∑ j ∈ T, (if G.Adj i j then (1:ℝ) else 0) =
      ((S ×ˢ T).filter (fun ij => G.Adj ij.1 ij.2)).card := by
    rw [Finset.card_filter, ← Finset.sum_product']
    push_cast; rfl
  rw [this]
  norm_cast
  symm
  refine Finset.card_bij (fun ij _ => s(ij.1, ij.2)) ?_ ?_ ?_
  · rintro ⟨i, j⟩ hij
    simp only [Finset.mem_filter, Finset.mem_product] at hij
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact ⟨hij.2, i, hij.1.1, j, hij.1.2, rfl⟩
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    simp only [Finset.mem_filter, Finset.mem_product] at hij hij'
    simp only [Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [h1, h2]
    · exfalso; rw [h1] at hij; exact Finset.disjoint_left.1 hd hij.1.1 hij'.1.2
  · intro e he
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
    obtain ⟨he, u, hu, u', hu', rfl⟩ := he
    rw [SimpleGraph.mem_edgeSet] at he
    refine ⟨(u, u'), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hu, hu'⟩, he⟩

lemma degree_sum_univ {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    (G.degree v : ℝ) = ∑ u, if G.Adj v u then 1 else 0 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter,
    Finset.card_filter]
  push_cast; rfl

lemma Xr_comm {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)) : Xr G A B = Xr G B A := by
  unfold Xr
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [G.adj_comm]

lemma sum_degree_T {n : ℕ} (G : SimpleGraph (Fin n)) (S T : Finset (Fin n)) (hd : Disjoint S T) :
    ∑ v ∈ T, (G.degree v : ℝ) = Xr G T T + Xr G S T + Xr G T (S ∪ T)ᶜ := by
  have h1 : ∑ v ∈ T, (G.degree v : ℝ) = Xr G T univ := by
    unfold Xr
    exact Finset.sum_congr rfl (fun v _ => degree_sum_univ G v)
  rw [h1, Xr_split_right G T univ (S ∪ T), Finset.univ_inter, ← Finset.compl_eq_univ_sdiff]
  have h2 : Xr G T (S ∪ T) = Xr G T S + Xr G T T := by
    unfold Xr
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_union hd)
  rw [h2, Xr_comm G T S]
  ring

/-- the pairs `i < j` inside `T`. -/
noncomputable def Pin {n : ℕ} (T : Finset (Fin n)) : Finset (Fin n × Fin n) :=
  (pairs n).filter (fun p => p.1 ∈ T ∧ p.2 ∈ T)

lemma sum_sq_to_Pin {n : ℕ} (T : Finset (Fin n)) (f : Fin n → Fin n → ℝ)
    (hf : ∀ i j, f i j = f j i) (h0 : ∀ i, f i i = 0) :
    ∑ i ∈ T, ∑ j ∈ T, f i j = 2 * ∑ p ∈ Pin T, f p.1 p.2 := by
  rw [← Finset.sum_product' (f := f)]
  rw [← Finset.sum_filter_add_sum_filter_not (T ×ˢ T) (fun ij => ij.1 < ij.2)]
  have h1 : (T ×ˢ T).filter (fun ij => ij.1 < ij.2) = Pin T := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_product, Pin, pairs, Finset.mem_univ, true_and]
    tauto
  have h2 : ∑ ij ∈ (T ×ˢ T).filter (fun ij => ¬ ij.1 < ij.2), f ij.1 ij.2 =
      ∑ p ∈ Pin T, f p.1 p.2 := by
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun ij => ij.1 = ij.2)]
    have h3 : ∑ ij ∈ ((T ×ˢ T).filter (fun ij => ¬ ij.1 < ij.2)).filter (fun ij => ij.1 = ij.2),
        f ij.1 ij.2 = 0 := by
      apply Finset.sum_eq_zero
      intro ij hij
      simp only [Finset.mem_filter] at hij
      rw [hij.2, h0]
    rw [h3, zero_add]
    refine Finset.sum_nbij' (fun ij => (ij.2, ij.1)) (fun p => (p.2, p.1)) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨i, j⟩ h
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at h
      simp only [Finset.mem_coe, Pin, pairs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨lt_of_le_of_ne (not_lt.1 h.1.2) (fun e => h.2 e.symm), h.1.1.2, h.1.1.1⟩
    · rintro ⟨i, j⟩ h
      simp only [Finset.mem_coe, Pin, pairs, Finset.mem_filter, Finset.mem_univ, true_and] at h
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨⟨h.2.2, h.2.1⟩, not_lt.2 h.1.le⟩, h.1.ne'⟩
    · rintro ⟨i, j⟩ _; rfl
    · rintro ⟨i, j⟩ _; rfl
    · rintro ⟨i, j⟩ _; exact hf i j
  rw [h1, h2]
  ring

/-- weighted sums over pairs: the mgf factorizes. -/
lemma mgf_w {n : ℕ} (r : Fin n → Fin n → ℝ) (w : Fin n × Fin n → ℝ) (s : ℝ) :
    ∑ G : SimpleGraph (Fin n), edgeWeight G r *
      Real.exp (s * ∑ p ∈ pairs n, w p * (if G.Adj p.1 p.2 then (1:ℝ) else 0)) =
      ∏ p ∈ pairs n, (clamp01 (r p.1 p.2) * Real.exp (s * w p) + (1 - clamp01 (r p.1 p.2))) := by
  rw [sum_graph r (fun G => Real.exp (s * ∑ p ∈ pairs n, w p * (if G.Adj p.1 p.2 then (1:ℝ) else 0)))]
  set φ : {p : Fin n × Fin n // p ∈ pairs n} → Bool → ℝ := fun p b =>
    Real.exp (s * (w p.1 * (if b then 1 else 0))) with hφ
  have hx : ∀ x : {p : Fin n × Fin n // p ∈ pairs n} → Bool,
      Real.exp (s * ∑ p ∈ pairs n, w p * (if ((graphEquiv n).symm x).Adj p.1 p.2 then (1:ℝ) else 0)) =
        ∏ p, φ p (x p) := by
    intro x
    rw [Finset.mul_sum, Real.exp_sum, ← Finset.prod_coe_sort (pairs n)]
    refine Fintype.prod_congr _ _ (fun p => ?_)
    have hxp : decide (((graphEquiv n).symm x).Adj p.1.1 p.1.2) = x p :=
      congrFun ((graphEquiv n).apply_symm_apply x) p
    simp only [hφ]
    congr 2
    cases h : x p <;> simp_all
  simp_rw [hx]
  rw [sum_W_mul_prod, ← Finset.prod_coe_sort (pairs n)]
  refine Fintype.prod_congr _ _ (fun p => ?_)
  simp only [hφ, aR]
  simp

/-- weighted lower tail. -/
lemma wtail {n : ℕ} (r : Fin n → Fin n → ℝ) (w : Fin n × Fin n → ℝ) (hw0 : ∀ p, 0 ≤ w p)
    (hw2 : ∀ p, w p ≤ 2) (t l : ℝ) (hl0 : 0 ≤ l) (hl : l ≤ 1 / 2) :
    ∑ G : SimpleGraph (Fin n), edgeWeight G r *
      (if ∑ p ∈ pairs n, w p * (if G.Adj p.1 p.2 then (1:ℝ) else 0) <
          ∑ p ∈ pairs n, clamp01 (r p.1 p.2) * w p - t then 1 else 0) ≤
      Real.exp (- l * t + l ^ 2 * ∑ p ∈ pairs n, clamp01 (r p.1 p.2) * w p ^ 2) := by
  set μ := ∑ p ∈ pairs n, clamp01 (r p.1 p.2) * w p with hμ
  have hfac : ∏ p ∈ pairs n, (clamp01 (r p.1 p.2) * Real.exp (-l * w p) + (1 - clamp01 (r p.1 p.2))) ≤
      Real.exp (-l * μ + l ^ 2 * ∑ p ∈ pairs n, clamp01 (r p.1 p.2) * w p ^ 2) := by
    have : -l * μ + l ^ 2 * ∑ p ∈ pairs n, clamp01 (r p.1 p.2) * w p ^ 2 =
        ∑ p ∈ pairs n, clamp01 (r p.1 p.2) * (-l * w p + (l * w p) ^ 2) := by
      rw [hμ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun p _ => by ring)
    rw [this, Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p _
      have := clamp01_nonneg (r p.1 p.2); have := clamp01_le_one (r p.1 p.2)
      have := Real.exp_pos (-l * w p)
      nlinarith
    · intro p _
      have h1 := clamp01_nonneg (r p.1 p.2)
      have hx : |(-l * w p)| ≤ 1 := by
        rw [abs_le]
        have := hw0 p; have := hw2 p
        constructor <;> nlinarith
      have hb := Real.abs_exp_sub_one_sub_id_le hx
      have hb' : Real.exp (-l * w p) - 1 ≤ -l * w p + (l * w p) ^ 2 := by
        have := (abs_le.1 hb).2
        have e : (-l * w p) ^ 2 = (l * w p) ^ 2 := by ring
        linarith
      calc clamp01 (r p.1 p.2) * Real.exp (-l * w p) + (1 - clamp01 (r p.1 p.2))
          = clamp01 (r p.1 p.2) * (Real.exp (-l * w p) - 1) + 1 := by ring
        _ ≤ clamp01 (r p.1 p.2) * (-l * w p + (l * w p) ^ 2) + 1 := by nlinarith
        _ ≤ Real.exp (clamp01 (r p.1 p.2) * (-l * w p + (l * w p) ^ 2)) := by
            have := Real.add_one_le_exp (clamp01 (r p.1 p.2) * (-l * w p + (l * w p) ^ 2))
            linarith
  clear_value μ
  have step1 : ∀ G : SimpleGraph (Fin n),
      (if ∑ p ∈ pairs n, w p * (if G.Adj p.1 p.2 then (1:ℝ) else 0) < μ - t then (1:ℝ) else 0) ≤
        Real.exp (l * μ - l * t) *
          Real.exp (-l * ∑ p ∈ pairs n, w p * (if G.Adj p.1 p.2 then (1:ℝ) else 0)) := by
    intro G
    rw [← Real.exp_add]
    split_ifs with h
    · apply Real.one_le_exp
      nlinarith
    · exact (Real.exp_pos _).le
  calc ∑ G : SimpleGraph (Fin n), edgeWeight G r *
        (if ∑ p ∈ pairs n, w p * (if G.Adj p.1 p.2 then (1:ℝ) else 0) < μ - t then 1 else 0)
      ≤ ∑ G : SimpleGraph (Fin n), edgeWeight G r * (Real.exp (l * μ - l * t) *
          Real.exp (-l * ∑ p ∈ pairs n, w p * (if G.Adj p.1 p.2 then (1:ℝ) else 0))) := by
        apply Finset.sum_le_sum
        intro G _
        exact mul_le_mul_of_nonneg_left (step1 G) (edgeWeight_nonneg _ _)
    _ = Real.exp (l * μ - l * t) * ∑ G : SimpleGraph (Fin n), edgeWeight G r *
          Real.exp (-l * ∑ p ∈ pairs n, w p * (if G.Adj p.1 p.2 then (1:ℝ) else 0)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun G _ => by ring)
    _ = Real.exp (l * μ - l * t) *
          ∏ p ∈ pairs n, (clamp01 (r p.1 p.2) * Real.exp (-l * w p) + (1 - clamp01 (r p.1 p.2))) := by
        rw [mgf_w r w (-l)]
    _ ≤ Real.exp (l * μ - l * t) *
          Real.exp (-l * μ + l ^ 2 * ∑ p ∈ pairs n, clamp01 (r p.1 p.2) * w p ^ 2) :=
        mul_le_mul_of_nonneg_left hfac (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

section GenV
variable {V : Type*} [Fintype V]

lemma oddComps_le_n (G : SimpleGraph V) (f : V → ℕ) (S T : Finset V) :
    oddComps G f S T ≤ Fintype.card V := by
  unfold oddComps
  refine le_trans (Finset.card_filter_le _ _) ?_
  rw [Finset.card_univ]
  calc Fintype.card (G.induce ((↑(S ∪ T) : Set V)ᶜ)).ConnectedComponent
      ≤ Fintype.card ((↑(S ∪ T) : Set V)ᶜ : Set V) :=
        Fintype.card_le_of_surjective (G.induce ((↑(S ∪ T) : Set V)ᶜ)).connectedComponentMk
          (fun C => SimpleGraph.ConnectedComponent.ind (fun v => ⟨v, rfl⟩) C)
    _ ≤ Fintype.card V := Fintype.card_subtype_le _

lemma oddComps_le_one (G : SimpleGraph V) (f : V → ℕ) (S T : Finset V)
    (h : (G.induce ((↑(S ∪ T) : Set V)ᶜ)).Connected) : oddComps G f S T ≤ 1 := by
  unfold oddComps
  refine le_trans (Finset.card_filter_le _ _) ?_
  rw [Finset.card_univ, Fintype.card_le_one_iff]
  intro C D
  induction C using SimpleGraph.ConnectedComponent.ind with
  | h v =>
    induction D using SimpleGraph.ConnectedComponent.ind with
    | h w => exact SimpleGraph.ConnectedComponent.eq.2 (h.preconnected v w)

lemma conn_of_lt_kappa (G : SimpleGraph V) (U : Finset V)
    (h : U.card < kappa G) : (G.induce ((↑U : Set V)ᶜ)).Connected := by
  by_contra hc
  have : kappa G ≤ U.card := Nat.sInf_le ⟨U, rfl, hc⟩
  omega

end GenV

lemma edgeCount_empty_right {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) :
    edgeCount G X ∅ = 0 := by
  unfold edgeCount
  simp

lemma oddComps_empty {n : ℕ} (G : SimpleGraph (Fin n)) (Dn : ℕ) (hD : Even Dn) :
    oddComps G (fun _ => Dn) ∅ ∅ = 0 := by
  unfold oddComps
  simp only [edgeCount_empty_right, add_zero, Finset.sum_const, smul_eq_mul]
  have : ∀ k : ℕ, ¬ Odd (k * Dn) := fun k => Nat.not_odd_iff_even.2 (hD.mul_left _)
  simp [this]

lemma mu_bound (p n a b D K : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ n) (hDlo : p * n - K ≤ D) (hDhi : D ≤ p * n - K + 2) (h12 : 12 ≤ K)
    (h7 : 7 * K ≤ p * n) :
    K / 4 * (a + b) ≤ p * b * (b - 1) + p * b * (n - a - b) - D * (b - a) := by
  have hE : (p * (n - b) - K) * a + (K - p - 2) * b ≤
      p * b * (b - 1) + p * b * (n - a - b) - D * (b - a) := by
    rcases le_total a b with h | h
    · have h1 : D * (b - a) ≤ (p * n - K + 2) * (b - a) :=
        mul_le_mul_of_nonneg_right hDhi (by linarith)
      have e : p * b * (b - 1) + p * b * (n - a - b) - (p * n - K + 2) * (b - a) =
          (p * (n - b) - K) * a + (K - p - 2) * b + 2 * a := by ring
      linarith
    · have h1 : (p * n - K) * (a - b) ≤ D * (a - b) :=
        mul_le_mul_of_nonneg_right hDlo (by linarith)
      have e : p * b * (b - 1) + p * b * (n - a - b) - (p * n - K) * (b - a) =
          (p * (n - b) - K) * a + (K - p - 2) * b + 2 * b := by ring
      have e2 : D * (b - a) = - (D * (a - b)) := by ring
      have e3 : (p * n - K) * (b - a) = - ((p * n - K) * (a - b)) := by ring
      linarith
  have hK3 : (3 / 4) * K ≤ K - p - 2 := by linarith
  by_cases hc : 2 * K ≤ p * (n - b)
  · have h1 : K * a ≤ (p * (n - b) - K) * a := mul_le_mul_of_nonneg_right (by linarith) ha
    have h2 : (3 / 4) * K * b ≤ (K - p - 2) * b := mul_le_mul_of_nonneg_right hK3 hb
    nlinarith
  · push Not at hc
    have hb5 : 5 * K < p * b := by nlinarith
    have ha2 : p * a ≤ p * (n - b) := mul_le_mul_of_nonneg_left (by linarith) hp0.le
    have hab5 : 5 * a < 2 * b := by
      have : p * (5 * a) < p * (2 * b) := by nlinarith
      exact lt_of_mul_lt_mul_left this hp0.le
    have h1 : -K * a ≤ (p * (n - b) - K) * a := by
      have : 0 ≤ p * (n - b) := by nlinarith
      nlinarith
    have h2 : (3 / 4) * K * b ≤ (K - p - 2) * b := mul_le_mul_of_nonneg_right hK3 hb
    have h3 : 0 ≤ K * (2 * b - 5 * a) := mul_nonneg (by linarith) (by linarith)
    nlinarith

lemma tutte_ok {n : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (G : SimpleGraph (Fin n)) (Dn : ℕ)
    (hDe : Even Dn) (s : ℝ) (hDlo : p * n - 128 * s ≤ Dn) (hDhi : (Dn : ℝ) ≤ p * n - 128 * s + 2)
    (h12 : 12 ≤ 128 * s) (h7 : 7 * (128 * s) ≤ p * n) (hQ : 2 / p ≤ 16 * s)
    (hkappa : p * n / 2 ≤ (kappa G : ℝ))
    (hY : ∀ S T : Finset (Fin n), Disjoint S T → 1 ≤ S.card + T.card →
      p * T.card * (T.card - 1) + p * T.card * (n - S.card - T.card) - 16 * s * (S.card + T.card)
        ≤ Xr G T T + Xr G T (S ∪ T)ᶜ) :
    HasFactor G (fun _ => Dn) := by
  refine (LPCommunity.SBMRecovery.proposition_7 G (fun _ => Dn)).2 (fun S T hd => ?_)
  by_cases h0 : S.card + T.card = 0
  · have hS : S = ∅ := Finset.card_eq_zero.1 (by omega)
    have hT : T = ∅ := Finset.card_eq_zero.1 (by omega)
    subst hS; subst hT
    rw [oddComps_empty G Dn hDe, edgeCount_empty_right]
    simp
  have h1 : 1 ≤ S.card + T.card := by omega
  have hcardU : (S ∪ T).card = S.card + T.card := Finset.card_union_of_disjoint hd
  have hR : ((S ∪ T)ᶜ.card : ℝ) = n - S.card - T.card := by
    rw [Finset.card_compl, Fintype.card_fin, hcardU, Nat.cast_sub (by
      have := Finset.card_le_univ (S ∪ T); rw [hcardU, Fintype.card_fin] at this
      exact this)]
    push_cast; ring
  have habn : (S.card : ℝ) + T.card ≤ n := by
    have := Finset.card_le_univ (S ∪ T)
    rw [hcardU, Fintype.card_fin] at this
    exact_mod_cast this
  -- the odd components
  have hQb : (oddComps G (fun _ => Dn) S T : ℝ) ≤ 16 * s * (S.card + T.card) := by
    have hab1 : (1:ℝ) ≤ S.card + T.card := by exact_mod_cast h1
    by_cases hk : S.card + T.card < kappa G
    · have := oddComps_le_one G (fun _ => Dn) S T (conn_of_lt_kappa G _
        (by convert hk using 1; convert Finset.card_union_of_disjoint hd))
      have : (oddComps G (fun _ => Dn) S T : ℝ) ≤ 1 := by exact_mod_cast this
      nlinarith
    · push Not at hk
      have hk' : (kappa G : ℝ) ≤ S.card + T.card := by
        exact_mod_cast hk
      have := oddComps_le_n G (fun _ => Dn) S T
      rw [Fintype.card_fin] at this
      have hQn : (oddComps G (fun _ => Dn) S T : ℝ) ≤ n := by exact_mod_cast this
      have hn2 : (n : ℝ) ≤ 2 / p * (S.card + T.card) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hp0]
        linarith
      have : 2 / p * ((S.card : ℝ) + T.card) ≤ 16 * s * (S.card + T.card) :=
        mul_le_mul_of_nonneg_right hQ (by positivity)
      linarith
  have hmu := mu_bound p n S.card T.card Dn (128 * s) hp0 hp1.le (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) habn hDlo hDhi h12 h7
  have hYST := hY S T hd h1
  have key : (0:ℝ) ≤ (∑ v ∈ S, ((fun _ => Dn) v : ℝ)) - (∑ v ∈ T, ((fun _ => Dn) v : ℝ)) +
      (∑ v ∈ T, (G.degree v : ℝ)) - (edgeCount G S T : ℝ) - (oddComps G (fun _ => Dn) S T : ℝ) := by
    rw [sum_degree_T G S T hd, edgeCount_disj G S T hd]
    simp only [Finset.sum_const, nsmul_eq_mul]
    nlinarith
  exact_mod_cast key

/-- weights: `2` on pairs inside `T`, `1` on pairs between `T` and `R`. -/
noncomputable def wST {n : ℕ} (T R : Finset (Fin n)) (p : Fin n × Fin n) : ℝ :=
  if p ∈ Pin T then 2 else if p ∈ Spair T R then 1 else 0

lemma Pin_sub {n : ℕ} (T : Finset (Fin n)) : Pin T ⊆ pairs n := Finset.filter_subset _ _

lemma Pin_Spair_disj {n : ℕ} (T R : Finset (Fin n)) (hd : Disjoint T R) (p : Fin n × Fin n)
    (h1 : p ∈ Pin T) : p ∉ Spair T R := by
  simp only [Pin, Spair, Finset.mem_filter] at h1 ⊢
  rintro ⟨_, (⟨_, h⟩ | ⟨h, _⟩)⟩
  · exact Finset.disjoint_left.1 hd h1.2.2 h
  · exact Finset.disjoint_left.1 hd h1.2.1 h

lemma wsum {n : ℕ} (T R : Finset (Fin n)) (hd : Disjoint T R) (k1 k2 : ℝ)
    (g : Fin n × Fin n → ℝ) :
    ∑ p ∈ pairs n, (if p ∈ Pin T then k1 else if p ∈ Spair T R then k2 else 0) * g p =
      k1 * ∑ p ∈ Pin T, g p + k2 * ∑ p ∈ Spair T R, g p := by
  have h : ∀ p, (if p ∈ Pin T then k1 else if p ∈ Spair T R then k2 else 0) * g p =
      (if p ∈ Pin T then k1 * g p else 0) + (if p ∈ Spair T R then k2 * g p else 0) := by
    intro p
    by_cases h1 : p ∈ Pin T
    · rw [if_pos h1, if_pos h1, if_neg (Pin_Spair_disj T R hd p h1)]; ring
    · rw [if_neg h1, if_neg h1]; split_ifs <;> ring
  simp_rw [h]
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
    Finset.inter_eq_right.2 (Pin_sub T), Finset.inter_eq_right.2 (Spair_sub T R),
    Finset.mul_sum, Finset.mul_sum]

lemma ind_eq {P : Prop} (i1 i2 : Decidable P) : @ite ℝ P i1 1 0 = @ite ℝ P i2 1 0 := by
  congr

lemma erProb_eq {n : ℕ} (p : ℝ) (E : SimpleGraph (Fin n) → Prop) [DecidablePred E] :
    erProb n p E = ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) * (if E G then 1 else 0) := by
  unfold erProb
  refine Finset.sum_congr rfl (fun G _ => ?_)
  rw [ind_eq]

set_option maxHeartbeats 1000000 in
/-- the per-`(S, T)` tail bound in the proof of Proposition 4. -/
lemma bad_ST {n : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hn : 3 ≤ n) (S T : Finset (Fin n))
    (hd : Disjoint S T) (h1 : 1 ≤ S.card + T.card) :
    ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) *
      (if Xr G T T + Xr G T (S ∪ T)ᶜ < p * T.card * (T.card - 1) + p * T.card * (n - S.card - T.card)
          - 16 * Real.sqrt (n * Real.log n) * (S.card + T.card) then 1 else 0) ≤
      Real.exp (- (4 * Real.log n * (S.card + T.card))) := by
  set R := (S ∪ T)ᶜ with hRdef
  have hTR : Disjoint T R := by
    rw [hRdef, Finset.disjoint_left]
    intro x hx hx'
    exact Finset.mem_compl.1 hx' (Finset.mem_union_right _ hx)
  have hc : clamp01 p = p := by
    unfold clamp01; rw [min_eq_right hp1.le, max_eq_right hp0.le]
  have hcardU : (S ∪ T).card = S.card + T.card := Finset.card_union_of_disjoint hd
  have hRc : (R.card : ℝ) = n - S.card - T.card := by
    rw [hRdef, Finset.card_compl, Fintype.card_fin, hcardU, Nat.cast_sub (by
      have := Finset.card_le_univ (S ∪ T); rw [hcardU, Fintype.card_fin] at this
      exact this)]
    push_cast; ring
  have hR0 : (0:ℝ) ≤ R.card := Nat.cast_nonneg _
  have hM : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hlog := log_ge_one hn
  set s := Real.sqrt (n * Real.log n) with hsdef
  have hsq : s ^ 2 = n * Real.log n := Real.sq_sqrt (by nlinarith)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hslog : Real.log n ≤ s := by
    rw [hsdef]
    apply Real.le_sqrt_of_sq_le
    have := Real.log_le_self (by linarith : (0:ℝ) ≤ n)
    nlinarith
  set a : ℝ := (S.card : ℝ) with ha
  set b : ℝ := (T.card : ℝ) with hb
  have ha0 : 0 ≤ a := Nat.cast_nonneg _
  have hb0 : 0 ≤ b := Nat.cast_nonneg _
  have hab1 : 1 ≤ a + b := by rw [ha, hb]; exact_mod_cast h1
  have hbn : b ≤ n := by
    have := Finset.card_le_univ T; rw [Fintype.card_fin] at this
    rw [hb]; exact_mod_cast this
  -- the statistic as a weighted pair sum
  have hY : ∀ G : SimpleGraph (Fin n), Xr G T T + Xr G T R =
      ∑ q ∈ pairs n, wST T R q * (if G.Adj q.1 q.2 then (1:ℝ) else 0) := by
    intro G
    unfold wST
    rw [wsum T R hTR 2 1]
    have e1 : Xr G T T = 2 * ∑ q ∈ Pin T, (if G.Adj q.1 q.2 then (1:ℝ) else 0) := by
      unfold Xr
      exact sum_sq_to_Pin T (fun i j => if G.Adj i j then 1 else 0)
        (fun i j => by simp only [G.adj_comm]) (fun i => by simp)
    have e2 : Xr G T R = ∑ q ∈ Spair T R, (if G.Adj q.1 q.2 then (1:ℝ) else 0) := by
      unfold Xr
      exact sum_to_Spair T R hTR (fun i j => if G.Adj i j then 1 else 0)
        (fun i j => by simp only [G.adj_comm])
    rw [e1, e2]; ring
  have hmu : ∑ q ∈ pairs n, clamp01 ((fun _ _ => p) q.1 q.2 : ℝ) * wST T R q =
      p * b * (b - 1) + p * b * (n - a - b) := by
    simp only [hc]
    have : ∀ q, p * wST T R q = wST T R q * p := fun q => by ring
    simp_rw [this]
    unfold wST
    rw [wsum T R hTR 2 1 (fun _ => p)]
    have e1 : 2 * ∑ q ∈ Pin T, p = ∑ i ∈ T, ∑ j ∈ T, (if i = j then 0 else p) := by
      rw [sum_sq_to_Pin T (fun i j => if i = j then 0 else p)
        (fun i j => by by_cases h : i = j <;> simp [h, eq_comm]) (fun i => by simp)]
      congr 1
      refine Finset.sum_congr rfl (fun q hq => ?_)
      simp only [Pin, pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      rw [if_neg hq.1.ne]
    have e2 : ∑ q ∈ Spair T R, p = ∑ i ∈ T, ∑ j ∈ R, p :=
      (sum_to_Spair T R hTR (fun _ _ => p) (fun _ _ => rfl)).symm
    have e3 : ∑ i ∈ T, ∑ j ∈ T, (if i = j then (0:ℝ) else p) = p * b * (b - 1) := by
      have : ∀ i ∈ T, ∑ j ∈ T, (if i = j then (0:ℝ) else p) = p * (b - 1) := by
        intro i hi
        have h2 : ∑ j ∈ T, (if i = j then (0:ℝ) else p) =
            ∑ j ∈ T, p - ∑ j ∈ T, (if i = j then p else 0) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          split_ifs <;> ring
        rw [h2, Finset.sum_ite_eq, if_pos hi, Finset.sum_const, nsmul_eq_mul, hb]; ring
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, hb]; ring
    have e4 : ∑ i ∈ T, ∑ j ∈ R, p = p * b * (n - a - b) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [hRc, hb, ha]; ring
    rw [e1, e2, e3, e4]; ring
  have hV : ∑ q ∈ pairs n, clamp01 ((fun _ _ => p) q.1 q.2 : ℝ) * wST T R q ^ 2 ≤ 3 * n * b := by
    simp only [hc]
    have : ∀ q, p * wST T R q ^ 2 =
        (if q ∈ Pin T then (4:ℝ) else if q ∈ Spair T R then 1 else 0) * p := by
      intro q; unfold wST; split_ifs <;> ring
    simp_rw [this]
    rw [wsum T R hTR 4 1 (fun _ => p)]
    have e1 : 2 * ∑ q ∈ Pin T, p = p * b * (b - 1) := by
      have := sum_sq_to_Pin T (fun i j => if i = j then (0:ℝ) else p)
        (fun i j => by by_cases h : i = j <;> simp [h, eq_comm]) (fun i => by simp)
      have e3 : ∑ i ∈ T, ∑ j ∈ T, (if i = j then (0:ℝ) else p) = p * b * (b - 1) := by
        have : ∀ i ∈ T, ∑ j ∈ T, (if i = j then (0:ℝ) else p) = p * (b - 1) := by
          intro i hi
          have h2 : ∑ j ∈ T, (if i = j then (0:ℝ) else p) =
              ∑ j ∈ T, p - ∑ j ∈ T, (if i = j then p else 0) := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            split_ifs <;> ring
          rw [h2, Finset.sum_ite_eq, if_pos hi, Finset.sum_const, nsmul_eq_mul, hb]; ring
        rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, hb]; ring
      rw [← e3, this]
      congr 1
      refine Finset.sum_congr rfl (fun q hq => ?_)
      simp only [Pin, pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      rw [if_neg hq.1.ne]
    have e2 : ∑ q ∈ Spair T R, p = p * b * (n - a - b) := by
      rw [← sum_to_Spair T R hTR (fun _ _ => p) (fun _ _ => rfl)]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [hRc, hb, ha]; ring
    rw [e2]
    have e1' : 4 * ∑ q ∈ Pin T, p = 2 * (p * b * (b - 1)) := by rw [← e1]; ring
    rw [e1']
    have hb1 : 0 ≤ b * (n - a - b) := by
      apply mul_nonneg hb0; rw [← hRc]; exact hR0
    have h2 : p * b * (b - 1) ≤ b * n := by
      by_cases hbz : b = 0
      · rw [hbz]; simp
      · have : 1 ≤ b := by
          rw [hb] at hbz ⊢
          have : T.card ≠ 0 := by exact_mod_cast hbz
          exact_mod_cast Nat.one_le_iff_ne_zero.2 this
        have hbb : 0 ≤ b * (b - 1) := mul_nonneg hb0 (by linarith)
        have e : p * b * (b - 1) = p * (b * (b - 1)) := by ring
        have h' : p * (b * (b - 1)) ≤ b * (b - 1) := by
          have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - p) hbb
          nlinarith
        have h'' : b * (b - 1) ≤ b * n := mul_le_mul_of_nonneg_left (by linarith) hb0
        linarith
    have h3 : p * b * (n - a - b) ≤ b * n := by
      have hX : 0 ≤ b * (n - a - b) := hb1
      have e : p * b * (n - a - b) = p * (b * (n - a - b)) := by ring
      have h' : p * (b * (n - a - b)) ≤ b * (n - a - b) := by
        have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - p) hX
        nlinarith
      have h'' : b * (n - a - b) ≤ b * n := mul_le_mul_of_nonneg_left (by linarith) hb0
      linarith
    nlinarith [h2, h3]
  have hw0 : ∀ q, 0 ≤ wST T R q := fun q => by unfold wST; split_ifs <;> norm_num
  have hw2 : ∀ q, wST T R q ≤ 2 := fun q => by unfold wST; split_ifs <;> norm_num
  set t := 16 * s * (a + b) with ht
  have ht0 : 0 < t := by
    have : 1 ≤ s := le_trans hlog hslog
    positivity
  -- reduce to the weighted tail
  have hred : ∀ l : ℝ, 0 ≤ l → l ≤ 1 / 2 →
      ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) *
        (if Xr G T T + Xr G T R < p * b * (b - 1) + p * b * (n - a - b) - t then 1 else 0) ≤
        Real.exp (- l * t + l ^ 2 * (3 * n * b)) := by
    intro l hl0 hl1
    calc _ = ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) *
          (if ∑ q ∈ pairs n, wST T R q * (if G.Adj q.1 q.2 then (1:ℝ) else 0) <
            ∑ q ∈ pairs n, clamp01 ((fun _ _ => p) q.1 q.2 : ℝ) * wST T R q - t then 1 else 0) := by
          refine Finset.sum_congr rfl (fun G _ => ?_)
          rw [hY G, hmu]
      _ ≤ Real.exp (- l * t + l ^ 2 *
            ∑ q ∈ pairs n, clamp01 ((fun _ _ => p) q.1 q.2 : ℝ) * wST T R q ^ 2) :=
          wtail (fun _ _ => p) (wST T R) hw0 hw2 t l hl0 hl1
      _ ≤ Real.exp (- l * t + l ^ 2 * (3 * n * b)) := by
          apply Real.exp_le_exp.2
          have := mul_le_mul_of_nonneg_left hV (sq_nonneg l)
          linarith
  have hlogn0 : 0 ≤ Real.log n := by linarith
  by_cases hcase : t ≤ 3 * n * b
  · have hbpos : 0 < b := by
      by_contra hb'
      push Not at hb'
      have : b = 0 := le_antisymm hb' hb0
      rw [this] at hcase
      linarith
    have hnb : 0 < 3 * n * b := by positivity
    set l := t / (2 * (3 * n * b)) with hl
    have hl0 : 0 ≤ l := by positivity
    have hl1 : l ≤ 1 / 2 := by
      rw [hl, div_le_iff₀ (by positivity)]; linarith
    refine le_trans (hred l hl0 hl1) (Real.exp_le_exp.2 ?_)
    have e : - l * t + l ^ 2 * (3 * n * b) = - t ^ 2 / (4 * (3 * n * b)) := by
      rw [hl]; field_simp; ring
    rw [e]
    have ht2 : t ^ 2 = 256 * (n * Real.log n) * (a + b) ^ 2 := by
      rw [ht, mul_pow, mul_pow, hsq]; ring
    rw [ht2, neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
    have hbab : b ≤ a + b := by linarith
    have : 0 ≤ (n:ℝ) * Real.log n := by positivity
    have h5 : 48 * (n * Real.log n) * b * (a + b) ≤ 256 * (n * Real.log n) * (a + b) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hbab (by positivity : (0:ℝ) ≤ 48 * (n * Real.log n) * (a + b))
      nlinarith
    nlinarith
  · push Not at hcase
    refine le_trans (hred (1 / 2) (by norm_num) (le_refl _)) (Real.exp_le_exp.2 ?_)
    have : 4 * Real.log n * (a + b) ≤ 4 * s * (a + b) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith

lemma erProb_compl {n : ℕ} (p : ℝ) (E : SimpleGraph (Fin n) → Prop) :
    erProb n p E + erProb n p (fun G => ¬ E G) = 1 := by
  unfold erProb
  rw [← Finset.sum_add_distrib]
  refine (Finset.sum_congr rfl (fun G _ => ?_)).trans (edgeWeight_sum (fun _ _ => p))
  by_cases h : E G <;> simp [h]

lemma erProb_nonneg {n : ℕ} (p : ℝ) (E : SimpleGraph (Fin n) → Prop) : 0 ≤ erProb n p E :=
  Finset.sum_nonneg (fun G _ => mul_nonneg (edgeWeight_nonneg _ _) (by split_ifs <;> norm_num))

lemma erProb_mono {n : ℕ} (p : ℝ) (E F : SimpleGraph (Fin n) → Prop) (h : ∀ G, E G → F G) :
    erProb n p E ≤ erProb n p F := by
  unfold erProb
  apply Finset.sum_le_sum
  intro G _
  apply mul_le_mul_of_nonneg_left _ (edgeWeight_nonneg _ _)
  by_cases hE : E G
  · rw [if_pos hE, if_pos (h G hE)]
  · rw [if_neg hE]; split_ifs <;> norm_num

lemma erProb_or_le {n : ℕ} (p : ℝ) (E F : SimpleGraph (Fin n) → Prop) :
    erProb n p (fun G => E G ∨ F G) ≤ erProb n p E + erProb n p F := by
  unfold erProb
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro G _
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (edgeWeight_nonneg _ _)
  by_cases hE : E G <;> by_cases hF : F G <;> simp [hE, hF]

lemma er_and_tendsto (p : ℝ) (E F : (n : ℕ) → SimpleGraph (Fin n) → Prop)
    (hE : Tendsto (fun n => erProb n p (E n)) atTop (𝓝 1))
    (hF : Tendsto (fun n => erProb n p (F n)) atTop (𝓝 1)) :
    Tendsto (fun n => erProb n p (fun G => E n G ∧ F n G)) atTop (𝓝 1) := by
  have key : ∀ n, erProb n p (E n) + erProb n p (F n) - 1 ≤ erProb n p (fun G => E n G ∧ F n G) := by
    intro n
    have h1 := erProb_compl p (E n)
    have h2 := erProb_compl p (F n)
    have h3 := erProb_compl p (fun G => E n G ∧ F n G)
    have h4 := erProb_or_le p (fun G => ¬ E n G) (fun G => ¬ F n G)
    have h5 : erProb n p (fun G => ¬ (E n G ∧ F n G)) ≤ erProb n p (fun G => ¬ E n G ∨ ¬ F n G) :=
      erProb_mono p _ _ (fun G h => by tauto)
    linarith
  have hle : ∀ n, erProb n p (fun G => E n G ∧ F n G) ≤ 1 := by
    intro n
    have := erProb_compl p (fun G => E n G ∧ F n G)
    have := erProb_nonneg p (fun G => ¬ (E n G ∧ F n G))
    linarith
  have hlow : Tendsto (fun n => erProb n p (E n) + erProb n p (F n) - 1) atTop (𝓝 1) := by
    have := (hE.add hF).sub_const 1
    norm_num at this
    exact this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds key hle

lemma poly_bound3 (n : ℕ) (hn : 3 ≤ n) :
    ((n : ℝ) + 1) ^ 2 * Real.exp (- (3 * Real.log n)) ≤ 4 / n := by
  have hn' : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hm0 : (0:ℝ) < n := by linarith
  have h3 : Real.exp (3 * Real.log n) = (n : ℝ) ^ 3 := by
    have := pow_eq_exp n 3 (by omega)
    push_cast at this
    rw [this]
  rw [Real.exp_neg, h3, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) hm0]
  have h1 : ((n : ℝ) + 1) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by nlinarith
  have h4 : ((n : ℝ) + 1) ^ 2 * n ≤ 4 * (n : ℝ) ^ 2 * n := mul_le_mul_of_nonneg_right h1 hm0.le
  nlinarith

end LP5Deg

open LP5Deg LPCommunity.SBMRecovery in
set_option maxHeartbeats 1000000 in
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ, 0 < p → p < 1 →
      Tendsto (fun n : ℕ => erProb n p (fun G =>
        ∃ H : SimpleGraph (Fin n), H ≤ G ∧
          ∀ v, (H.degree v : ℤ) = 2 * ⌈(p * n - C * Real.sqrt (n * Real.log n)) / 2⌉))
        atTop (𝓝 1) := by
  refine ⟨128, by norm_num, fun p hp0 hp1 => ?_⟩
  obtain ⟨C8, hC8, h8⟩ := LPCommunity.SBMRecovery.proposition_8 p hp0 hp1
  have h9 := LPCommunity.SBMRecovery.proposition_9 p hp0 hp1
  have hA := er_and_tendsto p (fun n G => kappa G = dMin G)
    (fun n G => (dMin G : ℝ) ≥ p * n - C8 * Real.sqrt (n * Real.log n)) h9 h8
  have key : ∀ᶠ n : ℕ in atTop,
      erProb n p (fun G => ¬ ∃ H : SimpleGraph (Fin n), H ≤ G ∧
          ∀ v, (H.degree v : ℤ) = 2 * ⌈(p * n - 128 * Real.sqrt (n * Real.log n)) / 2⌉) ≤
        erProb n p (fun G => ¬ (kappa G = dMin G ∧
          (dMin G : ℝ) ≥ p * n - C8 * Real.sqrt (n * Real.log n))) + 4 / n := by
    filter_upwards [eventually_ge_atTop 3, eventually_ge_atTop ⌈4 / p ^ 2⌉₊,
      sqrt_small (p / 896) (by positivity), sqrt_small (p / (2 * C8)) (by positivity)]
      with n hn3 hn4 hs7 hsC
    have hM : (3:ℝ) ≤ n := by exact_mod_cast hn3
    have hlog := log_ge_one hn3
    set s := Real.sqrt (n * Real.log n) with hsdef
    have hsq : s ^ 2 = n * Real.log n := Real.sq_sqrt (by nlinarith)
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs1 : 1 ≤ s := Real.one_le_sqrt.2 (by nlinarith)
    have hn4' : 4 / p ^ 2 ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn4)
    have hs2p : 2 / p ≤ s := by
      rw [hsdef]
      apply Real.le_sqrt_of_sq_le
      have : (2 / p) ^ 2 = 4 / p ^ 2 := by ring
      rw [this]
      nlinarith
    set x := p * n - 128 * s with hx
    have hx0 : 0 < x := by
      have : 896 * s ≤ p * n := by nlinarith
      have : 0 < p * n := by positivity
      linarith
    set k : ℤ := ⌈x / 2⌉ with hk
    have hk0 : 0 ≤ k := Int.ceil_nonneg (by positivity)
    set Dn : ℕ := 2 * k.toNat with hDn
    have hDnk : (Dn : ℤ) = 2 * k := by rw [hDn]; push_cast; rw [Int.toNat_of_nonneg hk0]
    have hDnR : (Dn : ℝ) = 2 * (k : ℝ) := by exact_mod_cast hDnk
    have hDlo : p * n - 128 * s ≤ (Dn : ℝ) := by
      rw [hDnR]; have := Int.le_ceil (x / 2); linarith
    have hDhi : (Dn : ℝ) ≤ p * n - 128 * s + 2 := by
      rw [hDnR]; have := Int.ceil_lt_add_one (x / 2); linarith
    have hDe : Even Dn := ⟨k.toNat, by rw [hDn]; ring⟩
    -- per-graph inequality
    set h : ℕ → ℕ → ℝ := fun a b => if 1 ≤ a + b then
        Real.exp (- (4 * Real.log n * ((a : ℝ) + b))) else 0 with hhdef
    have hper : ∀ G : SimpleGraph (Fin n),
        edgeWeight G (fun _ _ => p) * (if ¬ ∃ H : SimpleGraph (Fin n), H ≤ G ∧
          ∀ v, (H.degree v : ℤ) = 2 * k then 1 else 0) ≤
        edgeWeight G (fun _ _ => p) * (if ¬ (kappa G = dMin G ∧
          (dMin G : ℝ) ≥ p * n - C8 * s) then 1 else 0) +
        ∑ S ∈ (univ : Finset (Fin n)).powerset, ∑ T ∈ (univ : Finset (Fin n)).powerset,
          edgeWeight G (fun _ _ => p) * (if Disjoint S T ∧ 1 ≤ S.card + T.card ∧
            Xr G T T + Xr G T (S ∪ T)ᶜ < p * T.card * (T.card - 1) +
              p * T.card * (n - S.card - T.card) - 16 * s * (S.card + T.card) then 1 else 0) := by
      intro G
      have hw0 := edgeWeight_nonneg G (fun _ _ => p)
      have hR0 : 0 ≤ ∑ S ∈ (univ : Finset (Fin n)).powerset, ∑ T ∈ (univ : Finset (Fin n)).powerset,
          edgeWeight G (fun _ _ => p) * (if Disjoint S T ∧ 1 ≤ S.card + T.card ∧
            Xr G T T + Xr G T (S ∪ T)ᶜ < p * T.card * (T.card - 1) +
              p * T.card * (n - S.card - T.card) - 16 * s * (S.card + T.card) then (1:ℝ) else 0) :=
        Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
          mul_nonneg hw0 (by split_ifs <;> norm_num)))
      by_cases hE : ∃ H : SimpleGraph (Fin n), H ≤ G ∧ ∀ v, (H.degree v : ℤ) = 2 * k
      · rw [if_neg (not_not.2 hE), mul_zero]
        have : 0 ≤ edgeWeight G (fun _ _ => p) * (if ¬ (kappa G = dMin G ∧
            (dMin G : ℝ) ≥ p * n - C8 * s) then (1:ℝ) else 0) :=
          mul_nonneg hw0 (by split_ifs <;> norm_num)
        linarith
      rw [if_pos hE, mul_one]
      by_cases hAc : kappa G = dMin G ∧ (dMin G : ℝ) ≥ p * n - C8 * s
      · -- some (S, T) must be bad
        have hbad : ∃ S T : Finset (Fin n), Disjoint S T ∧ 1 ≤ S.card + T.card ∧
            Xr G T T + Xr G T (S ∪ T)ᶜ < p * T.card * (T.card - 1) +
              p * T.card * (n - S.card - T.card) - 16 * s * (S.card + T.card) := by
          by_contra hno
          push Not at hno
          apply hE
          have hkap : p * n / 2 ≤ (kappa G : ℝ) := by
            rw [hAc.1]
            have : C8 * s ≤ p * n / 2 := by
              have := mul_le_mul_of_nonneg_left hsC hC8.le
              have e : C8 * (p / (2 * C8) * n) = p * n / 2 := by field_simp
              linarith
            linarith [hAc.2]
          have hfac := tutte_ok p hp0 hp1 G Dn hDe s hDlo hDhi (by linarith) (by nlinarith)
            (by linarith) hkap (fun S T hd h1 => hno S T hd h1)
          obtain ⟨F, hFG, hFd⟩ := hfac
          exact ⟨F, hFG, fun v => by rw [hFd v, hDnk]⟩
        obtain ⟨S, T, hST⟩ := hbad
        have : edgeWeight G (fun _ _ => p) ≤
            ∑ S ∈ (univ : Finset (Fin n)).powerset, ∑ T ∈ (univ : Finset (Fin n)).powerset,
            edgeWeight G (fun _ _ => p) * (if Disjoint S T ∧ 1 ≤ S.card + T.card ∧
              Xr G T T + Xr G T (S ∪ T)ᶜ < p * T.card * (T.card - 1) +
                p * T.card * (n - S.card - T.card) - 16 * s * (S.card + T.card) then (1:ℝ) else 0) := by
          calc edgeWeight G (fun _ _ => p) = edgeWeight G (fun _ _ => p) *
              (if Disjoint S T ∧ 1 ≤ S.card + T.card ∧
                Xr G T T + Xr G T (S ∪ T)ᶜ < p * T.card * (T.card - 1) +
                  p * T.card * (n - S.card - T.card) - 16 * s * (S.card + T.card) then (1:ℝ) else 0) := by
                rw [if_pos hST, mul_one]
            _ ≤ ∑ T' ∈ (univ : Finset (Fin n)).powerset, edgeWeight G (fun _ _ => p) *
              (if Disjoint S T' ∧ 1 ≤ S.card + T'.card ∧
                Xr G T' T' + Xr G T' (S ∪ T')ᶜ < p * T'.card * (T'.card - 1) +
                  p * T'.card * (n - S.card - T'.card) - 16 * s * (S.card + T'.card)
                then (1:ℝ) else 0) :=
                Finset.single_le_sum (f := fun T' => edgeWeight G (fun _ _ => p) *
                  (if Disjoint S T' ∧ 1 ≤ S.card + T'.card ∧
                    Xr G T' T' + Xr G T' (S ∪ T')ᶜ < p * T'.card * (T'.card - 1) +
                      p * T'.card * (n - S.card - T'.card) - 16 * s * (S.card + T'.card)
                    then (1:ℝ) else 0))
                  (fun _ _ => mul_nonneg hw0 (by split_ifs <;> norm_num))
                  (Finset.mem_powerset.2 (Finset.subset_univ T))
            _ ≤ _ := Finset.single_le_sum (f := fun S' =>
                  ∑ T' ∈ (univ : Finset (Fin n)).powerset, edgeWeight G (fun _ _ => p) *
                  (if Disjoint S' T' ∧ 1 ≤ S'.card + T'.card ∧
                    Xr G T' T' + Xr G T' (S' ∪ T')ᶜ < p * T'.card * (T'.card - 1) +
                      p * T'.card * (n - S'.card - T'.card) - 16 * s * (S'.card + T'.card)
                    then (1:ℝ) else 0))
                  (fun _ _ => Finset.sum_nonneg (fun _ _ => mul_nonneg hw0 (by split_ifs <;> norm_num)))
                  (Finset.mem_powerset.2 (Finset.subset_univ S))
        have : 0 ≤ edgeWeight G (fun _ _ => p) * (if ¬ (kappa G = dMin G ∧
            (dMin G : ℝ) ≥ p * n - C8 * s) then (1:ℝ) else 0) :=
          mul_nonneg hw0 (by split_ifs <;> norm_num)
        linarith
      · rw [if_pos hAc, mul_one]
        linarith
    -- per-(S, T) bounds
    have hST : ∀ S ∈ (univ : Finset (Fin n)).powerset, ∀ T ∈ (univ : Finset (Fin n)).powerset,
        ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) * (if Disjoint S T ∧ 1 ≤ S.card + T.card ∧
            Xr G T T + Xr G T (S ∪ T)ᶜ < p * T.card * (T.card - 1) +
              p * T.card * (n - S.card - T.card) - 16 * s * (S.card + T.card) then 1 else 0)
          ≤ h S.card T.card := by
      intro S _ T _
      by_cases hc : Disjoint S T ∧ 1 ≤ S.card + T.card
      · simp only [hhdef, if_pos hc.2]
        refine le_trans ?_ (bad_ST p hp0 hp1 hn3 S T hc.1 hc.2)
        apply Finset.sum_le_sum
        intro G _
        apply mul_le_mul_of_nonneg_left _ (edgeWeight_nonneg _ _)
        by_cases hb : Xr G T T + Xr G T (S ∪ T)ᶜ < p * T.card * (T.card - 1) +
              p * T.card * (n - S.card - T.card) - 16 * s * (S.card + T.card)
        · rw [if_pos ⟨hc.1, hc.2, hb⟩, if_pos hb]
        · rw [if_neg (fun h' => hb h'.2.2)]; split_ifs <;> norm_num
      · have : ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) * (if Disjoint S T ∧
            1 ≤ S.card + T.card ∧ Xr G T T + Xr G T (S ∪ T)ᶜ < p * T.card * (T.card - 1) +
              p * T.card * (n - S.card - T.card) - 16 * s * (S.card + T.card) then (1:ℝ) else 0) = 0 :=
          Finset.sum_eq_zero (fun G _ => by rw [if_neg (fun h' => hc ⟨h'.1, h'.2.1⟩), mul_zero])
        rw [this]
        simp only [hhdef]
        split_ifs <;> [exact (Real.exp_pos _).le; exact le_refl _]
    -- the counting sum
    have hcount : ∑ S ∈ (univ : Finset (Fin n)).powerset, ∑ T ∈ (univ : Finset (Fin n)).powerset,
        h S.card T.card ≤ 4 / n := by
      have e1 : ∀ S : Finset (Fin n), ∑ T ∈ (univ : Finset (Fin n)).powerset, h S.card T.card =
          ∑ b ∈ range (n + 1), (n.choose b : ℝ) * h S.card b := by
        intro S
        rw [Finset.sum_powerset_apply_card (f := fun b => h S.card b), Finset.card_univ,
          Fintype.card_fin]
        simp only [nsmul_eq_mul]
      simp_rw [e1]
      rw [Finset.sum_powerset_apply_card (f := fun a => ∑ b ∈ range (n + 1), (n.choose b : ℝ) * h a b),
        Finset.card_univ, Fintype.card_fin]
      simp only [nsmul_eq_mul, Finset.mul_sum]
      have hterm : ∀ a ∈ range (n + 1), ∀ b ∈ range (n + 1),
          (n.choose a : ℝ) * ((n.choose b : ℝ) * h a b) ≤ Real.exp (- (3 * Real.log n)) := by
        intro a _ b _
        simp only [hhdef]
        split_ifs with hab
        · have hch : (n.choose a : ℝ) * n.choose b ≤ Real.exp (((a + b : ℕ) : ℝ) * Real.log n) := by
            rw [← pow_eq_exp n _ (by omega), pow_add]
            exact mul_le_mul (by exact_mod_cast Nat.choose_le_pow n a)
              (by exact_mod_cast Nat.choose_le_pow n b) (by positivity) (by positivity)
          have hab' : (1:ℝ) ≤ (a : ℝ) + b := by exact_mod_cast hab
          calc (n.choose a : ℝ) * ((n.choose b : ℝ) * Real.exp (- (4 * Real.log n * ((a : ℝ) + b))))
              = ((n.choose a : ℝ) * n.choose b) * Real.exp (- (4 * Real.log n * ((a : ℝ) + b))) := by
                ring
            _ ≤ Real.exp (((a + b : ℕ) : ℝ) * Real.log n) *
                Real.exp (- (4 * Real.log n * ((a : ℝ) + b))) :=
                mul_le_mul_of_nonneg_right hch (Real.exp_pos _).le
            _ = Real.exp (- (3 * Real.log n * ((a : ℝ) + b))) := by
                rw [← Real.exp_add]; congr 1; push_cast; ring
            _ ≤ Real.exp (- (3 * Real.log n)) := by
                apply Real.exp_le_exp.2
                have : 0 ≤ 3 * Real.log n * ((a : ℝ) + b - 1) := by
                  apply mul_nonneg (by linarith) (by linarith)
                nlinarith
        · rw [mul_zero, mul_zero]; exact (Real.exp_pos _).le
      calc ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), (n.choose a : ℝ) * ((n.choose b : ℝ) * h a b)
          ≤ ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), Real.exp (- (3 * Real.log n)) :=
            Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => hterm a ha b hb))
        _ = ((n : ℝ) + 1) ^ 2 * Real.exp (- (3 * Real.log n)) := by
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast; ring
        _ ≤ 4 / n := poly_bound3 n hn3
    -- assemble
    calc erProb n p (fun G => ¬ ∃ H : SimpleGraph (Fin n), H ≤ G ∧
          ∀ v, (H.degree v : ℤ) = 2 * ⌈(p * n - 128 * s) / 2⌉)
        = ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) * (if ¬ ∃ H : SimpleGraph (Fin n), H ≤ G ∧
          ∀ v, (H.degree v : ℤ) = 2 * k then 1 else 0) := erProb_eq p _
      _ ≤ ∑ G : SimpleGraph (Fin n), (edgeWeight G (fun _ _ => p) * (if ¬ (kappa G = dMin G ∧
          (dMin G : ℝ) ≥ p * n - C8 * s) then 1 else 0) +
          ∑ S ∈ (univ : Finset (Fin n)).powerset, ∑ T ∈ (univ : Finset (Fin n)).powerset,
          edgeWeight G (fun _ _ => p) * (if Disjoint S T ∧ 1 ≤ S.card + T.card ∧
            Xr G T T + Xr G T (S ∪ T)ᶜ < p * T.card * (T.card - 1) +
              p * T.card * (n - S.card - T.card) - 16 * s * (S.card + T.card) then 1 else 0)) :=
          Finset.sum_le_sum (fun G _ => hper G)
      _ = ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) * (if ¬ (kappa G = dMin G ∧
          (dMin G : ℝ) ≥ p * n - C8 * s) then 1 else 0) +
          ∑ S ∈ (univ : Finset (Fin n)).powerset, ∑ T ∈ (univ : Finset (Fin n)).powerset,
          ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) * (if Disjoint S T ∧ 1 ≤ S.card + T.card ∧
            Xr G T T + Xr G T (S ∪ T)ᶜ < p * T.card * (T.card - 1) +
              p * T.card * (n - S.card - T.card) - 16 * s * (S.card + T.card) then 1 else 0) := by
          rw [Finset.sum_add_distrib, add_right_inj, Finset.sum_comm]
          exact Finset.sum_congr rfl (fun S _ => Finset.sum_comm)
      _ ≤ ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) * (if ¬ (kappa G = dMin G ∧
          (dMin G : ℝ) ≥ p * n - C8 * s) then 1 else 0) + 4 / n := by
          refine add_le_add (le_refl _) (le_trans ?_ hcount)
          exact Finset.sum_le_sum (fun S hS => Finset.sum_le_sum (fun T hT => hST S hS T hT))
      _ = erProb n p (fun G => ¬ (kappa G = dMin G ∧
          (dMin G : ℝ) ≥ p * n - C8 * s)) + 4 / n := by
          rw [erProb_eq p (fun G => ¬ (kappa G = dMin G ∧ (dMin G : ℝ) ≥ p * n - C8 * s))]
  -- conclusion
  have hlow : Tendsto (fun n : ℕ => erProb n p (fun G => kappa G = dMin G ∧
      (dMin G : ℝ) ≥ p * n - C8 * Real.sqrt (n * Real.log n)) - 4 / n) atTop (𝓝 1) := by
    simpa using hA.sub (tendsto_const_div_atTop_nhds_zero_nat 4)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [key] with n hn
    have h1 := erProb_compl p (fun G => ∃ H : SimpleGraph (Fin n), H ≤ G ∧
      ∀ v, (H.degree v : ℤ) = 2 * ⌈(p * n - 128 * Real.sqrt (n * Real.log n)) / 2⌉)
    have h2 := erProb_compl (n := n) p (fun G => kappa G = dMin G ∧
      (dMin G : ℝ) ≥ p * n - C8 * Real.sqrt (n * Real.log n))
    linarith
  · filter_upwards with n
    have h1 := erProb_compl p (fun G => ∃ H : SimpleGraph (Fin n), H ≤ G ∧
      ∀ v, (H.degree v : ℤ) = 2 * ⌈(p * n - 128 * Real.sqrt (n * Real.log n)) / 2⌉)
    have h2 := erProb_nonneg p (fun G => ¬ ∃ H : SimpleGraph (Fin n), H ≤ G ∧
      ∀ v, (H.degree v : ℤ) = 2 * ⌈(p * n - 128 * Real.sqrt (n * Real.log n)) / 2⌉)
    linarith
