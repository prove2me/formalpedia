-- Prove2me | solution 1 for LPCommunity.SBMRecovery.proposition_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T11:41:25.01339+00:00
-- url     : https://prove2.me/submissions/ae4ed04c-301e-4042-8df3-c6520f75b199

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_LPCommunity_MinBisect_Setting
import Definitions.Def_LPCommunity_SBMRecovery_Factors

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


section Blocks
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sum_W_indicator {κ : Type*} [Fintype κ] [DecidableEq κ] (a : ι → ℝ) (φ : κ ↪ ι) (y : κ → Bool) :
    ∑ x : ι → Bool, W a x * (if x ∘ φ = y then 1 else 0) = W (a ∘ φ) y := by
  set ψ : ι → Bool → ℝ := fun i b =>
    if h : ∃ k, φ k = i then (if b = y h.choose then 1 else 0) else 1 with hψ
  have hprod : ∀ x : ι → Bool, (if x ∘ φ = y then (1:ℝ) else 0) = ∏ i, ψ i (x i) := by
    intro x
    split_ifs with hxy
    · symm
      apply Finset.prod_eq_one
      intro i _
      by_cases h : ∃ k, φ k = i
      · have hx : x i = y h.choose := by
          rw [← hxy]; simp [h.choose_spec]
        simp [hψ, dif_pos h, hx]
      · simp [hψ, dif_neg h]
    · symm
      have : ∃ k, x (φ k) ≠ y k := by
        by_contra hc
        push_neg at hc
        exact hxy (funext hc)
      obtain ⟨k, hk⟩ := this
      apply Finset.prod_eq_zero (Finset.mem_univ (φ k))
      have h : ∃ k', φ k' = φ k := ⟨k, rfl⟩
      have hc : h.choose = k := φ.injective h.choose_spec
      simp only [hψ, dif_pos h]
      rw [if_neg]
      rw [hc]; exact hk
  simp_rw [hprod]
  rw [sum_W_mul_prod]
  unfold W
  rw [← Finset.prod_subset (Finset.subset_univ (univ.map φ))]
  · rw [Finset.prod_map]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    have h : ∃ k', φ k' = φ k := ⟨k, rfl⟩
    have hc : h.choose = k := φ.injective h.choose_spec
    simp only [hψ, dif_pos h, hc, Function.comp_apply]
    cases y k <;> simp
  · intro i _ hi
    have h : ¬ ∃ k, φ k = i := by
      rintro ⟨k, rfl⟩
      exact hi (Finset.mem_map_of_mem _ (mem_univ k))
    simp [hψ, dif_neg h]

lemma sum_W_comp {κ : Type*} [Fintype κ] [DecidableEq κ] (a : ι → ℝ) (φ : κ ↪ ι) (F : (κ → Bool) → ℝ) :
    ∑ x : ι → Bool, W a x * F (x ∘ φ) = ∑ y : κ → Bool, W (a ∘ φ) y * F y := by
  have hF : ∀ x : ι → Bool, F (x ∘ φ) = ∑ y, (if x ∘ φ = y then 1 else 0) * F y := by
    intro x
    simp
  simp_rw [hF, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [← sum_W_indicator a φ y, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x _ => by ring)


lemma sum_W_blocks {J : Type*} [Fintype J] [DecidableEq J] (a : ι → ℝ) (α β : J → ι)
    (hinj : Function.Injective (Sum.elim α β)) (g : J → Bool → Bool → ℝ) :
    ∑ x : ι → Bool, W a x * ∏ j, g j (x (α j)) (x (β j)) =
      ∏ j, ∑ b1 : Bool, ∑ b2 : Bool, (if b1 then a (α j) else 1 - a (α j)) *
        (if b2 then a (β j) else 1 - a (β j)) * g j b1 b2 := by
  let φ : J ⊕ J ↪ ι := ⟨Sum.elim α β, hinj⟩
  change ∑ x : ι → Bool, W a x * (fun y : J ⊕ J → Bool => ∏ j, g j (y (Sum.inl j)) (y (Sum.inr j)))
    (x ∘ φ) = _
  rw [sum_W_comp a φ (fun y : J ⊕ J → Bool => ∏ j, g j (y (Sum.inl j)) (y (Sum.inr j)))]
  set h : J → Bool → Bool → ℝ := fun j b1 b2 => (if b1 then a (α j) else 1 - a (α j)) *
        (if b2 then a (β j) else 1 - a (β j)) * g j b1 b2 with hh
  have h2 : ∀ y : J ⊕ J → Bool, W (a ∘ φ) y * ∏ j, g j (y (Sum.inl j)) (y (Sum.inr j)) =
      ∏ j, h j (y (Sum.inl j)) (y (Sum.inr j)) := by
    intro y
    unfold W
    rw [Fintype.prod_sum_type, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    simp only [hh, Function.comp_apply, φ, Function.Embedding.coeFn_mk, Sum.elim_inl, Sum.elim_inr]
  simp_rw [h2]
  refine (Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow J J Bool) _
    (fun z => ∏ j, h j (z.1 j) (z.2 j)) (fun x => rfl)).trans ?_
  rw [Fintype.sum_prod_type]
  have h3 : ∀ y1 : J → Bool, ∑ y2 : J → Bool, ∏ j, h j (y1 j) (y2 j) = ∏ j, ∑ b2 : Bool, h j (y1 j) b2 := by
    intro y1
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp_rw [h3]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

end Blocks

/-- the pair `{i, j}` written increasingly. -/
def prr {n : ℕ} (i j : Fin n) : Fin n × Fin n := (min i j, max i j)

lemma prr_mem {n : ℕ} (i j : Fin n) (h : i ≠ j) : prr i j ∈ pairs n := by
  simp only [prr, pairs, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases lt_or_gt_of_ne h with h' | h'
  · rw [min_eq_left h'.le, max_eq_right h'.le]; exact h'
  · rw [min_eq_right h'.le, max_eq_left h'.le]; exact h'

lemma adj_iff_prr {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n) :
    G.Adj i j ↔ G.Adj (prr i j).1 (prr i j).2 := by
  simp only [prr]
  rcases le_total i j with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, G.adj_comm]

/-- codegree. -/
noncomputable def codeg {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) : ℕ :=
  (G.neighborFinset u ∩ G.neighborFinset v).card

lemma codeg_eq_sum {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    (codeg G u v : ℝ) = ∑ w : {w : Fin n // w ≠ u ∧ w ≠ v},
      (if G.Adj u w.1 then (1:ℝ) else 0) * (if G.Adj v w.1 then 1 else 0) := by
  unfold codeg
  have h1 : G.neighborFinset u ∩ G.neighborFinset v = univ.filter (fun w => G.Adj u w ∧ G.Adj v w) := by
    ext w; simp [SimpleGraph.mem_neighborFinset]
  rw [h1, Finset.card_filter]
  push_cast
  rw [← Fintype.sum_subtype_add_sum_subtype (fun w : Fin n => w ≠ u ∧ w ≠ v)]
  have h2 : ∑ w : {w : Fin n // ¬ (w ≠ u ∧ w ≠ v)},
      (if G.Adj u w.1 ∧ G.Adj v w.1 then (1:ℝ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro w _
    have := w.2
    rw [if_neg]
    rintro ⟨h1, h2⟩
    push Not at this
    by_cases hu : w.1 = u
    · rw [hu] at h1; exact G.loopless.irrefl _ h1
    · have := this hu; rw [this] at h2; exact G.loopless.irrefl _ h2
  rw [h2, add_zero]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases h1 : G.Adj u w.1 <;> by_cases h2 : G.Adj v w.1 <;> simp [h1, h2]

/-- the mgf of a codegree. -/
lemma mgf_codeg {n : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (u v : Fin n) (huv : u ≠ v) (s : ℝ) :
    ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) * Real.exp (s * codeg G u v) =
      (1 - p ^ 2 + p ^ 2 * Real.exp s) ^ (n - 2) := by
  have hc : clamp01 p = p := by
    unfold clamp01; rw [min_eq_right hp1.le, max_eq_right hp0.le]
  set J := {w : Fin n // w ≠ u ∧ w ≠ v}
  let α : J → {q : Fin n × Fin n // q ∈ pairs n} := fun w => ⟨prr u w.1, prr_mem u w.1 (Ne.symm w.2.1)⟩
  let β : J → {q : Fin n × Fin n // q ∈ pairs n} := fun w => ⟨prr v w.1, prr_mem v w.1 (Ne.symm w.2.2)⟩
  have hinj : Function.Injective (Sum.elim α β) := by
    have key : ∀ a b c d : Fin n, prr a b = prr c d → (a : ℕ) + b = c + d := by
      intro a b c d h
      simp only [prr, Prod.mk.injEq] at h
      have e1 : ((min a b : Fin n) : ℕ) + (max a b : Fin n) = a + b := by
        rcases le_total a b with h' | h'
        · rw [min_eq_left h', max_eq_right h']
        · rw [min_eq_right h', max_eq_left h']; ring
      have e2 : ((min c d : Fin n) : ℕ) + (max c d : Fin n) = c + d := by
        rcases le_total c d with h' | h'
        · rw [min_eq_left h', max_eq_right h']
        · rw [min_eq_right h', max_eq_left h']; ring
      rw [← e1, ← e2, h.1, h.2]
    have cross : ∀ w w' : J, α w ≠ β w' := by
      intro w w' h
      have h' : prr u w.1 = prr v w'.1 := congrArg Subtype.val h
      simp only [prr, Prod.mk.injEq] at h'
      rcases le_total u w.1 with h1 | h1
      · rw [min_eq_left h1] at h'
        rcases le_total v w'.1 with h2 | h2
        · rw [min_eq_left h2] at h'; exact huv h'.1
        · rw [min_eq_right h2] at h'; exact w'.2.1 h'.1.symm
      · rw [max_eq_left h1] at h'
        rcases le_total v w'.1 with h2 | h2
        · rw [max_eq_right h2] at h'; exact w'.2.1 h'.2.symm
        · rw [max_eq_left h2] at h'; exact huv h'.2
    rintro (w | w) (w' | w') h
    · simp only [Sum.elim_inl] at h
      have := key _ _ _ _ (congrArg Subtype.val h)
      congr 1
      apply Subtype.ext
      apply Fin.ext
      omega
    · exact absurd h (cross w w')
    · exact absurd h.symm (cross w' w)
    · simp only [Sum.elim_inr] at h
      have := key _ _ _ _ (congrArg Subtype.val h)
      congr 1
      apply Subtype.ext
      apply Fin.ext
      omega
  rw [sum_graph (fun _ _ => p) (fun G => Real.exp (s * codeg G u v))]
  have hx : ∀ x : {q : Fin n × Fin n // q ∈ pairs n} → Bool,
      Real.exp (s * codeg ((graphEquiv n).symm x) u v) =
        ∏ w : J, (fun _ b1 b2 => Real.exp (s * ((if b1 then 1 else 0) * (if b2 then 1 else 0))))
          w (x (α w)) (x (β w)) := by
    intro x
    rw [codeg_eq_sum, Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl (fun w _ => ?_)
    have hxa : decide (((graphEquiv n).symm x).Adj (α w).1.1 (α w).1.2) = x (α w) :=
      congrFun ((graphEquiv n).apply_symm_apply x) (α w)
    have hxb : decide (((graphEquiv n).symm x).Adj (β w).1.1 (β w).1.2) = x (β w) :=
      congrFun ((graphEquiv n).apply_symm_apply x) (β w)
    have ea := adj_iff_prr ((graphEquiv n).symm x) u w.1
    have eb := adj_iff_prr ((graphEquiv n).symm x) v w.1
    simp only []
    congr 2
    by_cases h1 : ((graphEquiv n).symm x).Adj u w.1 <;>
      by_cases h2 : ((graphEquiv n).symm x).Adj v w.1 <;> simp_all [α, β]
  simp_rw [hx]
  refine (sum_W_blocks (aR (fun _ _ => p)) α β hinj
    (fun _ b1 b2 => Real.exp (s * ((if b1 then 1 else 0) * (if b2 then 1 else 0))))).trans ?_
  have hJ : Fintype.card J = n - 2 := by
    rw [Fintype.card_subtype]
    have : (univ.filter (fun w : Fin n => w ≠ u ∧ w ≠ v)) = (univ.erase u).erase v := by
      ext w; simp [and_comm]
    rw [this, Finset.card_erase_of_mem, Finset.card_erase_of_mem (mem_univ _), Finset.card_univ,
      Fintype.card_fin]
    · omega
    · simp [Ne.symm huv]
  rw [← hJ, ← Finset.card_univ, ← Finset.prod_const]
  refine Finset.prod_congr rfl (fun w _ => ?_)
  simp only [aR, hc, Fintype.sum_bool]
  simp
  ring

/-- an upper tail from an mgf bound. -/
lemma tail_of_mgf {n : ℕ} (r : Fin n → Fin n → ℝ) (Y : SimpleGraph (Fin n) → ℝ) (μ M t : ℝ)
    (hμ0 : 0 ≤ μ) (hμM : μ ≤ M) (hM : 0 < M) (ht : 0 ≤ t) (htM : t ≤ 2 * M)
    (hmgf : ∀ l : ℝ, 0 ≤ l → l ≤ 1 → ∑ G : SimpleGraph (Fin n), edgeWeight G r * Real.exp (l * Y G) ≤
      Real.exp ((l + l ^ 2) * μ)) :
    ∑ G : SimpleGraph (Fin n), edgeWeight G r * (if Y G ≥ μ + t then 1 else 0) ≤
      Real.exp (- t ^ 2 / (4 * M)) := by
  set l := t / (2 * M) with hl
  have hl0 : 0 ≤ l := by positivity
  have hl1 : l ≤ 1 := by rw [hl, div_le_one (by positivity)]; exact htM
  have step1 : ∀ G : SimpleGraph (Fin n), (if Y G ≥ μ + t then (1:ℝ) else 0) ≤
      Real.exp (- l * μ - l * t) * Real.exp (l * Y G) := by
    intro G
    rw [← Real.exp_add]
    split_ifs with h
    · apply Real.one_le_exp; nlinarith
    · exact (Real.exp_pos _).le
  calc ∑ G : SimpleGraph (Fin n), edgeWeight G r * (if Y G ≥ μ + t then 1 else 0)
      ≤ ∑ G : SimpleGraph (Fin n), edgeWeight G r * (Real.exp (- l * μ - l * t) * Real.exp (l * Y G)) :=
        Finset.sum_le_sum (fun G _ => mul_le_mul_of_nonneg_left (step1 G) (edgeWeight_nonneg _ _))
    _ = Real.exp (- l * μ - l * t) * ∑ G : SimpleGraph (Fin n), edgeWeight G r * Real.exp (l * Y G) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun G _ => by ring)
    _ ≤ Real.exp (- l * μ - l * t) * Real.exp ((l + l ^ 2) * μ) :=
        mul_le_mul_of_nonneg_left (hmgf l hl0 hl1) (Real.exp_pos _).le
    _ = Real.exp (- l * t + l ^ 2 * μ) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (- t ^ 2 / (4 * M)) := by
        apply Real.exp_le_exp.2
        have h1 : l ^ 2 * μ ≤ l ^ 2 * M := mul_le_mul_of_nonneg_left hμM (by positivity)
        have h2 : - l * t + l ^ 2 * M = - t ^ 2 / (4 * M) := by rw [hl]; field_simp; ring
        linarith

lemma codeg_tail {n : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (u v : Fin n) (huv : u ≠ v)
    (t : ℝ) (ht : 0 ≤ t) (htM : t ≤ 2 * n) (hn : 1 ≤ n) :
    ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) *
      (if (codeg G u v : ℝ) ≥ p ^ 2 * ((n - 2 : ℕ) : ℝ) + t then 1 else 0) ≤
      Real.exp (- t ^ 2 / (4 * n)) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hn2 : ((n - 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 2
  refine tail_of_mgf (fun _ _ => p) (fun G => (codeg G u v : ℝ)) (p ^ 2 * ((n - 2 : ℕ) : ℝ)) n t
    (by positivity) ?_ hn' ht htM ?_
  · have : p ^ 2 ≤ 1 := by nlinarith
    nlinarith
  · intro l hl0 hl1
    rw [mgf_codeg p hp0 hp1 u v huv l]
    have hb : 0 ≤ 1 - p ^ 2 + p ^ 2 * Real.exp l := by
      have := Real.exp_pos l; have : p ^ 2 ≤ 1 := by nlinarith
      nlinarith
    have hfac : 1 - p ^ 2 + p ^ 2 * Real.exp l ≤ Real.exp ((l + l ^ 2) * p ^ 2) := by
      have hb2 := Real.abs_exp_sub_one_sub_id_le (by rw [abs_of_nonneg hl0]; exact hl1 : |l| ≤ 1)
      have hb' : Real.exp l - 1 ≤ l + l ^ 2 := by have := (abs_le.1 hb2).2; linarith
      have := Real.add_one_le_exp ((l + l ^ 2) * p ^ 2)
      have hp2 : 0 ≤ p ^ 2 := sq_nonneg p
      nlinarith
    calc (1 - p ^ 2 + p ^ 2 * Real.exp l) ^ (n - 2)
        ≤ (Real.exp ((l + l ^ 2) * p ^ 2)) ^ (n - 2) := pow_le_pow_left₀ hb hfac _
      _ = Real.exp ((l + l ^ 2) * (p ^ 2 * ((n - 2 : ℕ) : ℝ))) := by
          rw [← Real.exp_nat_mul]; congr 1; ring

/-- the probability that there are no edges between `C` and `D`. -/
lemma empty_between {n : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (C D : Finset (Fin n))
    (hd : Disjoint C D) :
    ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) * (if Xr G C D = 0 then 1 else 0) ≤
      (1 - p / 2) ^ (C.card * D.card) := by
  have hc : clamp01 p = p := by
    unfold clamp01; rw [min_eq_right hp1.le, max_eq_right hp0.le]
  have hX : ∀ G : SimpleGraph (Fin n), Xr G C D =
      ∑ q ∈ Spair C D, (if G.Adj q.1 q.2 then (1:ℝ) else 0) := by
    intro G
    unfold Xr
    exact sum_to_Spair C D hd (fun i j => if G.Adj i j then 1 else 0)
      (fun i j => by simp only [G.adj_comm])
  have hcard : (Spair C D).card = C.card * D.card := by
    have := sum_to_Spair C D hd (fun _ _ => (1:ℝ)) (fun _ _ => rfl)
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at this
    exact_mod_cast this.symm
  have hmgf := mgf_set (fun _ _ => p) (Spair C D) (Spair_sub C D) (- Real.log 2)
  have e2 : Real.exp (- Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  rw [e2] at hmgf
  simp only [hc, Finset.prod_const, hcard] at hmgf
  have e3 : p * (1 / 2) + (1 - p) = 1 - p / 2 := by ring
  rw [e3] at hmgf
  rw [← hmgf]
  apply Finset.sum_le_sum
  intro G _
  apply mul_le_mul_of_nonneg_left _ (edgeWeight_nonneg _ _)
  split_ifs with h
  · rw [← hX G, h, mul_zero, Real.exp_zero]
  · exact (Real.exp_pos _).le

lemma dMin_le_degree {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : dMin G ≤ G.degree v := by
  unfold dMin
  rw [dif_pos ⟨v, mem_univ v⟩]
  exact Finset.inf'_le _ (mem_univ v)

lemma dMin_attained {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 0 < n) : ∃ v, G.degree v = dMin G := by
  unfold dMin
  have hne : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, mem_univ _⟩
  rw [dif_pos hne]
  obtain ⟨v, _, hv⟩ := Finset.exists_mem_eq_inf' hne (fun v => G.degree v)
  exact ⟨v, hv.symm⟩

lemma kappa_le_dMin {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 0 < n) (hlt : dMin G + 1 < n) :
    kappa G ≤ dMin G := by
  obtain ⟨v, hv⟩ := dMin_attained G hn
  set S := G.neighborFinset v with hS
  have hSc : S.card = dMin G := by rw [hS, SimpleGraph.card_neighborFinset_eq_degree, hv]
  have hvS : v ∉ S := by rw [hS, SimpleGraph.mem_neighborFinset]; exact G.loopless.irrefl v
  obtain ⟨u, hu⟩ : ∃ u, u ∉ insert v S := by
    by_contra h
    push Not at h
    have : (insert v S) = univ := Finset.eq_univ_of_forall h
    have h2 := Finset.card_insert_le v S
    rw [this, Finset.card_univ, Fintype.card_fin] at h2
    omega
  rw [Finset.mem_insert, not_or] at hu
  have hnc : ¬ (G.induce ((↑S : Set (Fin n))ᶜ)).Connected := by
    intro hc
    have hr := hc.preconnected ⟨v, hvS⟩ ⟨u, hu.2⟩
    obtain ⟨W⟩ := hr
    cases W with
    | nil => exact hu.1 rfl
    | @cons _ w _ hadj _ =>
      have h1 : G.Adj v w.1 := hadj
      exact w.2 ((SimpleGraph.mem_neighborFinset G v w.1).2 h1)
  calc kappa G ≤ S.card := Nat.sInf_le ⟨S, rfl, hnc⟩
    _ = dMin G := hSc

/-- the side argument: a set closed under neighbours except through `S`. -/
lemma side_bound {n : ℕ} (G : SimpleGraph (Fin n)) (S A : Finset (Fin n)) (L U K c : ℝ)
    (hL : ∀ v, L < (G.degree v : ℝ)) (hU : ∀ v, (G.degree v : ℝ) < U)
    (hK : ∀ u v, u ≠ v → (codeg G u v : ℝ) < K) (hLKU : U ≤ 2 * L - K - c)
    (hA : ∀ z ∈ A, ∀ w, G.Adj z w → w ∈ A ∨ w ∈ S) (hdisj : Disjoint A S)
    (hne : A.Nonempty) (hsmall : (A.card : ℝ) ≤ c) : dMin G ≤ S.card := by
  by_cases h1 : A.card = 1
  · obtain ⟨z, rfl⟩ := Finset.card_eq_one.1 h1
    have hsub : G.neighborFinset z ⊆ S := by
      intro w hw
      rw [SimpleGraph.mem_neighborFinset] at hw
      rcases hA z (mem_singleton_self z) w hw with h | h
      · rw [Finset.mem_singleton] at h; subst h; exact absurd hw (G.loopless.irrefl _)
      · exact h
    calc dMin G ≤ G.degree z := dMin_le_degree G z
      _ = (G.neighborFinset z).card := (SimpleGraph.card_neighborFinset_eq_degree G z).symm
      _ ≤ S.card := Finset.card_le_card hsub
  · have h2 : 1 < A.card := by
      have := hne.card_pos; omega
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 h2
    have hsub : G.neighborFinset u ∪ G.neighborFinset v ⊆ A ∪ S := by
      intro w hw
      rw [Finset.mem_union, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset] at hw
      rw [Finset.mem_union]
      rcases hw with h | h
      · exact hA u hu w h
      · exact hA v hv w h
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj] at hcard
    have hui := Finset.card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
    rw [SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree] at hui
    have hcodeg : ((G.neighborFinset u ∩ G.neighborFinset v).card : ℝ) < K := hK u v huv
    have hR : ((G.neighborFinset u ∪ G.neighborFinset v).card : ℝ) ≤ A.card + S.card := by
      exact_mod_cast hcard
    have hui' : ((G.neighborFinset u ∪ G.neighborFinset v).card : ℝ) +
        (G.neighborFinset u ∩ G.neighborFinset v).card = G.degree u + G.degree v := by
      exact_mod_cast hui
    have hLu := hL u
    have hLv := hL v
    have hUu := hU u
    have hfinal : (G.degree u : ℝ) < S.card := by linarith
    have := dMin_le_degree G u
    have : (dMin G : ℝ) < S.card := lt_of_le_of_lt (by exact_mod_cast this) hfinal
    exact_mod_cast this.le

lemma dMin_le_cut {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (L U K c : ℝ)
    (hL : ∀ v, L < (G.degree v : ℝ)) (hU : ∀ v, (G.degree v : ℝ) < U)
    (hK : ∀ u v, u ≠ v → (codeg G u v : ℝ) < K) (hLKU : U ≤ 2 * L - K - c)
    (hE3 : ∀ C D : Finset (Fin n), Disjoint C D → c ≤ (C.card : ℝ) → c ≤ (D.card : ℝ) → Xr G C D ≠ 0)
    (hS : ¬ (G.induce ((↑S : Set (Fin n))ᶜ)).Connected) : dMin G ≤ S.card := by
  by_contra hlt
  push Not at hlt
  set H := G.induce ((↑S : Set (Fin n))ᶜ) with hH
  -- a vertex outside `S`
  obtain ⟨x0, hx0⟩ : ∃ x, x ∉ S := by
    by_contra h
    push Not at h
    have hSu : S = univ := Finset.eq_univ_of_forall h
    obtain ⟨v, hv⟩ := dMin_attained G (by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0
        exfalso
        have : dMin G = 0 := by unfold dMin; simp
        omega
      · exact h0)
    have hdv := dMin_le_degree G v
    have h3 : G.degree v < n := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      calc (G.neighborFinset v).card < (univ : Finset (Fin n)).card := by
            apply Finset.card_lt_card
            rw [Finset.ssubset_univ_iff]
            intro h4
            have : v ∈ G.neighborFinset v := by rw [h4]; exact mem_univ v
            rw [SimpleGraph.mem_neighborFinset] at this
            exact G.loopless.irrefl _ this
        _ = n := by rw [Finset.card_univ, Fintype.card_fin]
    rw [hSu, Finset.card_univ, Fintype.card_fin] at hlt
    omega
  have : Nonempty ↥((↑S : Set (Fin n))ᶜ) := ⟨⟨x0, hx0⟩⟩
  have hnp : ¬ H.Preconnected := by
    intro hp
    exact hS ⟨hp⟩
  have hnp' : ∃ x y, ¬ H.Reachable x y := by
    by_contra h
    push Not at h
    exact hnp h
  obtain ⟨x, y, hxy⟩ := hnp'
  set C : Finset (Fin n) := univ.filter (fun z => ∃ hz : z ∉ S, H.Reachable x ⟨z, hz⟩) with hC
  set D : Finset (Fin n) := univ.filter (fun z => ∃ hz : z ∉ S, ¬ H.Reachable x ⟨z, hz⟩) with hD
  have hxC : x.1 ∈ C := by
    rw [hC, Finset.mem_filter]; exact ⟨mem_univ _, x.2, by simp⟩
  have hyD : y.1 ∈ D := by
    rw [hD, Finset.mem_filter]; exact ⟨mem_univ _, y.2, by simpa using hxy⟩
  have hCD : Disjoint C D := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    rw [hC, Finset.mem_filter] at hz
    rw [hD, Finset.mem_filter] at hz'
    obtain ⟨_, h1, h2⟩ := hz
    obtain ⟨_, h1', h2'⟩ := hz'
    exact h2' h2
  have hCS : Disjoint C S := by
    rw [Finset.disjoint_left]
    intro z hz hzS
    rw [hC, Finset.mem_filter] at hz
    obtain ⟨_, h1, _⟩ := hz
    exact h1 hzS
  have hDS : Disjoint D S := by
    rw [Finset.disjoint_left]
    intro z hz hzS
    rw [hD, Finset.mem_filter] at hz
    obtain ⟨_, h1, _⟩ := hz
    exact h1 hzS
  have hCcl : ∀ z ∈ C, ∀ w, G.Adj z w → w ∈ C ∨ w ∈ S := by
    intro z hz w hw
    by_cases hwS : w ∈ S
    · exact Or.inr hwS
    left
    rw [hC, Finset.mem_filter] at hz ⊢
    obtain ⟨_, hzS, hr⟩ := hz
    refine ⟨mem_univ _, hwS, hr.trans ?_⟩
    exact SimpleGraph.Adj.reachable (show H.Adj ⟨z, hzS⟩ ⟨w, hwS⟩ from hw)
  have hDcl : ∀ z ∈ D, ∀ w, G.Adj z w → w ∈ D ∨ w ∈ S := by
    intro z hz w hw
    by_cases hwS : w ∈ S
    · exact Or.inr hwS
    left
    rw [hD, Finset.mem_filter] at hz ⊢
    obtain ⟨_, hzS, hr⟩ := hz
    refine ⟨mem_univ _, hwS, fun hw' => hr (hw'.trans ?_)⟩
    exact SimpleGraph.Adj.reachable (show H.Adj ⟨w, hwS⟩ ⟨z, hzS⟩ from hw.symm)
  have hX : Xr G C D = 0 := by
    unfold Xr
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    rw [if_neg]
    intro hij
    rcases hCcl i hi j hij with h | h
    · exact Finset.disjoint_left.1 hCD h hj
    · exact Finset.disjoint_left.1 hDS hj h
  by_cases hCs : (C.card : ℝ) ≤ c
  · have := side_bound G S C L U K c hL hU hK hLKU hCcl hCS ⟨_, hxC⟩ hCs
    omega
  by_cases hDs : (D.card : ℝ) ≤ c
  · have := side_bound G S D L U K c hL hU hK hLKU hDcl hDS ⟨_, hyD⟩ hDs
    omega
  push Not at hCs hDs
  exact hE3 C D hCD hCs.le hDs.le hX

lemma kappa_eq {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 0 < n) (L U K c : ℝ)
    (hL : ∀ v, L < (G.degree v : ℝ)) (hU : ∀ v, (G.degree v : ℝ) < U)
    (hK : ∀ u v, u ≠ v → (codeg G u v : ℝ) < K) (hLKU : U ≤ 2 * L - K - c)
    (hE3 : ∀ C D : Finset (Fin n), Disjoint C D → c ≤ (C.card : ℝ) → c ≤ (D.card : ℝ) → Xr G C D ≠ 0)
    (hUn : U ≤ n - 1) : kappa G = dMin G := by
  apply le_antisymm
  · apply kappa_le_dMin G hn
    obtain ⟨v, hv⟩ := dMin_attained G hn
    have := hU v
    rw [hv] at this
    have : (dMin G : ℝ) + 1 < n := by linarith
    exact_mod_cast this
  · apply le_csInf
    · refine ⟨n, univ, by rw [Finset.card_univ, Fintype.card_fin], ?_⟩
      intro hc
      obtain ⟨⟨z, hz⟩⟩ := hc.nonempty
      exact hz (by simp)
    · rintro k ⟨S, rfl, hS⟩
      exact dMin_le_cut G S L U K c hL hU hK hLKU hE3 hS

lemma ind_eq {P : Prop} (i1 i2 : Decidable P) : @ite ℝ P i1 1 0 = @ite ℝ P i2 1 0 := by
  congr

lemma erProb_eq {n : ℕ} (p : ℝ) (E : SimpleGraph (Fin n) → Prop) [DecidablePred E] :
    erProb n p E = ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) * (if E G then 1 else 0) := by
  unfold erProb
  refine Finset.sum_congr rfl (fun G _ => ?_)
  rw [ind_eq]

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


lemma ind_nonneg (P : Prop) [Decidable P] : (0:ℝ) ≤ if P then 1 else 0 := by split_ifs <;> norm_num

lemma sum_exists_le' {n : ℕ} {α : Type*} [Fintype α] (r : Fin n → Fin n → ℝ)
    (B : α → SimpleGraph (Fin n) → Prop) {inst : ∀ G, Decidable (∃ a, B a G)}
    {inst2 : ∀ a G, Decidable (B a G)} :
    ∑ G : SimpleGraph (Fin n), edgeWeight G r * (if ∃ a, B a G then 1 else 0) ≤
      ∑ a, ∑ G : SimpleGraph (Fin n), edgeWeight G r * (if B a G then 1 else 0) := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro G _
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (edgeWeight_nonneg _ _)
  split_ifs with h
  · obtain ⟨a, ha⟩ := h
    calc (1:ℝ) = if B a G then 1 else 0 := by simp [ha]
      _ ≤ ∑ a, (if B a G then (1:ℝ) else 0) :=
        Finset.single_le_sum (f := fun a => if B a G then (1:ℝ) else 0)
          (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ a)
  · exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)

end LP5Deg

open LP5Deg LPCommunity.SBMRecovery in
set_option maxHeartbeats 2000000 in
theorem solution (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    Tendsto (fun n : ℕ => erProb n p (fun G => kappa G = dMin G)) atTop (𝓝 1) := by
  have hc : clamp01 p = p := by
    unfold clamp01; rw [min_eq_right hp1.le, max_eq_right hp0.le]
  set c : ℝ := p * (1 - p) / 8 with hcdef
  have hc0 : 0 < c := by
    have : 0 < 1 - p := by linarith
    positivity
  set ℓ : ℝ := - Real.log (1 - p / 2) with hℓ
  have hℓ0 : 0 < ℓ := by
    rw [hℓ, neg_pos]
    apply Real.log_neg (by linarith) (by linarith)
  have key : ∀ᶠ n : ℕ in atTop, erProb n p (fun G => ¬ kappa G = dMin G) ≤ 4 / n := by
    filter_upwards [eventually_ge_atTop 3, eventually_ge_atTop ⌈2 / (1 - p)⌉₊,
      eventually_ge_atTop ⌈(2 * Real.log 2 + 1) / (ℓ * c ^ 2)⌉₊,
      sqrt_small (p / 6) (by positivity), sqrt_small (p * (1 - p) / 64) (by
        have : 0 < 1 - p := by linarith
        positivity),
      sqrt_small ((1 - p) / 12) (by
        have : 0 < 1 - p := by linarith
        positivity)] with n hn3 hn2 hnE hs6 hs64 hs12
    have hM : (3:ℝ) ≤ n := by exact_mod_cast hn3
    have hn0 : 0 < n := by omega
    have hlog := log_ge_one hn3
    set s := Real.sqrt (n * Real.log n) with hsdef
    have hsq : s ^ 2 = n * Real.log n := Real.sq_sqrt (by nlinarith)
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs1 : 1 ≤ s := Real.one_le_sqrt.2 (by nlinarith)
    have hn2' : 2 / (1 - p) ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn2)
    have hnE' : (2 * Real.log 2 + 1) / (ℓ * c ^ 2) ≤ (n : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hnE)
    have hμ : ∀ v : Fin n, ∑ u ∈ univ.erase v, clamp01 ((fun _ _ => p) v u : ℝ) = p * (n - 1) := by
      intro v
      simp only [hc]
      rw [Finset.sum_const, Finset.card_erase_of_mem (mem_univ v), Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega)]
      push_cast; ring
    have hn2c : ((n - 2 : ℕ) : ℝ) = n - 2 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
    -- the four bad events
    set B1 : Fin n → SimpleGraph (Fin n) → Prop := fun v G =>
      (1:ℝ) * ((G.degree v : ℝ) - ∑ u ∈ univ.erase v, clamp01 ((fun _ _ => p) v u)) ≥ 6 * s with hB1
    set B1' : Fin n → SimpleGraph (Fin n) → Prop := fun v G =>
      (-1:ℝ) * ((G.degree v : ℝ) - ∑ u ∈ univ.erase v, clamp01 ((fun _ _ => p) v u)) ≥ 6 * s with hB1'
    set B2 : Fin n → Fin n → SimpleGraph (Fin n) → Prop := fun u v G =>
      u ≠ v ∧ (codeg G u v : ℝ) ≥ p ^ 2 * ((n - 2 : ℕ) : ℝ) + 6 * s with hB2
    set B3 : Finset (Fin n) → Finset (Fin n) → SimpleGraph (Fin n) → Prop := fun C D G =>
      Disjoint C D ∧ c * n ≤ (C.card : ℝ) ∧ c * n ≤ (D.card : ℝ) ∧ Xr G C D = 0 with hB3
    -- deterministic step
    have hdet : ∀ G : SimpleGraph (Fin n), ¬ kappa G = dMin G →
        (∃ v, B1 v G) ∨ (∃ v, B1' v G) ∨ (∃ u, ∃ v, B2 u v G) ∨ (∃ C, ∃ D, B3 C D G) := by
      intro G hne
      by_contra hall
      push Not at hall
      obtain ⟨h1, h1', h2, h3⟩ := hall
      apply hne
      refine kappa_eq G hn0 (p * (n - 1) - 6 * s) (p * (n - 1) + 6 * s)
        (p ^ 2 * ((n - 2 : ℕ) : ℝ) + 6 * s) (c * n) ?_ ?_ ?_ ?_ ?_ ?_
      · intro v
        have := h1' v
        simp only [hB1', hμ v] at this
        linarith
      · intro v
        have := h1 v
        simp only [hB1, hμ v] at this
        linarith
      · intro u v huv
        have := h2 u v
        by_contra hge
        push Not at hge
        exact this ⟨huv, hge⟩
      · rw [hn2c, hcdef]
        have hδ : 24 * s ≤ 3 / 8 * (p * (1 - p)) * n := by nlinarith
        have h4 : p ≤ 1 / 2 * (p * (1 - p)) * n := by
          rw [div_le_iff₀ (by linarith)] at hn2'
          nlinarith
        nlinarith
      · intro C D hCD hC hD hX
        have := h3 C D
        exact this ⟨hCD, hC, hD, hX⟩
      · have : 6 * s ≤ (1 - p) * (n - 1) := by nlinarith
        linarith
    -- probability bounds
    have hP1 : ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) *
        (if ∃ v, B1 v G then 1 else 0) ≤ 1 / n := by
      calc _ ≤ ∑ v : Fin n, ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) *
            (if B1 v G then 1 else 0) := sum_exists_le' _ B1
        _ ≤ ∑ v : Fin n, Real.exp (- (6 * s) ^ 2 / (4 * (p * (n - 1)))) := by
            apply Finset.sum_le_sum
            intro v _
            exact degree_tail (fun _ _ => p) (fun _ _ => rfl) v 1 (Or.inl rfl) (6 * s) (p * (n - 1))
              (by positivity) (mul_pos hp0 (by linarith)) (by nlinarith) (le_of_eq (hμ v))
        _ ≤ ∑ v : Fin n, Real.exp (- (2 * Real.log n)) := by
            apply Finset.sum_le_sum
            intro v _
            apply Real.exp_le_exp.2
            have h5 : 2 * Real.log n ≤ (6 * s) ^ 2 / (4 * (p * (n - 1))) := by
              rw [le_div_iff₀ (mul_pos (by norm_num) (mul_pos hp0 (by linarith)))]
              have : (6 * s) ^ 2 = 36 * (n * Real.log n) := by rw [mul_pow, hsq]; ring
              rw [this]
              have : p * (n - 1) ≤ n := by nlinarith
              nlinarith
            rw [neg_div]; linarith
        _ = 1 / n := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              exp_neg_two_log n (by omega)]
            have : (n:ℝ) ≠ 0 := by positivity
            field_simp
    have hP1' : ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) *
        (if ∃ v, B1' v G then 1 else 0) ≤ 1 / n := by
      calc _ ≤ ∑ v : Fin n, ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) *
            (if B1' v G then 1 else 0) := sum_exists_le' _ B1'
        _ ≤ ∑ v : Fin n, Real.exp (- (6 * s) ^ 2 / (4 * (p * (n - 1)))) := by
            apply Finset.sum_le_sum
            intro v _
            exact degree_tail (fun _ _ => p) (fun _ _ => rfl) v (-1) (Or.inr rfl) (6 * s) (p * (n - 1))
              (by positivity) (mul_pos hp0 (by linarith)) (by nlinarith) (le_of_eq (hμ v))
        _ ≤ ∑ v : Fin n, Real.exp (- (2 * Real.log n)) := by
            apply Finset.sum_le_sum
            intro v _
            apply Real.exp_le_exp.2
            have h5 : 2 * Real.log n ≤ (6 * s) ^ 2 / (4 * (p * (n - 1))) := by
              rw [le_div_iff₀ (mul_pos (by norm_num) (mul_pos hp0 (by linarith)))]
              have : (6 * s) ^ 2 = 36 * (n * Real.log n) := by rw [mul_pow, hsq]; ring
              rw [this]
              have : p * (n - 1) ≤ n := by nlinarith
              nlinarith
            rw [neg_div]; linarith
        _ = 1 / n := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              exp_neg_two_log n (by omega)]
            have : (n:ℝ) ≠ 0 := by positivity
            field_simp
    have hP2 : ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) *
        (if ∃ u, ∃ v, B2 u v G then 1 else 0) ≤ 1 / n := by
      have hstep : ∀ u : Fin n, ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) *
          (if ∃ v, B2 u v G then 1 else 0) ≤ n * Real.exp (- (9 * Real.log n)) := by
        intro u
        calc _ ≤ ∑ v : Fin n, ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) *
              (if B2 u v G then 1 else 0) := sum_exists_le' _ (B2 u)
          _ ≤ ∑ v : Fin n, Real.exp (- (9 * Real.log n)) := by
              apply Finset.sum_le_sum
              intro v _
              by_cases huv : u = v
              · have : ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) *
                    (if B2 u v G then (1:ℝ) else 0) = 0 :=
                  Finset.sum_eq_zero (fun G _ => by
                    rw [if_neg (fun h => h.1 huv), mul_zero])
                rw [this]; exact (Real.exp_pos _).le
              · have ht := codeg_tail p hp0 hp1 u v huv (6 * s) (by positivity) (by nlinarith) (by omega)
                refine le_trans ?_ (le_trans ht (Real.exp_le_exp.2 ?_))
                · apply Finset.sum_le_sum
                  intro G _
                  apply mul_le_mul_of_nonneg_left _ (edgeWeight_nonneg _ _)
                  by_cases h : B2 u v G
                  · rw [if_pos h, if_pos h.2]
                  · rw [if_neg h]; split_ifs <;> norm_num
                · have : (6 * s) ^ 2 = 36 * (n * Real.log n) := by rw [mul_pow, hsq]; ring
                  rw [this, neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
                  nlinarith
          _ = n * Real.exp (- (9 * Real.log n)) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc _ ≤ ∑ u : Fin n, ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) *
            (if ∃ v, B2 u v G then 1 else 0) := sum_exists_le' _ (fun u G => ∃ v, B2 u v G)
        _ ≤ ∑ u : Fin n, (n : ℝ) * Real.exp (- (9 * Real.log n)) := Finset.sum_le_sum (fun u _ => hstep u)
        _ = (n : ℝ) * n * Real.exp (- (9 * Real.log n)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
        _ ≤ 1 / n := by
            have hm0 : (0:ℝ) < n := by linarith
            have h9 : Real.exp (9 * Real.log n) = (n : ℝ) ^ 9 := by
              have := pow_eq_exp n 9 (by omega)
              push_cast at this
              rw [this]
            rw [Real.exp_neg, h9]
            have hn7 : (n : ℝ) ≤ (n : ℝ) ^ 7 := by
              calc (n : ℝ) = (n : ℝ) ^ 1 := (pow_one _).symm
                _ ≤ (n : ℝ) ^ 7 := pow_le_pow_right₀ (by linarith) (by norm_num)
            calc (n : ℝ) * n * ((n : ℝ) ^ 9)⁻¹ = 1 / (n : ℝ) ^ 7 := by field_simp
              _ ≤ 1 / n := one_div_le_one_div_of_le hm0 hn7
    have hP3 : ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) *
        (if ∃ C, ∃ D, B3 C D G then 1 else 0) ≤ 1 / n := by
      have hstep : ∀ C : Finset (Fin n), ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) *
          (if ∃ D, B3 C D G then 1 else 0) ≤ 2 ^ n * Real.exp (- (ℓ * c ^ 2 * n ^ 2)) := by
        intro C
        calc _ ≤ ∑ D : Finset (Fin n), ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) *
              (if B3 C D G then 1 else 0) := sum_exists_le' _ (B3 C)
          _ ≤ ∑ D : Finset (Fin n), Real.exp (- (ℓ * c ^ 2 * n ^ 2)) := by
              apply Finset.sum_le_sum
              intro D _
              by_cases hb : Disjoint C D ∧ c * n ≤ (C.card : ℝ) ∧ c * n ≤ (D.card : ℝ)
              · refine le_trans ?_ (le_trans (empty_between p hp0 hp1 C D hb.1) ?_)
                · apply Finset.sum_le_sum
                  intro G _
                  apply mul_le_mul_of_nonneg_left _ (edgeWeight_nonneg _ _)
                  by_cases h : B3 C D G
                  · rw [if_pos h, if_pos h.2.2.2]
                  · rw [if_neg h]; split_ifs <;> norm_num
                · have hb2 : 0 < 1 - p / 2 := by linarith
                  rw [← Real.exp_log (pow_pos hb2 _), Real.log_pow]
                  apply Real.exp_le_exp.2
                  have hN : (c * n) ^ 2 ≤ ((C.card * D.card : ℕ) : ℝ) := by
                    push_cast
                    have h0 : 0 ≤ c * n := by positivity
                    calc (c * n) ^ 2 = (c * n) * (c * n) := by ring
                      _ ≤ (C.card : ℝ) * D.card := mul_le_mul hb.2.1 hb.2.2 h0 (by linarith)
                  have : Real.log (1 - p / 2) = - ℓ := by rw [hℓ]; ring
                  rw [this]
                  nlinarith
              · have : ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) *
                    (if B3 C D G then (1:ℝ) else 0) = 0 :=
                  Finset.sum_eq_zero (fun G _ => by
                    rw [if_neg (fun h => hb ⟨h.1, h.2.1, h.2.2.1⟩), mul_zero])
                rw [this]; exact (Real.exp_pos _).le
          _ = 2 ^ n * Real.exp (- (ℓ * c ^ 2 * n ^ 2)) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
                nsmul_eq_mul]
              push_cast; ring
      calc _ ≤ ∑ C : Finset (Fin n), ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) *
            (if ∃ D, B3 C D G then 1 else 0) := sum_exists_le' _ (fun C G => ∃ D, B3 C D G)
        _ ≤ ∑ C : Finset (Fin n), (2:ℝ) ^ n * Real.exp (- (ℓ * c ^ 2 * n ^ 2)) :=
            Finset.sum_le_sum (fun C _ => hstep C)
        _ = Real.exp (2 * n * Real.log 2 - ℓ * c ^ 2 * n ^ 2) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
              nsmul_eq_mul]
            have h2 : ((2:ℕ) : ℝ) ^ n = Real.exp (n * Real.log 2) := by
              have := pow_eq_exp 2 n (by norm_num)
              push_cast at this ⊢
              exact this
            push_cast at h2 ⊢
            rw [← mul_assoc, h2, ← Real.exp_add, ← Real.exp_add]
            congr 1; ring
        _ ≤ Real.exp (- Real.log n) := by
            apply Real.exp_le_exp.2
            have hlg : Real.log n ≤ n := Real.log_le_self (by linarith)
            have hq : 0 < ℓ * c ^ 2 := by positivity
            rw [div_le_iff₀ hq] at hnE'
            nlinarith
        _ = 1 / n := by
            rw [Real.exp_neg, Real.exp_log (by linarith)]; ring
    -- combine
    rw [erProb_eq p (fun G => ¬ kappa G = dMin G)]
    calc ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) *
          (if ¬ kappa G = dMin G then 1 else 0)
        ≤ ∑ G : SimpleGraph (Fin n), (edgeWeight G (fun _ _ => p) * (if ∃ v, B1 v G then 1 else 0) +
            edgeWeight G (fun _ _ => p) * (if ∃ v, B1' v G then 1 else 0) +
            edgeWeight G (fun _ _ => p) * (if ∃ u, ∃ v, B2 u v G then 1 else 0) +
            edgeWeight G (fun _ _ => p) * (if ∃ C, ∃ D, B3 C D G then 1 else 0)) := by
          apply Finset.sum_le_sum
          intro G _
          have hw0 := edgeWeight_nonneg G (fun _ _ => p)
          have i1 := mul_nonneg hw0 (ind_nonneg (∃ v, B1 v G))
          have i2 := mul_nonneg hw0 (ind_nonneg (∃ v, B1' v G))
          have i3 := mul_nonneg hw0 (ind_nonneg (∃ u, ∃ v, B2 u v G))
          have i4 := mul_nonneg hw0 (ind_nonneg (∃ C, ∃ D, B3 C D G))
          by_cases hk : kappa G = dMin G
          · rw [if_neg (not_not.2 hk), mul_zero]; linarith
          · rw [if_pos hk, mul_one]
            rcases hdet G hk with h | h | h | h
            · rw [if_pos h, mul_one]; linarith
            · rw [if_pos h, mul_one]; linarith
            · rw [if_pos h, mul_one]; linarith
            · rw [if_pos h, mul_one]; linarith
      _ = (∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) * (if ∃ v, B1 v G then 1 else 0)) +
          (∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) * (if ∃ v, B1' v G then 1 else 0)) +
          (∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) * (if ∃ u, ∃ v, B2 u v G then 1 else 0)) +
          (∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) *
            (if ∃ C, ∃ D, B3 C D G then 1 else 0)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ ≤ 1 / n + 1 / n + 1 / n + 1 / n := by linarith
      _ = 4 / n := by ring
  have hlow : Tendsto (fun n : ℕ => 1 - 4 / (n : ℝ)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub (tendsto_const_div_atTop_nhds_zero_nat 4)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [key] with n hn
    have h1 := erProb_compl (n := n) p (fun G => kappa G = dMin G)
    linarith
  · filter_upwards with n
    have h1 := erProb_compl (n := n) p (fun G => kappa G = dMin G)
    have h2 := erProb_nonneg (n := n) p (fun G => ¬ kappa G = dMin G)
    linarith
