-- Prove2me | solution 1 for LPCommunity.SBMRecovery.proposition_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T10:25:28.306988+00:00
-- url     : https://prove2.me/submissions/6d5fadf8-38d9-465d-9086-039f2c86a1e9

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
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

lemma dMin_ge {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) (X : ℝ)
    (h : ∀ v, X ≤ (G.degree v : ℝ)) : X ≤ (dMin G : ℝ) := by
  unfold dMin
  have hne : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, mem_univ _⟩
  rw [dif_pos hne]
  obtain ⟨v, _, hv⟩ := Finset.exists_mem_eq_inf' hne (fun v => G.degree v)
  rw [hv]
  exact h v

end LP5Deg

open LP5Deg LPCommunity.SBMRecovery in
theorem solution (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ C : ℝ, 0 < C ∧
      Tendsto (fun n : ℕ => erProb n p
        (fun G => (dMin G : ℝ) ≥ p * n - C * Real.sqrt (n * Real.log n))) atTop (𝓝 1) := by
  refine ⟨6, by norm_num, ?_⟩
  have hc : clamp01 p = p := by
    unfold clamp01; rw [min_eq_right hp1.le, max_eq_right hp0.le]
  have key : ∀ᶠ n : ℕ in atTop,
      ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) *
        (if ¬ ((dMin G : ℝ) ≥ p * n - 6 * Real.sqrt (n * Real.log n)) then 1 else 0) ≤ 1 / n := by
    filter_upwards [sqrt_small (p / 6) (by positivity), eventually_ge_atTop 3] with n hs hn3
    have hn : (3:ℝ) ≤ n := by exact_mod_cast hn3
    have hlog := log_ge_one hn3
    have hs1 : 1 ≤ Real.sqrt (n * Real.log n) := Real.one_le_sqrt.2 (by nlinarith)
    have hsq : Real.sqrt (n * Real.log n) ^ 2 = n * Real.log n := Real.sq_sqrt (by nlinarith)
    have hM0 : 0 < p * (n - 1) := mul_pos hp0 (by linarith)
    have hμ : ∀ v : Fin n, ∑ u ∈ univ.erase v, clamp01 p = p * (n - 1) := by
      intro v
      rw [Finset.sum_const, Finset.card_erase_of_mem (mem_univ v), Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, hc, Nat.cast_sub (by omega)]
      push_cast; ring
    set s := Real.sqrt (n * Real.log n) with hsdef
    set t := 6 * s - p with ht
    have ht0 : 0 ≤ t := by linarith
    have htM : t ≤ 2 * (p * (n - 1)) := by nlinarith
    calc ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) *
          (if ¬ ((dMin G : ℝ) ≥ p * n - 6 * s) then 1 else 0)
        ≤ ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) *
          (if ∃ v, (-1:ℝ) * ((G.degree v : ℝ) - ∑ u ∈ univ.erase v, clamp01 p) ≥ t
            then 1 else 0) := by
          apply Finset.sum_le_sum
          intro G _
          apply mul_le_mul_of_nonneg_left _ (edgeWeight_nonneg _ _)
          by_cases h1 : (dMin G : ℝ) ≥ p * n - 6 * s
          · rw [if_neg (not_not.2 h1)]
            split_ifs <;> norm_num
          · rw [if_pos h1]
            have h2 : ∃ v, (-1:ℝ) * ((G.degree v : ℝ) - ∑ u ∈ univ.erase v, clamp01 p) ≥ t := by
              by_contra h2
              apply h1
              apply dMin_ge (by omega) G
              intro v
              by_contra hv
              push Not at hv
              exact h2 ⟨v, by rw [hμ v]; linarith⟩
            rw [if_pos h2]
      _ ≤ ∑ v : Fin n, ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) *
          (if (-1:ℝ) * ((G.degree v : ℝ) - ∑ u ∈ univ.erase v, clamp01 p) ≥ t then 1 else 0) :=
          sum_exists_le _ (fun v G => (-1:ℝ) * ((G.degree v : ℝ) - ∑ u ∈ univ.erase v, clamp01 p) ≥ t)
      _ ≤ ∑ v : Fin n, Real.exp (- t ^ 2 / (4 * (p * (n - 1)))) := by
          apply Finset.sum_le_sum
          intro v _
          exact degree_tail (fun _ _ => p) (fun _ _ => rfl) v (-1) (Or.inr rfl) t (p * (n - 1))
            ht0 hM0 htM (le_of_eq (hμ v))
      _ ≤ ∑ v : Fin n, Real.exp (- (2 * Real.log n)) := by
          apply Finset.sum_le_sum
          intro v _
          apply Real.exp_le_exp.2
          have h3 : 3 * s ≤ t := by linarith
          have h4 : 9 * (n * Real.log n) ≤ t ^ 2 := by nlinarith
          have h5 : 2 * Real.log n ≤ t ^ 2 / (4 * (p * (n - 1))) := by
            rw [le_div_iff₀ (by positivity)]
            have : p * (n - 1) ≤ n := by nlinarith
            nlinarith
          rw [neg_div]
          linarith
      _ = 1 / n := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            exp_neg_two_log n (by omega)]
          have : (n:ℝ) ≠ 0 := by positivity
          field_simp
  have hlow : Tendsto (fun n : ℕ => 1 - 1 / (n:ℝ)) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1:ℝ))).sub tendsto_one_div_atTop_nhds_zero_nat
    simpa using this
  have hnn : ∀ n : ℕ, 0 ≤ ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => p) *
      (if ¬ ((dMin G : ℝ) ≥ p * n - 6 * Real.sqrt (n * Real.log n)) then 1 else 0) := fun n =>
    Finset.sum_nonneg (fun G _ => mul_nonneg (edgeWeight_nonneg _ _) (by split_ifs <;> norm_num))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [key] with n hn
    unfold erProb
    rw [sum_compl]
    linarith
  · filter_upwards with n
    unfold erProb
    rw [sum_compl]
    linarith [hnn n]
