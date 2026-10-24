-- Prove2me | solution 1 for LPCommunity.SBMDense.proposition_16
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T10:17:24.06826+00:00
-- url     : https://prove2.me/submissions/a0628147-8519-413b-930b-9e5e4d071379

import Mathlib
import Definitions.Def_LPCommunity_LPFail_Setting
import Definitions.Def_LPCommunity_SBMDense_RandomGraphs

open Finset
open scoped Classical

namespace LPC7Aux

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

end LPC7Aux

open Finset

namespace LPC26Aux

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- product Bernoulli weight on `ι → Bool`. -/
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

lemma W_nonneg (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (x : ι → Bool) : 0 ≤ W a x := by
  unfold W
  apply Finset.prod_nonneg
  intro i _
  have := ha i
  split_ifs <;> linarith

lemma sum_W (a : ι → ℝ) : ∑ x : ι → Bool, W a x = 1 := by
  have := sum_W_mul_prod a (fun _ _ => 1)
  simpa using this

/-- moment of a product of indicators over a set `T`. -/
lemma sum_W_prod_ind (a : ι → ℝ) (T : Finset ι) :
    ∑ x : ι → Bool, W a x * ∏ i ∈ T, (if x i then (1 : ℝ) else 0) = ∏ i ∈ T, a i := by
  have h := sum_W_mul_prod a (fun i b => if i ∈ T then (if b then (1 : ℝ) else 0) else 1)
  have e1 : ∀ x : ι → Bool, (∏ i, (if i ∈ T then (if x i then (1 : ℝ) else 0) else 1)) =
      ∏ i ∈ T, (if x i then (1 : ℝ) else 0) := by
    intro x
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  simp only [e1] at h
  rw [h]
  calc _ = ∏ x, (if x ∈ T then a x else 1) :=
        Finset.prod_congr rfl (fun x _ => by split_ifs <;> simp_all)
    _ = _ := by rw [Finset.prod_ite_mem, Finset.univ_inter]

lemma sum_W_ind (a : ι → ℝ) (i : ι) :
    ∑ x : ι → Bool, W a x * (if x i then (1 : ℝ) else 0) = a i := by
  simpa using sum_W_prod_ind a {i}

lemma sum_W_ind2 (a : ι → ℝ) (i j : ι) :
    ∑ x : ι → Bool, W a x * ((if x i then (1 : ℝ) else 0) * (if x j then (1 : ℝ) else 0)) =
      if i = j then a i else a i * a j := by
  by_cases hij : i = j
  · subst hij
    simp only [if_true]
    have : ∀ x : ι → Bool, ((if x i then (1 : ℝ) else 0) * (if x i then (1 : ℝ) else 0)) =
        (if x i then (1 : ℝ) else 0) := fun x => by split_ifs <;> simp
    simp only [this]
    exact sum_W_ind a i
  · simp only [hij, if_false]
    have := sum_W_prod_ind a {i, j}
    simp only [Finset.prod_pair hij] at this
    exact this

/-- the count of true coordinates in `S`. -/
noncomputable def cnt (S : Finset ι) (x : ι → Bool) : ℝ := ∑ i ∈ S, if x i then (1 : ℝ) else 0

lemma sum_W_cnt (a : ι → ℝ) (S : Finset ι) :
    ∑ x : ι → Bool, W a x * cnt S x = ∑ i ∈ S, a i := by
  unfold cnt
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => sum_W_ind a i)

lemma sum_W_cnt_sq (a : ι → ℝ) (S : Finset ι) :
    ∑ x : ι → Bool, W a x * cnt S x ^ 2 =
      (∑ i ∈ S, a i) ^ 2 + ∑ i ∈ S, (a i - a i ^ 2) := by
  unfold cnt
  have e : ∀ x : ι → Bool, W a x * (∑ i ∈ S, if x i then (1 : ℝ) else 0) ^ 2 =
      ∑ i ∈ S, ∑ j ∈ S, W a x * ((if x i then (1 : ℝ) else 0) * (if x j then (1 : ℝ) else 0)) := by
    intro x
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    simp only [Finset.mul_sum]
  simp only [e]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (univ : Finset (ι → Bool)))]
  simp only [sum_W_ind2]
  rw [sq, Finset.sum_mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have h' : ∀ x, (if i = x then a i else a i * a x) =
      a i * a x + (if i = x then a i - a i * a x else 0) := by
    intro x; split_ifs <;> ring
  simp only [h', Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos hi]
  ring

lemma sum_W_var (a : ι → ℝ) (S : Finset ι) :
    ∑ x : ι → Bool, W a x * (cnt S x - ∑ i ∈ S, a i) ^ 2 = ∑ i ∈ S, (a i - a i ^ 2) := by
  have e : ∀ x : ι → Bool, W a x * (cnt S x - ∑ i ∈ S, a i) ^ 2 =
      W a x * cnt S x ^ 2 - 2 * (∑ i ∈ S, a i) * (W a x * cnt S x) +
        (∑ i ∈ S, a i) ^ 2 * W a x := by intro x; ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_W_cnt_sq,
    sum_W_cnt, sum_W]
  ring

lemma cheb_aux (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (F : (ι → Bool) → ℝ) (t : ℝ) (ht : 0 < t) :
    ∑ x : ι → Bool, W a x * (if t ≤ |F x| then (1 : ℝ) else 0) ≤
      (∑ x : ι → Bool, W a x * F x ^ 2) / t ^ 2 := by
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro x _
  have hw := W_nonneg a ha x
  rw [mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ hw
  split_ifs with h
  · rw [le_div_iff₀ (by positivity), one_mul]
    have : t ^ 2 ≤ |F x| ^ 2 := pow_le_pow_left₀ ht.le h 2
    simpa [sq_abs] using this
  · positivity

lemma chebyshev (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (S : Finset ι) (t : ℝ) (ht : 0 < t) :
    ∑ x : ι → Bool, W a x * (if t ≤ |cnt S x - ∑ i ∈ S, a i| then (1 : ℝ) else 0) ≤
      (∑ i ∈ S, a i) / t ^ 2 := by
  refine (cheb_aux a ha _ t ht).trans ?_
  rw [sum_W_var]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro i _
  nlinarith [ha i]

end LPC26Aux

open Finset
open scoped Classical

namespace LPC26Aux

open LPCommunity.SBMRecovery LPC7Aux

abbrev PI (n : ℕ) := {p : Fin n × Fin n // p ∈ pairs n}

lemma edgeWeight_eq_W {n : ℕ} (G : SimpleGraph (Fin n)) (r : Fin n → Fin n → ℝ) :
    edgeWeight G r = W (fun i : PI n => clamp01 (r i.1.1 i.1.2)) (graphEquiv n G) := by
  unfold edgeWeight W
  rw [← Finset.prod_coe_sort]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  simp [graphEquiv]

lemma sum_edgeWeight_eq {n : ℕ} (r : Fin n → Fin n → ℝ) (F : SimpleGraph (Fin n) → ℝ) :
    ∑ G : SimpleGraph (Fin n), edgeWeight G r * F G =
      ∑ x : PI n → Bool, W (fun i : PI n => clamp01 (r i.1.1 i.1.2)) x * F ((graphEquiv n).symm x) := by
  refine Fintype.sum_equiv (graphEquiv n) _ _ (fun G => ?_)
  rw [edgeWeight_eq_W, Equiv.symm_apply_apply]

lemma card_filter_pairs_eq_cnt {n : ℕ} (G : SimpleGraph (Fin n)) (Q : Fin n × Fin n → Prop)
    [DecidablePred Q] :
    ((univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ G.Adj p.1 p.2 ∧ Q p).card : ℝ) =
      cnt (univ.filter fun i : PI n => Q i.1) (graphEquiv n G) := by
  unfold cnt
  rw [Finset.sum_filter]
  have : (univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ G.Adj p.1 p.2 ∧ Q p) =
      (pairs n).filter (fun p => G.Adj p.1 p.2 ∧ Q p) := by
    ext p; simp [pairs]
  rw [this, Finset.card_filter, Nat.cast_sum]
  rw [← Finset.sum_coe_sort (pairs n)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h1 : G.Adj i.1.1 i.1.2 <;> by_cases h2 : Q i.1 <;> simp [graphEquiv, h1, h2]

lemma edgeFinset_card_eq {n : ℕ} (G : SimpleGraph (Fin n)) :
    G.edgeFinset.card = ((pairs n).filter (fun p => G.Adj p.1 p.2)).card := by
  symm
  refine Finset.card_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter] at hp
    simpa using hp.2
  · intro p hp q hq h
    simp only [Finset.mem_filter, pairs, Finset.mem_univ, true_and] at hp hq
    rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exfalso; rw [h1, h2] at hp; exact absurd hp.1 (lt_asymm hq.1)
  · intro e he
    induction e using Sym2.ind with
    | h u v =>
      have hadj : G.Adj u v := by simpa using he
      rcases lt_trichotomy u v with h | h | h
      · exact ⟨(u, v), by simp [pairs, h, hadj], rfl⟩
      · exact absurd hadj (h ▸ G.loopless.irrefl u)
      · exact ⟨(v, u), by simp [pairs, h, hadj.symm], Sym2.eq_swap⟩

lemma edge_card_eq_cnt {n : ℕ} (G : SimpleGraph (Fin n)) :
    (G.edgeFinset.card : ℝ) = cnt (univ : Finset (PI n)) (graphEquiv n G) := by
  have := card_filter_pairs_eq_cnt G (fun _ => True)
  have e1 : (univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ G.Adj p.1 p.2 ∧ True) =
      (pairs n).filter (fun p => G.Adj p.1 p.2) := by
    ext p; simp [pairs]
  have e2 : (univ.filter fun _ : PI n => True) = univ := by ext; simp
  rw [e1, e2] at this
  rw [edgeFinset_card_eq, this]

/-- symmetric predicates: the ordered count is twice the count with `i < j`. -/
lemma card_lt_filter_two {n : ℕ} (P : Fin n × Fin n → Prop) [DecidablePred P] (hsymm : ∀ i j, P (i, j) → P (j, i))
    (hirr : ∀ i, ¬ P (i, i)) :
    2 * ((pairs n).filter P).card = (univ.filter P).card := by
  have hsplit : (univ.filter P) = ((pairs n).filter P) ∪ ((univ.filter fun p : Fin n × Fin n => p.2 < p.1).filter P) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, pairs]
    constructor
    · intro h
      rcases lt_trichotomy i j with hij | rfl | hij
      · exact Or.inl ⟨hij, h⟩
      · exact absurd h (hirr i)
      · exact Or.inr ⟨hij, h⟩
    · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
  have hdisj : Disjoint ((pairs n).filter P) ((univ.filter fun p : Fin n × Fin n => p.2 < p.1).filter P) := by
    rw [Finset.disjoint_left]
    rintro ⟨i, j⟩ h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, pairs] at h1 h2
    exact lt_asymm h1.1 h2.1
  have hswap : ((univ.filter fun p : Fin n × Fin n => p.2 < p.1).filter P).card = ((pairs n).filter P).card := by
    refine Finset.card_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_
    · rintro ⟨i, j⟩ h
      simp [pairs] at h ⊢
      exact ⟨h.1, hsymm _ _ h.2⟩
    · rintro ⟨i, j⟩ h
      simp [pairs] at h ⊢
      exact ⟨h.1, hsymm _ _ h.2⟩
    · intro p _; simp
    · intro p _; simp
  rw [hsplit, Finset.card_union_of_disjoint hdisj, hswap]
  ring

lemma card_cnt_set {n : ℕ} (Q : Fin n × Fin n → Prop) [DecidablePred Q] :
    (univ.filter fun i : PI n => Q i.1).card = ((pairs n).filter Q).card := by
  rw [Finset.card_filter, Finset.card_filter]
  exact Finset.sum_coe_sort (pairs n) (fun p => if Q p then 1 else 0)

lemma card_cross (m : ℕ) (V1 : Finset (Fin (2 * m))) (hV : V1.card = m) :
    ((pairs (2 * m)).filter fun p => ¬ LPCommunity.MinBisect.sameSide V1 p.1 p.2).card = m * m := by
  have h := card_lt_filter_two (n := 2 * m) (fun p => ¬ LPCommunity.MinBisect.sameSide V1 p.1 p.2)
    (fun i j h => by unfold LPCommunity.MinBisect.sameSide at *; tauto)
    (fun i h => by unfold LPCommunity.MinBisect.sameSide at h; tauto)
  have hc : (univ.filter fun p : Fin (2 * m) × Fin (2 * m) =>
      ¬ LPCommunity.MinBisect.sameSide V1 p.1 p.2) = (V1 ×ˢ V1ᶜ) ∪ (V1ᶜ ×ˢ V1) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_product,
      Finset.mem_compl]
    unfold LPCommunity.MinBisect.sameSide
    tauto
  have hd : Disjoint (V1 ×ˢ V1ᶜ) (V1ᶜ ×ˢ V1) := by
    rw [Finset.disjoint_left]
    rintro ⟨i, j⟩ h1 h2
    simp only [Finset.mem_product, Finset.mem_compl] at h1 h2
    exact h1.2 h2.2
  have hcV : V1ᶜ.card = m := by rw [Finset.card_compl, Fintype.card_fin]; omega
  rw [hc, Finset.card_union_of_disjoint hd, Finset.card_product, Finset.card_product, hV, hcV] at h
  linarith

lemma card_pairs (n : ℕ) : 2 * (pairs n).card + n = n * n := by
  have h := card_lt_filter_two (n := n) (fun p => p.1 ≠ p.2) (fun i j h => Ne.symm h)
    (fun i h => h rfl)
  have e1 : (pairs n).filter (fun p : Fin n × Fin n => p.1 ≠ p.2) = pairs n := by
    apply Finset.filter_true_of_mem
    intro p hp; simp [pairs] at hp; exact hp.ne
  have e2 : (univ.filter fun p : Fin n × Fin n => p.1 ≠ p.2) = (univ : Finset (Fin n)).offDiag := by
    ext p; simp
  rw [e1, e2, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin] at h
  have : n ≤ n * n := Nat.le_mul_self n
  omega

end LPC26Aux

open Finset Filter Topology
open scoped Classical

namespace LPC26Aux

open LPCommunity.SBMRecovery LPC7Aux

/-- per-bisection Chebyshev bound. -/
lemma perV1_bound {n : ℕ} (r : Fin n → Fin n → ℝ) (S0 S1 : Finset (PI n)) (δ : ℝ)
    (h0 : 0 < δ * ∑ i ∈ S0, clamp01 (r i.1.1 i.1.2)) (h1 : 0 < δ * ∑ i ∈ S1, clamp01 (r i.1.1 i.1.2))
    (E : SimpleGraph (Fin n) → Prop)
    (hE : ∀ G, |cnt S0 (graphEquiv n G) - ∑ i ∈ S0, clamp01 (r i.1.1 i.1.2)| <
        δ * ∑ i ∈ S0, clamp01 (r i.1.1 i.1.2) →
      |cnt S1 (graphEquiv n G) - ∑ i ∈ S1, clamp01 (r i.1.1 i.1.2)| <
        δ * ∑ i ∈ S1, clamp01 (r i.1.1 i.1.2) → E G) :
    1 - ((∑ i ∈ S0, clamp01 (r i.1.1 i.1.2)) / (δ * ∑ i ∈ S0, clamp01 (r i.1.1 i.1.2)) ^ 2 +
      (∑ i ∈ S1, clamp01 (r i.1.1 i.1.2)) / (δ * ∑ i ∈ S1, clamp01 (r i.1.1 i.1.2)) ^ 2) ≤
    ∑ G : SimpleGraph (Fin n), edgeWeight G r * (if E G then 1 else 0) := by
  set a : PI n → ℝ := fun i => clamp01 (r i.1.1 i.1.2) with ha_def
  have ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1 := fun i =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  rw [sum_edgeWeight_eq]
  have c0 := chebyshev a ha S0 _ h0
  have c1 := chebyshev a ha S1 _ h1
  have hpt : ∀ x : PI n → Bool, W a x * (1 - (if δ * ∑ i ∈ S0, a i ≤ |cnt S0 x - ∑ i ∈ S0, a i|
      then (1 : ℝ) else 0) - (if δ * ∑ i ∈ S1, a i ≤ |cnt S1 x - ∑ i ∈ S1, a i| then (1 : ℝ) else 0))
      ≤ W a x * (if E ((graphEquiv n).symm x) then 1 else 0) := by
    intro x
    apply mul_le_mul_of_nonneg_left _ (W_nonneg a ha x)
    have hx := hE ((graphEquiv n).symm x)
    rw [Equiv.apply_symm_apply] at hx
    by_cases b0 : δ * ∑ i ∈ S0, a i ≤ |cnt S0 x - ∑ i ∈ S0, a i|
    · rw [if_pos b0]; split_ifs <;> norm_num
    · rw [if_neg b0]
      by_cases b1 : δ * ∑ i ∈ S1, a i ≤ |cnt S1 x - ∑ i ∈ S1, a i|
      · rw [if_pos b1]; split_ifs <;> norm_num
      · rw [if_neg b1, if_pos (hx (not_le.1 b0) (not_le.1 b1))]; norm_num
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ (univ : Finset (PI n → Bool))) => hpt x)
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, sum_W] at hsum
  linarith

lemma sbmProb_ge {n : ℕ} (p q : ℝ) (hn : (bisections n).Nonempty) (b : ℝ)
    (E : Finset (Fin n) → SimpleGraph (Fin n) → Prop)
    (h : ∀ V1 ∈ bisections n, b ≤ ∑ G : SimpleGraph (Fin n),
      edgeWeight G (fun i j => if LPCommunity.MinBisect.sameSide V1 i j then p else q) *
        (if E V1 G then 1 else 0)) :
    b ≤ sbmProb n p q E := by
  unfold sbmProb
  have hc : (0 : ℝ) < (bisections n).card := by exact_mod_cast hn.card_pos
  rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hc]
  calc b * (bisections n).card = ∑ _V1 ∈ bisections n, b := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ _ := Finset.sum_le_sum h

end LPC26Aux

open Finset

namespace LPC16Aux

open LPC26Aux

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- disjoint pairs of coordinates are independent. -/
lemma sum_W_prod_one_sub {κ : Type*} [DecidableEq κ] (a : ι → ℝ) (K : Finset κ) (e f : κ → ι)
    (he : Set.InjOn e K) (hf : Set.InjOn f K) (hef : ∀ k ∈ K, ∀ k' ∈ K, e k ≠ f k') :
    ∑ x : ι → Bool, W a x * ∏ k ∈ K, (1 - (if x (e k) then (1 : ℝ) else 0) * (if x (f k) then (1 : ℝ) else 0)) =
      ∏ k ∈ K, (1 - a (e k) * a (f k)) := by
  have expand : ∀ (u v : κ → ℝ), ∏ k ∈ K, (1 - u k * v k) =
      ∑ t ∈ K.powerset, (∏ k ∈ t, (-1 : ℝ)) * ((∏ k ∈ t, u k) * ∏ k ∈ t, v k) := by
    intro u v
    rw [show (∏ k ∈ K, (1 - u k * v k)) = ∏ k ∈ K, (1 + (-1) * (u k * v k)) by
      refine Finset.prod_congr rfl (fun k _ => by ring)]
    rw [Finset.prod_one_add]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [expand, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  have htK : t ⊆ K := Finset.mem_powerset.1 ht
  have hdisj : Disjoint (t.image e) (t.image f) := by
    rw [Finset.disjoint_left]
    intro c hc1 hc2
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hc1
    obtain ⟨k', hk', hkk⟩ := Finset.mem_image.1 hc2
    exact hef k (htK hk) k' (htK hk') hkk.symm
  have hprod : ∀ g : ι → ℝ, (∏ k ∈ t, g (e k)) * (∏ k ∈ t, g (f k)) =
      ∏ c ∈ t.image e ∪ t.image f, g c := by
    intro g
    rw [Finset.prod_union hdisj, Finset.prod_image (fun k hk k' hk' h => he (htK hk) (htK hk') h),
      Finset.prod_image (fun k hk k' hk' h => hf (htK hk) (htK hk') h)]
  have h1 : ∀ x : ι → Bool, W a x * ((∏ k ∈ t, (-1 : ℝ)) * ((∏ k ∈ t, (if x (e k) then (1 : ℝ) else 0)) *
      ∏ k ∈ t, (if x (f k) then (1 : ℝ) else 0))) = (∏ k ∈ t, (-1 : ℝ)) *
      (W a x * ∏ c ∈ t.image e ∪ t.image f, (if x c then (1 : ℝ) else 0)) := by
    intro x
    rw [hprod (fun c => if x c then (1 : ℝ) else 0)]
    ring
  simp only [h1]
  rw [← Finset.mul_sum, sum_W_prod_ind, ← hprod a]

end LPC16Aux

open Finset
open scoped Classical

namespace LPC16Aux

open LPCommunity.SBMRecovery LPC7Aux LPC26Aux

lemma minmax_eq {α : Type*} [LinearOrder α] {a b c d : α}
    (h : (min a b, max a b) = (min c d, max c d)) : (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  rcases le_total a b with hab | hab <;> rcases le_total c d with hcd | hcd
  · rw [min_eq_left hab, min_eq_left hcd] at h1; rw [max_eq_right hab, max_eq_right hcd] at h2
    exact Or.inl ⟨h1, h2⟩
  · rw [min_eq_left hab, min_eq_right hcd] at h1; rw [max_eq_right hab, max_eq_left hcd] at h2
    exact Or.inr ⟨h1, h2⟩
  · rw [min_eq_right hab, min_eq_left hcd] at h1; rw [max_eq_left hab, max_eq_right hcd] at h2
    exact Or.inr ⟨h2, h1⟩
  · rw [min_eq_right hab, min_eq_right hcd] at h1; rw [max_eq_left hab, max_eq_left hcd] at h2
    exact Or.inl ⟨h2, h1⟩

/-- the coordinate of the pair `{i, k}`. -/
def pidx {n : ℕ} (i k : Fin n) (h : i ≠ k) : PI n :=
  ⟨(min i k, max i k), by simp [pairs]; exact Ne.symm h⟩

lemma graphEquiv_pidx {n : ℕ} (G : SimpleGraph (Fin n)) (i k : Fin n) (h : i ≠ k) :
    graphEquiv n G (pidx i k h) = decide (G.Adj i k) := by
  simp only [graphEquiv, pidx, Equiv.coe_fn_mk]
  rcases le_total i k with hik | hik
  · simp only [min_eq_left hik, max_eq_right hik]
  · simp only [min_eq_right hik, max_eq_left hik, G.adj_comm]

/-- probability that a non-adjacent pair `i ≠ j` has no common neighbour. -/
lemma bad_pair_bound {n : ℕ} (r : Fin n → Fin n → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hr : ∀ i j, q ≤ clamp01 (r i j)) (i j : Fin n) (hij : i ≠ j) :
    ∑ G : SimpleGraph (Fin n), edgeWeight G r *
      (if (∀ k, ¬ (G.Adj i k ∧ G.Adj j k)) then (1 : ℝ) else 0) ≤ (1 - q ^ 2) ^ (n - 2) := by
  set a : PI n → ℝ := fun c => clamp01 (r c.1.1 c.1.2) with ha_def
  have ha : ∀ c, 0 ≤ a c ∧ a c ≤ 1 := fun c =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have haq : ∀ c, q ≤ a c := fun c => hr _ _
  let κ := {k : Fin n // k ≠ i ∧ k ≠ j}
  let e : κ → PI n := fun k => pidx i k.1 (Ne.symm k.2.1)
  let f : κ → PI n := fun k => pidx j k.1 (Ne.symm k.2.2)
  have he : Set.InjOn e (univ : Finset κ) := by
    intro k _ k' _ h
    have h' := congrArg Subtype.val h
    rcases minmax_eq h' with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact Subtype.ext h2
    · exact absurd h1.symm k'.2.1
  have hf : Set.InjOn f (univ : Finset κ) := by
    intro k _ k' _ h
    have h' := congrArg Subtype.val h
    rcases minmax_eq h' with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact Subtype.ext h2
    · exact absurd h1.symm k'.2.2
  have hef : ∀ k ∈ (univ : Finset κ), ∀ k' ∈ (univ : Finset κ), e k ≠ f k' := by
    intro k _ k' _ h
    have h' := congrArg Subtype.val h
    rcases minmax_eq h' with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact hij h1
    · exact k.2.2 h2
  have hmain := sum_W_prod_one_sub a (univ : Finset κ) e f he hf hef
  rw [sum_edgeWeight_eq]
  have hpt : ∀ x : PI n → Bool, W a x * (if (∀ k, ¬ (((graphEquiv n).symm x).Adj i k ∧
      ((graphEquiv n).symm x).Adj j k)) then (1 : ℝ) else 0) ≤
      W a x * ∏ k ∈ (univ : Finset κ), (1 - (if x (e k) then (1 : ℝ) else 0) *
        (if x (f k) then (1 : ℝ) else 0)) := by
    intro x
    apply mul_le_mul_of_nonneg_left _ (W_nonneg a ha x)
    split_ifs with hb
    · apply le_of_eq; symm
      apply Finset.prod_eq_one
      intro k _
      have hx1 : x (e k) = decide (((graphEquiv n).symm x).Adj i k.1) := by
        conv_lhs => rw [← Equiv.apply_symm_apply (graphEquiv n) x]
        exact graphEquiv_pidx _ _ _ _
      have hx2 : x (f k) = decide (((graphEquiv n).symm x).Adj j k.1) := by
        conv_lhs => rw [← Equiv.apply_symm_apply (graphEquiv n) x]
        exact graphEquiv_pidx _ _ _ _
      have := hb k.1
      rw [hx1, hx2]
      by_cases h1 : ((graphEquiv n).symm x).Adj i k.1 <;>
        by_cases h2 : ((graphEquiv n).symm x).Adj j k.1 <;> simp_all
    · apply Finset.prod_nonneg
      intro k _
      split_ifs <;> norm_num
  refine (Finset.sum_le_sum (fun x _ => hpt x)).trans ?_
  rw [hmain]
  have hcard : Fintype.card κ = n - 2 := by
    rw [Fintype.card_subtype]
    have : (univ.filter fun k : Fin n => k ≠ i ∧ k ≠ j) = univ \ {i, j} := by
      ext k; simp
    rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_pair hij,
      Finset.card_univ, Fintype.card_fin]
  calc ∏ k ∈ (univ : Finset κ), (1 - a (e k) * a (f k)) ≤ ∏ _k ∈ (univ : Finset κ), (1 - q ^ 2) := by
        apply Finset.prod_le_prod
        · intro k _
          have := ha (e k); have := ha (f k)
          nlinarith
        · intro k _
          have := haq (e k); have := haq (f k)
          nlinarith
    _ = (1 - q ^ 2) ^ (n - 2) := by
        rw [Finset.prod_const, Finset.card_univ, hcard]

/-- probability that every pair is an edge. -/
lemma complete_bound {n : ℕ} (r : Fin n → Fin n → ℝ) (p : ℝ) (hp : 0 ≤ p)
    (hr : ∀ i j, clamp01 (r i j) ≤ p) :
    ∑ G : SimpleGraph (Fin n), edgeWeight G r *
      (if (∀ c : PI n, G.Adj c.1.1 c.1.2) then (1 : ℝ) else 0) ≤ p ^ (pairs n).card := by
  set a : PI n → ℝ := fun c => clamp01 (r c.1.1 c.1.2) with ha_def
  have ha : ∀ c, 0 ≤ a c ∧ a c ≤ 1 := fun c =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  rw [sum_edgeWeight_eq]
  have hpt : ∀ x : PI n → Bool, W a x * (if (∀ c : PI n, ((graphEquiv n).symm x).Adj c.1.1 c.1.2)
      then (1 : ℝ) else 0) ≤ W a x * ∏ c ∈ (univ : Finset (PI n)), (if x c then (1 : ℝ) else 0) := by
    intro x
    apply mul_le_mul_of_nonneg_left _ (W_nonneg a ha x)
    split_ifs with hb
    · apply le_of_eq; symm
      apply Finset.prod_eq_one
      intro c _
      have : x c = decide (((graphEquiv n).symm x).Adj c.1.1 c.1.2) := by
        conv_lhs => rw [← Equiv.apply_symm_apply (graphEquiv n) x]
        rfl
      rw [this]; simp [hb c]
    · apply Finset.prod_nonneg
      intro c _
      split_ifs <;> norm_num
  refine (Finset.sum_le_sum (fun x _ => hpt x)).trans ?_
  rw [sum_W_prod_ind]
  calc ∏ c ∈ (univ : Finset (PI n)), a c ≤ ∏ _c ∈ (univ : Finset (PI n)), p :=
        Finset.prod_le_prod (fun c _ => (ha c).1) (fun c _ => hr _ _)
    _ = p ^ (pairs n).card := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]

end LPC16Aux

open Finset
open scoped Classical ENNReal

namespace LPC16Aux

open LPCommunity.SBMRecovery LPC7Aux LPC26Aux LPCommunity.LPFail

lemma edist_cases {n : ℕ} (G : SimpleGraph (Fin n))
    (H1 : ∀ i j, i ≠ j → ¬ G.Adj i j → ∃ k, G.Adj i k ∧ G.Adj j k) (i j : Fin n) (hij : i ≠ j) :
    G.edist i j = if G.Adj i j then 1 else 2 := by
  split_ifs with h
  · exact SimpleGraph.edist_eq_one_iff_adj.2 h
  · obtain ⟨k, hk1, hk2⟩ := H1 i j hij h
    exact SimpleGraph.edist_eq_two_iff.2 ⟨hij, h, ⟨k, (G.mem_commonNeighbors).2 ⟨hk1, hk2⟩⟩⟩

lemma rhoMax_eq_two {n : ℕ} (G : SimpleGraph (Fin n))
    (H1 : ∀ i j, i ≠ j → ¬ G.Adj i j → ∃ k, G.Adj i k ∧ G.Adj j k)
    (H2 : ∃ i j, i ≠ j ∧ ¬ G.Adj i j) : rhoMax G = 2 := by
  unfold rhoMax
  apply le_antisymm
  · apply SimpleGraph.ediam_le_of_edist_le
    intro u v
    by_cases huv : u = v
    · subst huv; simp
    · rw [edist_cases G H1 u v huv]; split_ifs <;> norm_num
  · obtain ⟨i, j, hij, hn⟩ := H2
    have := edist_cases G H1 i j hij
    rw [if_neg hn] at this
    rw [← this]
    exact SimpleGraph.edist_le_ediam

lemma rhoAvg_eq {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    (H1 : ∀ i j, i ≠ j → ¬ G.Adj i j → ∃ k, G.Adj i k ∧ G.Adj j k) :
    rhoAvg G = ENNReal.ofReal (2 / (n : ℝ) ^ 2 *
      (2 * ((pairs n).card : ℝ) - (G.edgeFinset.card : ℝ))) := by
  unfold rhoAvg
  have hterm : ∀ i j : Fin n, (if i < j then ((G.edist i j : ℕ∞) : ℝ≥0∞) else 0) =
      ENNReal.ofReal (if i < j then (if G.Adj i j then (1 : ℝ) else 2) else 0) := by
    intro i j
    split_ifs with h1 h2 h2
    · rw [edist_cases G H1 i j h1.ne, if_pos h2]; simp
    · rw [edist_cases G H1 i j h1.ne, if_neg h2]; simp
    · simp
  simp only [hterm]
  rw [Finset.sum_congr rfl (fun i _ => (ENNReal.ofReal_sum_of_nonneg (fun j _ => by
    split_ifs <;> norm_num)).symm)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by
    split_ifs <;> norm_num))]
  have hsum : (∑ i : Fin n, ∑ j : Fin n, (if i < j then (if G.Adj i j then (1 : ℝ) else 2) else 0)) =
      2 * ((pairs n).card : ℝ) - (G.edgeFinset.card : ℝ) := by
    rw [← Finset.sum_product' (s := (univ : Finset (Fin n))) (t := univ)
      (f := fun i j => if i < j then (if G.Adj i j then (1 : ℝ) else 2) else 0)]
    rw [Finset.univ_product_univ, ← Finset.sum_filter]
    have e1 : ∀ c : Fin n × Fin n, (if G.Adj c.1 c.2 then (1 : ℝ) else 2) =
        2 - (if G.Adj c.1 c.2 then (1 : ℝ) else 0) := by intro c; split_ifs <;> norm_num
    simp only [e1]
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_boole,
      edgeFinset_card_eq, mul_comm]
    rfl
  rw [hsum]
  have hn' : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_div_of_pos hn', ENNReal.ofReal_pow
    (Nat.cast_nonneg n), ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]

end LPC16Aux

open Finset Filter Topology
open scoped Classical ENNReal

open LPCommunity.SBMRecovery LPC7Aux LPC26Aux LPC16Aux LPCommunity.LPFail

lemma b_tendsto (ρ p c : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hp0 : 0 ≤ p) (hp : p < 1) :
    Tendsto (fun m : ℕ => (4 / ρ ^ 2) * ((m : ℝ) ^ 2 * (ρ ^ 2) ^ m) + p ^ m + c * (1 / (m : ℝ)) ^ 2)
      atTop (𝓝 0) := by
  have t1 : Tendsto (fun m : ℕ => (m : ℝ) ^ 2 * (ρ ^ 2) ^ m) atTop (𝓝 0) :=
    tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 (by
      rw [abs_of_pos (pow_pos hρ0 2)]; exact pow_lt_one₀ hρ0.le hρ1 two_ne_zero)
  have t2 : Tendsto (fun m : ℕ => p ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hp0 hp
  have t3 : Tendsto (fun m : ℕ => (1 / (m : ℝ)) ^ 2) atTop (𝓝 0) := by
    have := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
    simpa using this
  have := ((t1.const_mul (4 / ρ ^ 2)).add t2).add (t3.const_mul c)
  simpa using this

lemma m_le_pairs (m : ℕ) (hm : 1 ≤ m) : m ≤ (pairs (2 * m)).card := by
  have := card_pairs (2 * m)
  nlinarith

lemma combine3 {n : ℕ} (r : Fin n → Fin n → ℝ) (E B C D : SimpleGraph (Fin n) → Prop)
    [iE : DecidablePred E] [DecidablePred B] [DecidablePred C] [DecidablePred D]
    (h : ∀ G, ¬ B G → ¬ C G → ¬ D G → E G) (x y z : ℝ)
    (hx : ∑ G : SimpleGraph (Fin n), edgeWeight G r * (if B G then (1 : ℝ) else 0) ≤ x)
    (hy : ∑ G : SimpleGraph (Fin n), edgeWeight G r * (if C G then (1 : ℝ) else 0) ≤ y)
    (hz : ∑ G : SimpleGraph (Fin n), edgeWeight G r * (if D G then (1 : ℝ) else 0) ≤ z) :
    1 - x - y - z ≤
    ∑ G : SimpleGraph (Fin n), edgeWeight G r * (if E G then (1 : ℝ) else 0) := by
  have key : ∑ G : SimpleGraph (Fin n), edgeWeight G r * (1 - (if B G then (1 : ℝ) else 0) -
      (if C G then (1 : ℝ) else 0) - (if D G then (1 : ℝ) else 0)) ≤
      ∑ G : SimpleGraph (Fin n), edgeWeight G r * (if E G then (1 : ℝ) else 0) := by
    apply Finset.sum_le_sum
    intro G _
    apply mul_le_mul_of_nonneg_left _ (edgeWeight_nonneg G r)
    by_cases h1 : B G
    · rw [if_pos h1]; split_ifs <;> norm_num
    by_cases h2 : C G
    · rw [if_pos h2]; split_ifs <;> norm_num
    by_cases h3 : D G
    · rw [if_pos h3]; split_ifs <;> norm_num
    rw [if_neg h1, if_neg h2, if_neg h3, if_pos (h G h1 h2 h3)]
    norm_num
  have e : ∑ G : SimpleGraph (Fin n), edgeWeight G r * (1 - (if B G then (1 : ℝ) else 0) -
      (if C G then (1 : ℝ) else 0) - (if D G then (1 : ℝ) else 0)) =
      1 - ∑ G : SimpleGraph (Fin n), edgeWeight G r * (if B G then (1 : ℝ) else 0) -
      ∑ G : SimpleGraph (Fin n), edgeWeight G r * (if C G then (1 : ℝ) else 0) -
      ∑ G : SimpleGraph (Fin n), edgeWeight G r * (if D G then (1 : ℝ) else 0) := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, edgeWeight_sum]
  linarith

set_option maxHeartbeats 1000000 in
theorem solution (p q : ℝ) (hq : 0 < q) (hqp : q < p) (hp : p < 1) (ε : ℝ) (hε : 0 < ε) :
    Filter.Tendsto
      (fun m : ℕ => LPCommunity.SBMRecovery.sbmProb (2 * m) p q
        (fun _ G => ENNReal.ofReal ((1 - ε) * (2 - (p + q) / 2)) ≤ LPCommunity.LPFail.rhoAvg G ∧
          LPCommunity.LPFail.rhoAvg G ≤ ((LPCommunity.LPFail.rhoMax G : ℕ∞) : ℝ≥0∞) ∧ LPCommunity.LPFail.rhoMax G = 2))
      Filter.atTop (nhds 1) := by
  set ρ := 1 - q ^ 2 with hρ
  have hρ0 : 0 < ρ := by nlinarith
  have hρ1 : ρ < 1 := by nlinarith
  have hs2 : 0 < 2 - (p + q) := by linarith
  set b : ℕ → ℝ := fun m => (4 / ρ ^ 2) * ((m : ℝ) ^ 2 * (ρ ^ 2) ^ m) + p ^ m +
    (1 / (ε ^ 2 * q)) * (1 / (m : ℝ)) ^ 2 with hb
  set M := max 1 ⌈1 / (ε * (2 - (p + q)))⌉₊ with hM
  have key : ∀ m ≥ M, 1 - b m ≤ sbmProb (2 * m) p q
      (fun _ G => ENNReal.ofReal ((1 - ε) * (2 - (p + q) / 2)) ≤ rhoAvg G ∧
          rhoAvg G ≤ ((rhoMax G : ℕ∞) : ℝ≥0∞) ∧ rhoMax G = 2) := by
    intro m hm
    have hm1 : 1 ≤ m := le_trans (le_max_left _ _) hm
    have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have hmε : 1 / (ε * (2 - (p + q))) ≤ (m : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hm)
    refine sbmProb_ge _ _ (bisections_nonempty m) _ _ (fun V1 hV1 => ?_)
    have hV : V1.card = m := by
      have : 2 * V1.card = 2 * m := by simpa [bisections, LPCommunity.MinBisect.IsBisection] using hV1
      omega
    set rr : Fin (2 * m) → Fin (2 * m) → ℝ :=
      fun i j => if LPCommunity.MinBisect.sameSide V1 i j then p else q with hrr
    have hclP : clamp01 p = p := by unfold clamp01; rw [min_eq_right hp.le, max_eq_right (by linarith)]
    have hclQ : clamp01 q = q := by unfold clamp01; rw [min_eq_right (by linarith), max_eq_right hq.le]
    have hcl : ∀ i j, clamp01 (rr i j) = rr i j := fun i j => by
      simp only [hrr]; split_ifs <;> assumption
    have hlo : ∀ i j, q ≤ clamp01 (rr i j) := fun i j => by
      rw [hcl]; simp only [hrr]; split_ifs <;> linarith
    have hhi : ∀ i j, clamp01 (rr i j) ≤ p := fun i j => by
      rw [hcl]; simp only [hrr]; split_ifs <;> linarith
    -- the mean edge count
    set μ := ∑ c : PI (2 * m), clamp01 (rr c.1.1 c.1.2) with hμ
    set S0 : Finset (PI (2 * m)) := univ.filter fun i => ¬ LPCommunity.MinBisect.sameSide V1 i.1.1 i.1.2 with hS0
    set S1 : Finset (PI (2 * m)) := univ.filter fun i => LPCommunity.MinBisect.sameSide V1 i.1.1 i.1.2 with hS1
    have hcS0 : (S0.card : ℝ) = m * m := by
      rw [hS0, card_cnt_set (fun p => ¬ LPCommunity.MinBisect.sameSide V1 p.1 p.2), card_cross m V1 hV]
      push_cast; ring
    have hpairs : ((pairs (2 * m)).card : ℝ) = 2 * m * m - m := by
      have := card_pairs (2 * m)
      have h' : ((2 * (pairs (2 * m)).card + 2 * m : ℕ) : ℝ) = ((2 * m * (2 * m) : ℕ) : ℝ) := by
        rw [this]
      push_cast at h'
      linarith
    have hcU : ((univ : Finset (PI (2 * m))).card : ℝ) = 2 * m * m - m := by
      rw [Finset.card_univ, Fintype.card_coe, hpairs]
    have hcS1 : (S1.card : ℝ) = m * m - m := by
      have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (PI (2 * m))))
        (fun i => LPCommunity.MinBisect.sameSide V1 i.1.1 i.1.2)
      have h' : ((S1.card + S0.card : ℕ) : ℝ) = ((univ : Finset (PI (2 * m))).card : ℝ) := by
        rw [hS1, hS0]; exact_mod_cast this
      push_cast at h'
      linarith
    have hμ0 : ∑ i ∈ S0, clamp01 (rr i.1.1 i.1.2) = m * m * q := by
      rw [Finset.sum_congr rfl (g := fun _ => q), Finset.sum_const, nsmul_eq_mul, hcS0]
      intro i hi
      rw [hS0, Finset.mem_filter] at hi
      simp only [hrr, if_neg hi.2, hclQ]
    have hμ1 : ∑ i ∈ S1, clamp01 (rr i.1.1 i.1.2) = (m * m - m) * p := by
      rw [Finset.sum_congr rfl (g := fun _ => p), Finset.sum_const, nsmul_eq_mul, hcS1]
      intro i hi
      rw [hS1, Finset.mem_filter] at hi
      simp only [hrr, if_pos hi.2, hclP]
    have hμv : μ = m * m * q + (m * m - m) * p := by
      rw [hμ, ← hμ0, ← hμ1, hS0, hS1, add_comm]
      exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have hmm : 0 ≤ (m : ℝ) * m - m := by nlinarith
    have hμpos : m * m * q ≤ μ := by rw [hμv]; nlinarith
    have hμpos' : 0 < μ := lt_of_lt_of_le (by positivity) hμpos
    -- the three bad events
    let Bad : SimpleGraph (Fin (2 * m)) → Prop := fun G => ∃ i j, i ≠ j ∧ ∀ k, ¬ (G.Adj i k ∧ G.Adj j k)
    let Comp : SimpleGraph (Fin (2 * m)) → Prop := fun G => ∀ c : PI (2 * m), G.Adj c.1.1 c.1.2
    let Dev : SimpleGraph (Fin (2 * m)) → Prop := fun G => ε * μ ≤ |cnt univ (graphEquiv (2 * m) G) - μ|
    have hdet : ∀ G, ¬ Bad G → ¬ Comp G → ¬ Dev G →
        (ENNReal.ofReal ((1 - ε) * (2 - (p + q) / 2)) ≤ rhoAvg G ∧
          rhoAvg G ≤ ((rhoMax G : ℕ∞) : ℝ≥0∞) ∧ rhoMax G = 2) := by
      intro G hB hC hD
      have H1 : ∀ i j, i ≠ j → ¬ G.Adj i j → ∃ k, G.Adj i k ∧ G.Adj j k := by
        intro i j hij _
        by_contra hk
        push_neg at hk
        exact hB ⟨i, j, hij, fun k h => hk k h.1 h.2⟩
      have H2 : ∃ i j, i ≠ j ∧ ¬ G.Adj i j := by
        by_contra hk
        push_neg at hk
        apply hC
        intro c
        have : c.1.1 < c.1.2 := by simpa [pairs] using c.2
        exact hk _ _ this.ne
      have hmax := rhoMax_eq_two G H1 H2
      have havg := rhoAvg_eq (by omega) G H1
      have hE : (G.edgeFinset.card : ℝ) < (1 + ε) * μ := by
        rw [edge_card_eq_cnt]
        have := not_le.1 hD
        have := (abs_lt.1 this).2
        linarith
      have hE0 : (0 : ℝ) ≤ G.edgeFinset.card := Nat.cast_nonneg _
      have hnR : ((2 * m : ℕ) : ℝ) = 2 * m := by push_cast; ring
      rw [hpairs, hnR] at havg
      refine ⟨?_, ?_, hmax⟩
      · rw [havg]
        apply ENNReal.ofReal_le_ofReal
        have hmpos : (0 : ℝ) < m := by linarith
        have e1 : 2 / (2 * (m : ℝ)) ^ 2 * (2 * (2 * m * m - m) - (G.edgeFinset.card : ℝ)) =
            2 - 1 / m - (G.edgeFinset.card : ℝ) / (2 * m * m) := by
          field_simp
        rw [e1]
        have hE' : (G.edgeFinset.card : ℝ) / (2 * m * m) ≤ (1 + ε) * (p + q) / 2 := by
          rw [div_le_iff₀ (by positivity)]
          rw [hμv] at hE
          have h1 : (m * m * q + (m * m - m) * p) ≤ (p + q) * (m * m) := by
            nlinarith [mul_nonneg hmpos.le (le_of_lt (by linarith : 0 < p))]
          have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 + ε)
          linarith
        have hm' : 1 / (m : ℝ) ≤ ε * (2 - (p + q)) := by
          rw [div_le_iff₀ hmpos]
          rw [div_le_iff₀ (by positivity)] at hmε
          linarith
        linarith
      · rw [hmax, havg]
        have : ((2 : ℕ∞) : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
        rw [this]
        apply ENNReal.ofReal_le_ofReal
        have hmpos : (0 : ℝ) < m := by linarith
        have e1 : 2 / (2 * (m : ℝ)) ^ 2 * (2 * (2 * m * m - m) - (G.edgeFinset.card : ℝ)) =
            2 - 1 / m - (G.edgeFinset.card : ℝ) / (2 * m * m) := by
          field_simp
        rw [e1]
        have : 0 ≤ 1 / (m : ℝ) := by positivity
        have : 0 ≤ (G.edgeFinset.card : ℝ) / (2 * m * m) := by positivity
        linarith
    -- probability bounds
    have pBad : ∑ G : SimpleGraph (Fin (2 * m)), edgeWeight G rr * (if Bad G then (1 : ℝ) else 0) ≤
        ((2 * m : ℕ) : ℝ) * ((2 * m : ℕ) : ℝ) * ρ ^ (2 * m - 2) := by
      have hpt : ∀ G : SimpleGraph (Fin (2 * m)), edgeWeight G rr * (if Bad G then (1 : ℝ) else 0) ≤
          ∑ i : Fin (2 * m), ∑ j : Fin (2 * m), (if i ≠ j then edgeWeight G rr *
            (if (∀ k, ¬ (G.Adj i k ∧ G.Adj j k)) then (1 : ℝ) else 0) else 0) := by
        intro G
        have hw := edgeWeight_nonneg G rr
        by_cases hBG : Bad G
        · obtain ⟨i, j, hij, hk⟩ := hBG
          rw [if_pos ⟨i, j, hij, hk⟩, mul_one]
          have hnn : ∀ i j : Fin (2 * m), 0 ≤ (if i ≠ j then edgeWeight G rr *
              (if (∀ k, ¬ (G.Adj i k ∧ G.Adj j k)) then (1 : ℝ) else 0) else 0) := by
            intro i j; split_ifs <;> simp [hw]
          calc edgeWeight G rr = (if i ≠ j then edgeWeight G rr *
                (if (∀ k, ¬ (G.Adj i k ∧ G.Adj j k)) then (1 : ℝ) else 0) else 0) := by
                rw [if_pos hij, if_pos hk, mul_one]
            _ ≤ ∑ j' : Fin (2 * m), (if i ≠ j' then edgeWeight G rr *
                (if (∀ k, ¬ (G.Adj i k ∧ G.Adj j' k)) then (1 : ℝ) else 0) else 0) :=
                Finset.single_le_sum (fun j' _ => hnn i j') (Finset.mem_univ j)
            _ ≤ _ := Finset.single_le_sum (f := fun i' => ∑ j' : Fin (2 * m), (if i' ≠ j' then edgeWeight G rr *
                (if (∀ k, ¬ (G.Adj i' k ∧ G.Adj j' k)) then (1 : ℝ) else 0) else 0))
                (fun i' _ => Finset.sum_nonneg (fun j' _ => hnn i' j')) (Finset.mem_univ i)
        · rw [if_neg hBG, mul_zero]
          exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by
            split_ifs <;> simp [hw]))
      refine (Finset.sum_le_sum (fun G _ => hpt G)).trans ?_
      rw [Finset.sum_comm]
      calc _ = ∑ i : Fin (2 * m), ∑ j : Fin (2 * m), (if i ≠ j then ∑ G : SimpleGraph (Fin (2 * m)), edgeWeight G rr *
            (if (∀ k, ¬ (G.Adj i k ∧ G.Adj j k)) then (1 : ℝ) else 0) else 0) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            split_ifs <;> simp
        _ ≤ ∑ _i : Fin (2 * m), ∑ _j : Fin (2 * m), ρ ^ (2 * m - 2) := by
            apply Finset.sum_le_sum; intro i _
            apply Finset.sum_le_sum; intro j _
            split_ifs with hij
            · exact bad_pair_bound rr q hq.le hlo i j hij
            · positivity
        _ = ((2 * m : ℕ) : ℝ) * ((2 * m : ℕ) : ℝ) * ρ ^ (2 * m - 2) := by
            simp [Finset.sum_const, Finset.card_univ]; ring
    have pComp : ∑ G : SimpleGraph (Fin (2 * m)), edgeWeight G rr * (if Comp G then (1 : ℝ) else 0) ≤
        p ^ m := by
      refine (complete_bound rr p (by linarith) hhi).trans ?_
      exact pow_le_pow_of_le_one (by linarith) hp.le (m_le_pairs m hm1)
    have pDev : ∑ G : SimpleGraph (Fin (2 * m)), edgeWeight G rr * (if Dev G then (1 : ℝ) else 0) ≤
        μ / (ε * μ) ^ 2 := by
      rw [sum_edgeWeight_eq]
      have hch := chebyshev (fun c : PI (2 * m) => clamp01 (rr c.1.1 c.1.2))
        (fun c => ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩) univ (ε * μ)
        (mul_pos hε hμpos')
      beta_reduce at hch
      rw [← hμ] at hch
      simp only [Dev, Equiv.apply_symm_apply]
      exact hch
    -- combine
    have hsum := combine3 (iE := fun _ => Classical.propDecidable _) rr _ Bad Comp Dev hdet _ _ _
      pBad pComp pDev
    refine le_trans ?_ hsum
    -- compare with b m
    have hb1 : ((2 * m : ℕ) : ℝ) * ((2 * m : ℕ) : ℝ) * ρ ^ (2 * m - 2) =
        (4 / ρ ^ 2) * ((m : ℝ) ^ 2 * (ρ ^ 2) ^ m) := by
      have hn2 : 2 * m - 2 + 2 = 2 * m := by omega
      have : ρ ^ (2 * m - 2) * ρ ^ 2 = (ρ ^ 2) ^ m := by rw [← pow_add, hn2, pow_mul]
      have hnR : ((2 * m : ℕ) : ℝ) = 2 * m := by push_cast; ring
      rw [hnR]
      field_simp
      rw [← this]; ring
    have hb3 : μ / (ε * μ) ^ 2 ≤ (1 / (ε ^ 2 * q)) * (1 / (m : ℝ)) ^ 2 := by
      have e1 : μ / (ε * μ) ^ 2 = 1 / (ε ^ 2 * μ) := by field_simp
      have e2 : (1 / (ε ^ 2 * q)) * (1 / (m : ℝ)) ^ 2 = 1 / (ε ^ 2 * (m * m * q)) := by
        field_simp
      rw [e1, e2]
      gcongr
    simp only [hb]
    linarith only [hb1, hb3]
  have hlim : Tendsto b atTop (𝓝 0) := b_tendsto ρ p (1 / (ε ^ 2 * q)) hρ0 hρ1 (by linarith) hp
  have hlow : Tendsto (fun m => 1 - b m) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_
    (Eventually.of_forall fun m => sbmProb_le_one m _ _ _)
  filter_upwards [eventually_ge_atTop M] with m hm
  exact key m hm
