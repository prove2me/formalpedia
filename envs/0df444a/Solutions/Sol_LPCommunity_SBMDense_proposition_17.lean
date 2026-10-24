-- Prove2me | solution 1 for LPCommunity.SBMDense.proposition_17
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T10:28:44.572574+00:00
-- url     : https://prove2.me/submissions/56742b59-03d4-4bc3-8972-14fc9f2ef909
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LPCommunity_LPFail_Setting
import Definitions.Def_LPCommunity_SBMDense_RandomGraphs
import Definitions.Def_LPCommunity_SBMDense_Thresholds
import Theorems.Thm_LPCommunity_SBMDense_proposition_12
import Theorems.Thm_LPCommunity_SBMDense_proposition_14

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

open Finset
open scoped Classical

namespace LPC17Aux

open LPCommunity.SBMRecovery LPC7Aux LPC26Aux

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- coordinatewise monotone coupling weights. -/
noncomputable def cpl (a a' : ι → ℝ) (i : ι) : Bool → Bool → ℝ
  | true, true => a i
  | false, true => a' i - a i
  | false, false => 1 - a' i
  | true, false => 0

lemma W_mono (a a' : ι → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ a' i ∧ a' i ≤ 1)
    (f : (ι → Bool) → ℝ) (hf : ∀ x y : ι → Bool, (∀ i, x i = true → y i = true) → f x ≤ f y) :
    ∑ x, W a x * f x ≤ ∑ x, W a' x * f x := by
  set V : (ι → Bool) → (ι → Bool) → ℝ := fun x y => ∏ i, cpl a a' i (x i) (y i) with hV
  have hc0 : ∀ i b b', 0 ≤ cpl a a' i b b' := by
    intro i b b'; have := ha i; cases b <;> cases b' <;> simp [cpl] <;> linarith
  have hV0 : ∀ x y, 0 ≤ V x y := fun x y => Finset.prod_nonneg (fun i _ => hc0 i _ _)
  have M1 : ∀ x, ∑ y, V x y = W a x := by
    intro x
    have h := Finset.prod_univ_sum (fun _ : ι => (univ : Finset Bool)) (fun i b => cpl a a' i (x i) b)
    rw [Fintype.piFinset_univ] at h
    rw [hV, ← h]
    unfold W
    refine Finset.prod_congr rfl (fun i _ => ?_)
    cases x i <;> simp [cpl, Fintype.sum_bool]
  have M2 : ∀ y, ∑ x, V x y = W a' y := by
    intro y
    have h := Finset.prod_univ_sum (fun _ : ι => (univ : Finset Bool)) (fun i b => cpl a a' i b (y i))
    rw [Fintype.piFinset_univ] at h
    rw [hV, ← h]
    unfold W
    refine Finset.prod_congr rfl (fun i _ => ?_)
    cases y i <;> simp [cpl, Fintype.sum_bool]
  have supp : ∀ x y, V x y ≠ 0 → ∀ i, x i = true → y i = true := by
    intro x y hne i hx
    by_contra hy
    apply hne
    rw [hV]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [Bool.not_eq_true] at hy
    rw [hx, hy]; rfl
  calc ∑ x, W a x * f x = ∑ x, ∑ y, V x y * f x := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [← M1 x, Finset.sum_mul]
    _ ≤ ∑ x, ∑ y, V x y * f y := by
        apply Finset.sum_le_sum; intro x _
        apply Finset.sum_le_sum; intro y _
        by_cases h0 : V x y = 0
        · simp [h0]
        · exact mul_le_mul_of_nonneg_left (hf x y (supp x y h0)) (hV0 x y)
    _ = ∑ y, W a' y * f y := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [← M2 y, Finset.sum_mul]

/-- monotone comparison for graph events. -/
lemma edgeWeight_mono {n : ℕ} (r r' : Fin n → Fin n → ℝ)
    (hr : ∀ i j, clamp01 (r i j) ≤ clamp01 (r' i j))
    (E : SimpleGraph (Fin n) → Prop) [DecidablePred E] (hE : ∀ G G', G ≤ G' → E G → E G') :
    ∑ G : SimpleGraph (Fin n), edgeWeight G r * (if E G then (1 : ℝ) else 0) ≤
      ∑ G : SimpleGraph (Fin n), edgeWeight G r' * (if E G then (1 : ℝ) else 0) := by
  rw [sum_edgeWeight_eq, sum_edgeWeight_eq]
  apply W_mono
  · intro c
    exact ⟨le_max_left _ _, hr _ _, max_le zero_le_one (min_le_left _ _)⟩
  · intro x y hxy
    have hle : (graphEquiv n).symm x ≤ (graphEquiv n).symm y := by
      intro i j h
      simp only [graphEquiv, Equiv.coe_fn_symm_mk] at h ⊢
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, hxy _ h2⟩
      · exact Or.inr ⟨h1, hxy _ h2⟩
    by_cases h : E ((graphEquiv n).symm x)
    · rw [if_pos h, if_pos (hE _ _ hle h)]
    · rw [if_neg h]; split_ifs <;> norm_num

lemma edgeWeight_anti {n : ℕ} (r r' : Fin n → Fin n → ℝ)
    (hr : ∀ i j, clamp01 (r i j) ≤ clamp01 (r' i j))
    (E : SimpleGraph (Fin n) → Prop) [DecidablePred E] (hE : ∀ G G', G ≤ G' → E G' → E G) :
    ∑ G : SimpleGraph (Fin n), edgeWeight G r' * (if E G then (1 : ℝ) else 0) ≤
      ∑ G : SimpleGraph (Fin n), edgeWeight G r * (if E G then (1 : ℝ) else 0) := by
  have h := edgeWeight_mono r r' hr (fun G => ¬ E G) (fun G G' hle h1 h2 => h1 (hE G G' hle h2))
  have e : ∀ s : Fin n → Fin n → ℝ, ∑ G : SimpleGraph (Fin n), edgeWeight G s * (if ¬ E G then (1 : ℝ) else 0) =
      1 - ∑ G : SimpleGraph (Fin n), edgeWeight G s * (if E G then (1 : ℝ) else 0) := by
    intro s
    have : ∀ G, edgeWeight G s * (if ¬ E G then (1 : ℝ) else 0) =
        edgeWeight G s - edgeWeight G s * (if E G then (1 : ℝ) else 0) := by
      intro G; by_cases hG : E G <;> simp [hG]
    simp only [this, Finset.sum_sub_distrib, edgeWeight_sum]
  have h1 := e r
  have h2 := e r'
  linarith

/-- the SBM probability of a graph event lies between those of the bounding ER laws. -/
lemma sbm_ge_er_mono (m : ℕ) (p q lo : ℝ) (hlo : clamp01 lo ≤ clamp01 p ∧ clamp01 lo ≤ clamp01 q)
    (E : SimpleGraph (Fin (2 * m)) → Prop) (hE : ∀ G G', G ≤ G' → E G → E G') :
    erProb (2 * m) lo E ≤ sbmProb (2 * m) p q (fun _ G => E G) := by
  unfold erProb sbmProb
  have hc : (0 : ℝ) < (bisections (2 * m)).card := by exact_mod_cast (bisections_nonempty m).card_pos
  rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hc]
  calc (∑ G, edgeWeight G (fun _ _ => lo) * (if E G then (1 : ℝ) else 0)) * (bisections (2 * m)).card
      = ∑ _V1 ∈ bisections (2 * m), ∑ G, edgeWeight G (fun _ _ => lo) * (if E G then (1 : ℝ) else 0) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ _ := by
        apply Finset.sum_le_sum
        intro V1 _
        apply edgeWeight_mono _ _ _ E hE
        intro i j
        split_ifs
        · exact hlo.1
        · exact hlo.2

lemma sbm_ge_er_anti (m : ℕ) (p q hi : ℝ) (hhi : clamp01 p ≤ clamp01 hi ∧ clamp01 q ≤ clamp01 hi)
    (E : SimpleGraph (Fin (2 * m)) → Prop) (hE : ∀ G G', G ≤ G' → E G' → E G) :
    erProb (2 * m) hi E ≤ sbmProb (2 * m) p q (fun _ G => E G) := by
  unfold erProb sbmProb
  have hc : (0 : ℝ) < (bisections (2 * m)).card := by exact_mod_cast (bisections_nonempty m).card_pos
  rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hc]
  calc (∑ G, edgeWeight G (fun _ _ => hi) * (if E G then (1 : ℝ) else 0)) * (bisections (2 * m)).card
      = ∑ _V1 ∈ bisections (2 * m), ∑ G, edgeWeight G (fun _ _ => hi) * (if E G then (1 : ℝ) else 0) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ _ := by
        apply Finset.sum_le_sum
        intro V1 _
        apply edgeWeight_anti _ _ _ E hE
        intro i j
        split_ifs
        · exact hhi.1
        · exact hhi.2

end LPC17Aux

open Finset Filter Topology
open scoped Classical ENNReal

namespace LPC17Aux

open LPCommunity.SBMRecovery LPC7Aux LPC26Aux LPCommunity.LPFail

lemma rhoAvg_le_rhoMax {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) :
    rhoAvg G ≤ ((rhoMax G : ℕ∞) : ℝ≥0∞) := by
  unfold rhoAvg rhoMax
  set D : ℝ≥0∞ := ((G.ediam : ℕ∞) : ℝ≥0∞)
  have h1 : (∑ i : Fin n, ∑ j : Fin n, if i < j then ((G.edist i j : ℕ∞) : ℝ≥0∞) else 0) ≤
      ∑ i : Fin n, ∑ j : Fin n, if i < j then D else 0 := by
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    split_ifs
    · exact ENat.toENNReal_le.2 SimpleGraph.edist_le_ediam
    · exact le_rfl
  have h2 : (∑ i : Fin n, ∑ j : Fin n, if i < j then D else 0) = ((pairs n).card : ℝ≥0∞) * D := by
    rw [← Finset.sum_product' (s := (univ : Finset (Fin n))) (t := univ)
      (f := fun i j => if i < j then D else 0), Finset.univ_product_univ, ← Finset.sum_filter,
      Finset.sum_const, nsmul_eq_mul]
    rfl
  have h3 : 2 / (n : ℝ≥0∞) ^ 2 * ((pairs n).card : ℝ≥0∞) ≤ 1 := by
    have hc := card_pairs n
    rw [mul_comm, ← mul_div_assoc]
    apply ENNReal.div_le_of_le_mul
    rw [one_mul]
    have : (pairs n).card * 2 ≤ n ^ 2 := by rw [sq]; omega
    exact_mod_cast this
  calc 2 / (n : ℝ≥0∞) ^ 2 * (∑ i : Fin n, ∑ j : Fin n, if i < j then ((G.edist i j : ℕ∞) : ℝ≥0∞) else 0)
      ≤ 2 / (n : ℝ≥0∞) ^ 2 * (((pairs n).card : ℝ≥0∞) * D) := by rw [← h2]; gcongr
    _ = (2 / (n : ℝ≥0∞) ^ 2 * ((pairs n).card : ℝ≥0∞)) * D := by ring
    _ ≤ 1 * D := by gcongr
    _ = D := one_mul D

lemma rhoAvg_anti {n : ℕ} (G G' : SimpleGraph (Fin n)) (h : G ≤ G') : rhoAvg G' ≤ rhoAvg G := by
  unfold rhoAvg
  gcongr with i _ j _
  split_ifs
  · exact ENat.toENNReal_le.2 (SimpleGraph.edist_anti h)
  · exact le_rfl

lemma erProb_mono {n : ℕ} (p : ℝ) (E F : SimpleGraph (Fin n) → Prop) (h : ∀ G, E G → F G) :
    erProb n p E ≤ erProb n p F := by
  unfold erProb
  apply Finset.sum_le_sum
  intro G _
  apply mul_le_mul_of_nonneg_left _ (edgeWeight_nonneg _ _)
  by_cases hE : E G
  · simp [hE, h G hE]
  · simp only [hE, if_false]; split_ifs <;> norm_num

lemma two_mul_tendsto : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨b, fun m hm => by omega⟩

lemma clamp01_mono {a b : ℝ} (h : a ≤ b) : clamp01 a ≤ clamp01 b :=
  max_le_max le_rfl (min_le_min le_rfl h)

/-- SBM distance profile from the bounding ER laws. -/
lemma sbm_dist_of_er (lo hi p q : ℕ → ℝ)
    (hlo : ∀ n, clamp01 (lo n) ≤ clamp01 (p n) ∧ clamp01 (lo n) ≤ clamp01 (q n))
    (hhi : ∀ n, clamp01 (p n) ≤ clamp01 (hi n) ∧ clamp01 (q n) ≤ clamp01 (hi n))
    (K : ℕ) (L : ℝ)
    (h12lo : Tendsto (fun n => erProb n (lo n) (fun G => rhoMax G = (K : ℕ∞))) atTop (𝓝 1))
    (h12hi : Tendsto (fun n => erProb n (hi n) (fun G => rhoMax G = (K : ℕ∞))) atTop (𝓝 1))
    (h14 : Tendsto (fun n => erProb n (hi n) (fun G => ENNReal.ofReal L ≤ rhoAvg G)) atTop (𝓝 1)) :
    Tendsto (fun m : ℕ => sbmProb (2 * m) (p (2 * m)) (q (2 * m))
      (fun _ G => ENNReal.ofReal L ≤ rhoAvg G ∧ rhoAvg G ≤ ((rhoMax G : ℕ∞) : ℝ≥0∞) ∧
        rhoMax G = (K : ℕ∞))) atTop (𝓝 1) := by
  have squeeze : ∀ (f : ℕ → ℝ) (E : (m : ℕ) → Finset (Fin (2 * m)) → SimpleGraph (Fin (2 * m)) → Prop),
      Tendsto f atTop (𝓝 1) → (∀ m, f m ≤ sbmProb (2 * m) (p (2 * m)) (q (2 * m)) (E m)) →
      Tendsto (fun m => sbmProb (2 * m) (p (2 * m)) (q (2 * m)) (E m)) atTop (𝓝 1) := by
    intro f E hf hle
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hf tendsto_const_nhds hle
      (fun m => sbmProb_le_one m _ _ _)
  have hA := squeeze (fun m => erProb (2 * m) (lo (2 * m)) (fun G => rhoMax G = (K : ℕ∞)))
    (fun m _ G => rhoMax G ≤ (K : ℕ∞)) (h12lo.comp two_mul_tendsto) (fun m => by
      refine le_trans (erProb_mono _ _ (fun G => rhoMax G ≤ (K : ℕ∞)) (fun G h => h.le)) ?_
      exact sbm_ge_er_mono m _ _ _ (hlo (2 * m)) _ (fun G G' hGG' h =>
        le_trans (SimpleGraph.ediam_anti hGG') h))
  have hC := squeeze (fun m => erProb (2 * m) (hi (2 * m)) (fun G => rhoMax G = (K : ℕ∞)))
    (fun m _ G => (K : ℕ∞) ≤ rhoMax G) (h12hi.comp two_mul_tendsto) (fun m => by
      refine le_trans (erProb_mono _ _ (fun G => (K : ℕ∞) ≤ rhoMax G) (fun G h => h.ge)) ?_
      exact sbm_ge_er_anti m _ _ _ (hhi (2 * m)) _ (fun G G' hGG' h =>
        le_trans h (SimpleGraph.ediam_anti hGG')))
  have hB := squeeze (fun m => erProb (2 * m) (hi (2 * m)) (fun G => ENNReal.ofReal L ≤ rhoAvg G))
    (fun m _ G => ENNReal.ofReal L ≤ rhoAvg G) (h14.comp two_mul_tendsto) (fun m =>
      sbm_ge_er_anti m _ _ _ (hhi (2 * m)) _ (fun G G' hGG' h => le_trans h (rhoAvg_anti G G' hGG')))
  have hBAC := tendsto_and _ _ hB (tendsto_and _ _ hA hC)
  refine tendsto_of_imp _ _ hBAC (eventually_ge_atTop 1 |>.mono fun m hm V1 _ G h => ?_)
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, rhoAvg_le_rhoMax (by omega) G, le_antisymm h2 h3⟩

end LPC17Aux

open Finset Filter Topology
open scoped Classical ENNReal

open LPCommunity.SBMDense LPCommunity.SBMRecovery LPC7Aux LPC26Aux LPC17Aux LPCommunity.LPFail

lemma erProb_le_one' {n : ℕ} (p : ℝ) (E : SimpleGraph (Fin n) → Prop) : erProb n p E ≤ 1 := by
  have h := erProb_mono p E (fun _ => True) (fun _ _ => trivial)
  have e : erProb n p (fun _ => True) = 1 := by
    unfold erProb; simp only [if_true, mul_one]; exact edgeWeight_sum _
  linarith

lemma er_weaken (r : ℕ → ℝ) (E F : (n : ℕ) → SimpleGraph (Fin n) → Prop)
    (h : ∀ n G, E n G → F n G) (hE : Tendsto (fun n => erProb n (r n) (E n)) atTop (𝓝 1)) :
    Tendsto (fun n => erProb n (r n) (F n)) atTop (𝓝 1) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le hE tendsto_const_nhds
    (fun n => erProb_mono _ _ _ (h n)) (fun n => erProb_le_one' _ _)

lemma dense_le {a b ω : ℝ} (h : a ≤ b) (n : ℕ) : clamp01 (denseRegime a ω n) ≤ clamp01 (denseRegime b ω n) :=
  clamp01_mono (mul_le_mul_of_nonneg_right h (Real.rpow_nonneg (Nat.cast_nonneg n) _))

theorem solution (α β ω : ℝ) (hα : 0 < α) (hβ : 0 < β) (hω0 : 0 < ω) (hω1 : ω < 1)
    (hk : ¬ ∃ k : ℕ, 1 / (1 - ω) = k) (ε : ℝ) (hε : 0 < ε) :
    Filter.Tendsto
      (fun m : ℕ => LPCommunity.SBMRecovery.sbmProb (2 * m) (denseRegime α ω (2 * m)) (denseRegime β ω (2 * m))
        (fun _ G => ENNReal.ofReal ((1 - ε) * (⌈1 / (1 - ω)⌉₊ : ℝ)) ≤ LPCommunity.LPFail.rhoAvg G ∧
          LPCommunity.LPFail.rhoAvg G ≤ ((LPCommunity.LPFail.rhoMax G : ℕ∞) : ℝ≥0∞) ∧ LPCommunity.LPFail.rhoMax G = (⌈1 / (1 - ω)⌉₊ : ℕ∞)))
      Filter.atTop (nhds 1) := by
  have hx0 : 0 ≤ 1 / (1 - ω) := by apply div_nonneg zero_le_one; linarith
  have hK : 1 + ⌊1 / (1 - ω)⌋₊ = ⌈1 / (1 - ω)⌉₊ := by
    have hne : (⌊1 / (1 - ω)⌋₊ : ℝ) ≠ 1 / (1 - ω) := fun h => hk ⟨_, h.symm⟩
    have hlt : (⌊1 / (1 - ω)⌋₊ : ℝ) < 1 / (1 - ω) := lt_of_le_of_ne (Nat.floor_le hx0) hne
    have h1 : ⌊1 / (1 - ω)⌋₊ < ⌈1 / (1 - ω)⌉₊ := Nat.lt_ceil.2 hlt
    have h2 : ⌈1 / (1 - ω)⌉₊ ≤ ⌊1 / (1 - ω)⌋₊ + 1 :=
      Nat.ceil_le.2 (by push_cast; exact (Nat.lt_floor_add_one _).le)
    omega
  have hlo := lt_min hα hβ
  have hhi : 0 < max α β := lt_max_of_lt_left hα
  have h12lo := proposition_12 (min α β) ω hlo hω0.le hω1 (fun h => absurd h hω0.ne')
  have h12hi := proposition_12 (max α β) ω hhi hω0.le hω1 (fun h => absurd h hω0.ne')
  rw [hK] at h12lo h12hi
  have h14 := proposition_14 (max α β) ω hhi hω0 hω1 ε hε
  have hmu : mu ω (max α β) = (⌈1 / (1 - ω)⌉₊ : ℝ) := by
    unfold mu; rw [if_neg hk, add_zero]
  rw [hmu] at h14
  have h14' := er_weaken _ _ (fun n (G : SimpleGraph (Fin n)) =>
      ENNReal.ofReal ((1 - ε) * (⌈1 / (1 - ω)⌉₊ : ℝ)) ≤ rhoAvg G)
    (fun n G h => h.1.le) h14
  exact sbm_dist_of_er (fun n => denseRegime (min α β) ω n) (fun n => denseRegime (max α β) ω n)
    (fun n => denseRegime α ω n) (fun n => denseRegime β ω n)
    (fun n => ⟨dense_le (min_le_left _ _) n, dense_le (min_le_right _ _) n⟩)
    (fun n => ⟨dense_le (le_max_left _ _) n, dense_le (le_max_right _ _) n⟩)
    _ _ h12lo h12hi h14'
