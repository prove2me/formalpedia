-- Prove2me | solution 1 for LPCommunity.SBMDense.display_26
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T09:54:33.162747+00:00
-- url     : https://prove2.me/submissions/51ccaa74-b011-4147-824a-d8173f72e77f

import Mathlib
import Definitions.Def_LPCommunity_MinBisect_Setting
import Definitions.Def_LPCommunity_SBMRecovery_Setting

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

namespace LPC26Aux

/-- deterministic ratio bounds. -/
lemma ratio_bounds (m P Q X0 X1 ε δ : ℝ) (hm : 2 ≤ m) (hP : 0 < P) (hQ : 0 < Q) (hε : 0 < ε)
    (hδ : δ = ε / (2 * (2 + ε))) (hmε : 2 * (1 + ε) / ε ≤ m)
    (h0 : |X0 - m * m * Q| < δ * (m * m * Q))
    (h1 : |X1 - (m * m - m) * P| < δ * ((m * m - m) * P)) :
    (1 - ε) * (Q / (P + Q)) ≤ X0 / (X0 + X1) ∧ X0 / (X0 + X1) ≤ (1 + ε) * (Q / (P + Q)) := by
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδ1 : δ * (2 + ε) = ε / 2 := by rw [hδ]; field_simp
  have hmm : 0 < m * m - m := by nlinarith
  have hA := abs_lt.1 h0
  have hB := abs_lt.1 h1
  have hmQ : 0 < m * m * Q := by positivity
  have hX0 : 0 < X0 := by nlinarith
  have hmP : 0 < (m * m - m) * P := by positivity
  have hX1 : 0 < X1 := by nlinarith
  have hS : 0 < X0 + X1 := by linarith
  have hPQ : 0 < P + Q := by linarith
  constructor
  · rw [mul_div_assoc', div_le_div_iff₀ hPQ hS]
    -- (1-ε) Q (X0+X1) ≤ X0 (P+Q)
    rcases le_or_gt 1 ε with hε1 | hε1
    · nlinarith [mul_pos hX0 hPQ, mul_nonneg (sub_nonneg.2 hε1) (mul_pos hQ hS).le]
    · have k1 : (1 - ε) * (1 + δ) ≤ 1 - δ := by nlinarith
      have k2 : X1 ≤ (1 + δ) * (m * m) * P := by nlinarith
      have k3 : (1 - δ) * (m * m) * Q ≤ X0 := by nlinarith
      have k4 : (1 - ε) * Q * X1 ≤ (1 - ε) * Q * ((1 + δ) * (m * m) * P) :=
        mul_le_mul_of_nonneg_left k2 (by nlinarith)
      have k5 : (1 - ε) * (1 + δ) * (m * m * Q * P) ≤ (1 - δ) * (m * m * Q * P) :=
        mul_le_mul_of_nonneg_right k1 (by positivity)
      have k6 : (1 - δ) * (m * m) * Q * P ≤ X0 * P := mul_le_mul_of_nonneg_right k3 hP.le
      nlinarith [mul_pos hX0 hQ]
  · rw [mul_div_assoc', div_le_div_iff₀ hS hPQ]
    -- X0 (P+Q) ≤ (1+ε) Q (X0+X1)
    have k1 : (1 + δ) * m ≤ (1 + ε) * (1 - δ) * (m - 1) := by
      have : (1 + ε) * (1 - δ) - (1 + δ) = ε / 2 := by nlinarith
      have h2 : m * (ε / 2) ≥ 1 + ε := by
        have := (div_le_iff₀ hε).1 hmε
        nlinarith
      nlinarith
    have k2 : X0 ≤ (1 + δ) * (m * m * Q) := by nlinarith
    have k3 : (1 - δ) * ((m * m - m) * P) ≤ X1 := by nlinarith
    -- X0 * P ≤ (1+δ) m m Q P ≤ (1+ε)(1-δ)(m-1) m Q P ≤ (1+ε) Q X1
    have k4 : X0 * P ≤ (1 + δ) * (m * m * Q) * P := mul_le_mul_of_nonneg_right k2 hP.le
    have k5 : (1 + δ) * m * (m * Q * P) ≤ (1 + ε) * (1 - δ) * (m - 1) * (m * Q * P) :=
      mul_le_mul_of_nonneg_right k1 (by positivity)
    have k6 : (1 + ε) * Q * ((1 - δ) * ((m * m - m) * P)) ≤ (1 + ε) * Q * X1 :=
      mul_le_mul_of_nonneg_left k3 (by positivity)
    nlinarith [mul_pos hX0 hQ]

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

open Finset Filter Topology
open scoped Classical

open LPCommunity.SBMRecovery LPC7Aux LPC26Aux

theorem solution (p q : ℕ → ℝ)
    (hpq : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      c * Real.log n / n ≤ p n ∧ c * Real.log n / n ≤ q n)
    (hpq1 : ∀ᶠ n : ℕ in Filter.atTop, p n ≤ 1 ∧ q n ≤ 1)
    (r : ℝ) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hlim : Filter.Tendsto (fun n : ℕ => q n / p n) Filter.atTop (nhds r))
    (ε : ℝ) (hε : 0 < ε) :
    Filter.Tendsto
      (fun m : ℕ => LPCommunity.SBMRecovery.sbmProb (2 * m) (p (2 * m)) (q (2 * m))
        (fun V1 G =>
          (1 - ε) * (q (2 * m) / (p (2 * m) + q (2 * m))) ≤
              (LPCommunity.MinBisect.cutCost G V1 : ℝ) / (G.edgeFinset.card : ℝ) ∧
            (LPCommunity.MinBisect.cutCost G V1 : ℝ) / (G.edgeFinset.card : ℝ) ≤
              (1 + ε) * (q (2 * m) / (p (2 * m) + q (2 * m)))))
      Filter.atTop (nhds 1) := by
  obtain ⟨c, hc, hev⟩ := hpq
  set δ := ε / (2 * (2 + ε)) with hδ
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K := 4 / (δ ^ 2 * c * Real.log 2) with hK
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hev.and hpq1)
  set M := max (max N 2) ⌈2 * (1 + ε) / ε⌉₊ with hM
  have key : ∀ m ≥ M, 1 - K / ((m : ℝ) - 1) ≤ sbmProb (2 * m) (p (2 * m)) (q (2 * m))
      (fun V1 G =>
          (1 - ε) * (q (2 * m) / (p (2 * m) + q (2 * m))) ≤
              (LPCommunity.MinBisect.cutCost G V1 : ℝ) / (G.edgeFinset.card : ℝ) ∧
            (LPCommunity.MinBisect.cutCost G V1 : ℝ) / (G.edgeFinset.card : ℝ) ≤
              (1 + ε) * (q (2 * m) / (p (2 * m) + q (2 * m)))) := by
    intro m hm
    have hmN : N ≤ 2 * m := by
      have := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hm); omega
    have hm2 : 2 ≤ m := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hm)
    have hmε : 2 * (1 + ε) / ε ≤ (m : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hm)
    obtain ⟨⟨hPc, hQc⟩, hP1, hQ1⟩ := hN (2 * m) hmN
    set P := p (2 * m) with hPdef
    set Q := q (2 * m) with hQdef
    have hm2' : (2 : ℝ) ≤ m := by exact_mod_cast hm2
    have hn : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
    have hlog : Real.log 2 ≤ Real.log ((2 * m : ℕ) : ℝ) := by
      rw [hn]; exact Real.log_le_log (by norm_num) (by linarith)
    have hcl : c * Real.log 2 / 2 * m ≤ c * Real.log ((2 * m : ℕ) : ℝ) / ((2 * m : ℕ) : ℝ) * (m * m) := by
      rw [hn]
      have : c * Real.log (2 * (m : ℝ)) / (2 * m) * (m * m) = c * Real.log (2 * (m : ℝ)) / 2 * m := by
        field_simp
      rw [this, ← hn]
      gcongr
    have hcl0 : 0 < c * Real.log ((2 * m : ℕ) : ℝ) / ((2 * m : ℕ) : ℝ) := by
      have : 0 < Real.log ((2 * m : ℕ) : ℝ) := lt_of_lt_of_le hl2 hlog
      rw [hn] at this ⊢; positivity
    have hP0 : 0 < P := lt_of_lt_of_le hcl0 hPc
    have hQ0 : 0 < Q := lt_of_lt_of_le hcl0 hQc
    refine sbmProb_ge _ _ (bisections_nonempty m) _ _ (fun V1 hV1 => ?_)
    have hV : V1.card = m := by
      have : 2 * V1.card = 2 * m := by simpa [bisections, LPCommunity.MinBisect.IsBisection] using hV1
      omega
    set rr : Fin (2 * m) → Fin (2 * m) → ℝ :=
      fun i j => if LPCommunity.MinBisect.sameSide V1 i j then P else Q with hrr
    set S0 : Finset (PI (2 * m)) :=
      univ.filter fun i => ¬ LPCommunity.MinBisect.sameSide V1 i.1.1 i.1.2 with hS0
    set S1 : Finset (PI (2 * m)) :=
      univ.filter fun i => LPCommunity.MinBisect.sameSide V1 i.1.1 i.1.2 with hS1
    have hclP : clamp01 P = P := by unfold clamp01; rw [min_eq_right hP1, max_eq_right hP0.le]
    have hclQ : clamp01 Q = Q := by unfold clamp01; rw [min_eq_right hQ1, max_eq_right hQ0.le]
    have hcS0 : (S0.card : ℝ) = m * m := by
      rw [hS0, card_cnt_set (fun p => ¬ LPCommunity.MinBisect.sameSide V1 p.1 p.2), card_cross m V1 hV]
      push_cast; ring
    have hcU : ((univ : Finset (PI (2 * m))).card : ℝ) = 2 * m * m - m := by
      rw [Finset.card_univ, Fintype.card_coe]
      have := card_pairs (2 * m)
      have h' : ((2 * (pairs (2 * m)).card + 2 * m : ℕ) : ℝ) = ((2 * m * (2 * m) : ℕ) : ℝ) := by
        rw [this]
      push_cast at h'
      linarith
    have hcS1 : (S1.card : ℝ) = m * m - m := by
      have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (PI (2 * m))))
        (fun i => LPCommunity.MinBisect.sameSide V1 i.1.1 i.1.2)
      have h' : ((S1.card + S0.card : ℕ) : ℝ) = ((univ : Finset (PI (2 * m))).card : ℝ) := by
        rw [hS1, hS0]; exact_mod_cast this
      push_cast at h'
      linarith
    have hμ0 : ∑ i ∈ S0, clamp01 (rr i.1.1 i.1.2) = m * m * Q := by
      rw [Finset.sum_congr rfl (g := fun _ => Q), Finset.sum_const, nsmul_eq_mul, hcS0]
      intro i hi
      rw [hS0, Finset.mem_filter] at hi
      simp only [hrr, if_neg hi.2, hclQ]
    have hμ1 : ∑ i ∈ S1, clamp01 (rr i.1.1 i.1.2) = (m * m - m) * P := by
      rw [Finset.sum_congr rfl (g := fun _ => P), Finset.sum_const, nsmul_eq_mul, hcS1]
      intro i hi
      rw [hS1, Finset.mem_filter] at hi
      simp only [hrr, if_pos hi.2, hclP]
    have hmm : 0 < (m : ℝ) * m - m := by nlinarith
    have hb := perV1_bound rr S0 S1 δ (by rw [hμ0]; positivity) (by rw [hμ1]; positivity)
      (fun G => (1 - ε) * (Q / (P + Q)) ≤
              (LPCommunity.MinBisect.cutCost G V1 : ℝ) / (G.edgeFinset.card : ℝ) ∧
            (LPCommunity.MinBisect.cutCost G V1 : ℝ) / (G.edgeFinset.card : ℝ) ≤
              (1 + ε) * (Q / (P + Q))) (fun G h0 h1 => by
        rw [hμ0] at h0; rw [hμ1] at h1
        have hcut : (LPCommunity.MinBisect.cutCost G V1 : ℝ) = cnt S0 (graphEquiv (2 * m) G) := by
          unfold LPCommunity.MinBisect.cutCost
          rw [card_filter_pairs_eq_cnt G (fun p => ¬ LPCommunity.MinBisect.sameSide V1 p.1 p.2)]
        have hEc : (G.edgeFinset.card : ℝ) = cnt S0 (graphEquiv (2 * m) G) +
            cnt S1 (graphEquiv (2 * m) G) := by
          rw [edge_card_eq_cnt]
          unfold cnt
          rw [hS0, hS1, add_comm]
          exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
        rw [hcut, hEc]
        exact ratio_bounds m P Q _ _ ε δ hm2' hP0 hQ0 hε hδ hmε h0 h1)
    refine le_trans ?_ hb
    rw [hμ0, hμ1]
    -- bound the Chebyshev error
    have hA : 0 < (m : ℝ) - 1 := by linarith
    have hμ0' : c * Real.log 2 / 2 * ((m : ℝ) - 1) ≤ m * m * Q := by
      have h1 := mul_le_mul_of_nonneg_left hQc (by positivity : (0:ℝ) ≤ m * m)
      have h2 : c * Real.log 2 / 2 * ((m : ℝ) - 1) ≤ c * Real.log 2 / 2 * m :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      calc _ ≤ _ := h2
        _ ≤ _ := hcl
        _ = (m * m) * (c * Real.log ((2 * m : ℕ) : ℝ) / ((2 * m : ℕ) : ℝ)) := by ring
        _ ≤ _ := h1
    have hμ1' : c * Real.log 2 / 2 * ((m : ℝ) - 1) ≤ (m * m - m) * P := by
      have h1 := mul_le_mul_of_nonneg_left hPc hmm.le
      have e : c * Real.log ((2 * m : ℕ) : ℝ) / ((2 * m : ℕ) : ℝ) * ((m : ℝ) * m - m) =
          c * Real.log ((2 * m : ℕ) : ℝ) / 2 * ((m : ℝ) - 1) := by
        rw [hn]; field_simp
      have h2 : c * Real.log 2 / 2 * ((m : ℝ) - 1) ≤ c * Real.log ((2 * m : ℕ) : ℝ) / 2 * ((m : ℝ) - 1) := by
        gcongr
      calc _ ≤ _ := h2
        _ = _ := e.symm
        _ = ((m : ℝ) * m - m) * (c * Real.log ((2 * m : ℕ) : ℝ) / ((2 * m : ℕ) : ℝ)) := by ring
        _ ≤ _ := h1
    have hB : 0 < c * Real.log 2 / 2 * ((m : ℝ) - 1) := by positivity
    have f : ∀ μ : ℝ, c * Real.log 2 / 2 * ((m : ℝ) - 1) ≤ μ →
        μ / (δ * μ) ^ 2 ≤ (K / 2) / ((m : ℝ) - 1) := by
      intro μ hμ
      have hμ0 : 0 < μ := lt_of_lt_of_le hB hμ
      have e1 : μ / (δ * μ) ^ 2 = 1 / (δ ^ 2 * μ) := by field_simp
      have e2 : (K / 2) / ((m : ℝ) - 1) = 1 / (δ ^ 2 * (c * Real.log 2 / 2 * ((m : ℝ) - 1))) := by
        rw [hK]; field_simp; ring
      rw [e1, e2]
      gcongr
    have := f _ hμ0'
    have := f _ hμ1'
    have e3 : K / ((m : ℝ) - 1) = (K / 2) / ((m : ℝ) - 1) + (K / 2) / ((m : ℝ) - 1) := by ring
    linarith
  have hlow : Tendsto (fun m : ℕ => 1 - K / ((m : ℝ) - 1)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun m : ℕ => (m : ℝ) - 1) atTop atTop :=
      tendsto_atTop_add_const_right _ (-1) tendsto_natCast_atTop_atTop |>.congr (fun m => by ring)
    have h2 := (tendsto_const_nhds (x := K)).div_atTop h1
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_
    (Eventually.of_forall fun m => sbmProb_le_one m _ _ _)
  filter_upwards [eventually_ge_atTop M] with m hm
  exact key m hm
