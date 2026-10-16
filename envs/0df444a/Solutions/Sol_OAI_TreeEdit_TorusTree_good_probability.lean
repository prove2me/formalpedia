-- Prove2me | solution 1 for OAI.TreeEdit.TorusTree.good_probability
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:48:56.426525+00:00
-- url     : https://prove2.me/submissions/c491de6a-6a8a-442e-a0ac-8fe84b8ea513

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/CircleTree.lean:L435-L458
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.TorusTree.good_probability. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree
import Theorems.Thm_OAI_TreeEdit_FiniteProbability_probability_eq_of_uniform
import Theorems.Thm_OAI_TreeEdit_FiniteProbability_probability_union_bound
import Theorems.Thm_OAI_TreeEdit_TorusTree_fixed_residue_failure

-- ---- from OAI.Combinatorics.TreeEdit.FiniteProbability ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

namespace TreeEdit.FiniteProbability
open scoped BigOperators
open Classical

lemma mean_nonneg {A : Type*} [Fintype A] {f : A → ℝ} (hf : ∀ a, 0 ≤ f a) :
    0 ≤ mean f := mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg (fun a _ => hf a))

lemma mean_le {A : Type*} [Fintype A] {f g : A → ℝ} (h : ∀ a, f a ≤ g a) :
    mean f ≤ mean g := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => h a)) (by positivity)

lemma mean_const {A : Type*} [Fintype A] [Nonempty A] (c : ℝ) : mean (fun _ : A => c) = c := by
  simp only [mean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]

lemma mean_add {A : Type*} [Fintype A] (f g : A → ℝ) :
    mean (fun a => f a + g a) = mean f + mean g := by simp [mean, Finset.sum_add_distrib, mul_add]

lemma probability_nonneg {A : Type*} [Fintype A] (E : A → Prop) : 0 ≤ probability E := by
  classical
  exact mean_nonneg (fun _ => by split_ifs <;> norm_num)

lemma probability_le_one {A : Type*} [Fintype A] [Nonempty A] (E : A → Prop) :
    probability E ≤ 1 := by
  classical
  exact (mean_le (fun a => show (if E a then (1 : ℝ) else 0) ≤ 1 by split_ifs <;> norm_num)).trans_eq (mean_const 1)

lemma probability_not {A : Type*} [Fintype A] [Nonempty A] (E : A → Prop) :
    probability (fun a => ¬ E a) = 1 - probability E := by
  classical
  have hh : probability E + probability (fun a => ¬ E a) = 1 := by
    rw [probability, probability, ← mean_add]
    calc
      _ = mean (fun _ : A => (1 : ℝ)) := by
        apply congrArg mean
        funext a
        by_cases h : E a <;> simp [h]
      _ = 1 := mean_const 1
  linarith

lemma probability_mono {A : Type*} [Fintype A] {E F : A → Prop} (h : ∀ a, E a → F a) :
    probability E ≤ probability F := by
  classical
  apply mean_le
  intro a
  by_cases he : E a <;> by_cases hf : F a <;> simp_all

lemma mean_equiv {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) (f : B → ℝ) :
    mean (fun a => f (e a)) = mean f := by
  simp only [mean, Fintype.card_congr e]
  congr 1
  exact e.sum_comp f

lemma mean_pair {A B : Type*} [Fintype A] [Fintype B] (f : A × B → ℝ) :
    mean f = mean (fun a => mean (fun b => f (a, b))) := by
  simp only [mean, Fintype.card_prod, Nat.cast_mul, mul_inv_rev,
    Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma perm_eval_probability {A : Type*} [Fintype A] (a b : A) :
    probability (fun σ : Equiv.Perm A => σ a = b) = (Fintype.card A : ℝ)⁻¹ := by
  apply probability_eq_of_uniform
  intro b c
  let τ := Equiv.swap b c
  let e : Equiv.Perm A ≃ Equiv.Perm A := Equiv.mulLeft τ
  have he (σ : Equiv.Perm A) : e σ a = c ↔ σ a = b := by
    change τ (σ a) = c ↔ σ a = b
    rw [← Equiv.swap_apply_left b c]
    exact τ.injective.eq_iff
  have hh := mean_equiv e (fun σ : Equiv.Perm A => if σ a = c then (1 : ℝ) else 0)
  simpa only [he, probability] using hh

lemma permutation_avoidance {A I : Type*} [Fintype A] [Fintype I]
    (f : I → A) (a : A) :
    probability (fun σ : Equiv.Perm A => ∃ i, σ (f i) = a) ≤
      (Fintype.card I : ℝ) / Fintype.card A := by
  calc
    _ ≤ ∑ i : I, probability (fun σ : Equiv.Perm A => σ (f i) = a) := by
      simpa using probability_union_bound Finset.univ (fun (i : I) (σ : Equiv.Perm A) => σ (f i) = a)
    _ = _ := by simp [perm_eval_probability, div_eq_mul_inv]

lemma probability_pair {A B : Type*} [Fintype A] [Fintype B] (E : A × B → Prop) :
    probability E = mean (fun a => probability (fun b => E (a, b))) := mean_pair _

lemma pair_failure_bound {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (E : A → Prop) (F : A → B → Prop) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ a, ¬ E a → probability (F a) ≤ δ) :
    probability (fun x : A × B => F x.1 x.2) ≤ probability E + δ := by
  rw [probability_pair]
  calc
    _ ≤ mean (fun a => (if E a then (1 : ℝ) else 0) + δ) := mean_le (by
      intro a
      by_cases ha : E a
      · simp only [ha, ↓reduceIte]
        exact (probability_le_one (F a)).trans (by linarith)
      · simpa [ha] using h a ha)
    _ = _ := by rw [mean_add, mean_const]; rfl

end TreeEdit.FiniteProbability

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.CircleTree ----
namespace OAI

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical

lemma point_period {n : ℕ} (hn : 0 < n) : n • point n = 0 := by
  simp only [point, ← AddCircle.coe_nsmul, nsmul_eq_mul]
  rw [mul_inv_cancel₀ (by exact_mod_cast hn.ne')]
  exact AddCircle.coe_period (1 : ℝ)

lemma circle_period_lower {x : UnitAddCircle} {d : ℕ} (hd : 0 < d)
    (hx : d • x = 0) (hx0 : x ≠ 0) : 1 ≤ (d : ℝ) * ‖x‖ := by
  let : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  have hf : IsOfFinAddOrder x := isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨d, hd, hx⟩
  have hh := AddCircle.le_add_order_smul_norm_of_isOfFinAddOrder hf hx0
  simp only [nsmul_eq_mul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast addOrderOf_le_of_nsmul_eq_zero hd hx) (norm_nonneg _))

lemma nearby_unique {t x y : UnitAddCircle} {d e K : ℕ} {ε : ℝ}
    (hd : 0 < d) (he : 0 < e) (hdK : d ≤ K) (heK : e ≤ K)
    (hx : d • x = 0) (hy : e • y = 0) (hε : 2 * ε * (K : ℝ) ^ 2 < 1)
    (htx : ‖t + x‖ < ε) (hty : ‖t + y‖ < ε) : x = y := by
  by_contra hn
  have hperiod : (d * e) • (x - y) = 0 := by
    rw [nsmul_sub]
    rw [show d * e = e * d by ring, mul_smul, hx, smul_zero,
      show e * d = d * e by ring, mul_smul, hy, smul_zero, sub_self]
  have hh := circle_period_lower (Nat.mul_pos hd he) hperiod (sub_ne_zero.mpr hn)
  have hnorm : ‖x - y‖ < 2 * ε := by
    calc
      _ = ‖(t + x) - (t + y)‖ := by congr 1; abel
      _ ≤ ‖t + x‖ + ‖t + y‖ := norm_sub_le _ _
      _ < _ := by linarith
  have hK : 0 < (K : ℝ) := by exact_mod_cast hd.trans_le hdK
  have hde : (d : ℝ) * e ≤ (K : ℝ) ^ 2 := by
    have hd' : (d : ℝ) ≤ K := by exact_mod_cast hdK
    have he' : (e : ℝ) ≤ K := by exact_mod_cast heK
    nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d), (Nat.cast_nonneg e : (0 : ℝ) ≤ e)]
  push_cast at hh
  have hh' := mul_le_mul_of_nonneg_right hde (norm_nonneg (x - y))
  have hh'' := mul_lt_mul_of_pos_left hnorm (sq_pos_of_pos hK)
  nlinarith

lemma sparse_order {I : Type*} [Fintype I] (r : I → ℕ)
    (hr : ∀ i, Nat.Prime (r i)) (hinj : Function.Injective r)
    {U k a : ℕ} (hU : 1 ≤ U) (hrU : ∀ i, r i ≤ U)
    (hcard : (Finset.univ.filter (fun i => ¬ r i ∣ a)).card ≤ k) :
    addOrderOf (a • point (∏ i, r i)) ≤ U ^ k := by
  let s := Finset.univ.filter (fun i => ¬ r i ∣ a)
  let t := Finset.univ.filter (fun i => r i ∣ a)
  let D := ∏ i ∈ s, r i
  let P := ∏ i, r i
  have hP : 0 < P := product_positive r (fun i => (hr i).pos)
  have hD : 0 < D := Finset.prod_pos (fun i _ => (hr i).pos)
  have ht : (∏ i ∈ t, r i) ∣ a := by
    have hcop : (↑t : Set I).Pairwise (fun i j => IsCoprime (r i : ℤ) (r j : ℤ)) := by
      intro i _ j _ hij
      exact ((Nat.coprime_primes (hr i) (hr j)).mpr (fun h => hij (hinj h))).isCoprime
    have hd : (∏ i ∈ t, (r i : ℤ)) ∣ (a : ℤ) := Finset.prod_dvd_of_coprime hcop
      (fun i hi => by exact_mod_cast (Finset.mem_filter.mp hi).2)
    exact_mod_cast hd
  have he : D * (∏ i ∈ t, r i) = P := by
    simpa [D, s, t, P] using Finset.prod_filter_mul_prod_filter_not (s := Finset.univ) (p := fun i => ¬ r i ∣ a) r
  have hPD : P ∣ D * a := by
    obtain ⟨b, hb⟩ := ht
    exact ⟨b, by rw [hb, ← he]; ring⟩
  have hz : D • (a • point P) = 0 := by
    rw [← mul_smul]
    obtain ⟨b, hb⟩ := hPD
    rw [hb, mul_smul, smul_comm, point_period hP, smul_zero]
  calc
    _ ≤ D := addOrderOf_le_of_nsmul_eq_zero hD hz
    _ ≤ U ^ s.card := by
      calc
        _ ≤ ∏ _i ∈ s, U := Finset.prod_le_prod' (fun i _ => hrU i)
        _ = _ := Finset.prod_const U
    _ ≤ U ^ k := pow_le_pow_right₀ hU hcard

lemma sparse_bad_prime {t : UnitAddCircle} {ε : ℝ} {U k : ℕ}
    (ht : ε ≤ ‖t‖) (hε : 2 * ε * ((U ^ k : ℕ) : ℝ) ^ 2 < 1) :
    ∃ p : ℕ, Nat.Prime p ∧ ∀ {I : Type*} [Fintype I] (r : I → ℕ),
      (∀ i, Nat.Prime (r i)) → Function.Injective r → 1 ≤ U → (∀ i, r i ≤ U) →
      ∀ a : ℕ, (Finset.univ.filter (fun i => ¬ r i ∣ a)).card ≤ k →
        ‖t + a • point (∏ i, r i)‖ < ε → ∃ i, r i = p := by
  let E (x : UnitAddCircle) := IsOfFinAddOrder x ∧ addOrderOf x ≤ U ^ k ∧ ‖t + x‖ < ε
  by_cases hex : ∃ x, E x
  · obtain ⟨x, hxfin, hxK, hxnorm⟩ := hex
    have hx0 : x ≠ 0 := by intro hz; rw [hz, add_zero] at hxnorm; exact hxnorm.not_ge ht
    have ho : addOrderOf x ≠ 1 := by simpa using hx0
    let p := (addOrderOf x).minFac
    have hp : Nat.Prime p := Nat.minFac_prime ho
    refine ⟨p, hp, ?_⟩
    intro I _ r hr hi hU hrU a hcard hbad
    have hP : 0 < ∏ i, r i := product_positive r (fun i => (hr i).pos)
    have hyper : (∏ i, r i) • (a • point (∏ i, r i)) = 0 := by
      rw [smul_comm, point_period hP, smul_zero]
    have hyfin : IsOfFinAddOrder (a • point (∏ i, r i)) :=
      isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨_, hP, hyper⟩
    have hxy : x = a • point (∏ i, r i) := nearby_unique
      (addOrderOf_pos_iff.mpr hxfin) (addOrderOf_pos_iff.mpr hyfin)
      hxK (sparse_order r hr hi hU hrU hcard)
      (addOrderOf_nsmul_eq_zero x) (addOrderOf_nsmul_eq_zero _) hε hxnorm hbad
    have hdiv : p ∣ ∏ i, r i := (Nat.minFac_dvd _).trans
      (by rw [hxy]; exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hyper)
    obtain ⟨i, _, hpi⟩ := (hp.prime.dvd_finsetProd_iff r).mp hdiv
    exact ⟨i, ((hr i).eq_one_or_self_of_dvd p hpi).resolve_left hp.ne_one |>.symm⟩
  · refine ⟨2, Nat.prime_two, ?_⟩
    intro I _ r hr hi hU hrU a hcard hbad
    exfalso
    apply hex
    have hP : 0 < ∏ i, r i := product_positive r (fun i => (hr i).pos)
    refine ⟨a • point (∏ i, r i), ?_, sparse_order r hr hi hU hrU hcard, hbad⟩
    exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨_, hP, by rw [smul_comm, point_period hP, smul_zero]⟩

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical
open FiniteProbability

lemma prime_list_event {I : Type*} [Fintype I] (r : I → ℕ)
    (hr : ∀ i, Nat.Prime (r i)) (hi : Function.Injective r)
    {U k g : ℕ} (hU : 1 ≤ U) (hrU : ∀ i, r i ≤ U) (j : Fin g ↪ I)
    {t : UnitAddCircle} {ε : ℝ} (ht : ε ≤ ‖t‖)
    (hε : 2 * ε * ((U ^ k : ℕ) : ℝ) ^ 2 < 1) :
    probability (fun σ : Equiv.Perm I => ¬ ∀ a : ℕ,
      (Finset.univ.filter (fun i => ¬ r (σ (j i)) ∣ a)).card ≤ k →
      ε ≤ ‖t + a • point (∏ i : Fin g, r (σ (j i)))‖) ≤
      (g : ℝ) / Fintype.card I := by
  obtain ⟨p, _, hp⟩ := sparse_bad_prime ht hε
  have himpl (σ : Equiv.Perm I) (hbad : ¬ ∀ a : ℕ,
      (Finset.univ.filter (fun i => ¬ r (σ (j i)) ∣ a)).card ≤ k →
      ε ≤ ‖t + a • point (∏ i : Fin g, r (σ (j i)))‖) :
      ∃ i : Fin g, r (σ (j i)) = p := by
    push Not at hbad
    obtain ⟨a, ha, hna⟩ := hbad
    exact hp (fun i : Fin g => r (σ (j i))) (fun _ => hr _) (hi.comp (σ.injective.comp j.injective))
      hU (fun _ => hrU _) a ha hna
  by_cases hex : ∃ v, r v = p
  · obtain ⟨v, hv⟩ := hex
    calc
      _ ≤ probability (fun σ : Equiv.Perm I => ∃ i : Fin g, σ (j i) = v) := probability_mono (by
        intro σ hσ
        obtain ⟨i, hh⟩ := himpl σ hσ
        exact ⟨i, hi (hh.trans hv.symm)⟩)
      _ ≤ _ := by simpa using permutation_avoidance j v
  · have hz : probability (fun σ : Equiv.Perm I => ¬ ∀ a : ℕ,
        (Finset.univ.filter (fun i => ¬ r (σ (j i)) ∣ a)).card ≤ k →
        ε ≤ ‖t + a • point (∏ i : Fin g, r (σ (j i)))‖) = 0 := by
      apply le_antisymm _ (probability_nonneg _)
      calc
        _ ≤ probability (fun _ : Equiv.Perm I => False) := probability_mono (by
          intro σ hσ
          obtain ⟨i, hh⟩ := himpl σ hσ
          exact hex ⟨_, hh⟩)
        _ = 0 := by simp [probability, mean]
    rw [hz]
    positivity

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical
open FiniteProbability

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical
open FiniteProbability

lemma conditional_good_failure {I : Type} [Fintype I] {k s L U h : ℕ} [NeZero L]
    (r : I → ℕ) (hr : ∀ i, Nat.Prime (r i)) (hr10 : ∀ i, 10 ≤ r i)
    (hrU : ∀ i, r i ≤ U) (hL : ∀ i, r i ∣ L) (j : Fin (16 * k) ↪ I)
    {ε : ℝ} (hgrid : ∀ i, 2 * ε * r i < 1)
    (ih : ∀ t : UnitAddCircle, ε ≤ ‖t‖ → 9 / 10 ≤
      probability (fun C : Config I L (16 * k * s) h => Good ε r j h C t))
    (σ : Equiv.Perm I) (t : UnitAddCircle)
    (hlist : ∀ a : ℕ, (Finset.univ.filter (fun v : Fin (16 * k) => ¬ r (σ (j v)) ∣ a)).card ≤ k →
      ε ≤ ‖t + a • point (period r j σ)‖) :
    probability (fun C : Fin (16 * k * s) → ZMod L × Config I L (16 * k * s) h =>
      ¬ Good ε r j (h + 1) (σ, C) t) ≤ (U : ℝ) ^ (16 * k) * (4 / 5 : ℝ) ^ (k * s) := by
  let E (a : Fin (period r j σ)) (C : Fin (16 * k * s) → ZMod L × Config I L (16 * k * s) h) :=
    ¬ 16 * k * s ≤ 64 * (Finset.univ.filter (fun i =>
      Good ε r j h (C i).2 (t + (a.val * coefficient r j σ (C i).1 i) • point (period r j σ)))).card
  have he : (fun C : Fin (16 * k * s) → ZMod L × Config I L (16 * k * s) h =>
      ¬ Good ε r j (h + 1) (σ, C) t) = (fun C => ∃ a ∈ Finset.univ, E a C) := by
    funext C
    simp only [Good, E, Finset.mem_univ, true_and, not_forall]
  rw [he]
  calc
    _ ≤ ∑ a, probability (E a) := probability_union_bound Finset.univ E
    _ ≤ ∑ _a : Fin (period r j σ), (4 / 5 : ℝ) ^ (k * s) := Finset.sum_le_sum (fun a _ =>
      fixed_residue_failure r hr hr10 hL j hgrid ih σ t hlist a)
    _ = (period r j σ : ℝ) * (4 / 5 : ℝ) ^ (k * s) := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hP : period r j σ ≤ U ^ (16 * k) := by
        calc
          _ ≤ ∏ _v : Fin (16 * k), U := Finset.prod_le_prod' (fun _ _ => hrU _)
          _ = _ := by simp
      exact_mod_cast hP

theorem good_probability {I : Type} [Fintype I] {k s L U : ℕ} [NeZero L]
    (r : I → ℕ) (hr : ∀ i, Nat.Prime (r i)) (hi : Function.Injective r)
    (hr10 : ∀ i, 10 ≤ r i) (hU : 1 ≤ U) (hrU : ∀ i, r i ≤ U)
    (hL : ∀ i, r i ∣ L) (j : Fin (16 * k) ↪ I)
    {ε : ℝ} (hgrid : ∀ i, 2 * ε * r i < 1)
    (hε : 2 * ε * ((U ^ k : ℕ) : ℝ) ^ 2 < 1)
    (herr : (16 * k : ℝ) / Fintype.card I + (U : ℝ) ^ (16 * k) * (4 / 5 : ℝ) ^ (k * s) ≤ 1 / 10)
    (h : ℕ) (t : UnitAddCircle) (ht : ε ≤ ‖t‖) :
    9 / 10 ≤ probability (fun C : Config I L (16 * k * s) h => Good ε r j h C t) := by
  induction h generalizing t with
  | zero => norm_num [Good, ht, probability, mean_const]
  | succ h ih =>
    let bad (σ : Equiv.Perm I) := ¬ ∀ a : ℕ,
      (Finset.univ.filter (fun v : Fin (16 * k) => ¬ r (σ (j v)) ∣ a)).card ≤ k →
      ε ≤ ‖t + a • point (period r j σ)‖
    have hbad : probability bad ≤ (16 * k : ℝ) / Fintype.card I := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, bad, period] using prime_list_event r hr hi hU hrU j ht hε
    have hh := pair_failure_bound bad (fun σ C => ¬ Good ε r j (h + 1) (σ, C) t)
      (δ := (U : ℝ) ^ (16 * k) * (4 / 5 : ℝ) ^ (k * s)) (by positivity)
      (fun σ hσ => conditional_good_failure r hr hr10 hrU hL j hgrid ih σ t (not_not.mp hσ))
    have he : probability (fun C : Config I L (16 * k * s) (h + 1) => ¬ Good ε r j (h + 1) C t) ≤ 1 / 10 := by
      exact hh.trans (by linarith)
    rw [probability_not] at he
    linarith

end TreeEdit.TorusTree

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.TorusTree
open scoped BigOperators
open Classical
open FiniteProbability


theorem solution : type_of% @_root_.OAI.TreeEdit.TorusTree.good_probability := @_root_.OAI.TreeEdit.TorusTree.good_probability
