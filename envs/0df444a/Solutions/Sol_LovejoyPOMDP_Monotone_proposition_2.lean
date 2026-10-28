-- Prove2me | solution 1 for LovejoyPOMDP.Monotone.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-28T02:36:42.738743+00:00
-- url     : https://prove2.me/submissions/e5d4a1cf-901a-4d8a-abe4-9082b3cfb151

import Mathlib
import Definitions.Def_LovejoyPOMDP_Monotone_Model




noncomputable section
open scoped BigOperators
namespace LovejoyPOMDP.Monotone.LPFresh
variable {S O A : Type*} [Fintype S] [Fintype O]

lemma predict_simplex (M : POMDP S O A) {π : S → ℝ}
    (hπ : π ∈ stdSimplex ℝ S) (a : A) : M.predict π a ∈ stdSimplex ℝ S := by
  constructor
  · intro j
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hπ.1 i) ((M.P_row a i).1 j))
  · simp only [POMDP.predict]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, (M.P_row a _).2, mul_one]
    exact hπ.2

lemma sigma_predict (M : POMDP S O A) (π : S → ℝ) (a : A) (k : O) :
    M.sigma π a k = ∑ j, M.predict π a j*M.R a j k := by
  simp only [POMDP.sigma, POMDP.predict, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma sigma_simplex (M : POMDP S O A) {π : S → ℝ}
    (hπ : π ∈ stdSimplex ℝ S) (a : A) : M.sigma π a ∈ stdSimplex ℝ O := by
  have hp := predict_simplex M hπ a
  constructor
  · intro k
    rw [sigma_predict]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hp.1 j) ((M.R_row a j).1 k))
  · simp only [sigma_predict]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, (M.R_row a _).2, mul_one]
    exact hp.2

lemma sigma_pos (M : POMDP S O A) {π : S → ℝ}
    (hπ : π ∈ stdSimplex ℝ S) (a : A) (k : O) : 0 < M.sigma π a k := by
  classical
  have hp := predict_simplex M hπ a
  have hpos : 0 < ∑ j, M.predict π a j := by rw [hp.2]; norm_num
  have he : ∃ j, 0 < M.predict π a j := by
    by_contra hn
    push Not at hn
    have hz := Finset.sum_nonpos (s := Finset.univ) (fun j _ => hn j)
    linarith
  obtain ⟨j, hj⟩ := he
  rw [sigma_predict]
  exact Finset.sum_pos' (fun i _ => mul_nonneg (hp.1 i) (le_of_lt (M.R_pos a i k)))
    ⟨j, Finset.mem_univ j, mul_pos hj (M.R_pos a j k)⟩

lemma bayes_eq (M : POMDP S O A) (π : S → ℝ) (a : A) (k : O) (j : S) :
    M.bayes π a k j = (M.predict π a j*M.R a j k)/M.sigma π a k := by
  simp only [POMDP.bayes, POMDP.predict, Finset.sum_mul]

lemma bayes_simplex (M : POMDP S O A) {π : S → ℝ}
    (hπ : π ∈ stdSimplex ℝ S) (a : A) (k : O) :
    M.bayes π a k ∈ stdSimplex ℝ S := by
  have hp := predict_simplex M hπ a
  have hs := sigma_pos M hπ a k
  constructor
  · intro j
    rw [bayes_eq]
    exact div_nonneg (mul_nonneg (hp.1 j) (le_of_lt (M.R_pos a j k))) (le_of_lt hs)
  · simp only [bayes_eq, ← Finset.sum_div, ← sigma_predict]
    exact div_self (ne_of_gt hs)

end LovejoyPOMDP.Monotone.LPFresh



noncomputable section
open scoped BigOperators
namespace LovejoyPOMDP.Monotone.LPFresh

lemma pair_sum_le {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hac : a ≤ c) (hbc : b ≤ c) (hp : a*b ≤ c*d) : a+b ≤ c+d := by
  have hc : 0 ≤ c := ha.trans hac
  by_cases hz : c = 0
  · subst c
    have : a = 0 := le_antisymm hac ha
    have : b = 0 := le_antisymm hbc hb
    linarith
  · have hc' : 0 < c := lt_of_le_of_ne hc (Ne.symm hz)
    have h := mul_nonneg (sub_nonneg.mpr hac) (sub_nonneg.mpr hbc)
    have hm : c*(a+b) ≤ c*(c+d) := by nlinarith
    exact (mul_le_mul_iff_right₀ hc').mp hm

lemma tp_pair {I J : Type*} [LinearOrder I] [LinearOrder J]
    (f g : I → J → ℝ) (hf : ∀ i j, 0 ≤ f i j) (hg : ∀ i j, 0 ≤ g i j)
    (h : TPGE f g) {i l : I} {j k : J} (hi : l ≤ i) (hj : k ≤ j) :
    f i k*g l j + f l k*g i j ≤ f i j*g l k + f l j*g i k := by
  have h1 := h i k l j
  have h2 := h l k i j
  have h3 := h i k i j
  have h4 := h l k l j
  simp only [max_eq_left hi, min_eq_right hi, max_eq_right hi, min_eq_left hi,
    max_eq_right hj, min_eq_left hj, max_self, min_self] at h1 h2 h3 h4
  apply pair_sum_le (mul_nonneg (hf _ _) (hg _ _))
    (mul_nonneg (hf _ _) (hg _ _)) (mul_nonneg (hf _ _) (hg _ _)) h1 h2
  have hh := mul_le_mul h3 h4 (mul_nonneg (hf _ _) (hg _ _))
    (mul_nonneg (hf _ _) (hg _ _))
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hh

lemma paired_sum {I : Type*} [Fintype I] (w u v : I → ℝ) :
    (∑ i, ∑ l, w i*w l*(u i*v l+u l*v i)) =
      2*(∑ i, w i*u i)*(∑ i, w i*v i) := by
  classical
  have h (u v : I → ℝ) : (∑ i, ∑ l, w i*w l*(u i*v l)) =
      (∑ i, w i*u i)*(∑ i, w i*v i) := by
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hs : (∑ i, ∑ l, w i*w l*(u l*v i)) =
      ∑ i, ∑ l, w i*w l*(u i*v l) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp only [mul_add, Finset.sum_add_distrib]
  rw [hs, h]
  ring

lemma tp_marginal {I J : Type*} [Fintype I] [LinearOrder I] [LinearOrder J]
    (f g : I → J → ℝ) (hf : ∀ i j, 0 ≤ f i j) (hg : ∀ i j, 0 ≤ g i j)
    (h : TPGE f g) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) :
    MLRGE (fun j => ∑ i, w i*f i j) (fun j => ∑ i, w i*g i j) := by
  intro j k hj
  have hp (i l : I) : f i k*g l j+f l k*g i j ≤ f i j*g l k+f l j*g i k := by
    rcases le_total l i with hi | hi
    · exact tp_pair f g hf hg h hi hj
    · simpa only [add_comm] using tp_pair f g hf hg h hi hj
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun l _ =>
      mul_le_mul_of_nonneg_left (hp i l) (mul_nonneg (hw i) (hw l))))
  rw [paired_sum, paired_sum] at hs
  linarith

end LovejoyPOMDP.Monotone.LPFresh



noncomputable section
open scoped BigOperators
namespace LovejoyPOMDP.Monotone.LPFresh

lemma paired_function_sum {I : Type*} [Fintype I] (F : I → I → ℝ) :
    (∑ i, ∑ l, (F i l+F l i)) = 2*(∑ i, ∑ l, F i l) := by
  simp only [Finset.sum_add_distrib]
  have h : (∑ i, ∑ l, F l i) = ∑ i, ∑ l, F i l := Finset.sum_comm
  rw [h]
  ring

lemma product_sum {I : Type*} [Fintype I] (p q u v : I → ℝ) :
    (∑ i, p i*u i)*(∑ i, q i*v i) = ∑ i, ∑ l, p i*q l*(u i*v l) := by
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma kernel_mlr {I J : Type*} [Fintype I] [LinearOrder I] [LinearOrder J]
    (K : I → J → ℝ) (hK : TP2 K) (p q : I → ℝ) (hpq : MLRGE p q) :
    MLRGE (fun j => ∑ i, p i*K i j) (fun j => ∑ i, q i*K i j) := by
  intro j k hkj
  have hh {i l : I} (hli : l ≤ i) :
      p i*q l*(K i k*K l j)+p l*q i*(K l k*K i j) ≤
        p i*q l*(K i j*K l k)+p l*q i*(K l j*K i k) := by
    have hm := hpq i l hli
    have hk := hK i k l j
    simp only [max_eq_left hli, min_eq_right hli,
      max_eq_right hkj, min_eq_left hkj] at hk
    have h := mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr hk)
    nlinarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun l _ => (show
      p i*q l*(K i k*K l j)+p l*q i*(K l k*K i j) ≤
        p i*q l*(K i j*K l k)+p l*q i*(K l j*K i k) from by
      rcases le_total l i with h | h
      · exact hh h
      · simpa only [add_comm] using hh h)))
  rw [paired_function_sum, paired_function_sum] at hs
  rw [product_sum, product_sum]
  linarith

lemma predict_mlr_belief {S O A : Type*} [Fintype S] [Fintype O]
    [LinearOrder S] (M : POMDP S O A) (a : A) (hP : TP2 (M.P a))
    {π ρ : S → ℝ} (h : MLRGE π ρ) : MLRGE (M.predict π a) (M.predict ρ a) :=
  kernel_mlr (M.P a) hP π ρ h

lemma predict_mlr_action {S O A : Type*} [Fintype S] [Fintype O]
    [LinearOrder S] (M : POMDP S O A) {a b : A} (hP : TPGE (M.P a) (M.P b))
    {π : S → ℝ} (hπ : π ∈ stdSimplex ℝ S) :
    MLRGE (M.predict π a) (M.predict π b) :=
  tp_marginal (M.P a) (M.P b) (fun i j => (M.P_row a i).1 j)
    (fun i j => (M.P_row b i).1 j) hP π hπ.1

end LovejoyPOMDP.Monotone.LPFresh



noncomputable section
namespace LovejoyPOMDP.Monotone.LPFresh

lemma mlr_refl {I : Type*} [LinearOrder I] (p : I → ℝ) : MLRGE p p := by
  intro i j _
  exact le_of_eq (mul_comm _ _)

lemma mlr_mul {I : Type*} [LinearOrder I] (p q r s : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hr : ∀ i, 0 ≤ r i) (hs : ∀ i, 0 ≤ s i)
    (h1 : MLRGE p q) (h2 : MLRGE r s) :
    MLRGE (fun i => p i*r i) (fun i => q i*s i) := by
  intro i j hji
  have h := mul_le_mul (h1 i j hji) (h2 i j hji)
    (mul_nonneg (hr j) (hs i)) (mul_nonneg (hp i) (hq j))
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h

lemma mlr_div {I : Type*} [LinearOrder I] (p q : I → ℝ) {z w : ℝ}
    (hz : 0 < z) (hw : 0 < w) (h : MLRGE p q) :
    MLRGE (fun i => p i/z) (fun i => q i/w) := by
  intro i j hji
  rw [div_mul_div_comm, div_mul_div_comm]
  exact div_le_div_of_nonneg_right (h i j hji) (le_of_lt (mul_pos hz hw))

variable {S O A : Type*} [Fintype S] [Fintype O] [LinearOrder S] [LinearOrder O]

omit [LinearOrder O] in
lemma bayes_mlr_belief (M : POMDP S O A) (a : A) (hP : TP2 (M.P a))
    {π ρ : S → ℝ} (hπ : π ∈ stdSimplex ℝ S) (hρ : ρ ∈ stdSimplex ℝ S)
    (h : MLRGE π ρ) (k : O) : MLRGE (M.bayes π a k) (M.bayes ρ a k) := by
  have hp := predict_simplex M hπ a
  have hq := predict_simplex M hρ a
  have hn := mlr_mul (M.predict π a) (M.predict ρ a) (fun j => M.R a j k)
    (fun j => M.R a j k) hp.1 hq.1 (fun j => (M.R_row a j).1 k)
    (fun j => (M.R_row a j).1 k) (predict_mlr_belief M a hP h) (mlr_refl _)
  intro i j hji
  simp only [bayes_eq]
  exact (mlr_div _ _ (sigma_pos M hπ a k) (sigma_pos M hρ a k) hn) i j hji

lemma bayes_mlr_observation (M : POMDP S O A) (a : A)
    (hR : ∀ j j' : S, j' ≤ j → MLRGE (M.R a j) (M.R a j'))
    {π : S → ℝ} (hπ : π ∈ stdSimplex ℝ S) {k l : O} (hlk : l ≤ k) :
    MLRGE (M.bayes π a k) (M.bayes π a l) := by
  have hp := predict_simplex M hπ a
  have hc : MLRGE (fun j => M.R a j k) (fun j => M.R a j l) := by
    intro j i hij
    simpa only [mul_comm] using hR j i hij k l hlk
  have hn := mlr_mul (M.predict π a) (M.predict π a) (fun j => M.R a j k)
    (fun j => M.R a j l) hp.1 hp.1 (fun j => (M.R_row a j).1 k)
    (fun j => (M.R_row a j).1 l) (mlr_refl _) hc
  intro i j hji
  simp only [bayes_eq]
  exact (mlr_div _ _ (sigma_pos M hπ a k) (sigma_pos M hπ a l) hn) i j hji

omit [LinearOrder O] in
lemma bayes_mlr_action (M : POMDP S O A) {a b : A}
    (hP : TPGE (M.P a) (M.P b))
    (hR : ∀ j i : S, i ≤ j → ∀ k, M.R b j k*M.R a i k ≤ M.R a j k*M.R b i k)
    {π : S → ℝ} (hπ : π ∈ stdSimplex ℝ S) (k : O) :
    MLRGE (M.bayes π a k) (M.bayes π b k) := by
  have hp := predict_simplex M hπ a
  have hq := predict_simplex M hπ b
  have hc : MLRGE (fun j => M.R a j k) (fun j => M.R b j k) := by
    intro j i hij
    simpa only [mul_comm] using hR j i hij k
  have hn := mlr_mul (M.predict π a) (M.predict π b) (fun j => M.R a j k)
    (fun j => M.R b j k) hp.1 hq.1 (fun j => (M.R_row a j).1 k)
    (fun j => (M.R_row b j).1 k) (predict_mlr_action M hP hπ) hc
  intro i j hji
  simp only [bayes_eq]
  exact (mlr_div _ _ (sigma_pos M hπ a k) (sigma_pos M hπ b k) hn) i j hji

end LovejoyPOMDP.Monotone.LPFresh



namespace LovejoyPOMDP.Monotone.LPFresh
open Finset

lemma tail_weighted_bound {X : Type*} [LinearOrder X] (s : Finset X)
    (w f : X → ℝ) (hf : Monotone f) (b : ℝ)
    (hb : ∀ i ∈ s, b ≤ f i)
    (ht : ∀ q ∈ s, 0 ≤ ∑ i ∈ s.filter (q ≤ ·), w i) :
    b * (∑ i ∈ s, w i) ≤ ∑ i ∈ s, w i * f i := by
  classical
  induction s using Finset.induction_on_min generalizing b with
  | empty => simp
  | @insert a s ha ih =>
    have han : a ∉ s := fun h => (lt_irrefl a) (ha a h)
    have htail : ∀ q ∈ s, 0 ≤ ∑ i ∈ s.filter (q ≤ ·), w i := by
      intro q hq
      have h := ht q (mem_insert_of_mem hq)
      simpa [filter_insert, not_le.mpr (ha q hq)] using h
    have htotal := ht a (mem_insert_self a s)
    have hfilter : (insert a s).filter (a ≤ ·) = insert a s := by
      apply filter_true_of_mem
      intro i hi
      rcases mem_insert.mp hi with rfl | hi
      · exact le_rfl
      · exact (ha i hi).le
    rw [hfilter] at htotal
    have hrec := ih (f a) (fun i hi => hf (ha i hi).le) htail
    have hbase := mul_le_mul_of_nonneg_right (hb a (mem_insert_self a s)) htotal
    simp only [sum_insert han] at hbase ⊢
    nlinarith

lemma stoch_expect_le {X : Type*} [Fintype X] [LinearOrder X]
    {π ρ : X → ℝ} (hπ : π ∈ stdSimplex ℝ X) (hρ : ρ ∈ stdSimplex ℝ X)
    (hst : StochGE π ρ) {f : X → ℝ} (hf : Monotone f) :
    ∑ i, ρ i * f i ≤ ∑ i, π i * f i := by
  classical
  obtain hempty | hne := (Finset.univ : Finset X).eq_empty_or_nonempty
  · simp [hempty]
  let b := (Finset.univ : Finset X).inf' hne f
  have h := tail_weighted_bound Finset.univ (fun i => π i - ρ i) f hf b
    (fun i hi => Finset.inf'_le f hi) (by
      intro q _
      simpa only [Finset.sum_sub_distrib] using sub_nonneg.mpr (hst q))
  have hz : ∑ i, (π i - ρ i) = 0 := by rw [sum_sub_distrib, hπ.2, hρ.2]; norm_num
  simp only [hz, mul_zero, sub_mul, sum_sub_distrib] at h
  linarith

lemma mlr_expect_le {X : Type*} [Fintype X] [LinearOrder X]
    {π ρ : X → ℝ} (hπ : π ∈ stdSimplex ℝ X) (hρ : ρ ∈ stdSimplex ℝ X)
    (hm : MLRGE π ρ) {f : X → ℝ} (hf : Monotone f) :
    ∑ i, ρ i * f i ≤ ∑ i, π i * f i := by
  classical
  have hp : ∀ i j, 0 ≤ (π i * ρ j - π j * ρ i) * (f i - f j) := by
    intro i j
    rcases le_total j i with hij | hij
    · exact mul_nonneg (sub_nonneg.mpr (hm i j hij)) (sub_nonneg.mpr (hf hij))
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hm j i hij))
        (sub_nonpos.mpr (hf hij))
  have hs := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hp i j))
  have he : (∑ i, ∑ j, (π i * ρ j - π j * ρ i) * (f i - f j)) =
      2 * ((∑ i, π i * f i) - ∑ i, ρ i * f i) := by
    have hepoint : ∀ i j, (π i * ρ j - π j * ρ i) * (f i - f j) =
        (π i * f i) * ρ j - π i * (ρ j * f j) -
          (ρ i * f i) * π j + ρ i * (π j * f j) := by intros; ring
    simp_rw [hepoint, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hπ.2, hρ.2, mul_one, ← Finset.sum_mul,
      hπ.2, hρ.2, one_mul]
    ring
  rw [he] at hs
  linarith

lemma mlr_stoch {X : Type*} [Fintype X] [LinearOrder X]
    {π ρ : X → ℝ} (hπ : π ∈ stdSimplex ℝ X) (hρ : ρ ∈ stdSimplex ℝ X)
    (hm : MLRGE π ρ) : StochGE π ρ := by
  classical
  intro q
  have hf : Monotone (fun i : X => if q ≤ i then (1 : ℝ) else 0) := by
    intro i j hij
    dsimp only
    split_ifs with hi hj hj
    · rfl
    · exact (hj (hi.trans hij)).elim
    · norm_num
    · rfl
  have h := mlr_expect_le hπ hρ hm hf
  simpa [Finset.sum_filter, mul_ite] using h

end LovejoyPOMDP.Monotone.LPFresh



noncomputable section
open scoped BigOperators
namespace LovejoyPOMDP.Monotone.LPFresh
variable {S O A : Type*} [Fintype S] [Fintype O] [LinearOrder S] [LinearOrder O]

lemma row_tail_mono (M : POMDP S O A) (a : A)
    (hR : ∀ j i : S, i ≤ j → MLRGE (M.R a j) (M.R a i)) (q : O) :
    Monotone (fun j => ∑ k ∈ Finset.univ.filter (q ≤ ·), M.R a j k) := by
  intro i j hij
  exact mlr_stoch (M.R_row a j) (M.R_row a i) (hR j i hij) q

omit [LinearOrder S] in
lemma sigma_tail (M : POMDP S O A) (π : S → ℝ) (a : A) (q : O) :
    (∑ k ∈ Finset.univ.filter (q ≤ ·), M.sigma π a k) =
      ∑ j, M.predict π a j*(∑ k ∈ Finset.univ.filter (q ≤ ·), M.R a j k) := by
  simp only [sigma_predict]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

lemma sigma_stoch_belief (M : POMDP S O A) (a : A) (hP : TP2 (M.P a))
    (hR : ∀ j i : S, i ≤ j → MLRGE (M.R a j) (M.R a i))
    {π ρ : S → ℝ} (hπ : π ∈ stdSimplex ℝ S) (hρ : ρ ∈ stdSimplex ℝ S)
    (h : MLRGE π ρ) : StochGE (M.sigma π a) (M.sigma ρ a) := by
  intro q
  rw [sigma_tail, sigma_tail]
  exact mlr_expect_le (predict_simplex M hπ a) (predict_simplex M hρ a)
    (predict_mlr_belief M a hP h) (row_tail_mono M a hR q)

lemma sigma_stoch_action (M : POMDP S O A) {a b : A}
    (hP : TPGE (M.P a) (M.P b))
    (hR : ∀ j i : S, i ≤ j → MLRGE (M.R a j) (M.R a i))
    (hE : ∀ j, StochGE (M.R a j) (M.R b j))
    {π : S → ℝ} (hπ : π ∈ stdSimplex ℝ S) :
    StochGE (M.sigma π a) (M.sigma π b) := by
  intro q
  rw [sigma_tail, sigma_tail]
  calc
    _ ≤ ∑ j, M.predict π b j*(∑ k ∈ Finset.univ.filter (q ≤ ·), M.R a j k) :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hE j q)
        ((predict_simplex M hπ b).1 j))
    _ ≤ _ := mlr_expect_le (predict_simplex M hπ a) (predict_simplex M hπ b)
      (predict_mlr_action M hP hπ) (row_tail_mono M a hR q)

end LovejoyPOMDP.Monotone.LPFresh



noncomputable section
open Filter
open scoped Topology
namespace LovejoyPOMDP.Monotone.LPFresh

lemma finite_sup_abs_diff {I : Type*} [Fintype I] [Nonempty I]
    (f g : I → ℝ) (c : ℝ) (h : ∀ i, |f i - g i| ≤ c) :
    |Finset.univ.sup' Finset.univ_nonempty f -
      Finset.univ.sup' Finset.univ_nonempty g| ≤ c := by
  classical
  apply abs_le.mpr
  constructor
  · have hh : Finset.univ.sup' Finset.univ_nonempty g ≤
        Finset.univ.sup' Finset.univ_nonempty f + c := by
      apply Finset.sup'_le
      intro i _
      have h1 := (abs_le.mp (h i)).1
      have h2 := Finset.le_sup' f (Finset.mem_univ i)
      linarith
    linarith
  · have hh : Finset.univ.sup' Finset.univ_nonempty f ≤
        Finset.univ.sup' Finset.univ_nonempty g + c := by
      apply Finset.sup'_le
      intro i _
      have h1 := (abs_le.mp (h i)).2
      have h2 := Finset.le_sup' g (Finset.mem_univ i)
      linarith
    linarith

variable {S O A : Type*} [Fintype S] [Fintype O] [Fintype A]

omit [Fintype A] in
lemma hop_abs_diff (M : POMDP S O A) {V W : (S → ℝ) → ℝ} {C : ℝ}
    (h : ∀ π ∈ stdSimplex ℝ S, |V π - W π| ≤ C)
    {π : S → ℝ} (hπ : π ∈ stdSimplex ℝ S) (a : A) :
    |M.hOp π a V - M.hOp π a W| ≤ M.β * C := by
  have hs := sigma_simplex M hπ a
  have he : M.hOp π a V - M.hOp π a W =
      M.β * ∑ k, M.sigma π a k * (V (M.bayes π a k) - W (M.bayes π a k)) := by
    simp [POMDP.hOp, mul_sub, Finset.sum_sub_distrib]
  rw [he, abs_mul, abs_of_nonneg M.β_nonneg]
  apply mul_le_mul_of_nonneg_left _ M.β_nonneg
  calc
    |∑ k, M.sigma π a k * (V (M.bayes π a k) - W (M.bayes π a k))| ≤
        ∑ k, |M.sigma π a k * (V (M.bayes π a k) - W (M.bayes π a k))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, M.sigma π a k * C := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul, abs_of_nonneg (hs.1 k)]
      exact mul_le_mul_of_nonneg_left (h _ (bayes_simplex M hπ a k)) (hs.1 k)
    _ = C := by rw [← Finset.sum_mul, hs.2, one_mul]

lemma bellman_approximation [Nonempty A] (M : POMDP S O A)
    {V : (S → ℝ) → ℝ} (hV : M.IsBellmanSolution V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n π, π ∈ stdSimplex ℝ S →
      |V π - M.valueToGo (fun _ => 0) n π| ≤ M.β ^ n * C := by
  obtain ⟨C, hC⟩ := hV.1
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro n
  induction n with
  | zero =>
    intro π hπ
    simpa [POMDP.valueToGo] using (hC π hπ).trans (le_max_left C 0)
  | succ n ih =>
    intro π hπ
    rw [hV.2 π hπ, POMDP.valueToGo]
    have hh := finite_sup_abs_diff (M.hOp π · V)
      (M.hOp π · (M.valueToGo (fun _ => 0) n)) (M.β * (M.β ^ n * max C 0))
      (fun a => hop_abs_diff M ih hπ a)
    convert hh using 1
    ring

lemma bellman_value_limit [Nonempty A] (M : POMDP S O A) (hβ : M.β < 1)
    {V : (S → ℝ) → ℝ} (hV : M.IsBellmanSolution V)
    {π : S → ℝ} (hπ : π ∈ stdSimplex ℝ S) :
    Tendsto (fun n => M.valueToGo (fun _ => 0) n π) atTop (𝓝 (V π)) := by
  obtain ⟨C, _, hC⟩ := bellman_approximation M hV
  have ht : Tendsto (fun n : ℕ => M.β ^ n * C) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one M.β_nonneg hβ).mul_const C
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) _ ht
  intro n
  simpa [Real.norm_eq_abs, abs_sub_comm] using hC n π hπ

end LovejoyPOMDP.Monotone.LPFresh



noncomputable section
open Filter
open scoped Topology
namespace LovejoyPOMDP.Monotone.LPFresh

variable {S O A : Type*} [Fintype S] [Fintype O] [Fintype A]
  [LinearOrder S] [LinearOrder O]

def ValueMonotone (V : (S → ℝ) → ℝ) : Prop :=
  ∀ {π ρ}, π ∈ stdSimplex ℝ S → ρ ∈ stdSimplex ℝ S → MLRGE π ρ → V ρ ≤ V π

omit [Fintype A] in
lemma continuation_belief (M : POMDP S O A) (a : A) (hP : TP2 (M.P a))
    (hR : ∀ j j' : S, j' ≤ j → MLRGE (M.R a j) (M.R a j'))
    {V : (S → ℝ) → ℝ} (hV : ValueMonotone V)
    {π ρ : S → ℝ} (hπ : π ∈ stdSimplex ℝ S) (hρ : ρ ∈ stdSimplex ℝ S)
    (h : MLRGE π ρ) :
    ∑ k, M.sigma ρ a k * V (M.bayes ρ a k) ≤
      ∑ k, M.sigma π a k * V (M.bayes π a k) := by
  calc
    _ ≤ ∑ k, M.sigma π a k * V (M.bayes ρ a k) := by
      apply stoch_expect_le (sigma_simplex M hπ a) (sigma_simplex M hρ a)
        (sigma_stoch_belief M a hP hR hπ hρ h)
      intro k l hkl
      exact hV (bayes_simplex M hρ a l) (bayes_simplex M hρ a k)
        (bayes_mlr_observation M a hR hρ hkl)
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left
        (hV (bayes_simplex M hπ a k) (bayes_simplex M hρ a k)
          (bayes_mlr_belief M a hP hπ hρ h k)) ((sigma_simplex M hπ a).1 k)

omit [Fintype A] in
lemma hop_belief (M : POMDP S O A) (a : A)
    (hg : Monotone (fun i => M.g i a)) (hP : TP2 (M.P a))
    (hR : ∀ j j' : S, j' ≤ j → MLRGE (M.R a j) (M.R a j'))
    {V : (S → ℝ) → ℝ} (hV : ValueMonotone V) :
    ValueMonotone (fun π => M.hOp π a V) := by
  intro π ρ hπ hρ h
  exact add_le_add (mlr_expect_le hπ hρ h hg)
    (mul_le_mul_of_nonneg_left (continuation_belief M a hP hR hV hπ hρ h) M.β_nonneg)

lemma finite_value_monotone [Nonempty A] (M : POMDP S O A)
    (hg : ∀ a, Monotone (fun i => M.g i a)) (hP : ∀ a, TP2 (M.P a))
    (hR : ∀ a (j j' : S), j' ≤ j → MLRGE (M.R a j) (M.R a j'))
    {gs : S → ℝ} (hgs : Monotone gs) (n : ℕ) : ValueMonotone (M.valueToGo gs n) := by
  classical
  induction n with
  | zero => exact fun hπ hρ h => mlr_expect_le hπ hρ h hgs
  | succ n ih =>
    intro π ρ hπ hρ h
    change Finset.univ.sup' Finset.univ_nonempty (fun a => M.hOp ρ a (M.valueToGo gs n)) ≤
      Finset.univ.sup' Finset.univ_nonempty (fun a => M.hOp π a (M.valueToGo gs n))
    apply Finset.sup'_le
    intro a _
    exact (hop_belief M a (hg a) (hP a) (hR a) ih hπ hρ h).trans
      (Finset.le_sup' (fun a => M.hOp π a (M.valueToGo gs n)) (Finset.mem_univ a))

lemma infinite_value_monotone [Nonempty A] (M : POMDP S O A)
    (hg : ∀ a, Monotone (fun i => M.g i a)) (hP : ∀ a, TP2 (M.P a))
    (hR : ∀ a (j j' : S), j' ≤ j → MLRGE (M.R a j) (M.R a j'))
    (hβ : M.β < 1) {V : (S → ℝ) → ℝ} (hV : M.IsBellmanSolution V) :
    ValueMonotone V := by
  intro π ρ hπ hρ h
  exact le_of_tendsto_of_tendsto (bellman_value_limit M hβ hV hρ)
    (bellman_value_limit M hβ hV hπ)
    (Filter.Eventually.of_forall (fun n =>
      finite_value_monotone M hg hP hR (fun _ _ _ => le_rfl) n hπ hρ h))

end LovejoyPOMDP.Monotone.LPFresh



noncomputable section
namespace LovejoyPOMDP.Monotone.LPFresh

lemma argmax_nonempty {A : Type*} [Fintype A] [Nonempty A] (f : A → ℝ) :
    (argmaxSet f).Nonempty := by
  classical
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  exact ⟨a, fun b => ha b (Finset.mem_univ b)⟩

lemma argmax_order {A : Type*} [Fintype A] [Nonempty A] [LinearOrder A]
    (f c : A → ℝ) (hc : Monotone c) :
    (∀ d ∈ argmaxSet (fun a => f a+c a), ∃ a ∈ argmaxSet f, a ≤ d) ∧
    (∀ a ∈ argmaxSet f, ∃ d ∈ argmaxSet (fun a => f a+c a), a ≤ d) := by
  constructor
  · intro d hd
    obtain ⟨a, ha⟩ := argmax_nonempty f
    by_cases had : a ≤ d
    · exact ⟨a, ha, had⟩
    · have hda := le_of_lt (lt_of_not_ge had)
      have h1 := hc hda
      have h2 := hd a
      have h3 := ha d
      have he : f d = f a := by linarith
      exact ⟨d, fun b => (ha b).trans (le_of_eq he.symm), le_rfl⟩
  · intro a ha
    obtain ⟨d, hd⟩ := argmax_nonempty (fun a => f a+c a)
    by_cases had : a ≤ d
    · exact ⟨d, hd, had⟩
    · have hda := le_of_lt (lt_of_not_ge had)
      have h1 := hc hda
      have h2 := hd a
      have h3 := ha d
      have he : f d+c d = f a+c a := by linarith
      exact ⟨a, fun b => (hd b).trans (le_of_eq he), le_rfl⟩

end LovejoyPOMDP.Monotone.LPFresh



noncomputable section
namespace LovejoyPOMDP.Monotone.LPFresh
variable {S O A : Type*} [Fintype S] [Fintype O] [Fintype A]
  [LinearOrder S] [LinearOrder O] [LinearOrder A]

omit [Fintype A] in
lemma continuation_action (M : POMDP S O A)
    (hP : ∀ a b : A, b ≤ a → TPGE (M.P a) (M.P b))
    (hRd : ∀ a (j i : S), i ≤ j → MLRGE (M.R a j) (M.R a i))
    (hRe : ∀ a b : A, b ≤ a → ∀ j, StochGE (M.R a j) (M.R b j))
    (hRf : ∀ a b : A, b ≤ a → ∀ j i : S, i ≤ j → ∀ k,
      M.R b j k * M.R a i k ≤ M.R a j k * M.R b i k)
    {V : (S → ℝ) → ℝ} (hV : ValueMonotone V)
    {π : S → ℝ} (hπ : π ∈ stdSimplex ℝ S) :
    Monotone (fun a => M.β * ∑ k, M.sigma π a k * V (M.bayes π a k)) := by
  intro b a hba
  apply mul_le_mul_of_nonneg_left _ M.β_nonneg
  calc
    _ ≤ ∑ k, M.sigma π a k * V (M.bayes π b k) := by
      apply stoch_expect_le (sigma_simplex M hπ a) (sigma_simplex M hπ b)
        (sigma_stoch_action M (hP a b hba) (hRd a) (hRe a b hba) hπ)
      intro k l hkl
      exact hV (bayes_simplex M hπ b l) (bayes_simplex M hπ b k)
        (bayes_mlr_observation M b (hRd b) hπ hkl)
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left
        (hV (bayes_simplex M hπ a k) (bayes_simplex M hπ b k)
          (bayes_mlr_action M (hP a b hba) (hRf a b hba) hπ k))
        ((sigma_simplex M hπ a).1 k)

lemma policy_bound [Nonempty A] (M : POMDP S O A)
    (hP : ∀ a b : A, b ≤ a → TPGE (M.P a) (M.P b))
    (hRd : ∀ a (j i : S), i ≤ j → MLRGE (M.R a j) (M.R a i))
    (hRe : ∀ a b : A, b ≤ a → ∀ j, StochGE (M.R a j) (M.R b j))
    (hRf : ∀ a b : A, b ≤ a → ∀ j i : S, i ≤ j → ∀ k,
      M.R b j k * M.R a i k ≤ M.R a j k * M.R b i k)
    {V : (S → ℝ) → ℝ} (hV : ValueMonotone V)
    {π : S → ℝ} (hπ : π ∈ stdSimplex ℝ S) :
    (∀ d ∈ argmaxSet (fun a => M.hOp π a V), ∃ a ∈ argmaxSet (M.myopic π), a ≤ d) ∧
    (∀ a ∈ argmaxSet (M.myopic π), ∃ d ∈ argmaxSet (fun a => M.hOp π a V), a ≤ d) := by
  exact argmax_order (M.myopic π) _ (continuation_action M hP hRd hRe hRf hV hπ)

end LovejoyPOMDP.Monotone.LPFresh



namespace LovejoyPOMDP.Monotone.LPFresh

theorem native_proposition_2 {S O A : Type*} [Fintype S] [Fintype O] [Fintype A]
    [LinearOrder S] [LinearOrder O] [LinearOrder A] [Nonempty S] [Nonempty O] [Nonempty A]
    (M : POMDP S O A)
    (hg : ∀ a, Monotone (fun i => M.g i a))
    (hP : ∀ a a' : A, a' ≤ a → TPGE (M.P a) (M.P a'))
    (hRd : ∀ a (j j' : S), j' ≤ j → MLRGE (M.R a j) (M.R a j'))
    (hRe : ∀ a a' : A, a' ≤ a → ∀ j, StochGE (M.R a j) (M.R a' j))
    (hRf : ∀ a a' : A, a' ≤ a → ∀ j j' : S, j' ≤ j → ∀ k,
      M.R a' j k * M.R a j' k ≤ M.R a j k * M.R a' j' k) :
    (∀ gs : S → ℝ, Monotone gs → ∀ N t : ℕ, 1 ≤ t → t ≤ N → ∀ π ∈ stdSimplex ℝ S,
      (∀ d ∈ argmaxSet (fun a => M.hOp π a (M.Vstar gs N (t + 1))),
          ∃ α ∈ argmaxSet (M.myopic π), α ≤ d) ∧
        (∀ α ∈ argmaxSet (M.myopic π),
          ∃ d ∈ argmaxSet (fun a => M.hOp π a (M.Vstar gs N (t + 1))), α ≤ d)) ∧
    (0 < M.β → M.β < 1 → ∀ V : (S → ℝ) → ℝ, M.IsBellmanSolution V → ∀ π ∈ stdSimplex ℝ S,
      (∀ d ∈ argmaxSet (fun a => M.hOp π a V), ∃ α ∈ argmaxSet (M.myopic π), α ≤ d) ∧
        (∀ α ∈ argmaxSet (M.myopic π), ∃ d ∈ argmaxSet (fun a => M.hOp π a V), α ≤ d)) := by
  constructor
  · intro gs hgs N t _ _ π hπ
    exact policy_bound M hP hRd hRe hRf
      (finite_value_monotone M hg (fun a => hP a a le_rfl) hRd hgs _) hπ
  · intro _ hβ V hV π hπ
    exact policy_bound M hP hRd hRe hRf
      (infinite_value_monotone M hg (fun a => hP a a le_rfl) hRd hβ hV) hπ

end LovejoyPOMDP.Monotone.LPFresh



namespace LovejoyPOMDP.Monotone

theorem proposition_2 {S O A : Type*} [Fintype S] [Fintype O] [Fintype A]
    [LinearOrder S] [LinearOrder O] [LinearOrder A] [Nonempty S] [Nonempty O] [Nonempty A]
    (M : POMDP S O A)
    (hg : ∀ a, Monotone (fun i => M.g i a))
    (hP : ∀ a a' : A, a' ≤ a → TPGE (M.P a) (M.P a'))
    (hRd : ∀ a (j j' : S), j' ≤ j → MLRGE (M.R a j) (M.R a j'))
    (hRe : ∀ a a' : A, a' ≤ a → ∀ j, StochGE (M.R a j) (M.R a' j))
    (hRf : ∀ a a' : A, a' ≤ a → ∀ j j' : S, j' ≤ j → ∀ k,
      M.R a' j k * M.R a j' k ≤ M.R a j k * M.R a' j' k) :
    (∀ gs : S → ℝ, Monotone gs → ∀ N t : ℕ, 1 ≤ t → t ≤ N → ∀ π ∈ stdSimplex ℝ S,
      (∀ d ∈ argmaxSet (fun a => M.hOp π a (M.Vstar gs N (t + 1))),
          ∃ α ∈ argmaxSet (M.myopic π), α ≤ d) ∧
        (∀ α ∈ argmaxSet (M.myopic π),
          ∃ d ∈ argmaxSet (fun a => M.hOp π a (M.Vstar gs N (t + 1))), α ≤ d)) ∧
    (0 < M.β → M.β < 1 → ∀ V : (S → ℝ) → ℝ, M.IsBellmanSolution V → ∀ π ∈ stdSimplex ℝ S,
      (∀ d ∈ argmaxSet (fun a => M.hOp π a V), ∃ α ∈ argmaxSet (M.myopic π), α ≤ d) ∧
        (∀ α ∈ argmaxSet (M.myopic π), ∃ d ∈ argmaxSet (fun a => M.hOp π a V), α ≤ d)) := by
  exact LPFresh.native_proposition_2 M hg hP hRd hRe hRf

end LovejoyPOMDP.Monotone


open LovejoyPOMDP.Monotone
theorem solution {S O A : Type*} [Fintype S] [Fintype O] [Fintype A]
    [LinearOrder S] [LinearOrder O] [LinearOrder A] [Nonempty S] [Nonempty O] [Nonempty A]
    (M : POMDP S O A)
    (hg : ∀ a, Monotone (fun i => M.g i a))
    (hP : ∀ a a' : A, a' ≤ a → TPGE (M.P a) (M.P a'))
    (hRd : ∀ a (j j' : S), j' ≤ j → MLRGE (M.R a j) (M.R a j'))
    (hRe : ∀ a a' : A, a' ≤ a → ∀ j, StochGE (M.R a j) (M.R a' j))
    (hRf : ∀ a a' : A, a' ≤ a → ∀ j j' : S, j' ≤ j → ∀ k,
      M.R a' j k * M.R a j' k ≤ M.R a j k * M.R a' j' k) :
    (∀ gs : S → ℝ, Monotone gs → ∀ N t : ℕ, 1 ≤ t → t ≤ N → ∀ π ∈ stdSimplex ℝ S,
      (∀ d ∈ argmaxSet (fun a => M.hOp π a (M.Vstar gs N (t + 1))),
          ∃ α ∈ argmaxSet (M.myopic π), α ≤ d) ∧
        (∀ α ∈ argmaxSet (M.myopic π),
          ∃ d ∈ argmaxSet (fun a => M.hOp π a (M.Vstar gs N (t + 1))), α ≤ d)) ∧
    (0 < M.β → M.β < 1 → ∀ V : (S → ℝ) → ℝ, M.IsBellmanSolution V → ∀ π ∈ stdSimplex ℝ S,
      (∀ d ∈ argmaxSet (fun a => M.hOp π a V), ∃ α ∈ argmaxSet (M.myopic π), α ≤ d) ∧
        (∀ α ∈ argmaxSet (M.myopic π), ∃ d ∈ argmaxSet (fun a => M.hOp π a V), α ≤ d)) := by
  exact LovejoyPOMDP.Monotone.proposition_2 M hg hP hRd hRe hRf
