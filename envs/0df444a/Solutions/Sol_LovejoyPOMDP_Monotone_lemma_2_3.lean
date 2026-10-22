-- Prove2me | solution 1 for LovejoyPOMDP.Monotone.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:10:41.612387+00:00
-- url     : https://prove2.me/submissions/8dd197a7-80a5-4ed9-acf0-2999912926a4

import Mathlib
import Definitions.Def_LovejoyPOMDP_Monotone_Model

set_option autoImplicit false
open LovejoyPOMDP.Monotone

section lpm
variable {S O A : Type*} [Fintype S] [Fintype O] [Fintype A]

lemma lpm_predict_nonneg (M : POMDP S O A) {π : S → ℝ} (hπ : π ∈ stdSimplex ℝ S) (a : A) (j : S) :
    0 ≤ M.predict π a j := by
  unfold POMDP.predict
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hπ.1 i) ((M.P_row a i).1 j))

lemma lpm_sigma_nonneg (M : POMDP S O A) {π : S → ℝ} (hπ : π ∈ stdSimplex ℝ S) (a : A) (k : O) :
    0 ≤ M.sigma π a k := by
  unfold POMDP.sigma
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    mul_nonneg (mul_nonneg (hπ.1 i) ((M.P_row a i).1 j)) (M.R_pos a j k).le))

lemma lpm_bayes_eq (M : POMDP S O A) (π : S → ℝ) (a : A) (k : O) (j : S) :
    M.bayes π a k j = M.predict π a j * M.R a j k / M.sigma π a k := by
  unfold POMDP.bayes POMDP.predict
  rw [Finset.sum_mul]

lemma lpm_two_pt (A B C D a b c d : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (c1 : B * a ≤ A * b) (c2 : D * c ≤ C * d) (c5 : A * d ≤ C * b) (c6 : D * a ≤ C * b)
    (c7 : B * c ≤ C * b) : 0 ≤ A * d + C * b - B * c - D * a := by
  by_cases hCb : C * b = 0
  · have h1 : A * d = 0 := le_antisymm (by linarith) (mul_nonneg hA hd)
    have h2 : D * a = 0 := le_antisymm (by linarith) (mul_nonneg hD ha)
    have h3 : B * c = 0 := le_antisymm (by linarith) (mul_nonneg hB hc)
    linarith
  · have hpos : 0 < C * b := lt_of_le_of_ne (mul_nonneg hC hb) (Ne.symm hCb)
    have key : (A * d + C * b - B * c - D * a) * (C * b) =
        (A * b - B * a) * (C * d) + (C * d - D * c) * (B * a) + (C * b - D * a) * (C * b - B * c) := by
      ring
    have hrhs : 0 ≤ (A * b - B * a) * (C * d) + (C * d - D * c) * (B * a) +
        (C * b - D * a) * (C * b - B * c) := by
      have := mul_nonneg (sub_nonneg.2 c1) (mul_nonneg hC hd)
      have := mul_nonneg (sub_nonneg.2 c2) (mul_nonneg hB ha)
      have := mul_nonneg (sub_nonneg.2 c6) (sub_nonneg.2 c7)
      linarith
    by_contra hneg
    push_neg at hneg
    have := mul_neg_of_neg_of_pos hneg hpos
    linarith

lemma lpm_tp_cons {S : Type*} [LinearOrder S] (f g : S → S → ℝ) (h : TPGE f g) (i i' j j' : S)
    (hii' : i ≤ i') (hjj' : j' ≤ j) :
    f i j' * g i j ≤ f i j * g i j' ∧ f i' j' * g i' j ≤ f i' j * g i' j' ∧
    f i j * g i' j' ≤ f i' j * g i j' ∧ f i' j' * g i j ≤ f i' j * g i j' ∧
    f i j' * g i' j ≤ f i' j * g i j' := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := h i j' i j
    rwa [max_self, min_self, max_eq_right hjj', min_eq_left hjj'] at this
  · have := h i' j' i' j
    rwa [max_self, min_self, max_eq_right hjj', min_eq_left hjj'] at this
  · have := h i j i' j'
    rwa [max_eq_right hii', min_eq_left hii', max_eq_left hjj', min_eq_right hjj'] at this
  · have := h i' j' i j
    rwa [max_eq_left hii', min_eq_right hii', max_eq_right hjj', min_eq_left hjj'] at this
  · have := h i j' i' j
    rwa [max_eq_right hii', min_eq_left hii', max_eq_right hjj', min_eq_left hjj'] at this


theorem lpm_predict_mem (M : POMDP S O A) {π : S → ℝ} (hπ : π ∈ stdSimplex ℝ S) (a : A) :
    M.predict π a ∈ stdSimplex ℝ S :=
  ⟨fun j => lpm_predict_nonneg M hπ a j, by
    unfold POMDP.predict
    rw [Finset.sum_comm]
    have : ∀ i, ∑ j, π i * M.P a i j = π i := by
      intro i
      rw [← Finset.mul_sum, (M.P_row a i).2, mul_one]
    rw [Finset.sum_congr rfl (fun i _ => this i)]
    exact hπ.2⟩

theorem lpm_sigma_eq (M : POMDP S O A) (π : S → ℝ) (a : A) (k : O) :
    M.sigma π a k = ∑ j, M.predict π a j * M.R a j k := by
  unfold POMDP.sigma POMDP.predict
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul]

theorem lpm_sigma_mem (M : POMDP S O A) {π : S → ℝ} (hπ : π ∈ stdSimplex ℝ S) (a : A) :
    M.sigma π a ∈ stdSimplex ℝ O := by
  refine ⟨fun k => lpm_sigma_nonneg M hπ a k, ?_⟩
  simp only [lpm_sigma_eq]
  rw [Finset.sum_comm]
  have : ∀ j, ∑ k, M.predict π a j * M.R a j k = M.predict π a j := by
    intro j
    rw [← Finset.mul_sum, (M.R_row a j).2, mul_one]
  rw [Finset.sum_congr rfl (fun j _ => this j)]
  exact (lpm_predict_mem M hπ a).2

theorem lpm_sigma_exp (M : POMDP S O A) (π : S → ℝ) (a : A) (f : O → ℝ) :
    ∑ k, M.sigma π a k * f k = ∑ j, M.predict π a j * ∑ k, M.R a j k * f k := by
  simp only [lpm_sigma_eq]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

end lpm


theorem lpm_abel_aux {X : Type*} [LinearOrder X] (f : X → ℝ) (hf : Monotone f) (s : Finset X) :
    ∀ d : X → ℝ, ∑ i ∈ s, d i = 0 → (∀ q, 0 ≤ ∑ i ∈ s.filter (fun i => q ≤ i), d i) →
      0 ≤ ∑ i ∈ s, d i * f i := by
  induction s using Finset.induction_on_min with
  | empty => intro d _ _; simp
  | insert a s ha ih =>
    intro d hsum htail
    have hna : a ∉ s := fun h => lt_irrefl a (ha a h)
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp at hsum ⊢
      simp [hsum]
    · set b := s.min' hne with hb
      have hbs : b ∈ s := Finset.min'_mem s hne
      have hab : a < b := ha b hbs
      have hbs' : ∀ i ∈ s, b ≤ i := fun i hi => Finset.min'_le s i hi
      rw [Finset.sum_insert hna] at hsum
      let d' : X → ℝ := fun i => d i + if i = b then d a else 0
      have hd'sum : ∑ i ∈ s, d' i = 0 := by
        simp only [d', Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos hbs]
        linarith
      have hd'tail : ∀ q, 0 ≤ ∑ i ∈ s.filter (fun i => q ≤ i), d' i := by
        intro q
        by_cases hq : q ≤ b
        · have : s.filter (fun i => q ≤ i) = s := by
            apply Finset.filter_true_of_mem
            intro i hi; exact le_trans hq (hbs' i hi)
          rw [this, hd'sum]
        · push_neg at hq
          have h1 : ∑ i ∈ s.filter (fun i => q ≤ i), d' i = ∑ i ∈ s.filter (fun i => q ≤ i), d i := by
            apply Finset.sum_congr rfl
            intro i hi
            simp only [Finset.mem_filter] at hi
            have : i ≠ b := by
              intro hib; rw [hib] at hi; exact absurd hi.2 (not_le.mpr hq)
            simp [d', this]
          have h2 := htail q
          rw [Finset.filter_insert, if_neg (not_le.mpr (lt_trans hab hq)), ] at h2
          rw [h1]; exact h2
      have hih := ih d' hd'sum hd'tail
      have hda : d a ≤ 0 := by
        have h3 := htail b
        rw [Finset.filter_insert, if_neg (not_le.mpr hab)] at h3
        have : s.filter (fun i => b ≤ i) = s := Finset.filter_true_of_mem hbs'
        rw [this] at h3
        linarith
      have hfab : f a ≤ f b := hf hab.le
      have hexp : ∑ i ∈ s, d' i * f i = ∑ i ∈ s, d i * f i + d a * f b := by
        simp only [d', add_mul, Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_congr rfl (fun i _ => by rw [ite_mul, zero_mul])]
        rw [Finset.sum_ite_eq' s b, if_pos hbs]
      rw [Finset.sum_insert hna]
      nlinarith [mul_nonneg (neg_nonneg.mpr hda) (sub_nonneg.mpr hfab)]


theorem lpm_stoch_iff {X : Type*} [Fintype X] [LinearOrder X] {π π' : X → ℝ}
    (hπ : π ∈ stdSimplex ℝ X) (hπ' : π' ∈ stdSimplex ℝ X) :
    StochGE π π' ↔ ∀ f : X → ℝ, Monotone f → ∑ i, π' i * f i ≤ ∑ i, π i * f i := by
  constructor
  · intro h f hf
    have := lpm_abel_aux f hf Finset.univ (fun i => π i - π' i)
      (by rw [Finset.sum_sub_distrib, hπ.2, hπ'.2]; ring)
      (by
        intro q
        rw [Finset.sum_sub_distrib]
        linarith [h q])
    simp only [sub_mul, Finset.sum_sub_distrib] at this
    linarith
  · intro h q
    have := h (fun i => if q ≤ i then (1:ℝ) else 0) (by
      intro i j hij
      by_cases hi : q ≤ i
      · have : q ≤ j := le_trans hi hij
        simp [hi, this]
      · simp only [hi, if_false]
        split_ifs <;> norm_num)
    simpa [Finset.sum_filter] using this

theorem lpm_mlr_stoch {X : Type*} [Fintype X] [LinearOrder X] {π π' : X → ℝ}
    (hπ : π ∈ stdSimplex ℝ X) (hπ' : π' ∈ stdSimplex ℝ X) (h : MLRGE π π') :
    StochGE π π' := by
  intro q
  have h1 : (∑ i ∈ Finset.univ.filter (fun i => q ≤ i), π i)
      + ∑ i ∈ Finset.univ.filter (fun i => ¬ q ≤ i), π i = 1 := by
    rw [Finset.sum_filter_add_sum_filter_not]; exact hπ.2
  have h1' : (∑ i ∈ Finset.univ.filter (fun i => q ≤ i), π' i)
      + ∑ i ∈ Finset.univ.filter (fun i => ¬ q ≤ i), π' i = 1 := by
    rw [Finset.sum_filter_add_sum_filter_not]; exact hπ'.2
  have key : (∑ i ∈ Finset.univ.filter (fun i => ¬ q ≤ i), π i) * (∑ i ∈ Finset.univ.filter (fun i => q ≤ i), π' i)
      ≤ (∑ i ∈ Finset.univ.filter (fun i => q ≤ i), π i) * (∑ i ∈ Finset.univ.filter (fun i => ¬ q ≤ i), π' i) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm]
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    have hji : j ≤ i := le_trans (not_le.mp hj).le hi
    exact h i j hji
  set A := ∑ i ∈ Finset.univ.filter (fun i => q ≤ i), π i
  set B := ∑ i ∈ Finset.univ.filter (fun i => ¬ q ≤ i), π i
  set A' := ∑ i ∈ Finset.univ.filter (fun i => q ≤ i), π' i
  set B' := ∑ i ∈ Finset.univ.filter (fun i => ¬ q ≤ i), π' i
  have hB : B = 1 - A := by linarith
  have hB' : B' = 1 - A' := by linarith
  rw [hB, hB'] at key
  nlinarith [key]

theorem lpm_132 {S O A : Type*} [Fintype S] [Fintype O] [Fintype A]
    [LinearOrder S] [LinearOrder O] [LinearOrder A] [Nonempty S] [Nonempty O] [Nonempty A]
    (M : POMDP S O A)
    (hP : ∀ a a' : A, a' ≤ a → TPGE (M.P a) (M.P a')) {π : S → ℝ}
    (hπ : π ∈ stdSimplex ℝ S) {a a' : A} (haa' : a' ≤ a) :
    MLRGE (M.predict π a) (M.predict π a') := by
  intro j j' hjj'
  set f := M.P a with hf
  set g := M.P a' with hg
  have hfn : ∀ x y, 0 ≤ f x y := fun x y => (M.P_row a x).1 y
  have hgn : ∀ x y, 0 ≤ g x y := fun x y => (M.P_row a' x).1 y
  have hTP := hP a a' haa'
  set B : S → S → ℝ := fun i i' => f i j * g i' j' - f i j' * g i' j with hB
  have hpair : ∀ i i', 0 ≤ B i i' + B i' i := by
    have key : ∀ i i', i ≤ i' → 0 ≤ B i i' + B i' i := by
      intro i i' hii'
      obtain ⟨c1, c2, c5, c6, c7⟩ := lpm_tp_cons f g hTP i i' j j' hii' hjj'
      have := lpm_two_pt (f i j) (f i j') (f i' j) (f i' j') (g i j) (g i j') (g i' j) (g i' j')
        (hfn _ _) (hfn _ _) (hfn _ _) (hfn _ _) (hgn _ _) (hgn _ _) (hgn _ _) (hgn _ _)
        c1 c2 c5 c6 c7
      simp only [hB]
      linarith
    intro i i'
    rcases le_total i i' with h | h
    · exact key i i' h
    · have := key i' i h; linarith
  set F : ℝ := ∑ i, ∑ i', π i * π i' * B i i' with hF
  have e1 : M.predict π a j * M.predict π a' j' - M.predict π a j' * M.predict π a' j = F := by
    unfold POMDP.predict
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i' _
    simp only [hB, hf, hg]
    ring
  have e2 : F = ∑ i, ∑ i', π i * π i' * B i' i := by
    rw [hF, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro i' _
    ring
  have hsum : 0 ≤ ∑ i, ∑ i', π i * π i' * (B i i' + B i' i) := by
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro i' _
    exact mul_nonneg (mul_nonneg (hπ.1 i) (hπ.1 i')) (hpair i i')
  have e3 : ∑ i, ∑ i', π i * π i' * (B i i' + B i' i) = F + F := by
    have h1 : ∑ i, ∑ i', π i * π i' * (B i i' + B i' i) =
        ∑ i, ∑ i', π i * π i' * B i i' + ∑ i, ∑ i', π i * π i' * B i' i := by
      simp only [mul_add, Finset.sum_add_distrib]
    rw [h1, ← e2]
  have : 0 ≤ F := by linarith
  linarith


theorem solution {S O A : Type*} [Fintype S] [Fintype O] [Fintype A]
    [LinearOrder S] [LinearOrder O] [LinearOrder A] [Nonempty S] [Nonempty O] [Nonempty A]
    (M : POMDP S O A)
    (hP : ∀ a a' : A, a' ≤ a → TPGE (M.P a) (M.P a'))
    (hRa : ∀ a a' : A, a' ≤ a → ∀ j, StochGE (M.R a j) (M.R a' j))
    (hRj : ∀ a (j j' : S), j' ≤ j → StochGE (M.R a j) (M.R a j'))
    {π : S → ℝ} (hπ : π ∈ stdSimplex ℝ S) {a a' : A} (haa' : a' ≤ a) :
    StochGE (M.sigma π a) (M.sigma π a') := by
  rw [lpm_stoch_iff (lpm_sigma_mem M hπ a) (lpm_sigma_mem M hπ a')]
  intro f hf
  rw [lpm_sigma_exp, lpm_sigma_exp]
  set φ : A → S → ℝ := fun b j => ∑ k, M.R b j k * f k with hφ
  have hmono : ∀ b, Monotone (φ b) := by
    intro b j' j hjj'
    exact (lpm_stoch_iff (M.R_row b j) (M.R_row b j')).1 (hRj b j j' hjj') f hf
  have hab : ∀ j, φ a' j ≤ φ a j := by
    intro j
    exact (lpm_stoch_iff (M.R_row a j) (M.R_row a' j)).1 (hRa a a' haa' j) f hf
  have hw : StochGE (M.predict π a) (M.predict π a') :=
    lpm_mlr_stoch (lpm_predict_mem M hπ a) (lpm_predict_mem M hπ a') (lpm_132 M hP hπ haa')
  have h1 := (lpm_stoch_iff (lpm_predict_mem M hπ a) (lpm_predict_mem M hπ a')).1 hw (φ a) (hmono a)
  calc ∑ j, M.predict π a' j * ∑ k, M.R a' j k * f k
      = ∑ j, M.predict π a' j * φ a' j := rfl
    _ ≤ ∑ j, M.predict π a' j * φ a j :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hab j) (lpm_predict_nonneg M hπ a' j))
    _ ≤ ∑ j, M.predict π a j * φ a j := h1
    _ = ∑ j, M.predict π a j * ∑ k, M.R a j k * f k := rfl
