-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.Categorical.Selected.binaryGreedyOutput_expected_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:26:51.826505+00:00
-- url     : https://prove2.me/submissions/6e64d80b-18d5-4897-8b8b-40f41c9d06ba

import Mathlib
import Definitions.Def_Q238L010
import Theorems.Thm_OAI_MetricKMedianRecovery_Categorical_Selected_greedyRun_good_s238r

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Average
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery
namespace FiniteSampling

open scoped BigOperators

section Average
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

lemma average_mono {X Y : Ω → ℝ} (h : ∀ ω, X ω ≤ Y ω) : average X ≤ average Y :=
  Finset.expect_le_expect (fun ω _ => h ω)

lemma average_nonneg {X : Ω → ℝ} (h : ∀ ω, 0 ≤ X ω) : 0 ≤ average X :=
  Finset.expect_nonneg (fun ω _ => h ω)

lemma average_sub (X Y : Ω → ℝ) :
    average (fun ω => X ω - Y ω) = average X - average Y :=
  Finset.expect_sub_distrib _ _ _

lemma average_const_mul (X : Ω → ℝ) (c : ℝ) :
    average (fun ω => c * X ω) = c * average X :=
  (Finset.mul_expect _ _ _).symm

lemma average_prod (X : Ω × Ξ → ℝ) :
    average X = average (fun ω => average (fun ξ => X (ω,ξ))) := by
  simpa only [average, Finset.univ_product_univ] using
    Finset.expect_product (Finset.univ : Finset Ω) (Finset.univ : Finset Ξ) X

lemma average_equiv (e : Ω ≃ Ξ) (X : Ω → ℝ) (Y : Ξ → ℝ)
    (h : ∀ ω, X ω = Y (e ω)) : average X = average Y :=
  Fintype.expect_equiv e X Y h

lemma average_pi_apply {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty Ω]
    (i : ι) (X : Ω → ℝ) : average (fun s : ι → Ω => X (s i)) = average X := by
  classical
  rw [average_equiv (Equiv.funSplitAt i Ω) (fun s : ι → Ω => X (s i)) (fun p => X p.1) (fun _ => rfl),
    average_prod]
  simp

lemma average_pi_mul {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty Ω]
    (i j : ι) (hij : i ≠ j) (X Y : Ω → ℝ) :
    average (fun s : ι → Ω => X (s i) * Y (s j)) = average X * average Y := by
  classical
  have hji : j ≠ i := Ne.symm hij
  rw [average_equiv (Equiv.funSplitAt i Ω) (fun s : ι → Ω => X (s i) * Y (s j))
    (fun p => X p.1 * Y (p.2 ⟨j,hji⟩)) (fun _ => rfl), average_prod]
  simp_rw [average_const_mul, average_pi_apply]
  exact average_mul_const _ _

lemma variance_identity [Nonempty Ω] (X : Ω → ℝ) :
    average (fun ω => (X ω - average X)^2) = average (fun ω => (X ω)^2) - (average X)^2 := by
  rw [average_congr (Y := fun ω => X ω ^ 2 - 2 * average X * X ω + (average X)^2)
    (fun ω => by ring), average_add, average_sub, average_const_mul, average_const]
  ring

lemma bounded_variance [Nonempty Ω] (X : Ω → ℝ) {M : ℝ}
    (hX : ∀ ω, 0 ≤ X ω ∧ X ω ≤ M) :
    average (fun ω => (X ω - average X)^2) ≤ M^2/4 := by
  have hs : average (fun ω => X ω ^ 2) ≤ M * average X := by
    rw [← average_const_mul]
    apply average_mono
    intro ω
    nlinarith [(hX ω).1, (hX ω).2]
  rw [variance_identity]
  nlinarith [sq_nonneg (average X - M/2)]

lemma sum_square {ι : Type*} [Fintype ι] (z : ι → ℝ) :
    (∑ i, z i)^2 = ∑ i, ∑ j, z i * z j := by
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

lemma variance_sum_pi {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty Ω] (X : Ω → ℝ) :
    average (fun s : ι → Ω => (∑ i, (X (s i) - average X))^2) =
      (Fintype.card ι : ℝ) * average (fun ω => (X ω - average X)^2) := by
  classical
  simp_rw [sum_square, average_sum]
  have hcenter : average (fun ω => X ω - average X) = 0 := by
    rw [average_sub, average_const, sub_self]
  have hm (i j : ι) :
      average (fun s : ι → Ω => (X (s i) - average X) * (X (s j) - average X)) =
        if i = j then average (fun ω => (X ω - average X)^2) else 0 := by
    split_ifs with hij
    · subst j
      simpa only [← pow_two] using average_pi_apply i (fun ω => (X ω - average X)^2)
    · rw [average_pi_mul i j hij (fun ω => X ω - average X) (fun ω => X ω - average X), hcenter, zero_mul]
  simp_rw [hm]
  simp

lemma sampleMean_variance [Nonempty Ω] (X : Ω → ℝ) (L : ℕ) (hL : 0 < L) :
    average (fun s : Fin L → Ω => (sampleMean L X s - average X)^2) =
      average (fun ω => (X ω - average X)^2) / L := by
  have hLR : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hL)
  have hm (s : Fin L → Ω) : sampleMean L X s - average X =
      (∑ i, (X (s i) - average X)) / L := by
    simp only [sampleMean, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  simp_rw [hm, div_pow, div_eq_mul_inv]
  rw [average_mul_const, variance_sum_pi, Fintype.card_fin]
  field_simp

end Average

section Probability
variable {Ω : Type*} [Fintype Ω]

lemma probability_false : probability (fun _ : Ω => False) = 0 := by
  classical
  simp [probability, average]

lemma probability_compl [Nonempty Ω] (P : Ω → Prop) :
    probability (fun ω => ¬P ω) = 1 - probability P := by
  classical
  unfold probability
  rw [average_congr (Y := fun ω => 1 - if P ω then 1 else 0) (by
    intro ω
    by_cases hp : P ω <;> simp [hp]), average_sub, average_const]

lemma probability_union (P Q : Ω → Prop) :
    probability (fun ω => P ω ∨ Q ω) ≤ probability P + probability Q := by
  classical
  unfold probability
  rw [← average_add]
  apply average_mono
  intro ω
  by_cases hp : P ω <;> by_cases hq : Q ω <;> simp [hp,hq]

lemma probability_chebyshev (X : Ω → ℝ) (μ tol : ℝ) (htol : 0 < tol) :
    probability (fun ω => tol < |X ω - μ|) ≤
      average (fun ω => (X ω - μ)^2) / tol^2 := by
  classical
  apply (le_div_iff₀ (sq_pos_of_pos htol)).mpr
  rw [show probability (fun ω => tol < |X ω - μ|) * tol^2 =
    average (fun ω => (if tol < |X ω - μ| then (1:ℝ) else 0) * tol^2) from
    (average_mul_const _ _).symm]
  apply average_mono
  intro ω
  split_ifs with h
  · simp only [one_mul]
    have hs := mul_self_le_mul_self htol.le h.le
    simpa only [← pow_two, sq_abs] using hs
  · simpa only [zero_mul] using sq_nonneg (X ω - μ)

theorem sampleMean_error [Nonempty Ω]
    (X : Ω → ℝ) (L : ℕ) (hL : 0 < L) {M tol : ℝ}
    (hX : ∀ ω, 0 ≤ X ω ∧ X ω ≤ M) (htol : 0 < tol) :
    probability (fun s : Fin L → Ω => tol < |sampleMean L X s - average X|)
      ≤ M^2 / (4 * L * tol^2) := by
  have hLR : (0:ℝ) < L := Nat.cast_pos.mpr hL
  have hc := probability_chebyshev (sampleMean L X) (average X) tol htol
  rw [sampleMean_variance X L hL] at hc
  have hv := div_le_div_of_nonneg_right (bounded_variance X hX) hLR.le
  have hv' := div_le_div_of_nonneg_right hv (sq_nonneg tol)
  refine hc.trans (hv'.trans_eq ?_)
  ring

lemma probability_pi_apply {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty Ω]
    (i : ι) (P : Ω → Prop) :
    probability (fun s : ι → Ω => P (s i)) = probability P := by
  classical
  exact average_pi_apply i (fun ω => if P ω then 1 else 0)

lemma probability_exists {ι : Type*} [Fintype ι] (P : ι → Ω → Prop) :
    probability (fun ω => ∃ i, P i ω) ≤ ∑ i, probability (P i) := by
  classical
  unfold probability
  rw [← average_sum]
  apply average_mono
  intro ω
  by_cases h : ∃ i, P i ω
  · obtain ⟨i,hi⟩ := h
    simp only [ite_eq_left (show ∃ index, P index ω from ⟨i,hi⟩)]
    calc
      (1:ℝ) = if P i ω then 1 else 0 := (ite_eq_left hi).symm
      _ ≤ ∑ j, if P j ω then 1 else 0 := by
        apply Finset.single_le_sum (f := fun j : ι => if P j ω then (1:ℝ) else 0)
        · intro j _
          split_ifs <;> norm_num
        · exact Finset.mem_univ i
  · simp only [ite_eq_right h]
    apply Finset.sum_nonneg
    intro i _
    split_ifs <;> norm_num

theorem simultaneous_sample_error {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty Ω]
    (X : ι → Ω → ℝ) (L : ℕ) (hL : 0 < L) {M tol : ℝ}
    (hX : ∀ i ω, 0 ≤ X i ω ∧ X i ω ≤ M) (htol : 0 < tol) :
    probability (fun seed : ι → Fin L → Ω =>
      ∃ i, tol < |sampleMean L (X i) (seed i) - average (X i)|) ≤
      (Fintype.card ι : ℝ) * (M^2 / (4 * L * tol^2)) := by
  have hu := probability_exists (Ω := ι → Fin L → Ω)
    (fun i seed => tol < |sampleMean L (X i) (seed i) - average (X i)|)
  refine hu.trans ?_
  calc
    _ ≤ ∑ i : ι, M^2 / (4 * L * tol^2) := by
      apply Finset.sum_le_sum
      intro i _
      rw [probability_pi_apply i (fun seed : Fin L → Ω =>
        tol < |sampleMean L (X i) seed - average (X i)|)]
      exact sampleMean_error (X i) L hL (hX i) htol
    _ = _ := by simp

theorem categorical_batch_error {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty Ω]
    (X : ι → Ω → ℝ) (L T a : ℕ) (hL : 0 < L) (hT : 0 < T) (ha : 0 < a)
    {M tau : ℝ} (hM : 0 < M) (htau : 0 < tau)
    (hX : ∀ i ω, 0 ≤ X i ω ∧ X i ω ≤ M)
    (hcount : (T:ℝ) * Fintype.card ι * a^2 / (4 * tau^3) ≤ L) :
    probability (fun seed : ι → Fin L → Ω =>
      ∃ i, tau*M/a < |sampleMean L (X i) (seed i) - average (X i)|) ≤ tau/T := by
  have hLR : (0:ℝ) < L := Nat.cast_pos.mpr hL
  have hTR : (0:ℝ) < T := Nat.cast_pos.mpr hT
  have haR : (0:ℝ) < a := Nat.cast_pos.mpr ha
  have htol : 0 < tau*M/a := by positivity
  refine (simultaneous_sample_error X L hL hX htol).trans ?_
  have hc := (div_le_iff₀ (show (0:ℝ) < 4*tau^3 by positivity)).mp hcount
  calc
    (Fintype.card ι : ℝ) * (M^2 / (4*L*(tau*M/a)^2)) =
        Fintype.card ι * (a:ℝ)^2 / (4*L*tau^2) := by
      field_simp
    _ ≤ tau/T := by
      apply (div_le_div_iff₀ (show (0:ℝ) < 4*L*tau^2 by positivity) hTR).mpr
      nlinarith

end Probability

lemma average_fin_succ {Ω : Type*} [Fintype Ω] (n : ℕ)
    (X : (Fin (n+1) → Ω) → ℝ) :
    average X = average (fun ω => average (fun s : Fin n → Ω => X (Fin.cons ω s))) := by
  calc
    average X = average (fun p : Ω × (Fin n → Ω) => X (Fin.cons p.1 p.2)) := by
      apply average_equiv (Fin.consEquiv (fun _ : Fin (n+1) => Ω)).symm
      intro s
      exact congrArg X (Fin.cons_self_tail s).symm
    _ = _ := average_prod _

theorem adaptive_union_bound {S Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : S → Ω → S) (bad : S → Ω → Prop) (Inv : S → Prop) {p : ℝ}
    (hInv : ∀ s, Inv s → ∀ ω, Inv (f s ω))
    (hbad : ∀ s, Inv s → probability (bad s) ≤ p)
    (n : ℕ) (s : S) (hs : Inv s) :
    probability (adaptiveBad f bad n s) ≤ n * p := by
  classical
  induction n generalizing s with
  | zero => simp only [adaptiveBad, probability_false, Nat.cast_zero, zero_mul, le_refl]
  | succ n ih =>
    unfold probability
    rw [average_fin_succ]
    have hrow (ω : Ω) :
        average (fun seed : Fin n → Ω =>
          if adaptiveBad f bad (n+1) s (Fin.cons ω seed) then (1:ℝ) else 0) ≤
          (if bad s ω then 1 else 0) + n*p := by
      change probability (fun seed : Fin n → Ω =>
        bad s ω ∨ adaptiveBad f bad n (f s ω) seed) ≤ _
      have hu := probability_union (fun _ : Fin n → Ω => bad s ω)
        (adaptiveBad f bad n (f s ω))
      have hp : probability (fun _ : Fin n → Ω => bad s ω) =
          (if bad s ω then (1:ℝ) else 0) := average_const _
      rw [hp] at hu
      exact hu.trans (add_le_add (le_refl _) (ih (f s ω) (hInv s hs ω)))
    have h := average_mono hrow
    rw [average_add, average_const] at h
    have hb := hbad s hs
    change average (fun ω => if bad s ω then (1:ℝ) else 0) ≤ p at hb
    simp only [Nat.cast_add, Nat.cast_one]
    linarith

theorem adaptive_categorical_error {S Ω ι : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype ι] [DecidableEq ι]
    (X : S → ι → Ω → ℝ) (L T a : ℕ) (hL : 0 < L) (hT : 0 < T) (ha : 0 < a)
    {M tau : ℝ} (hM : 0 < M) (htau : 0 < tau)
    (f : S → (ι → Fin L → Ω) → S) (Inv : S → Prop)
    (hInv : ∀ s, Inv s → ∀ seed, Inv (f s seed))
    (hX : ∀ s, Inv s → ∀ i ω, 0 ≤ X s i ω ∧ X s i ω ≤ M)
    (hcount : (T:ℝ) * Fintype.card ι * a^2 / (4*tau^3) ≤ L)
    (s : S) (hs : Inv s) :
    probability (adaptiveBad f (fun u seed =>
      ∃ i, tau*M/a < |sampleMean L (X u i) (seed i) - average (X u i)|) T s) ≤ tau := by
  have h := adaptive_union_bound f
    (fun u seed => ∃ i, tau*M/a < |sampleMean L (X u i) (seed i) - average (X u i)|)
    Inv hInv (fun u hu => categorical_batch_error (X u) L T a hL hT ha hM htau (hX u hu) hcount)
    T s hs
  have hTR : (T:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hT)
  simpa only [mul_div_cancel₀ tau hTR] using h

lemma average_on_good {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (bad : Ω → Prop) {c : ℝ}
    (hX : ∀ ω, 0 ≤ X ω) (hgood : ∀ ω, ¬bad ω → c ≤ X ω) :
    (1 - probability bad) * c ≤ average X := by
  classical
  rw [← probability_compl bad]
  unfold probability
  rw [← average_mul_const]
  apply average_mono
  intro ω
  by_cases hb : bad ω
  · simpa [hb] using hX ω
  · simpa [hb] using hgood ω hb

end FiniteSampling
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_SetFunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery
namespace Categorical

variable {E : Type*} [Fintype E] [DecidableEq E]

omit [Fintype E] in
lemma boundedMarginals_of_submodular (g : SetFunction E) (hmono : Monotone g)
    (hsub : Diminishing g) (hg0 : g ∅ = 0) {M : ℝ}
    (hM : ∀ e, g {e} ≤ M) : BoundedMarginals g M := by
  intro e S
  constructor
  · exact sub_nonneg.mpr (hmono (Finset.subset_insert _ _))
  · have hh := hsub ∅ S (Finset.empty_subset _) e
    simp only [marginal, Finset.insert_empty, hg0, sub_zero] at hh
    exact hh.trans (hM e)

end Categorical
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialState2
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Categorical
open FiniteSampling

section Run
variable {E : Type*} [Fintype E] [DecidableEq E] {a T L : ℕ}

omit [Fintype E] in
lemma tableValue_nonneg [NeZero T] (g : SetFunction E) (hmono : Monotone g)
    (hg0 : g ∅ = 0) (r : Fin a → Table (Fin T) E) : 0 ≤ tableValue g r := by
  apply average_nonneg
  intro seed
  rw [← hg0]
  exact hmono (Finset.empty_subset _)

end Run
end MetricKMedianRecovery.Categorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_GreedyOutputExpected
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Categorical
open FiniteSampling

section Feasible
variable {E : Type*} [Fintype E] [DecidableEq E] {a : ℕ}

omit [Fintype E] [DecidableEq E] in
lemma partitionFeasible_singleton (part : E → Fin a) (e : E) :
    PartitionFeasible part {e} := by
  intro j
  exact (Finset.card_filter_le _ _).trans (by simp)

omit [Fintype E] in

lemma exists_filling (part : E → Fin a) (hp : Function.Surjective part)
    (S : Finset E) (hS : PartitionFeasible part S) :
    ∃ o : Fin a → E, (∀ j, part (o j) = j) ∧ S ⊆ Finset.univ.image o := by
  classical
  have hc : ∀ j : Fin a, ∃ e, part e = j ∧ ∀ f ∈ S, part f = j → f = e := by
    intro j
    by_cases hn : (S.filter (fun e => part e = j)).Nonempty
    · obtain ⟨e, he⟩ := hn
      refine ⟨e, (Finset.mem_filter.mp he).2, ?_⟩
      intro f hf hp
      exact (Finset.card_le_one.mp (hS j)) _ (Finset.mem_filter.mpr ⟨hf,hp⟩) _ he
    · obtain ⟨e, he⟩ := hp j
      refine ⟨e, he, ?_⟩
      intro f hf hp
      exact False.elim (hn ⟨f, Finset.mem_filter.mpr ⟨hf,hp⟩⟩)
  choose o ho hfill using hc
  refine ⟨o, ho, ?_⟩
  intro e he
  exact Finset.mem_image.mpr ⟨part e, Finset.mem_univ _, (hfill _ e he rfl).symm⟩

lemma exists_optimal_assignment (part : E → Fin a) (hp : Function.Surjective part)
    (g : SetFunction E) (hmono : Monotone g) :
    ∃ o : Fin a → E, (∀ j, part (o j) = j) ∧
      ∀ S, PartitionFeasible part S → g S ≤ g (Finset.univ.image o) := by
  classical
  let A : Finset (Fin a → E) := Finset.univ.filter (fun o => ∀ j, part (o j) = j)
  have hA : A.Nonempty := by
    choose o ho using hp
    exact ⟨o, Finset.mem_filter.mpr ⟨Finset.mem_univ _,ho⟩⟩
  obtain ⟨o, ho, hmax⟩ := A.exists_max_image (fun o => g (Finset.univ.image o)) hA
  refine ⟨o, (Finset.mem_filter.mp ho).2, ?_⟩
  intro S hS
  obtain ⟨c, hc, hfill⟩ := exists_filling part hp S hS
  exact (hmono hfill).trans (hmax c (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩))

omit [Fintype E] in
lemma zero_of_boundedMarginals_zero (g : SetFunction E) (hg0 : g ∅ = 0)
    (hg : BoundedMarginals g 0) (S : Finset E) : g S = 0 := by
  induction S using Finset.induction_on with
  | empty => exact hg0
  | @insert e S he ih =>
    have h := hg e S
    unfold marginal at h
    linarith

end Feasible
end MetricKMedianRecovery.Categorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalRule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Categorical.Selected
open FiniteSampling
lemma Rule.surjective {E : Type*} {a : ℕ} {part : E→Fin a} (rule : Rule part) : Function.Surjective part :=
  fun j=>⟨rule.choose (fun _=>0) j,(rule.spec _ j).1⟩
variable {E : Type*} [Fintype E] [DecidableEq E] {a T L : ℕ}

lemma greedy_failure_bound [NeZero T] (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) {M tau : ℝ} (hM : 0 < M) (htau : 0 < tau)
    (hg : BoundedMarginals g M) (ha : 0 < a) (hL : 0 < L)
    (hcount : (T:ℝ) * Fintype.card E * a^2 / (4*tau^3) ≤ L)
    (s : GreedyState E a T) :
    probability (adaptiveBad (greedyStep (L := L) part rule g)
      (estimationBad part g M tau) T s) ≤ tau := by
  let X : GreedyState E a T → E → (Fin a → Fin T) → ℝ :=
    fun u e => marginalSample part g u.2 e
  have hX : ∀ u : GreedyState E a T, True → ∀ e seed,
      0 ≤ X u e seed ∧ X u e seed ≤ M := by
    intro u _ e seed
    exact hg e (draw a (Function.update u.2 (part e) (fun _ => none)) seed ∅)
  have hb := adaptive_categorical_error X L T a hL
    (Nat.pos_of_ne_zero (NeZero.ne T)) ha hM htau (greedyStep part rule g)
    (fun _ => True) (fun _ _ _ => trivial) hX hcount s trivial
  exact hb

lemma greedyRun_expectation (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) :
    average (fun seed : (Fin T → OracleSeed E a T L) × (Fin a → Fin T) =>
      g (greedyOutput part rule g seed)) =
        average (fun seed : Fin T → OracleSeed E a T L =>
          tableValue g (greedyRun part rule g seed).2) := by
  exact average_prod _

lemma greedyOutput_expected {E : Type*} [Fintype E] [DecidableEq E]
    {a T L : ℕ} [NeZero T] (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) (o : Fin a → E) (ho : ∀ j, part (o j) = j)
    (hmono : Monotone g) (hsub : Diminishing g) (hg0 : g ∅ = 0)
    {M tau : ℝ} (hM : 0 < M) (hMo : M ≤ g (Finset.univ.image o))
    (hg : BoundedMarginals g M) (ha : 0 < a) (htau : 0 < tau) (htau1 : tau ≤ 1/8)
    (hscale : (a:ℝ)^2 ≤ tau*T) (hL : 0 < L)
    (hcount : (T:ℝ) * Fintype.card E * a^2 / (4*tau^3) ≤ L) :
    (1 - 1/Real.exp 1 - 4*tau) * g (Finset.univ.image o) ≤
      average (fun seed : (Fin T → OracleSeed E a T L) × (Fin a → Fin T) =>
        g (greedyOutput part rule g seed)) := by
  have hO : 0 ≤ g (Finset.univ.image o) := le_trans hM.le hMo
  have he2 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have he0 : 0 ≤ 1/Real.exp 1 := by positivity
  have hehalf : 1/Real.exp 1 ≤ (1:ℝ)/2 := by
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    linarith
  have hc : 0 ≤ (1 - 1/Real.exp 1 - 3*tau) * g (Finset.univ.image o) :=
    mul_nonneg (by linarith) hO
  have hb := greedy_failure_bound part rule g hM htau hg ha hL hcount
    (initialState E a T)
  have havg := average_on_good (fun seed : Fin T → OracleSeed E a T L =>
      tableValue g (greedyRun part rule g seed).2)
    (adaptiveBad (greedyStep part rule g) (estimationBad part g M tau)
      T (initialState E a T))
    (fun _ => tableValue_nonneg g hmono hg0 _)
    (fun seed hgood => greedyRun_good_s238r part rule g o ho hmono hsub hg0 hM.le hMo
        hg ha htau.le htau1 hscale seed hgood)
  rw [greedyRun_expectation]
  calc
    _ ≤ (1-tau) * ((1 - 1/Real.exp 1 - 3*tau) * g (Finset.univ.image o)) := by
      have hs : 1 - 1/Real.exp 1 - 4*tau ≤
          (1-tau)*(1 - 1/Real.exp 1 - 3*tau) := by
        nlinarith [mul_nonneg htau.le he0, sq_nonneg tau]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hs hO
    _ ≤ (1 - probability (adaptiveBad (greedyStep part rule g)
        (estimationBad part g M tau) T (initialState E a T))) *
          ((1 - 1/Real.exp 1 - 3*tau) * g (Finset.univ.image o)) :=
      mul_le_mul_of_nonneg_right (sub_le_sub_left hb 1) hc
    _ ≤ _ := havg

lemma categorical_expected {E : Type*} [Fintype E] [DecidableEq E]
    {a T L : ℕ} [NeZero T] (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) (hmono : Monotone g) (hsub : Diminishing g) (hg0 : g ∅ = 0)
    {tau : ℝ} (ha : 0 < a) (htau : 0 < tau) (htau1 : tau ≤ 1/8)
    (hscale : (a:ℝ)^2 ≤ tau*T) (hL : 0 < L)
    (hcount : (T:ℝ) * Fintype.card E * a^2 / (4*tau^3) ≤ L)
    (S : Finset E) (hS : PartitionFeasible part S) :
    (1 - 1/Real.exp 1 - 4*tau) * g S ≤
      average (fun seed : (Fin T → OracleSeed E a T L) × (Fin a → Fin T) =>
        g (greedyOutput part rule g seed)) := by
  have hnonneg : ∀ U, 0 ≤ g U := fun U => by
    rw [← hg0]
    exact hmono (Finset.empty_subset U)
  obtain ⟨e, _⟩ := rule.surjective ⟨0,ha⟩
  have hE : (Finset.univ : Finset E).Nonempty := ⟨e, Finset.mem_univ e⟩
  obtain ⟨emax, _, hmax⟩ := Finset.univ.exists_max_image (fun e : E => g {e}) hE
  have hbound := boundedMarginals_of_submodular g hmono hsub hg0
    (fun e => hmax e (Finset.mem_univ _))
  by_cases hM : 0 < g {emax}
  · obtain ⟨o, ho, hopt⟩ := exists_optimal_assignment part rule.surjective g hmono
    have havg := greedyOutput_expected part rule g o ho hmono hsub hg0 hM
      (hopt {emax} (partitionFeasible_singleton part emax)) hbound ha htau htau1
      hscale hL hcount
    have he2 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
    have hehalf : 1/Real.exp 1 ≤ (1:ℝ)/2 := by
      apply (div_le_iff₀ (Real.exp_pos _)).mpr
      linarith
    exact (mul_le_mul_of_nonneg_left (hopt S hS) (by linarith)).trans havg
  · have hM0 : g {emax} = 0 := le_antisymm (not_lt.mp hM) (hnonneg _)
    rw [hM0] at hbound
    rw [zero_of_boundedMarginals_zero g hg0 hbound S, mul_zero]
    exact average_nonneg (fun _ => hnonneg _)

lemma binaryGreedyOutput_expected_s238r_oai {E : Type*} [Fintype E] [DecidableEq E]
    {a b L : ℕ} (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) (hmono : Monotone g) (hsub : Diminishing g) (hg0 : g ∅ = 0)
    {tau : ℝ} (ha : 0 < a) (htau : 0 < tau) (htau1 : tau ≤ 1/8)
    (hscale : (a:ℝ)^2 ≤ tau*(2^b:ℕ)) (hL : 0 < L)
    (hcount : ((2^b:ℕ):ℝ)*Fintype.card E*a^2/(4*tau^3) ≤ L)
    (S : Finset E) (hS : PartitionFeasible part S) :
    (1 - 1/Real.exp 1 - 4*tau) * g S ≤
      average (fun bits : BinaryOracleIndex E a b L → Bool =>
        g (binaryGreedyOutput part rule g bits)) := by
  simp only [binaryGreedyOutput]
  rw [average_equiv (binarySeedEquiv E a b L) _
    (fun seed => g (greedyOutput part rule g seed)) (fun _ => rfl)]
  exact categorical_expected part rule g hmono hsub hg0 ha htau htau1 hscale hL hcount S hS

end MetricKMedianRecovery.Categorical.Selected

end OAI
end

theorem solution.{u_2} : type_of% @OAI.MetricKMedianRecovery.Categorical.Selected.binaryGreedyOutput_expected_s238r_oai.{u_2} := @OAI.MetricKMedianRecovery.Categorical.Selected.binaryGreedyOutput_expected_s238r_oai.{u_2}
