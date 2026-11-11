-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.Categorical.Selected.greedyRun_good_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:19:43.836232+00:00
-- url     : https://prove2.me/submissions/49beb4cb-4292-4b81-8181-5d76e4867257

import Mathlib
import Definitions.Def_Q238K014

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

lemma average_nonneg {X : Ω → ℝ} (h : ∀ ω, 0 ≤ X ω) : 0 ≤ average X :=
  Finset.expect_nonneg (fun ω _ => h ω)

lemma average_prod (X : Ω × Ξ → ℝ) :
    average X = average (fun ω => average (fun ξ => X (ω,ξ))) := by
  simpa only [average, Finset.univ_product_univ] using
    Finset.expect_product (Finset.univ : Finset Ω) (Finset.univ : Finset Ξ) X

lemma average_equiv (e : Ω ≃ Ξ) (X : Ω → ℝ) (Y : Ξ → ℝ)
    (h : ∀ ω, X ω = Y (e ω)) : average X = average Y :=
  Fintype.expect_equiv e X Y h

end Average

section Probability
variable {Ω : Type*} [Fintype Ω]

lemma probability_nonneg (P : Ω → Prop) : 0 ≤ probability P := by
  classical
  apply average_nonneg
  intro ω
  split_ifs <;> norm_num

lemma probability_false : probability (fun _ : Ω => False) = 0 := by
  classical
  simp [probability, average]

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

lemma operator_const (w : E → ℝ) (c : ℝ) (S : Finset E) :
    operator w (fun _ => c) S = c := by
  simp only [operator, ← Finset.sum_mul]
  ring

lemma operator_add (w : E → ℝ) (g h : SetFunction E) (S : Finset E) :
    operator w (fun U => g U + h U) S = operator w g S + operator w h S := by
  simp only [operator, mul_add, Finset.sum_add_distrib]
  ring

lemma operator_smul (w : E → ℝ) (c : ℝ) (g : SetFunction E) (S : Finset E) :
    operator w (fun U => c * g U) S = c * operator w g S := by
  have hs : (∑ e, w e * (c * g (insert e S))) = c * ∑ e, w e * g (insert e S) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  unfold operator
  rw [hs]
  ring

lemma operator_mono (w : E → ℝ) (hw : IsWeight w) (g h : SetFunction E)
    (hgh : ∀ S, g S ≤ h S) (S : Finset E) : operator w g S ≤ operator w h S := by
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (hgh S) (sub_nonneg.mpr hw.2)
  · exact Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (hgh _) (hw.1 e)

lemma operator_bounds (w : E → ℝ) (hw : IsWeight w) (g : SetFunction E) (a b : ℝ)
    (hg : ∀ S, a ≤ g S ∧ g S ≤ b) (S : Finset E) :
    a ≤ operator w g S ∧ operator w g S ≤ b := by
  constructor
  · simpa only [operator_const] using operator_mono w hw (fun _ => a) g (fun U => (hg U).1) S
  · simpa only [operator_const] using operator_mono w hw g (fun _ => b) (fun U => (hg U).2) S

lemma marginal_operator (w : E → ℝ) (g : SetFunction E) (e : E) (S : Finset E) :
    marginal (operator w g) e S = operator w (marginal g e) S := by
  have hs : (∑ f, w f * g (insert f (insert e S))) =
      ∑ f, w f * g (insert e (insert f S)) := by
    apply Finset.sum_congr rfl
    intro f _
    rw [Finset.insert_comm e f]
  unfold marginal operator
  rw [hs]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

lemma operator_marginals (w : E → ℝ) (hw : IsWeight w) (g : SetFunction E) (M : ℝ)
    (hg : BoundedMarginals g M) : BoundedMarginals (operator w g) M := by
  intro e S
  rw [marginal_operator]
  exact operator_bounds w hw (marginal g e) 0 M (hg e) S

lemma sum_addMass (w : E → ℝ) (e : E) (d : ℝ) :
    ∑ f, addMass w e d f = (∑ f, w f) + d := by
  simp [addMass, Finset.sum_add_distrib]

lemma addMass_weight (w : E → ℝ) (e : E) {d : ℝ} (hd : 0 ≤ d)
    (hw : IsWeight w) (hr : (∑ f, w f) + d ≤ 1) : IsWeight (addMass w e d) := by
  refine ⟨?_, ?_⟩
  · intro f
    unfold addMass
    split_ifs <;> linarith [hw.1 f]
  · rwa [sum_addMass]

lemma operator_addMass (w : E → ℝ) (e : E) (d : ℝ) (g : SetFunction E) (S : Finset E) :
    operator (addMass w e d) g S = operator w g S + d * marginal g e S := by
  unfold operator
  rw [sum_addMass]
  have hsum : (∑ f, addMass w e d f * g (insert f S)) =
      (∑ f, w f * g (insert f S)) + d * g (insert e S) := by
    simp only [addMass, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
    simp
  rw [hsum]
  unfold marginal
  ring

lemma evaluate_add (b : Batch E) (g h : SetFunction E) (S : Finset E) :
    evaluate b (fun U => g U + h U) S = evaluate b g S + evaluate b h S := by
  induction b generalizing g h with
  | nil => rfl
  | cons p tail ih =>
    rcases p with ⟨w, e⟩
    simp only [evaluate]
    conv_lhs => arg 2; ext U; rw [operator_add]
    exact ih _ _

lemma evaluate_smul (b : Batch E) (c : ℝ) (g : SetFunction E) (S : Finset E) :
    evaluate b (fun U => c * g U) S = c * evaluate b g S := by
  induction b generalizing g with
  | nil => rfl
  | cons p tail ih =>
    rcases p with ⟨w, e⟩
    simp only [evaluate]
    conv_lhs => arg 2; ext U; rw [operator_smul]
    exact ih _

lemma evaluate_const (b : Batch E) (c : ℝ) (S : Finset E) :
    evaluate b (fun _ => c) S = c := by
  induction b with
  | nil => rfl
  | cons p tail ih =>
    rcases p with ⟨w, e⟩
    simp only [evaluate]
    conv_lhs => arg 2; ext U; rw [operator_const]
    exact ih

lemma evaluate_mono (b : Batch E) (hb : ∀ p ∈ b, IsWeight p.1)
    (g h : SetFunction E) (hgh : ∀ S, g S ≤ h S) (S : Finset E) :
    evaluate b g S ≤ evaluate b h S := by
  induction b generalizing g h with
  | nil => exact hgh S
  | cons p tail ih =>
    rcases p with ⟨w, e⟩
    exact ih (fun p hp => hb p (List.mem_cons_of_mem _ hp)) _ _
      (operator_mono w (hb _ (List.mem_cons_self)) g h hgh)

lemma evaluate_addMass_head (tail : Batch E) (w : E → ℝ) (e : E) (d : ℝ)
    (g : SetFunction E) (S : Finset E) :
    evaluate ((addMass w e d, e) :: tail) g S =
      evaluate tail (operator w g) S + d * evaluate tail (marginal g e) S := by
  simp only [evaluate]
  conv_lhs => arg 2; ext U; rw [operator_addMass]
  rw [evaluate_add, evaluate_smul]

lemma update_weights {d : ℝ} (b : Batch E) (hd : 0 ≤ d) (hr : HasRoom d b) :
    ∀ p ∈ update d b, IsWeight p.1 := by
  intro p hp
  obtain ⟨⟨w,e⟩, hmem, rfl⟩ := List.mem_map.mp hp
  exact addMass_weight w e hd (hr _ hmem).1 (hr _ hmem).2

lemma evaluate_update_lower (b : Batch E) (g : SetFunction E) {M d : ℝ}
    (_hM : 0 ≤ M) (hd : 0 ≤ d) (hr : HasRoom d b)
    (hg : ∀ S, 0 ≤ g S ∧ g S ≤ M) (S : Finset E) :
    evaluate b g S - (b.length : ℝ) * d * M ≤ evaluate (update d b) g S := by
  induction b generalizing g with
  | nil => simp [evaluate, update]
  | cons p tail ih =>
    rcases p with ⟨w,e⟩
    have hw := (hr _ List.mem_cons_self).1
    have htail : HasRoom d tail := fun p hp => hr p (List.mem_cons_of_mem _ hp)
    have ihg := ih (operator w g) htail (operator_bounds w hw g 0 M hg)
    have hm : ∀ U, -M ≤ marginal g e U := fun U => by
      unfold marginal
      linarith [(hg (insert e U)).1, (hg U).2]
    have hm' : -M ≤ evaluate (update d tail) (marginal g e) S := by
      simpa only [evaluate_const] using evaluate_mono (update d tail)
        (update_weights tail hd htail) (fun _ => -M) (marginal g e) hm S
    have heq : update d ((w,e)::tail) = (addMass w e d,e)::update d tail := rfl
    rw [heq, evaluate_addMass_head]
    simp only [evaluate, List.length_cons, Nat.cast_add, Nat.cast_one]
    have hmul := mul_le_mul_of_nonneg_left hm' hd
    nlinarith

theorem categorical_update_bound (b : Batch E) (g : SetFunction E) {M d : ℝ}
    (hM : 0 ≤ M) (hd : 0 ≤ d) (hr : HasRoom d b)
    (hg : BoundedMarginals g M) (S : Finset E) :
    evaluate b g S + d * direction b g S - (b.length : ℝ)^2 * d^2 * M ≤
      evaluate (update d b) g S := by
  induction b generalizing g with
  | nil => simp [evaluate, direction, update]
  | cons p tail ih =>
    rcases p with ⟨w,e⟩
    have hw := (hr _ List.mem_cons_self).1
    have htail : HasRoom d tail := fun p hp => hr p (List.mem_cons_of_mem _ hp)
    have ihg := ih (operator w g) htail (operator_marginals w hw g M hg)
    have hder := evaluate_update_lower tail (marginal g e) hM hd htail (hg e) S
    have hder' := mul_le_mul_of_nonneg_left hder hd
    have heq : update d ((w,e)::tail) = (addMass w e d,e)::update d tail := rfl
    rw [heq, evaluate_addMass_head]
    simp only [evaluate, direction, List.length_cons, Nat.cast_add, Nat.cast_one]
    have hlen : (0 : ℝ) ≤ tail.length := Nat.cast_nonneg _
    have herr : 0 ≤ ((tail.length : ℝ) + 1) * d^2 * M := by positivity
    nlinarith

omit [Fintype E] in
lemma submodular_telescope (b : Batch E) (g : SetFunction E) (hg : Diminishing g)
    (S : Finset E) : g (S ∪ choices b) - g S ≤ allMarginals b g S := by
  induction b with
  | nil => simp [choices, allMarginals]
  | cons p tail ih =>
    rcases p with ⟨w,e⟩
    have hm := hg S (S ∪ choices tail) Finset.subset_union_left e
    simp only [choices, allMarginals, Finset.union_insert]
    unfold marginal at hm ⊢
    linarith

omit [Fintype E] in
lemma comparison_gap (b : Batch E) (g : SetFunction E) (hmono : Monotone g)
    (hsub : Diminishing g) (S : Finset E) :
    g (choices b) - g S ≤ allMarginals b g S := by
  have ht := submodular_telescope b g hsub S
  have hm := hmono (Finset.subset_union_right : choices b ⊆ S ∪ choices b)
  linarith

lemma operator_diminishing (w : E → ℝ) (hw : IsWeight w)
    (g : SetFunction E) (hg : Diminishing g) : Diminishing (operator w g) := by
  intro U V hUV e
  rw [marginal_operator, marginal_operator]
  unfold operator
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (hg U V hUV e) (sub_nonneg.mpr hw.2)
  · apply Finset.sum_le_sum
    intro f _
    exact mul_le_mul_of_nonneg_left (hg (insert f U) (insert f V)
      (Finset.insert_subset_insert f hUV) e) (hw.1 f)

lemma operator_le_self (w : E → ℝ) (hw : IsWeight w) (g : SetFunction E)
    (S : Finset E) (hg : ∀ e, g (insert e S) ≤ g S) : operator w g S ≤ g S := by
  calc
    operator w g S ≤ operator w (fun _ => g S) S := by
      unfold operator
      apply add_le_add le_rfl
      exact Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (hg e) (hw.1 e)
    _ = g S := operator_const _ _ _

lemma operator_marginal_le (w : E → ℝ) (hw : IsWeight w) (g : SetFunction E)
    (hg : Diminishing g) (e : E) (S : Finset E) :
    operator w (marginal g e) S ≤ marginal g e S := by
  apply operator_le_self w hw (marginal g e) S
  intro f
  exact hg S (insert f S) (Finset.subset_insert _ _) e

lemma operator_allMarginals (w : E → ℝ) (b : Batch E) (g : SetFunction E) (S : Finset E) :
    operator w (allMarginals b g) S = allMarginals b (operator w g) S := by
  induction b with
  | nil => exact operator_const _ _ _
  | cons p tail ih =>
    rcases p with ⟨v,e⟩
    simp only [allMarginals, operator_add, ← marginal_operator, ih]

lemma direction_dominates (b : Batch E) (g : SetFunction E)
    (hb : ∀ p ∈ b, IsWeight p.1) (hg : Diminishing g) (S : Finset E) :
    evaluate b (allMarginals b g) S ≤ direction b g S := by
  induction b generalizing g with
  | nil => simp [evaluate, direction, allMarginals]
  | cons p tail ih =>
    rcases p with ⟨w,e⟩
    have hw := hb _ List.mem_cons_self
    have htail : ∀ p ∈ tail, IsWeight p.1 := fun p hp => hb p (List.mem_cons_of_mem _ hp)
    have ht := ih (operator w g) htail (operator_diminishing w hw g hg)
    have hm := evaluate_mono tail htail (operator w (marginal g e)) (marginal g e)
      (operator_marginal_le w hw g hg e) S
    simp only [evaluate, direction, allMarginals]
    have heq : operator w (fun U => marginal g e U + allMarginals tail g U) =
        fun U => operator w (marginal g e) U + allMarginals tail (operator w g) U := by
      funext U
      rw [operator_add, operator_allMarginals]
    rw [heq, evaluate_add]
    exact add_le_add hm ht

lemma evaluate_sub (b : Batch E) (g h : SetFunction E) (S : Finset E) :
    evaluate b (fun U => g U - h U) S = evaluate b g S - evaluate b h S := by
  have hh : (fun U => g U - h U) = (fun U => g U + (-1) * h U) := by
    funext U
    ring
  rw [hh, evaluate_add, evaluate_smul]
  ring

theorem categorical_comparison_direction (b : Batch E) (g : SetFunction E)
    (hb : ∀ p ∈ b, IsWeight p.1) (hmono : Monotone g) (hsub : Diminishing g)
    (S : Finset E) : g (choices b) - evaluate b g S ≤ direction b g S := by
  have h := evaluate_mono b hb (fun U => g (choices b) - g U) (allMarginals b g)
    (comparison_gap b g hmono hsub) S
  rw [evaluate_sub, evaluate_const] at h
  exact h.trans (direction_dominates b g hb hsub S)

lemma evaluate_eq_of_sameWeights (b c : Batch E) (h : SameWeights b c)
    (g : SetFunction E) (S : Finset E) : evaluate b g S = evaluate c g S := by
  induction h generalizing g with
  | nil => rfl
  | @cons p q b c hp hbc ih =>
    rcases p with ⟨w,e⟩
    rcases q with ⟨v,f⟩
    dsimp at hp
    subst v
    exact ih _

end Categorical
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Table
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery
namespace Categorical

open FiniteSampling
variable {E Ω : Type*} [Fintype E] [DecidableEq E] [Fintype Ω] [Nonempty Ω]

lemma tableWeights_valid (r : Table Ω E) : IsWeight (tableWeights r) := by
  refine ⟨fun e => probability_nonneg _, ?_⟩
  have h := tableWeights_total r
  have hp := probability_nonneg (fun ω => r ω = none)
  linarith

omit [Nonempty Ω] in
lemma average_update [DecidableEq Ω] (X : Ω → ℝ) (ω : Ω) (v : ℝ) :
    average (Function.update X ω v) = average X + (v-X ω)/(Fintype.card Ω) := by
  rw [average, Fintype.expect_eq_sum_div_card, average, Fintype.expect_eq_sum_div_card]
  have hsum : ∑ ξ, Function.update X ω v ξ = (∑ ξ, X ξ) + (v-X ω) := by
    have hp (ξ : Ω) : Function.update X ω v ξ =
        X ξ + if ξ = ω then v-X ω else 0 := by
      by_cases h : ξ = ω <;> simp [h]
    simp_rw [hp, Finset.sum_add_distrib]
    simp
  rw [hsum, add_div]

omit [Fintype E] [Nonempty Ω] in
lemma tableWeights_update [DecidableEq Ω] (r : Table Ω E) (ω : Ω) (e : E)
    (hr : r ω = none) :
    tableWeights (Function.update r ω (some e)) =
      addMass (tableWeights r) e (1 / (Fintype.card Ω : ℝ)) := by
  classical
  funext f
  unfold tableWeights probability
  calc
    _ = average (Function.update (fun ξ => if r ξ = some f then (1:ℝ) else 0) ω
        (if f = e then 1 else 0)) := by
      apply average_congr
      intro ξ
      by_cases h : ξ = ω <;> simp [h, eq_comm]
    _ = _ := by
      rw [average_update]
      unfold addMass
      simp only [hr, reduceCtorEq, ite_false, if_false, sub_zero]
      split_ifs <;> simp
      all_goals
        apply average_congr
        intro ξ
        by_cases h : r ξ = some f <;> simp [h]

omit [Fintype E] [DecidableEq E] [Nonempty Ω] in
lemma average_comm {Ξ : Type*} [Fintype Ξ] (X : Ω → Ξ → ℝ) :
    average (fun ω => average (X ω)) = average (fun ξ => average (fun ω => X ω ξ)) := by
  exact Finset.expect_comm Finset.univ Finset.univ X

omit [Fintype E] [DecidableEq E] [Nonempty Ω] in
lemma batch_cons {a : ℕ} (r : Fin (a+1) → Table Ω E) (c : Fin (a+1) → E) :
    batch r c = (tableWeights (r 0), c 0) :: batch (Fin.tail r) (Fin.tail c) := by
  exact List.ofFn_succ

lemma average_draw (a : ℕ) (r : Fin a → Table Ω E) (c : Fin a → E)
    (g : SetFunction E) (S : Finset E) :
    average (fun seed : Fin a → Ω => g (draw a r seed S)) = evaluate (batch r c) g S := by
  induction a generalizing g S with
  | zero => simp [draw, batch, evaluate]
  | succ a ih =>
    rw [average_fin_succ, batch_cons]
    change average (fun ω => average (fun seed : Fin a → Ω =>
      g (put (r 0 ω) (draw a (Fin.tail r) seed S)))) = _
    rw [average_comm]
    have ht (U : Finset E) : average (fun ω => g (put (r 0 ω) U)) =
        operator (tableWeights (r 0)) g U := by
      rw [table_operator]
      apply average_congr
      intro ω
      cases r 0 ω <;> rfl
    simp_rw [ht]
    exact ih (Fin.tail r) (Fin.tail c) _ S

lemma batch_valid {a : ℕ} (r : Fin a → Table Ω E) (c : Fin a → E) :
    ∀ p ∈ batch r c, IsWeight p.1 := by
  intro p hp
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hp
  exact tableWeights_valid _

omit [Fintype E] [DecidableEq E] [Nonempty Ω] in
lemma batch_length {a : ℕ} (r : Fin a → Table Ω E) (c : Fin a → E) :
    (batch r c).length = a := List.length_ofFn

lemma operator_zero (g : SetFunction E) : operator (fun _ => 0) g = g := by
  funext S
  simp [operator]

omit [Fintype E] [DecidableEq E] [Nonempty Ω] in
lemma tableWeights_none : tableWeights (fun _ : Ω => (none : Option E)) = fun _ => 0 := by
  funext e
  unfold tableWeights
  simpa using probability_false (Ω := Ω)

omit [Fintype E] [DecidableEq E] [Nonempty Ω] in
lemma batch_sameweights {a : ℕ} (r : Fin a → Table Ω E) (c d : Fin a → E) :
    SameWeights (batch r c) (batch r d) := by
  induction a with
  | zero => exact List.Forall₂.nil
  | succ a ih =>
    rw [batch_cons, batch_cons]
    exact List.Forall₂.cons rfl (ih (Fin.tail r) (Fin.tail c) (Fin.tail d))

omit [Nonempty Ω] in
lemma partial_choice {a : ℕ} (r : Fin a → Table Ω E) (c d : Fin a → E)
    (j : Fin a) (e : E) (g : SetFunction E) (S : Finset E) :
    derivative r c j e g S = derivative r d j e g S := by
  exact evaluate_eq_of_sameWeights _ _ (batch_sameweights _ _ _) _ _

lemma partial_sample {a : ℕ} (r : Fin a → Table Ω E) (c : Fin a → E)
    (j : Fin a) (e : E) (g : SetFunction E) (S : Finset E) :
    derivative r c j e g S = average (fun seed : Fin a → Ω =>
      marginal g e (draw a (Function.update r j (fun _ => none)) seed S)) := by
  exact (average_draw _ _ _ _ _).symm

omit [Nonempty Ω] in
lemma partial_zero {a : ℕ} (r : Fin (a+1) → Table Ω E) (c : Fin (a+1) → E)
    (e : E) (g : SetFunction E) (S : Finset E) :
    derivative r c 0 e g S = evaluate (batch (Fin.tail r) (Fin.tail c)) (marginal g e) S := by
  unfold derivative
  rw [batch_cons]
  simp only [Function.update_self, tableWeights_none, evaluate, operator_zero]
  have ht : Fin.tail (Function.update r 0 (fun _ => none)) = Fin.tail r := by
    funext j
    simp [Fin.tail_def]
  rw [ht]

omit [Nonempty Ω] in
lemma partial_succ {a : ℕ} (r : Fin (a+1) → Table Ω E) (c : Fin (a+1) → E)
    (j : Fin a) (e : E) (g : SetFunction E) (S : Finset E) :
    derivative r c j.succ e g S =
      derivative (Fin.tail r) (Fin.tail c) j e (operator (tableWeights (r 0)) g) S := by
  unfold derivative
  rw [batch_cons]
  simp only [Function.update_of_ne (Fin.succ_ne_zero j).symm, evaluate]
  have ht : Fin.tail (Function.update r j.succ (fun _ => none)) =
      Function.update (Fin.tail r) j (fun _ => none) := by
    funext k
    by_cases h : k = j
    · subst k; simp [Fin.tail_def]
    · simp [Fin.tail_def, Fin.succ_inj, h]
  rw [ht]
  congr 1
  funext U
  exact (marginal_operator _ _ _ _).symm

omit [Nonempty Ω] in
lemma direction_sum {a : ℕ} (r : Fin a → Table Ω E) (c : Fin a → E)
    (g : SetFunction E) (S : Finset E) :
    direction (batch r c) g S = ∑ j, derivative r c j (c j) g S := by
  induction a generalizing g with
  | zero => simp [batch, direction]
  | succ a ih =>
    rw [batch_cons, direction, Fin.sum_univ_succ, partial_zero]
    simp_rw [partial_succ]
    congr 1
    exact ih _ _ _

end Categorical
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Advance
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Categorical

open FiniteSampling

section TableAdvance
variable {E Ω : Type*} [Fintype E] [DecidableEq E] [Fintype Ω] [DecidableEq Ω]

omit [Fintype E] in
lemma batch_advance {a : ℕ} (r : Fin a → Table Ω E) (ω : Ω) (c : Fin a → E)
    (h : ∀ j, r j ω = none) :
    batch (advance r ω c) c = update (1 / (Fintype.card Ω : ℝ)) (batch r c) := by
  unfold batch update advance
  rw [List.map_ofFn]
  congr 1
  funext j
  rw [tableWeights_update (r j) ω (c j) (h j)]
  rfl

lemma batch_room [Nonempty Ω] {a : ℕ} (r : Fin a → Table Ω E) (ω : Ω)
    (c : Fin a → E) (h : ∀ j, r j ω = none) :
    HasRoom (1 / (Fintype.card Ω : ℝ)) (batch r c) := by
  intro p hp
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hp
  refine ⟨tableWeights_valid _, ?_⟩
  have hv := (tableWeights_valid (Function.update (r j) ω (some (c j)))).2
  rw [tableWeights_update (r j) ω (c j) (h j), sum_addMass] at hv
  exact hv

end TableAdvance

section SampledDirection
variable {E Ω : Type*} [Fintype E] [DecidableEq E] [Fintype Ω] [Nonempty Ω]

omit [Fintype E] [Nonempty Ω] in
lemma choices_batch {a : ℕ} (r : Fin a → Table Ω E) (c : Fin a → E) :
    choices (batch r c) = Finset.univ.image c := by
  induction a with
  | zero => simp [batch, choices]
  | succ a ih =>
    rw [batch_cons, choices, ih]
    ext e
    simp [Fin.exists_fin_succ, Fin.tail_def, eq_comm]

lemma sampled_direction {a : ℕ} (r : Fin a → Table Ω E)
    (c o : Fin a → E) (g : SetFunction E) (S : Finset E)
    (hmono : Monotone g) (hsub : Diminishing g) {tol : ℝ}
    (hchoice : ∀ j, derivative r c j (o j) g S ≤
      derivative r c j (c j) g S + 2 * tol) :
    g (Finset.univ.image o) - evaluate (batch r c) g S - 2 * a * tol ≤
      direction (batch r c) g S := by
  have hc := categorical_comparison_direction (batch r o) g (batch_valid r o)
    hmono hsub S
  rw [choices_batch, ← evaluate_eq_of_sameWeights (batch r c) (batch r o)
    (batch_sameweights r c o) g S] at hc
  have hd : direction (batch r o) g S ≤ direction (batch r c) g S + 2 * a * tol := by
    rw [direction_sum, direction_sum]
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hchoice j)
    simp_rw [partial_choice r o c]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hs
    nlinarith only [hs]
  linarith

end SampledDirection

end MetricKMedianRecovery.Categorical

namespace MetricKMedianRecovery.FiniteSampling

lemma adaptiveRun_growth {S Ω : Type*} (f : S → Ω → S) (bad : S → Ω → Prop)
    (Inv : S → Prop) (clock : S → ℕ) (V : S → ℝ) (T : ℕ) {r Q : ℝ}
    (hr : 0 ≤ r)
    (hInv : ∀ s, Inv s → ∀ ω, Inv (f s ω))
    (hclock : ∀ s, clock s < T → ∀ ω, clock (f s ω) = clock s + 1)
    (hstep : ∀ s, Inv s → clock s < T → ∀ ω, ¬bad s ω →
      r * V s + (1-r) * Q ≤ V (f s ω))
    (n : ℕ) (s : S) (hs : Inv s) (hn : clock s + n ≤ T)
    (seed : Fin n → Ω) (hg : ¬adaptiveBad f bad n s seed) :
    r^n * V s + (1-r^n) * Q ≤ V (adaptiveRun f n s seed) := by
  induction n generalizing s with
  | zero => simp [adaptiveRun]
  | succ n ih =>
    have hlt : clock s < T := by omega
    have hgood : ¬bad s (seed 0) ∧
        ¬adaptiveBad f bad n (f s (seed 0)) (Fin.tail seed) := not_or.mp hg
    have hi := ih (f s (seed 0)) (hInv s hs (seed 0))
      (by rw [hclock s hlt]; omega) (Fin.tail seed) hgood.2
    have hl := mul_le_mul_of_nonneg_left
      (hstep s hs hlt (seed 0) hgood.1) (pow_nonneg hr n)
    change _ ≤ V (adaptiveRun f n (f s (seed 0)) (Fin.tail seed))
    rw [pow_succ]
    nlinarith

end MetricKMedianRecovery.FiniteSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_DirectionChoiceErrors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery
namespace Categorical
variable {E : Type*} [Fintype E] [DecidableEq E]

lemma two_estimates_choice {trueChosen trueOther estChosen estOther tol : ℝ}
    (hchosen : |estChosen - trueChosen| ≤ tol)
    (hother : |estOther - trueOther| ≤ tol) (hmax : estOther ≤ estChosen) :
    trueOther ≤ trueChosen + 2 * tol := by
  rcases abs_le.mp hchosen with ⟨hca,hcb⟩
  rcases abs_le.mp hother with ⟨hoa,hob⟩
  linarith

end Categorical

end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_TableValue
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Categorical
open FiniteSampling

section GreedyStep
variable {E : Type*} [Fintype E] [DecidableEq E] {a T L : ℕ}

lemma marginalSample_average [NeZero T] (part : E → Fin a) (g : SetFunction E)
    (r : Fin a → Table (Fin T) E) (c : Fin a → E) (e : E) :
    average (marginalSample part g r e) = derivative r c (part e) e g ∅ := by
  exact (partial_sample r c (part e) e g ∅).symm

end GreedyStep
end MetricKMedianRecovery.Categorical

namespace MetricKMedianRecovery.Categorical
open FiniteSampling

section StepBound
variable {E : Type*} [Fintype E] [DecidableEq E] {a T L : ℕ} [NeZero T]

lemma tableValue_eq (g : SetFunction E) (r : Fin a → Table (Fin T) E) (c : Fin a → E) :
    tableValue g r = evaluate (batch r c) g ∅ := average_draw a r c g ∅

lemma advance_gain (g : SetFunction E) (r : Fin a → Table (Fin T) E)
    (ω : Fin T) (c o : Fin a → E) (hempty : ∀ j, r j ω = none)
    (hmono : Monotone g) (hsub : Diminishing g) {M tol : ℝ} (hM : 0 ≤ M)
    (hg : BoundedMarginals g M)
    (hchoice : ∀ j, derivative r c j (o j) g ∅ ≤
      derivative r c j (c j) g ∅ + 2 * tol) :
    tableValue g r + (1/(T:ℝ)) * (g (Finset.univ.image o) - tableValue g r - 2*a*tol) -
      (a:ℝ)^2 * (1/(T:ℝ))^2 * M ≤ tableValue g (advance r ω c) := by
  have hu := categorical_update_bound (batch r c) g hM
    (show 0 ≤ 1/(T:ℝ) by positivity)
    (by simpa only [Fintype.card_fin] using batch_room r ω c hempty) hg ∅
  have he : update (1/(T:ℝ)) (batch r c) = batch (advance r ω c) c := by
    simpa only [Fintype.card_fin] using (batch_advance r ω c hempty).symm
  rw [he, batch_length, ← tableValue_eq g r c, ← tableValue_eq] at hu
  have hd := sampled_direction r c o g ∅ hmono hsub hchoice
  rw [← tableValue_eq] at hd
  have hm := mul_le_mul_of_nonneg_left hd (show 0 ≤ 1/(T:ℝ) by positivity)
  linarith

lemma advance_recurrence (g : SetFunction E) (r : Fin a → Table (Fin T) E)
    (ω : Fin T) (c o : Fin a → E) (hempty : ∀ j, r j ω = none)
    (hmono : Monotone g) (hsub : Diminishing g) {M tau : ℝ} (hM : 0 ≤ M)
    (hg : BoundedMarginals g M) (ha : 0 < a) (hscale : (a:ℝ)^2 ≤ tau*T)
    (hchoice : ∀ j, derivative r c j (o j) g ∅ ≤
      derivative r c j (c j) g ∅ + 2 * (tau*M/a)) :
    tableValue g r + (g (Finset.univ.image o) - tableValue g r - 3*tau*M)/T ≤
      tableValue g (advance r ω c) := by
  have haR : (a:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt ha)
  have hTR : (T:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne T)
  have hs := advance_gain g r ω c o hempty hmono hsub hM hg hchoice
  have ht : 2*(a:ℝ)*(tau*M/a) = 2*tau*M := by field_simp
  rw [ht] at hs
  have herr : (a:ℝ)^2 * (1/(T:ℝ))^2 * M ≤ tau*M/T := by
    calc
      _ = ((a:ℝ)^2*M) / (T:ℝ)^2 := by ring
      _ ≤ (tau*T*M) / (T:ℝ)^2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hscale hM) (sq_nonneg _)
      _ = _ := by field_simp
  calc
    _ = tableValue g r + (1/(T:ℝ)) *
        (g (Finset.univ.image o) - tableValue g r - 2*tau*M) - tau*M/T := by ring
    _ ≤ tableValue g r + (1/(T:ℝ)) *
        (g (Finset.univ.image o) - tableValue g r - 2*tau*M) -
          (a:ℝ)^2 * (1/(T:ℝ))^2 * M := sub_le_sub_left herr _
    _ ≤ _ := hs

end StepBound
end MetricKMedianRecovery.Categorical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialState2
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Categorical
open FiniteSampling

lemma initialState_invariant {E : Type*} {a T : ℕ} (part : E → Fin a) :
    GreedyInvariant part (initialState E a T) := by
  constructor
  · intro j ω e he
    change (none : Option E) = some e at he
    cases he
  · intro j ω h
    rfl

lemma draw_none {E Ω : Type*} [DecidableEq E] (a : ℕ) (seed : Fin a → Ω)
    (S : Finset E) : draw a (fun _ _ => (none : Option E)) seed S = S := by
  induction a with
  | zero => rfl
  | succ a ih => exact ih (Fin.tail seed)

lemma tableValue_none {E Ω : Type*} [DecidableEq E] [Fintype Ω] [Nonempty Ω]
    (a : ℕ) (g : SetFunction E) :
    tableValue g (fun _ : Fin a => fun _ : Ω => none) = g ∅ := by
  unfold tableValue
  simp_rw [draw_none]
  exact average_const _

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
variable {E : Type*} [Fintype E] [DecidableEq E] {a T L : ℕ}

omit [Fintype E] in
lemma greedyStep_clock (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) (s : GreedyState E a T) (ht : s.1 < T)
    (seed : OracleSeed E a T L) : (greedyStep part rule g s seed).1 = s.1+1 := by
  simp [greedyStep, ht]

omit [Fintype E] in
lemma greedyStep_invariant (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) (s : GreedyState E a T) (hs : GreedyInvariant part s)
    (seed : OracleSeed E a T L) : GreedyInvariant part (greedyStep part rule g s seed) := by
  by_cases ht : s.1 < T
  · simp only [greedyStep, dite_eq_left ht, GreedyInvariant, advance]
    constructor
    · intro j ω e he
      by_cases hω : ω = (⟨s.1,ht⟩ : Fin T)
      · subst ω
        simp only [Function.update_self, Option.some.injEq] at he
        rw [← he]
        exact (rule.spec _ j).1
      · rw [Function.update_of_ne hω] at he
        exact hs.1 j ω e he
    · intro j ω hω
      have hne : ω ≠ (⟨s.1,ht⟩ : Fin T) := by
        intro he
        have := congrArg Fin.val he
        simp only at this
        omega
      rw [Function.update_of_ne hne]
      exact hs.2 j ω (by omega)
  · simpa only [greedyStep, dite_eq_right ht] using hs

lemma sampled_select_choice [NeZero T] (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) (r : Fin a → Table (Fin T) E) (o : Fin a → E)
    (ho : ∀ j, part (o j) = j) (seed : OracleSeed E a T L) {tol : ℝ}
    (hgood : ∀ e, |scores part g r seed e - average (marginalSample part g r e)| ≤ tol) :
    let c := rule.choose (scores part g r seed)
    ∀ j, derivative r c j (o j) g ∅ ≤ derivative r c j (c j) g ∅ + 2 * tol := by
  intro c j
  have hc := (rule.spec (scores part g r seed) j)
  have hg1 := hgood (c j)
  have hg2 := hgood (o j)
  rw [marginalSample_average part g r c, hc.1] at hg1
  rw [marginalSample_average part g r c, ho] at hg2
  exact two_estimates_choice hg1 hg2 (hc.2 (o j) (ho j))

lemma greedyStep_recurrence [NeZero T] (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) (o : Fin a → E) (ho : ∀ j, part (o j) = j)
    (hmono : Monotone g) (hsub : Diminishing g) {M tau : ℝ} (hM : 0 ≤ M)
    (hg : BoundedMarginals g M) (ha : 0 < a) (hscale : (a:ℝ)^2 ≤ tau*T)
    (s : GreedyState E a T) (hs : GreedyInvariant part s) (ht : s.1 < T)
    (seed : OracleSeed E a T L) (hgood : ¬estimationBad part g M tau s seed) :
    tableValue g s.2 + (g (Finset.univ.image o) - tableValue g s.2 - 3*tau*M)/T ≤
      tableValue g (greedyStep part rule g s seed).2 := by
  have hgood' : ∀ e, |scores part g s.2 seed e - average (marginalSample part g s.2 e)|
      ≤ tau*M/a := by
    intro e
    exact not_lt.mp (fun he => hgood ⟨e,he⟩)
  have hc := sampled_select_choice part rule g s.2 o ho seed hgood'
  simpa only [greedyStep, dite_eq_left ht] using
    advance_recurrence g s.2 ⟨s.1,ht⟩ (rule.choose (scores part g s.2 seed)) o
      (fun j => hs.2 j ⟨s.1,ht⟩ (le_refl _)) hmono hsub hM hg ha hscale hc

lemma greedyRun_good_s238_oai [NeZero T] (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) (o : Fin a → E) (ho : ∀ j, part (o j) = j)
    (hmono : Monotone g) (hsub : Diminishing g) (hg0 : g ∅ = 0)
    {M tau : ℝ} (hM : 0 ≤ M) (hMo : M ≤ g (Finset.univ.image o))
    (hg : BoundedMarginals g M) (ha : 0 < a) (htau : 0 ≤ tau) (htau1 : tau ≤ 1/8)
    (hscale : (a:ℝ)^2 ≤ tau*T) (seed : Fin T → OracleSeed E a T L)
    (hgood : ¬adaptiveBad (greedyStep part rule g) (estimationBad part g M tau)
      T (initialState E a T) seed) :
    (1 - 1/Real.exp 1 - 3*tau) * g (Finset.univ.image o) ≤
      tableValue g (greedyRun part rule g seed).2 := by
  have hTR : (0:ℝ) < T := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne T))
  have hT1 : (1:ℝ) ≤ T := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (NeZero.ne T))
  have hr : 0 ≤ 1 - 1/(T:ℝ) := sub_nonneg.mpr ((div_le_one hTR).mpr hT1)
  have hQ : 0 ≤ g (Finset.univ.image o) - 3*tau*M := by nlinarith
  have hh := adaptiveRun_growth (greedyStep part rule g) (estimationBad part g M tau)
    (GreedyInvariant part) Prod.fst (fun s => tableValue g s.2) T
    (Q := g (Finset.univ.image o) - 3*tau*M) hr
    (greedyStep_invariant part rule g) (greedyStep_clock part rule g)
    (fun s hs hlt ω hw => by
      have h := greedyStep_recurrence part rule g o ho hmono hsub hM hg ha hscale s hs hlt ω hw
      convert h using 1 ; ring)
    T (initialState E a T) (initialState_invariant part) (by simp [initialState]) seed hgood
  simp only [initialState, tableValue_none, hg0, mul_zero, zero_add] at hh
  have he := Real.one_sub_div_pow_le_exp_neg (n := T) (t := (1:ℝ)) hT1
  rw [Real.exp_neg] at he
  have he' := mul_le_mul_of_nonneg_right (sub_le_sub_left he 1) hQ
  have hexp : 0 ≤ 1 / Real.exp 1 := by positivity
  have hexp1 : 1 / Real.exp 1 ≤ 1 := by
    apply (div_le_one (Real.exp_pos _)).mpr
    exact Real.one_le_exp_iff.mpr (by norm_num)
  have hprod : (1 - 1 / Real.exp 1) * M ≤ g (Finset.univ.image o) := by nlinarith
  have hprod' := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 3*tau by positivity)
  calc
    _ ≤ (1 - 1/Real.exp 1) * (g (Finset.univ.image o) - 3*tau*M) := by nlinarith
    _ ≤ (1 - (1-1/(T:ℝ))^T) * (g (Finset.univ.image o) - 3*tau*M) :=
      by simpa only [one_div] using he'
    _ ≤ _ := hh

end MetricKMedianRecovery.Categorical.Selected

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.Categorical.Selected.greedyRun_good_s238_oai.{u_1} := @OAI.MetricKMedianRecovery.Categorical.Selected.greedyRun_good_s238_oai.{u_1}
