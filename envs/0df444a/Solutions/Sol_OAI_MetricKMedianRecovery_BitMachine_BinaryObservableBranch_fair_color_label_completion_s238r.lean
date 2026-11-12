-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.fair_color_label_completion_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:34:40.5932+00:00
-- url     : https://prove2.me/submissions/ab4cecd9-15e3-4df4-bb38-9e7294685867

import Mathlib
import Definitions.Def_Q238L010
import Definitions.Def_Q238L011
import Definitions.Def_Q238L018
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryObservableBranch_successful_probability_s238r

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelRange
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.ColorLabel

lemma labelRange_bounds (b : ℕ) (hb : 0 < b) : b ≤ labelRange b ∧ labelRange b < 2*b := by
  refine ⟨Nat.le_pow_clog (by decide) b, ?_⟩
  by_cases h : 1 < b
  · have he : Nat.clog 2 b = (Nat.clog 2 b-1)+1 := by
      have := Nat.clog_pos (by decide : 1 < 2) h
      omega
    have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) h
    have hp' : 2^(Nat.clog 2 b-1) < b := by simpa only [Nat.pred_eq_sub_one] using hp
    unfold labelRange
    rw [he, pow_succ]
    omega
  · have he : b=1 := by omega
    simp [he, labelRange]

lemma labelMass_nonneg (b : ℕ) (hb : 0 < b) (j : Fin b) : 0 ≤ labelMass b hb j := by
  unfold labelMass
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)

lemma labelMass_lower (b : ℕ) (hb : 0 < b) (j : Fin b) :
    1/(2*(b:ℝ)) ≤ labelMass b hb j := by
  have hbound := labelRange_bounds b hb
  let x : Fin (labelRange b) := ⟨j.val, j.isLt.trans_le hbound.1⟩
  have hj : label b hb x = j := by apply Fin.ext; exact Nat.mod_eq_of_lt j.isLt
  have hs : 1/(labelRange b : ℝ) ≤ labelMass b hb j := by
    have hh := Finset.single_le_sum (s := (Finset.univ : Finset (Fin (labelRange b))))
      (f := fun x => if label b hb x = j then 1/(labelRange b:ℝ) else 0)
      (fun _ _ => by split_ifs <;> positivity) (Finset.mem_univ x)
    simpa only [hj, ↓reduceIte, labelMass] using hh
  apply le_trans ?_ hs
  apply one_div_le_one_div_of_le
  · exact_mod_cast (lt_of_lt_of_le hb hbound.1)
  · exact_mod_cast hbound.2.le

lemma factorial_probability (b : ℕ) (hb : 0 < b) :
    (1/(2*Real.exp 1))^b ≤ (b.factorial : ℝ)*(1/(2*(b:ℝ)))^b := by
  have hbR : (0:ℝ) < b := Nat.cast_pos.mpr hb
  have hf : (0:ℝ) < b.factorial := Nat.cast_pos.mpr (Nat.factorial_pos b)
  have he := Real.pow_div_factorial_le_exp (b:ℝ) (Nat.cast_nonneg (α := ℝ) b) b
  have hexp : Real.exp (b:ℝ) = (Real.exp 1)^b := by
    simpa only [mul_one] using Real.exp_nat_mul 1 b
  rw [hexp, div_le_iff₀ hf] at he
  rw [div_pow, one_pow, div_pow, one_pow, mul_one_div]
  apply (div_le_div_iff₀ (pow_pos (mul_pos (by norm_num) (Real.exp_pos 1)) b)
    (pow_pos (mul_pos (by norm_num) hbR) b)).mpr
  rw [mul_pow, mul_pow]
  nlinarith [mul_le_mul_of_nonneg_left he (show (0:ℝ) ≤ 2^b by positivity)]

lemma distinctMass_lower (b : ℕ) (μ : Fin b → ℝ) (hμ : ∀ j, 0 ≤ μ j)
    (q : ℝ) (hq : 0 ≤ q) (hlower : ∀ j, q ≤ μ j) :
    (b.factorial : ℝ)*q^b ≤ distinctMass b μ := by
  classical
  let fn : Equiv.Perm (Fin b) → (Fin b → Fin b) := fun e => e
  have hinj : Function.Injective fn := fun _ _ h => Equiv.ext (congrFun h)
  let T := Finset.univ.image fn
  have hc : (T.card : ℝ) = b.factorial := by
    simp only [T, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_perm,
      Fintype.card_fin]
  have hlo : (b.factorial : ℝ)*q^b ≤
      ∑ f ∈ T, if Function.Injective f then ∏ i, μ (f i) else 0 := by
    rw [← hc]
    calc
      _ = ∑ _f ∈ T, q^b := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun f hf => by
        obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hf
        rw [ite_eq_left e.injective]
        have hh := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin b)))
          (fun _ _ => hq) (fun i _ => hlower (e i))
        simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hh)
  exact hlo.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
    (fun f _ _ => by split_ifs; exact Finset.prod_nonneg (fun i _ => hμ (f i)); exact le_rfl))

lemma actual_distinct_probability (b : ℕ) (hb : 0 < b) :
    (1/(2*Real.exp 1))^b ≤ distinctMass b (labelMass b hb) := by
  exact (factorial_probability b hb).trans
    (distinctMass_lower b (labelMass b hb) (labelMass_nonneg b hb) _ (by positivity)
      (labelMass_lower b hb))

lemma product_event {I X : Type*} [Fintype I] [Fintype X] [DecidableEq I]
    (p : I → X → ℝ) (E : I → X → Prop) [∀ i, DecidablePred (E i)] :
    (∑ f : I → X, if ∀ i, E i (f i) then ∏ i, p i (f i) else 0) =
      ∏ i, ∑ x, if E i x then p i x else 0 := by
  classical
  have hh := Finset.sum_prod_piFinset (ι := I) (Finset.univ : Finset X)
    (fun i x => if E i x then p i x else 0)
  simpa only [Fintype.piFinset_univ, Fintype.prod_ite_zero] using hh

lemma colorMass_values (c : Fin 3) : colorMass c = if c=0 then (1/2 : ℝ) else 1/4 := by
  fin_cases c
  all_goals
    simp only [colorMass, Fin.sum_univ_succ]
    first | (simp [color, Fin.ext_iff]; all_goals first | (norm_num [color, Fin.ext_iff]; done) | rfl | decide) | (norm_num [color, Fin.ext_iff]; done) | norm_num [color, Fin.ext_iff]

lemma colorMass_lower (c : Fin 3) : (1/4 : ℝ) ≤ colorMass c := by
  rw [colorMass_values]
  split_ifs <;> norm_num

lemma specified_color_probability {I : Type*} [Fintype I] [DecidableEq I]
    (Q : Finset I) (required : I → Fin 3) :
    (1/4 : ℝ)^Q.card ≤
      ∑ seed : I → Fin 4,
        if ∀ i ∈ Q, color (seed i) = required i then (1/4 : ℝ)^(Fintype.card I) else 0 := by
  classical
  have he : (∑ seed : I → Fin 4,
      if ∀ i ∈ Q, color (seed i) = required i then (1/4 : ℝ)^(Fintype.card I) else 0) =
      ∏ i ∈ Q, colorMass (required i) := by
    have hh := product_event (fun (_ : I) (_ : Fin 4) => (1/4 : ℝ))
      (fun i x => i ∈ Q → color x = required i)
    simp only [Finset.prod_const, Finset.card_univ] at hh
    rw [hh]
    have hsum : ∀ i : I,
        (∑ x : Fin 4, if i ∈ Q → color x = required i then (1/4 : ℝ) else 0) =
          if i ∈ Q then colorMass (required i) else 1 := by
      intro i
      by_cases hi : i ∈ Q
      · simp only [hi, true_implies, ↓reduceIte, colorMass]
      · simp [hi]
    simp_rw [hsum]
    simp only [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.prod_const_one, mul_one]
  rw [he]
  have hh := Finset.prod_le_prod (s := Q) (f := fun _ => (1/4 : ℝ))
    (fun _ _ => by norm_num) (fun i _ => colorMass_lower (required i))
  simpa only [Finset.prod_const] using hh

lemma event_pushforward {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (f : X → Y) (w : X → ℝ) (E : Y → Prop) [DecidablePred E] :
    (∑ y : Y, if E y then ∑ x : X, if f x = y then w x else 0 else 0) =
      ∑ x : X, if E (f x) then w x else 0 := by
  classical
  have hh : ∀ y, (if E y then ∑ x : X, if f x = y then w x else 0 else 0) =
      ∑ x : X, if E y then (if f x = y then w x else 0) else 0 := by
    intro y
    split_ifs <;> simp
  simp_rw [hh]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  have ht : ∀ y, (if E y then (if f x = y then w x else 0) else 0) =
      if f x = y then (if E (f x) then w x else 0) else 0 := by
    intro y
    by_cases h : f x = y
    · subst y; simp
    · simp [h]
  simp_rw [ht]
  simp

lemma binaryDistinctMass_eq (b : ℕ) (hb : 0 < b) :
    binaryDistinctMass b hb = distinctMass b (labelMass b hb) := by
  classical
  symm
  have hprod : ∀ f : Fin b → Fin b,
      (∏ i, labelMass b hb (f i)) =
        ∑ seed : Fin b → Fin (labelRange b),
          if (fun i => label b hb (seed i)) = f then (1/(labelRange b : ℝ))^b else 0 := by
    intro f
    have hh := product_event (fun (_ : Fin b) (_ : Fin (labelRange b)) =>
      (1/(labelRange b : ℝ))) (fun i x => label b hb x = f i)
    simpa only [labelMass, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      funext_iff] using hh.symm
  unfold distinctMass
  simp_rw [hprod]
  exact event_pushforward (fun seed : Fin b → Fin (labelRange b) =>
    fun i => label b hb (seed i)) (fun _ => (1/(labelRange b : ℝ))^b) Function.Injective

lemma binary_distinct_probability (b : ℕ) (hb : 0 < b) :
    (1/(2*Real.exp 1))^b ≤ binaryDistinctMass b hb := by
  rw [binaryDistinctMass_eq]
  exact actual_distinct_probability b hb

end MetricKMedianRecovery.ColorLabel

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_Blue
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_proxy _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_uncovered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion

variable {V : Type*} [DecidableEq V] {a : ℕ}

lemma designatedProxies_card_le (R : Finset V) (dest : V → Destination V a) :
    (designatedProxies R dest).card ≤ R.card := by
  unfold designatedProxies
  apply (Finset.card_biUnion_le).trans
  calc
    _ ≤ ∑ _s ∈ R, 1 := Finset.sum_le_sum (fun s _ => by cases dest s <;> simp)
    _ = R.card := by simp

lemma color_requirement_count (R : Finset V) (dest : V → Destination V a) (m : ℕ)
    (hR : R.card ≤ m) : (R ∪ designatedProxies R dest).card ≤ 2*m := by
  have hc := Finset.card_union_le R (designatedProxies R dest)
  have hp := designatedProxies_card_le R dest
  omega

end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Average
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
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

lemma probability_congr {P Q : Ω → Prop} (h : ∀ ω, P ω ↔ Q ω) :
    probability P = probability Q := by
  classical
  apply average_congr
  intro ω
  simp only [h ω]

end Probability

end FiniteSampling
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Cluster
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

namespace Comparison
variable {D S O : Finset V}

lemma nonproxy_card (C : Comparison D S O) : C.nonproxy.card = C.bad.card := by
  have hsub : C.good.image C.proxy ⊆ S := Finset.image_subset_iff.mpr C.proxy_mem
  rw [nonproxy, Finset.card_sdiff_of_subset hsub, bad,
    Finset.card_sdiff_of_subset C.good_subset, C.same_card,
    Finset.card_image_of_injOn C.proxy_inj]

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_ProbabilityProd
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.FiniteSampling
variable {I Ω Ξ : Type*} [Fintype I] [Fintype Ω] [Fintype Ξ]

lemma probability_prod (E : Ω → Ξ → Prop) :
    probability (fun p : Ω × Ξ => E p.1 p.2) =
      average (fun x => probability (E x)) := by
  classical
  exact average_prod _

lemma probability_prod_lower (P : Ω → Prop) (E : Ω → Ξ → Prop) {p : ℝ}
    (h : ∀ x, P x → p ≤ probability (E x)) :
    probability P * p ≤ probability (fun xy : Ω × Ξ => E xy.1 xy.2) := by
  classical
  rw [probability_prod,probability,← average_mul_const]
  apply average_mono
  intro x
  split_ifs with hx
  · simpa only [one_mul] using h x hx
  · simpa only [zero_mul] using probability_nonneg (E x)

lemma probability_prod_conj (P : Ω → Prop) (Q : Ξ → Prop) :
    probability (fun xy : Ω × Ξ => P xy.1 ∧ Q xy.2) = probability P * probability Q := by
  classical
  rw [probability_prod (fun x y => P x ∧ Q y)]
  have he : (fun x => probability (fun y => P x ∧ Q y)) =
      fun x => (if P x then (1:ℝ) else 0)*probability Q := by
    funext x
    by_cases hx : P x
    · simp only [hx,true_and,ite_true, if_true,one_mul]
    · simp only [hx,false_and,ite_false, if_false,zero_mul,probability_false]
  rw [he,average_mul_const]
  rfl

lemma average_pi_restrict [DecidableEq I] [Nonempty Ω] (Q : Finset I)
    (X : (↥Q → Ω) → ℝ) :
    average (fun seed : I → Ω => X (fun i => seed i)) = average X := by
  classical
  rw [average_equiv (Equiv.piEquivPiSubtypeProd (fun i => i ∈ Q) (fun _ => Ω))
    (fun seed : I → Ω => X (fun i => seed i)) (fun p => X p.1) (fun _ => rfl),average_prod]
  simp

lemma probability_pi_restrict [DecidableEq I] [Nonempty Ω] (Q : Finset I)
    (E : (↥Q → Ω) → Prop) :
    probability (fun seed : I → Ω => E (fun i => seed i)) = probability E := by
  classical
  exact average_pi_restrict Q (fun x => if E x then 1 else 0)

lemma probability_uniform_fun [DecidableEq I] (b : ℕ) (E : (I → Fin b) → Prop)
    [DecidablePred E] :
    probability E = ∑ seed : I → Fin b,
      if E seed then (1/(b:ℝ))^(Fintype.card I) else 0 := by
  classical
  rw [probability,average,Fintype.expect_eq_sum_div_card,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow]
  split_ifs <;> simp

end MetricKMedianRecovery.FiniteSampling

namespace MetricKMedianRecovery.ColorLabel
open FiniteSampling
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma color_event_probability (Q : Finset I) (required : I → Fin 3) :
    (1/4:ℝ)^Q.card ≤ probability (fun seed : I → Fin 4 =>
      ∀ i ∈ Q, color (seed i) = required i) := by
  rw [probability_uniform_fun]
  exact specified_color_probability Q required

lemma label_event_probability (B : Finset I) (b : ℕ) (hb : 0 < b) (hB : B.card = b) :
    (1/(2*Real.exp 1))^b ≤ probability (fun seed : I → Fin (labelRange b) =>
      Set.InjOn (fun i => label b hb (seed i)) (↑B)) := by
  classical
  have hr : 0 < labelRange b := pow_pos (by omega) _
  let : Nonempty (Fin (labelRange b)) := ⟨⟨0,hr⟩⟩
  have hrestrict : probability (fun seed : I → Fin (labelRange b) =>
        Set.InjOn (fun i => label b hb (seed i)) (↑B)) =
      probability (fun seed : ↥B → Fin (labelRange b) =>
        Function.Injective (fun i => label b hb (seed i))) := by
    rw [← probability_pi_restrict B (fun seed : ↥B → Fin (labelRange b) =>
      Function.Injective (fun i => label b hb (seed i)))]
    apply probability_congr
    intro seed
    constructor
    · intro h i j hij
      exact Subtype.ext (h i.property j.property hij)
    · intro h i hi j hj hij
      exact congrArg Subtype.val (h (a₁ := ⟨i,hi⟩) (a₂ := ⟨j,hj⟩) hij)
  rw [hrestrict]
  let e : ↥B ≃ Fin b := Fintype.equivOfCardEq (by simpa only [Fintype.card_coe,Fintype.card_fin] using hB)
  let ee : (↥B → Fin (labelRange b)) ≃ (Fin b → Fin (labelRange b)) :=
    { toFun := fun f i => f (e.symm i)
      invFun := fun f i => f (e i)
      left_inv := by intro f; funext i; simp
      right_inv := by intro f; funext i; simp }
  have he (seed : ↥B → Fin (labelRange b)) :
      Function.Injective (fun i => label b hb (seed i)) ↔
      Function.Injective (fun i => label b hb (ee seed i)) := by
    constructor
    · intro hi i j hij
      exact e.symm.injective (hi hij)
    · intro hi i j hij
      apply e.injective
      apply hi
      simpa only [ee,Equiv.coe_fn_mk,e.symm_apply_apply] using hij
  have hev : probability (fun seed : ↥B → Fin (labelRange b) =>
        Function.Injective (fun i => label b hb (seed i))) =
      binaryDistinctMass b hb := by
    unfold probability
    rw [average_equiv ee _
      (fun seed => if Function.Injective (fun i => label b hb (seed i)) then 1 else 0)
      (fun seed => by simp only [he seed])]
    have hu := probability_uniform_fun (I := Fin b) (labelRange b)
      (fun seed => Function.Injective (fun i => label b hb (seed i)))
    simp only [probability,Fintype.card_fin,binaryDistinctMass] at hu ⊢
    convert hu using 1
    all_goals try with_reducible_and_instances rfl
    apply average_congr
    intro seed
    split_ifs <;> rfl
  rw [hev]
  exact binary_distinct_probability b hb

end MetricKMedianRecovery.ColorLabel

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_FavorableReady
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryObservableBranch
open Completion Categorical FiniteSampling BinaryBranchContext Sampling BinaryBranchProgram
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
lemma fair_color_label_completion_s238r_oai
    (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S O : Finset (Fin n)) (C : Comparison D S O) (hD : D.Nonempty)
    (hSF : S⊆F) (hOF : O⊆F) (hS : S.Nonempty)
    (Δ : ℚ) (hΔ : 0≤Δ) (hbound : ∀ x,∀ f∈F,δ x f≤Δ)
    (s : RationalSampling.State n) (hs : C.Correct hD (1/1000000) s.real)
    (hP : 0 < comparisonCost D C.assign) (hm : 0<C.bad.card)
    (hI : C.removalTotal (Δ:ℝ) s.real≤(1/1000000:ℝ)*comparisonCost D C.assign)
    (hN : C.nearTotal (Δ:ℝ) s.real≤(1/1000000:ℝ)*comparisonCost D C.assign)
    (b : ℕ) (hb : 0<b)
    (hcard : (designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card=b)
    (r0 y0 : Fin n) :
    let q:=(designatedRed (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card
    let c:=((designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).image
      (C.blueDestination hD s.real (19/50))).card
    (1/(32*Real.exp 1))^C.bad.card*(3/197:ℝ)≤
      probability (fun seed : ((Fin n→Fin 4) × (Fin n→Fin (ColorLabel.labelRange b))) × Bits n s.leaves.length=>
        realCost D (output δ D F S Δ s (fun u=>ColorLabel.color (seed.1.1 u))
          (fun u=>ColorLabel.label b hb (seed.1.2 u)) q c r0 y0 seed.2)≤
            (197/100:ℝ)*comparisonCost D C.assign) := by
  classical
  dsimp only
  let R := C.nonproxy \ s.real.deleted
  let dest := C.designatedDestination hD s.real (19/50)
  let Q := R ∪ designatedProxies R dest
  let B := designatedBlue R dest
  let PC : (Fin n → Fin 4) → Prop := fun seed =>
    ∀ i ∈ Q, ColorLabel.color (seed i) = requiredColors R dest i
  let PL : (Fin n → Fin (ColorLabel.labelRange b)) → Prop := fun seed =>
    Set.InjOn (fun i => ColorLabel.label b hb (seed i)) (↑B)
  have hR : R.card ≤ C.bad.card := by
    rw [← C.nonproxy_card]
    exact Finset.card_le_card Finset.sdiff_subset
  have hQ : Q.card ≤ 2*C.bad.card := color_requirement_count R dest C.bad.card hR
  have hB : b ≤ C.bad.card := by
    rw [← hcard]
    exact (Finset.card_filter_le _ _).trans hR
  have hc : (1/4:ℝ)^Q.card ≤ probability PC :=
    ColorLabel.color_event_probability Q (requiredColors R dest)
  have hl : (1/(2*Real.exp 1))^b ≤ probability PL :=
    ColorLabel.label_event_probability B b hb hcard
  have hexp : 1 ≤ Real.exp (1:ℝ) := Real.one_le_exp (by norm_num)
  have hbase : 0 ≤ 1/(2*Real.exp (1:ℝ)) := by positivity
  have hbase1 : 1/(2*Real.exp (1:ℝ)) ≤ 1 := by
    rw [div_le_iff₀ (by positivity : 0 < 2*Real.exp (1:ℝ))]
    linarith
  have hc' : (1/4:ℝ)^(2*C.bad.card) ≤ probability PC :=
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) hQ).trans hc
  have hl' : (1/(2*Real.exp 1))^C.bad.card ≤ probability PL :=
    (pow_le_pow_of_le_one hbase hbase1 hB).trans hl
  have hp : (1/(32*Real.exp 1))^C.bad.card ≤ probability (fun seed : (Fin n → Fin 4) × (Fin n → Fin (ColorLabel.labelRange b)) => PC seed.1 ∧ PL seed.2) := by
    rw [probability_prod_conj]
    calc
      _ = (1/4:ℝ)^(2*C.bad.card)*(1/(2*Real.exp 1))^C.bad.card := by
        rw [pow_mul,← mul_pow]
        congr 1
        ring
      _ ≤ probability PC * probability PL :=
        mul_le_mul hc' hl' (by positivity) (probability_nonneg PC)
  apply (mul_le_mul_of_nonneg_right hp (by norm_num : (0:ℝ) ≤ 3/197)).trans
  refine probability_prod_lower
    (fun seed : (Fin n → Fin 4) × (Fin n → Fin (ColorLabel.labelRange b)) => PC seed.1 ∧ PL seed.2)
    (fun seed bits => realCost D (output δ D F S Δ s
      (fun u => ColorLabel.color (seed.1 u))
      (fun u => ColorLabel.label b hb (seed.2 u))
      (designatedRed R dest).card (B.image (C.blueDestination hD s.real (19/50))).card r0 y0 bits) ≤
        (197/100:ℝ)*comparisonCost D C.assign) ?_
  intro seed hseed
  exact successful_probability_s238r δ hδ D F S O C hD hSF hOF hS Δ hΔ hbound s hs hP hm hI hN
    (fun u=>ColorLabel.color (seed.1 u)) hseed.1
    (fun u=>ColorLabel.label b hb (seed.2 u)) hcard hseed.2 r0 y0
end MetricKMedianRecovery.BitMachine.BinaryObservableBranch

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.fair_color_label_completion_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.fair_color_label_completion_s238r_oai
