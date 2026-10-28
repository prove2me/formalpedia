-- Prove2me | solution 1 for OAI.SharpTerminalLeave.averaged_disjoint_grid_collision
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T06:54:04.81908+00:00
-- url     : https://prove2.me/submissions/f4920462-82ad-45fc-85ba-39013f4ca4f6

import Mathlib
import Definitions.Def_TriangleRemoval
import Definitions.Def_OAIQ4Tr000

section
-- module Solutions.OAIQ4_Tr.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_WitnessMu
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave

theorem witness_exp_series (x : ℝ) :
    HasSum (fun j : ℕ => x ^ j / (j.factorial : ℝ)) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_EndpointMarksExponential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

lemma endpoint_marks_exponential (s : ℕ) :
    ((s : ℝ)+4)^2 ≤ 32*(5/4 : ℝ)^s := by
  induction s with
  | zero => norm_num
  | succ s ih =>
    by_cases hs : s < 5
    · interval_cases s <;> norm_num
    · have hn : (5 : ℝ) ≤ s := by exact_mod_cast Nat.le_of_not_gt hs
      have hstep : ((s : ℝ)+5)^2 ≤ (5/4 : ℝ)*((s : ℝ)+4)^2 := by
        nlinarith [sq_nonneg ((s : ℝ)-5)]
      have hh := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 5/4)
      simp only [Nat.cast_add,Nat.cast_one,pow_succ]
      nlinarith

lemma pattern_marks_exponential {R s : ℕ} (hR : R ≤ 4) :
    (((R+s)^2 * 6^s : ℕ) : ℝ) ≤ 32*(15/2 : ℝ)^s := by
  have hr : (R : ℝ) ≤ 4 := by exact_mod_cast hR
  have hp : ((R : ℝ)+(s : ℝ))^2 ≤ ((s : ℝ)+4)^2 := by
    exact pow_le_pow_left₀ (by positivity) (by linarith : (R : ℝ)+(s : ℝ) ≤ (s : ℝ)+4) 2
  push_cast
  calc
    _ ≤ (((s : ℝ)+4)^2)*(6 : ℝ)^s :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ ≤ (32*(5/4 : ℝ)^s)*(6 : ℝ)^s :=
      mul_le_mul_of_nonneg_right (endpoint_marks_exponential s) (by positivity)
    _ = 32*(15/2 : ℝ)^s := by rw [mul_assoc,← mul_pow]; norm_num

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Probability_ProductPMF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

theorem productPMF_update_apply {K V : Type*} [Fintype K] [DecidableEq K]
    [Fintype V] [DecidableEq V] (ρ : K → PMF V) (k : K) (v : V) (ω : K → V) :
    productPMF (Function.update ρ k (PMF.pure v)) ω =
      (if ω k = v then 1 else 0) * ∏ j ∈ Finset.univ.erase k, ρ j (ω j) := by
  rw [productPMF_apply, ← Finset.prod_erase_mul _ _ (Finset.mem_univ k)]
  have hh : (∏ j ∈ Finset.univ.erase k, Function.update ρ k (PMF.pure v) j (ω j)) =
      ∏ j ∈ Finset.univ.erase k, ρ j (ω j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [hh, Function.update_self]
  simp only [PMF.pure_apply, eq_comm]
  exact mul_comm _ _

theorem productPMF_split {K V : Type*} [Fintype K] [DecidableEq K]
    [Fintype V] [DecidableEq V] (ρ : K → PMF V) (k : K) :
    productPMF ρ = (ρ k).bind (fun v => productPMF (Function.update ρ k (PMF.pure v))) := by
  ext ω
  rw [PMF.bind_apply, tsum_fintype]
  simp only [productPMF_update_apply]
  rw [Finset.sum_eq_single (ω k)]
  · simp only [ite_true, one_mul]
    rw [productPMF_apply, ← Finset.prod_erase_mul _ _ (Finset.mem_univ k)]
    exact mul_comm _ _
  · intro v _ hv
    simp only [ite_eq_right (Ne.symm hv), zero_mul, mul_zero]
  · simp

theorem pmf_bind_congr_on_support {α β : Type*} (p : PMF α) (f g : α → PMF β)
    (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  ext b
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro a
  by_cases ha : p a = 0
  · simp only [ha, zero_mul]
  · rw [h a ha]

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_TreeBind
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

theorem bool_probability_sum (p : PMF Bool) : trueProbability p + falseProbability p = 1 := by
  have hh := p.tsum_coe
  rw [tsum_fintype, Fintype.sum_bool] at hh
  have hr := congrArg ENNReal.toReal hh
  simpa only [ENNReal.toReal_add (p.apply_ne_top _) (p.apply_ne_top _),
    ENNReal.toReal_one, trueProbability, falseProbability] using hr

theorem trueProbability_nonneg (p : PMF Bool) : 0 ≤ trueProbability p := ENNReal.toReal_nonneg

theorem falseProbability_nonneg (p : PMF Bool) : 0 ≤ falseProbability p := ENNReal.toReal_nonneg

theorem trueProbability_le_one (p : PMF Bool) : trueProbability p ≤ 1 := by
  have := bool_probability_sum p
  have := falseProbability_nonneg p
  linarith

theorem trueProbability_bind {V : Type*} [Fintype V] (p : PMF V) (f : V → PMF Bool) :
    trueProbability (p.bind f) = ∑ v, (p v).toReal * trueProbability (f v) := by
  unfold trueProbability
  rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul]
  · intro v _
    exact ENNReal.mul_ne_top (p.apply_ne_top v) ((f v).apply_ne_top true)

theorem trueProbability_bool_bind (p : PMF Bool) (f : Bool → PMF Bool) :
    trueProbability (p.bind f) = trueProbability p * trueProbability (f true) +
      falseProbability p * trueProbability (f false) := by
  rw [trueProbability_bind, Fintype.sum_bool]
  rfl

namespace ExposureTree
variable {K V : Type*}

theorem fresh_checkNone_true (ν : K → PMF V) (As : List (ExposureTree K V Bool)) :
    trueProbability (fresh ν (checkNone As)) = (As.map (fun A => falseProbability (fresh ν A))).prod := by
  induction As with
  | nil => simp [checkNone, fresh]
  | cons A As ih =>
    rw [checkNone, fresh_bind, trueProbability_bool_bind]
    simp [fresh, ih]

theorem exposeLabeled_product {A : Type*} [Fintype V] (ν : K → PMF V) (key : A → K) (ks : List A)
    (C : List (A × V) → ExposureTree K V Bool) (h : A → V → ℝ)
    (hc : ∀ xs, trueProbability (fresh ν (C xs)) = (xs.map (fun p => h p.1 p.2)).prod) :
    trueProbability (fresh ν (ExposureTree.bind (exposeLabeled key ks) C)) =
      (ks.map (fun k => ∑ v, (ν (key k) v).toReal * h k v)).prod := by

  suffices hh : ∀ (ks : List A) (a : ℝ) (C : List (A × V) → ExposureTree K V Bool),
      (∀ xs, trueProbability (fresh ν (C xs)) = a * (xs.map (fun p => h p.1 p.2)).prod) →
      trueProbability (fresh ν (ExposureTree.bind (exposeLabeled key ks) C)) =
        a * (ks.map (fun k => ∑ v, (ν (key k) v).toReal * h k v)).prod by
    simpa only [one_mul] using hh ks 1 C (by simpa only [one_mul] using hc)
  intro ks
  induction ks with
  | nil =>
    intro a C hh
    simpa only [exposeLabeled, bind, List.map_nil, List.prod_nil] using hh []
  | cons k ks ih =>
    intro a C hh
    simp only [exposeLabeled, bind, fresh, trueProbability_bind]
    have hx : ∀ v, trueProbability (fresh ν
        (bind (bind (exposeLabeled key ks) (fun xs => .done ((k, v) :: xs))) C)) =
        (a * h k v) * (ks.map (fun k => ∑ v, (ν (key k) v).toReal * h k v)).prod := by
      intro v
      have hassoc : bind (bind (exposeLabeled (V := V) key ks) (fun xs => .done ((k, v) :: xs))) C =
          bind (exposeLabeled key ks) (fun xs => C ((k, v) :: xs)) := by
        induction exposeLabeled (V := V) key ks with
        | done xs => rfl
        | ask k f hi => simp only [bind, hi]
      rw [hassoc]
      apply ih
      intro xs
      rw [hh]
      simp only [List.map_cons, List.prod_cons]
      ring
    simp only [hx, List.map_cons, List.prod_cons]
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring

end ExposureTree

section GridQuery
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem gridAnswerProbability_step (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (focus : Finset ι) (parent : Option τ) :
    gridAnswerProbability H N (d + 1) k focus parent =
      ∏ p ∈ gridCandidates H focus parent,
        ∑ u : Fin N, (1 / (N : ℝ)) *
          (if u.val < k then 1 - gridAnswerProbability H N d u.val
            ((H p.2).erase p.1) (some p.2) else 1) := by
  unfold gridAnswerProbability
  rw [gridQueryDepth]
  have hh := ExposureTree.exposeLabeled_product (gridPriorities (τ := τ) N) Prod.snd
    (gridCandidates H focus parent).toList
    (fun values => ExposureTree.checkNone
      (((values.mergeSort (fun a b => a.2.val ≤ b.2.val)).map
        (fun p => if p.2.val < k then
          gridQueryDepth H N d p.2.val ((H p.1.2).erase p.1.1) (some p.1.2)
          else .done false))))
    (fun p u => if u.val < k then 1 - gridAnswerProbability H N d u.val
      ((H p.2).erase p.1) (some p.2) else 1) (by
      intro values
      rw [ExposureTree.fresh_checkNone_true, List.map_map]
      have hp := (List.mergeSort_perm values (fun a b => a.2.val ≤ b.2.val)).map
        (fun p => falseProbability (ExposureTree.fresh (gridPriorities N)
          (if p.2.val < k then gridQueryDepth H N d p.2.val
            ((H p.1.2).erase p.1.1) (some p.1.2) else .done false)))
      refine hp.prod_eq.trans ?_
      congr 1
      apply List.map_congr_left
      intro p _
      by_cases hpk : p.2.val < k
      · simp only [hpk, ite_true]
        have hb := bool_probability_sum (ExposureTree.fresh (gridPriorities N)
          (gridQueryDepth H N d p.2.val ((H p.1.2).erase p.1.1) (some p.1.2)))
        change falseProbability _ = 1 - trueProbability _
        linarith
      · simp [hpk, ExposureTree.fresh])
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [gridPriorities, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, Fintype.card_fin, one_div]
  exact (Finset.prod_map_toList _ _).symm

theorem gridAnswerProbability_mem_unit (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (focus : Finset ι) (parent : Option τ) :
    gridAnswerProbability H N d k focus parent ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨trueProbability_nonneg _, trueProbability_le_one _⟩

theorem prod_gridCandidates {M : Type*} [CommMonoid M] (H : τ → Finset ι)
    (focus : Finset ι) (parent : Option τ) (f : ι × τ → M) :
    (∏ p ∈ gridCandidates H focus parent, f p) =
      ∏ e ∈ focus, ∏ T ∈ messageCandidates H e parent, f (e, T) := by
  simp only [gridCandidates, messageCandidates, Finset.prod_filter]
  exact Finset.prod_product _ _ _

theorem gridAnswerProbability_factor (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (focus : Finset ι) (parent : Option τ) :
    gridAnswerProbability H N d k focus parent =
      ∏ e ∈ focus, gridAnswerProbability H N d k {e} parent := by
  cases d with
  | zero => simp
  | succ d =>
    simp only [gridAnswerProbability_step, prod_gridCandidates, Finset.prod_singleton]

theorem uniform_grid_average (N : ℕ) [NeZero N] (k : ℕ) (f : Fin N → ℝ) :
    (∑ u : Fin N, (1 / (N : ℝ)) * (if u.val < k then 1 - f u else 1)) =
      1 - (1 / (N : ℝ)) * ∑ u ∈ Finset.univ.filter (fun u : Fin N => u.val < k), f u := by
  have hpoint : ∀ u : Fin N, (if u.val < k then 1 - f u else 1) =
      1 - (if u.val < k then f u else 0) := by
    intro u; split_ifs <;> ring
  simp only [hpoint, mul_sub, mul_one, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum,
    Finset.sum_filter, mul_ite, mul_zero]
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [mul_one_div_cancel hN]

theorem gridMessage_step (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (e : ι) (parent : Option τ) :
    gridMessage H N (d + 1) k e parent =
      ∏ T ∈ messageCandidates H e parent,
        (1 - (1 / (N : ℝ)) * ∑ u ∈ Finset.univ.filter (fun u : Fin N => u.val < k),
          ∏ f ∈ (H T).erase e, gridMessage H N d u.val f (some T)) := by
  simp only [gridMessage, gridAnswerProbability_step, prod_gridCandidates,
    Finset.prod_singleton, uniform_grid_average]
  apply Finset.prod_congr rfl
  intro T _
  congr 2
  apply Finset.sum_congr rfl
  intro u _
  exact gridAnswerProbability_factor H N d u.val ((H T).erase e) (some T)

theorem gridQueryDepth_threshold_zero (H : τ → Finset ι) (N d : ℕ)
    (focus : Finset ι) (parent : Option τ) :
    gridQueryDepth H N d 0 focus parent = gridQueryDepth H N 0 0 focus parent := by
  cases d with
  | zero => rfl
  | succ d => simp only [gridQueryDepth, Nat.not_lt_zero, ↓reduceIte,
      ExposureTree.checkNone_done_false]

theorem gridQueryDepth_stable (H : τ → Finset ι) (N k d d' : ℕ)
    (hd : k ≤ d) (hd' : k ≤ d') (focus : Finset ι) (parent : Option τ) :
    gridQueryDepth H N d k focus parent = gridQueryDepth H N d' k focus parent := by
  induction k using Nat.strong_induction_on generalizing d d' focus parent with
  | h k ih =>
    by_cases hk : k = 0
    · subst k
      exact (gridQueryDepth_threshold_zero H N d focus parent).trans
        (gridQueryDepth_threshold_zero H N d' focus parent).symm
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
      obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d' ≠ 0)
      simp only [gridQueryDepth]
      congr 1
      funext values
      congr 1
      apply List.map_congr_left
      intro x _
      split_ifs with hx
      · exact ih x.2.val hx d d' (by omega) (by omega) _ _
      · rfl

theorem gridMessage_stable (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (k d d' : ℕ) (hd : k ≤ d) (hd' : k ≤ d') (e : ι) (parent : Option τ) :
    gridMessage H N d k e parent = gridMessage H N d' k e parent := by
  unfold gridMessage gridAnswerProbability
  rw [gridQueryDepth_stable H N k d d' hd hd']

theorem gridMessage_exact (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (k : ℕ) (hk : k ≤ N) (e : ι) (parent : Option τ) :
    gridMessage H N N k e parent =
      ∏ T ∈ messageCandidates H e parent,
        (1 - (1 / (N : ℝ)) * ∑ u ∈ Finset.univ.filter (fun u : Fin N => u.val < k),
          ∏ f ∈ (H T).erase e, gridMessage H N N u.val f (some T)) := by
  rw [gridMessage_stable H N k N (N + 1) hk (by omega), gridMessage_step]

end GridQuery
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_FreshLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave.ExposureTree
open scoped BigOperators

variable {K V O P : Type*}

theorem repeats_false_iff [DecidableEq K] (seen : Finset K) (ks : List K) :
    repeats seen ks = false ↔ ks.Nodup ∧ ∀ k ∈ ks, k ∉ seen := by
  induction ks generalizing seen with
  | nil => simp [repeats]
  | cons k ks ih =>
    simp only [repeats_cons, Bool.or_eq_false_iff, decide_eq_false_iff_not,
      ih, List.nodup_cons, List.mem_cons, Finset.mem_insert, not_or]
    constructor
    · rintro ⟨hk, hnd, hh⟩
      refine ⟨⟨?_, hnd⟩, ?_⟩
      · intro hmem
        exact (hh k hmem).1 rfl
      · intro a ha
        rcases ha with rfl | ha
        · exact hk
        · exact (hh a ha).2
    · rintro ⟨⟨hkm,hnd⟩, hh⟩
      refine ⟨hh k (Or.inl rfl), hnd, ?_⟩
      intro a ha
      refine ⟨?_, hh a (Or.inr ha)⟩
      intro hak
      exact hkm (hak ▸ ha)

@[simp] theorem repeats_empty_false_iff [DecidableEq K] (ks : List K) :
    repeats ∅ ks = false ↔ ks.Nodup := by simp [repeats_false_iff]

end SharpTerminalLeave.ExposureTree

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_FreshLogExposeLabeled
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave.ExposureTree
variable {K V O R A : Type*}

theorem freshLog_checkNoneTrace_support (ν : K → PMF V) (keys : R → List K)
    (as : List (ExposureTree K V (Bool × List R)))
    (ha : ∀ A ∈ as, ∀ z ∈ (freshLog ν A).support, z.2 = z.1.2.flatMap keys)
    {z : (Bool × List R) × List K}
    (hz : z ∈ (freshLog ν (checkNoneTrace as)).support) :
    z.2 = z.1.2.flatMap keys := by
  induction as generalizing z with
  | nil =>
    have heq : z = ((true,[]),[]) := by simpa [checkNoneTrace,freshLog] using hz
    simp [heq]
  | cons A as ih =>
    rw [checkNoneTrace, freshLog_bind] at hz
    obtain ⟨x,hx,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    have hxlog := ha A (by simp) x hx
    have has (B) (hB : B ∈ as) := ha B (by simp [hB])
    cases hb : x.1.1
    · simp only [hb, Bool.false_eq_true, ↓reduceIte, freshLog_mapOutput] at hy
      obtain ⟨w,hw,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
      simp only [List.flatMap_append, hxlog, ih has hw]
    · simp only [hb, ↓reduceIte, freshLog, PMF.mem_support_pure_iff] at hy
      subst y
      simp [hxlog]

end SharpTerminalLeave.ExposureTree

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Probability_FiniteMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem pmf_weight_sum {α : Type*} [Fintype α] (p : PMF α) :
    ∑ a, (p a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => p.apply_ne_top a)]
  have h : ∑ a, p a = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  rw [h, ENNReal.toReal_one]

@[simp] theorem pmfMean_const {α : Type*} [Fintype α] (p : PMF α) (c : ℝ) :
    pmfMean p (fun _ => c) = c := by
  simp only [pmfMean, ← Finset.sum_mul, pmf_weight_sum, one_mul]

theorem pmfMean_congr {α : Type*} [Fintype α] (p : PMF α) {f g : α → ℝ}
    (h : ∀ a ∈ p.support, f a = g a) : pmfMean p f = pmfMean p g := by
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · have hz : p a = 0 := by simpa only [PMF.mem_support_iff, not_not] using ha
    simp [hz]

theorem pmfMean_add {α : Type*} [Fintype α] (p : PMF α) (f g : α → ℝ) :
    pmfMean p (fun a => f a + g a) = pmfMean p f + pmfMean p g := by
  simp only [pmfMean, mul_add, Finset.sum_add_distrib]

theorem pmfMean_sub {α : Type*} [Fintype α] (p : PMF α) (f g : α → ℝ) :
    pmfMean p (fun a => f a - g a) = pmfMean p f - pmfMean p g := by
  simp only [pmfMean, mul_sub, Finset.sum_sub_distrib]

theorem pmfMean_mul_const {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) (c : ℝ) :
    pmfMean p (fun a => f a * c) = pmfMean p f * c := by
  simp only [pmfMean, ← mul_assoc, ← Finset.sum_mul]

theorem pmfMean_nonneg {α : Type*} [Fintype α] (p : PMF α) {f : α → ℝ}
    (h : ∀ a ∈ p.support, 0 ≤ f a) : 0 ≤ pmfMean p f := by
  apply Finset.sum_nonneg
  intro a _
  by_cases ha : a ∈ p.support
  · exact mul_nonneg ENNReal.toReal_nonneg (h a ha)
  · have hz : p a = 0 := by simpa only [PMF.mem_support_iff, not_not] using ha
    simp [hz]

theorem pmfMean_mono {α : Type*} [Fintype α] (p : PMF α) {f g : α → ℝ}
    (h : ∀ a ∈ p.support, f a ≤ g a) : pmfMean p f ≤ pmfMean p g := by
  have hh := pmfMean_nonneg p (fun a ha => sub_nonneg.mpr (h a ha))
  rwa [pmfMean_sub, sub_nonneg] at hh

theorem pmfMean_bind {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (q : α → PMF β) (f : β → ℝ) :
    pmfMean (p.bind q) f = pmfMean p (fun a => pmfMean (q a) f) := by
  classical
  simp only [pmfMean, PMF.bind_apply, tsum_fintype]
  have hfin (b : β) (a : α) : p a * q a b ≠ ⊤ :=
    ENNReal.mul_ne_top (p.apply_ne_top a) ((q a).apply_ne_top b)
  simp_rw [ENNReal.toReal_sum (fun a _ => hfin _ a), Finset.sum_mul,
    ENNReal.toReal_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

@[simp] theorem pmfMean_map {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (g : α → β) (f : β → ℝ) :
    pmfMean (p.map g) f = pmfMean p (fun a => f (g a)) := by
  rw [← PMF.bind_pure_comp, pmfMean_bind]
  simp

theorem pmfMean_uniformOfFinset {α : Type*} [Fintype α]
    (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    pmfMean (PMF.uniformOfFinset s hs) f = (∑ a ∈ s, f a) / (s.card : ℝ) := by
  classical
  simp only [pmfMean, PMF.uniformOfFinset_apply]
  simp_rw [apply_ite ENNReal.toReal, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_zero, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_univ_mem]
  simp only [div_eq_mul_inv, mul_comm, Finset.sum_mul]

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_TriangleDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem pmfMean_sum {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (f : β → α → ℝ) :
    pmfMean p (fun a => ∑ b, f b a) = ∑ b, pmfMean p (f b) := by
  simp only [pmfMean, Finset.mul_sum]
  exact Finset.sum_comm

theorem three_le_card_union {α : Type*} [DecidableEq α]
    {e f : Finset α} (he : e.card = 2) (hf : f.card = 2) (hef : e ≠ f) :
    3 ≤ (e ∪ f).card := by
  have hi : (e ∩ f).card < 2 := by
    by_contra h
    have hge : 2 ≤ (e ∩ f).card := by omega
    have heq : e ∩ f = e := Finset.eq_of_subset_of_card_le
      Finset.inter_subset_left (by omega)
    have hfq : e ∩ f = f := Finset.eq_of_subset_of_card_le
      Finset.inter_subset_right (by omega)
    exact hef (heq.symm.trans hfq)
  have h := Finset.card_union_add_card_inter e f
  omega

theorem triangle_eq_of_two_edges {α : Type*} [DecidableEq α]
    {t u e f : Finset α} (ht : t.card = 3) (hu : u.card = 3)
    (he : e.card = 2) (hf : f.card = 2) (hef : e ≠ f)
    (het : e ⊆ t) (hft : f ⊆ t) (heu : e ⊆ u) (hfu : f ⊆ u) : t = u := by
  have hm := three_le_card_union he hf hef
  have ht' : e ∪ f = t := Finset.eq_of_subset_of_card_le
    (Finset.union_subset het hft) (by omega)
  have hu' : e ∪ f = u := Finset.eq_of_subset_of_card_le
    (Finset.union_subset heu hfu) (by omega)
  exact ht'.symm.trans hu'

end SharpTerminalLeave
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixEpsilon
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem prefixDensity_bounds (n : ℕ) (hn : 0 < n)
    (ht : 0 ≤ prefixTargetTime n) :
    prefixTargetDensity n ≤ prefixDensity n ∧
      prefixDensity n < prefixTargetDensity n + 6 / (n : ℝ)^2 := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn2 : 0 < (n : ℝ)^2 := sq_pos_of_pos hnR
  have hf : (prefixTime n : ℝ) ≤ prefixTargetTime n := Nat.floor_le ht
  have hg : prefixTargetTime n < (prefixTime n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hx : prefixTargetTime n * 6 =
      (n : ℝ)^2 * (1 - 1 / (n : ℝ) - prefixTargetDensity n) := by
    unfold prefixTargetTime
    ring
  have hp : prefixDensity n * (n : ℝ)^2 =
      (1 - 1 / (n : ℝ)) * (n : ℝ)^2 - 6 * prefixTime n := by
    unfold prefixDensity
    field_simp
  constructor
  · apply (le_of_mul_le_mul_right (a := (n : ℝ)^2) _ hn2)
    nlinarith
  · apply (lt_of_mul_lt_mul_right (a := (n : ℝ)^2) _ (le_of_lt hn2))
    have he : (6 / (n : ℝ)^2) * (n : ℝ)^2 = 6 := div_mul_cancel₀ _ (ne_of_gt hn2)
    nlinarith

end SharpTerminalLeave

open InnerProductSpace
open scoped InnerProductSpace

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Asymptotics_OneAddLogRpow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

open Asymptotics

lemma one_add_log_rpow_isLittleO (C : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (fun x : ℝ => (1 + Real.log x) ^ C) =o[atTop] fun x => x ^ δ := by
  let C' := max C 1
  have hC' : 0 < C' := lt_max_iff.mpr (Or.inr zero_lt_one)
  have hq : 0 < δ / C' := div_pos hδ hC'
  have hc : (fun _ : ℝ => (1 : ℝ)) =o[atTop] fun x => x ^ (δ / C') := by
    apply (isLittleO_const_left_of_ne one_ne_zero).mpr
    apply (tendsto_rpow_atTop hq).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact (Real.norm_of_nonneg (Real.rpow_nonneg hx _)).symm
  have hs := hc.add (isLittleO_log_rpow_atTop hq)
  calc
    (fun x : ℝ => (1 + Real.log x) ^ C) =O[atTop]
        fun x => (1 + Real.log x) ^ C' := by
      apply IsBigO.of_norm_eventuallyLE
      filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 0] with x hx
      simp only [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ 1 + Real.log x) C)]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
    _ =o[atTop] fun x => (x ^ (δ / C')) ^ C' :=
      hs.rpow hC' ((eventually_ge_atTop (0 : ℝ)).mono fun x hx => Real.rpow_nonneg hx _)
    _ =ᶠ[atTop] fun x => x ^ δ := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      rw [← Real.rpow_mul hx,div_mul_cancel₀ _ hC'.ne']

 theorem prefixTemplateFactor_subpower (C : ℝ) {δ b : ℝ} (hδ : 0 < δ) (hb : 0 < b) :
    ∀ᶠ n : ℕ in atTop, prefixTemplateFactor n C ≤ b * (n : ℝ) ^ δ := by
  have h := ((one_add_log_rpow_isLittleO C hδ).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).bound hb
  filter_upwards [h,eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hl : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hb0 : 0 ≤ 1 + Real.log (n : ℝ) := by linarith
  simpa only [Function.comp_apply,Real.norm_of_nonneg (Real.rpow_nonneg hb0 C),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) δ),prefixTemplateFactor] using hn

lemma prefixTargetDensity_eq (n : ℕ) :
    prefixTargetDensity n = (n : ℝ) ^ (-(999 / 2000 : ℝ)) := by
  unfold prefixTargetDensity prefixEpsilon
  congr 1
  norm_num

lemma prefixTargetDensity_tendsto : Tendsto prefixTargetDensity atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => prefixTargetDensity n) atTop (𝓝 0)
  simp_rw [prefixTargetDensity_eq]
  exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 999 / 2000)).comp
    tendsto_natCast_atTop_atTop

lemma prefixTargetTime_eventually_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ prefixTargetTime n := by
  have hi : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div,Function.comp_def] using (tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))
  filter_upwards [prefixTargetDensity_tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1/2),
    hi.eventually_le_const (by norm_num : (0 : ℝ) < 1/2)] with n hp hi
  unfold prefixTargetTime
  exact mul_nonneg (by positivity) (by linarith)

theorem prefixDensity_eventual_envelope : ∀ᶠ n : ℕ in atTop,
    (n : ℝ) ^ (-(999 / 2000 : ℝ)) ≤ prefixDensity n ∧
      prefixDensity n ≤ 2 * (n : ℝ) ^ (-(999 / 2000 : ℝ)) := by
  filter_upwards [prefixTargetTime_eventually_nonneg,eventually_ge_atTop (6 : ℕ)] with n ht hn
  have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨hl,hu⟩ := prefixDensity_bounds n (by omega) ht
  rw [prefixTargetDensity_eq] at hl hu
  refine ⟨hl,?_⟩
  have h1 : 6 / (n : ℝ)^2 ≤ 1 / (n : ℝ) := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ)^2) hn0).mpr
    nlinarith
  have h2 : 1 / (n : ℝ) ≤ (n : ℝ) ^ (-(999 / 2000 : ℝ)) := by
    rw [one_div,← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  linarith

lemma prefix_target_D_identity (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * ((n : ℝ) ^ (-(999 / 2000 : ℝ))) ^ 2 =
      (n : ℝ) ^ (1 / 1000 : ℝ) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [← Real.rpow_natCast,← Real.rpow_mul hnR.le]
  conv_lhs => lhs; rw [← Real.rpow_one (n : ℝ)]
  rw [← Real.rpow_add hnR]
  congr 1
  norm_num

theorem prefixD_eventual_envelope : ∀ᶠ n : ℕ in atTop,
    (n : ℝ) ^ (1 / 1000 : ℝ) ≤ prefixD n ∧
      prefixD n ≤ 4 * (n : ℝ) ^ (1 / 1000 : ℝ) := by
  filter_upwards [prefixDensity_eventual_envelope,eventually_ge_atTop (1 : ℕ)] with n hp hn
  have hn0 : 0 < n := by omega
  have hq : 0 ≤ (n : ℝ) ^ (-(999 / 2000 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hpl : 0 ≤ prefixDensity n := hq.trans hp.1
  rw [← prefix_target_D_identity n hn0]
  unfold prefixD
  constructor
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq hp.1 2) (Nat.cast_nonneg n)
  · have hsq := pow_le_pow_left₀ hpl hp.2 2
    nlinarith [mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hsq)]

lemma prefixDensity_le_one (n : ℕ) : prefixDensity n ≤ 1 := by
  have h₁ : 0 ≤ 1 / (n : ℝ) := by positivity
  have h₂ : 0 ≤ 6 * (prefixTime n : ℝ) / (n : ℝ)^2 := by positivity
  unfold prefixDensity
  linarith

lemma prefix_scales_eventually_pos : ∀ᶠ n : ℕ in atTop,
    0 < prefixDensity n ∧ 1 ≤ prefixD n := by
  filter_upwards [prefixDensity_eventual_envelope,prefixD_eventual_envelope,
    eventually_ge_atTop (1 : ℕ)] with n hp hD hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact ⟨(Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < n) _).trans_le hp.1,
    (Real.one_le_rpow hnR (by norm_num : (0 : ℝ) ≤ 1/1000)).trans hD.1⟩

lemma prefix_mixed_power_envelope (k : ℕ) : ∀ᶠ n : ℕ in atTop,
    prefixDensity n * prefixD n ^ k ≤
      (2 * 4 ^ k) * (n : ℝ) ^ (-(999 / 2000 : ℝ) + (k : ℝ) / 1000) := by
  filter_upwards [prefixDensity_eventual_envelope,prefixD_eventual_envelope,
    prefix_scales_eventually_pos,eventually_ge_atTop (1 : ℕ)] with n hp hD hpos hn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hD0 : 0 ≤ prefixD n := by linarith [hpos.2]
  calc
    _ ≤ (2 * (n : ℝ) ^ (-(999 / 2000 : ℝ))) *
        (4 * (n : ℝ) ^ (1/1000 : ℝ)) ^ k :=
      mul_le_mul hp.2 (pow_le_pow_left₀ hD0 hD.2 k) (pow_nonneg hD0 k) (by positivity)
    _ = _ := by
      rw [mul_pow,← Real.rpow_natCast ((n : ℝ) ^ (1/1000 : ℝ)) k,← Real.rpow_mul hnR.le]
      have he : (1/1000 : ℝ) * k = (k : ℝ) / 1000 := by ring
      rw [he,Real.rpow_add hnR]
      ring

theorem prefixTemplateFactor_mixed_gain (C : ℝ) (k : ℕ)
    (hk : (k : ℝ) / 1000 < 999 / 2000) :
    ∀ᶠ n : ℕ in atTop, prefixTemplateFactor n C *
      (prefixDensity n * prefixD n ^ k) ≤ 1 := by
  let δ : ℝ := 999/2000 - (k : ℝ)/1000
  have hδ : 0 < δ := sub_pos.mpr hk
  have hK : (0 : ℝ) < 2 * 4 ^ k := by positivity
  filter_upwards [prefixTemplateFactor_subpower C hδ (inv_pos.mpr hK),
    prefix_mixed_power_envelope k,prefix_scales_eventually_pos,
    eventually_ge_atTop (1 : ℕ)] with n hκ hmix hpos hn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hb : 0 ≤ prefixDensity n * prefixD n ^ k :=
    mul_nonneg hpos.1.le (pow_nonneg (by linarith [hpos.2]) k)
  calc
    _ ≤ ((2 * 4 ^ k)⁻¹ * (n : ℝ) ^ δ) *
        ((2 * 4 ^ k) * (n : ℝ) ^ (-(999/2000 : ℝ) + (k : ℝ)/1000)) :=
      mul_le_mul hκ hmix hb (by positivity)
    _ = 1 := by
      rw [mul_mul_mul_comm,inv_mul_cancel₀ hK.ne',one_mul,← Real.rpow_add hnR]
      have he : δ + (-(999/2000 : ℝ) + (k : ℝ)/1000) = 0 := by dsimp [δ]; ring
      rw [he,Real.rpow_zero]

theorem prefix_short_suppression (C : ℝ) : ∀ᶠ n : ℕ in atTop,
    prefixTemplateFactor n C * prefixDensity n ≤ (prefixD n ^ 50)⁻¹ := by
  filter_upwards [prefixTemplateFactor_mixed_gain C 50 (by norm_num),
    prefix_scales_eventually_pos] with n hm hp
  have hD : 0 < prefixD n ^ 50 := pow_pos (by linarith [hp.2]) _
  rw [← one_div,(le_div_iff₀ hD)]
  simpa only [mul_assoc] using hm

theorem prefix_suffix_scaling : ∀ᶠ n : ℕ in atTop,
    (n : ℝ)^100 * prefixDensity n ^ 201 ≤ 1 := by
  filter_upwards [prefixTemplateFactor_mixed_gain 0 100 (by norm_num)] with n hn
  simpa only [prefixTemplateFactor,Real.rpow_zero,one_mul,prefixD,mul_pow,
    ← pow_mul,show 201 = 1 + 2 * 100 from rfl,pow_add,pow_one,mul_left_comm] using hn

lemma prefixTemplateFactor_le_D_power (C : ℝ) (k : ℕ) (hk : 0 < k) :
    ∀ᶠ n : ℕ in atTop, prefixTemplateFactor n C ≤ prefixD n ^ k := by
  have he : 0 < (k : ℝ) / 1000 := div_pos (Nat.cast_pos.mpr hk) (by norm_num)
  filter_upwards [prefixTemplateFactor_subpower C he zero_lt_one,
    prefixD_eventual_envelope,eventually_ge_atTop (1 : ℕ)] with n hκ hD hn
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hm : ((n : ℝ) ^ (1/1000 : ℝ))^k ≤ prefixD n ^ k :=
    pow_le_pow_left₀ (Real.rpow_nonneg hn0 _) hD.1 _
  have hid : ((n : ℝ) ^ (1/1000 : ℝ))^k = (n : ℝ) ^ ((k : ℝ)/1000) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hn0]
    congr 1
    ring
  rw [hid] at hm
  apply le_trans _ hm
  simpa only [one_mul] using hκ

theorem prefix_long_suppression (C : ℝ) : ∀ᶠ n : ℕ in atTop,
    prefixTemplateFactor n C ≤ (2 * prefixD n)^100 / prefixD n^50 := by
  filter_upwards [prefixTemplateFactor_le_D_power C 50 (by norm_num),
    prefix_scales_eventually_pos] with n hκ hp
  have hD : 0 < prefixD n := by linarith [hp.2]
  apply (le_div_iff₀ (pow_pos hD 50)).mpr
  calc
    _ ≤ prefixD n^50 * prefixD n^50 := mul_le_mul_of_nonneg_right hκ (by positivity)
    _ = prefixD n^100 := by rw [← pow_add]
    _ ≤ (2 * prefixD n)^100 :=
      pow_le_pow_left₀ hD.le (by linarith) _

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Stability_GridCavityError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave
open Filter
open scoped BigOperators Topology

section GridApproximation
variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

omit [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ] in
theorem sum_fin_filter_lt_eq_range (N k : ℕ) (hk : k ≤ N) (f : ℕ → ℝ) :
    (∑ u ∈ Finset.univ.filter (fun u : Fin N => u.val < k), f u.val) =
      ∑ j ∈ Finset.range k, f j := by
  rw [Finset.sum_filter]
  calc
    _ = ∑ j ∈ Finset.range N, if j < k then f j else 0 :=
      Fin.sum_univ_eq_sum_range (fun j => if j < k then f j else 0) N
    _ =
        ∑ j ∈ Finset.range k, if j < k then f j else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hk)
      intro j _ hj
      simp only [Finset.mem_range] at hj
      simp only [hj, ↓reduceIte]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_range.mp hj, ↓reduceIte]

omit [Fintype ι] in

theorem gridMessage_exact_range (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (k : ℕ) (hk : k ≤ N) (e : ι) (parent : Option τ) :
    gridMessage H N N k e parent =
      ∏ T ∈ messageCandidates H e parent,
        (1 - (1 / (N : ℝ)) * ∑ j ∈ Finset.range k,
          ∏ f ∈ (H T).erase e, gridMessage H N N j f (some T)) := by
  rw [gridMessage_exact H N k hk]
  apply Finset.prod_congr rfl
  intro T _
  congr 2
  exact sum_fin_filter_lt_eq_range N k hk
    (fun j => ∏ f ∈ (H T).erase e, gridMessage H N N j f (some T))

end GridApproximation
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Coupling_GridUniformError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave
section GridRowBounds
variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

omit [Fintype ι] in
lemma gridCandidateFailure_product (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (k : ℕ) (hk : k ≤ N) (focus : Finset ι) (p : Option τ) :
    (∏ a : gridCandidates H focus p, gridCandidateFailure H N k a.val.1 a.val.2) =
      gridAnswerProbability H N N k focus p := by
  change (∏ a : gridCandidates H focus p,
    (fun a : ι × τ => gridCandidateFailure H N k a.1 a.2) a.val) = _
  rw [Finset.prod_coe_sort (gridCandidates H focus p)
    (fun a : ι × τ => gridCandidateFailure H N k a.1 a.2),
    prod_gridCandidates,gridAnswerProbability_factor]
  apply Finset.prod_congr rfl
  intro e _
  exact (gridMessage_exact_range H N k hk e p).symm

end GridRowBounds
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Embeddings_BirthGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

namespace BirthGraph
variable {N : ℕ} (B : BirthGraph N)

theorem graph_adj_of_lt {u v : Fin N} (huv : u < v) :
    B.graph.Adj u v ↔ u ∈ B.older v := by
  constructor
  · intro h
    rcases h with h | h
    · exact h
    · exact False.elim ((not_lt_of_gt huv) (B.older_lt u v h))
  · exact Or.inl

section Labels
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) (label : Fin N → V)

theorem no_repeated_exposure (hinj : Function.Injective label)
    (hno : ∀ a b, ¬ B.ExtraEdge G label a b)
    {v w : Fin N} (hvw : v ≠ w) {T : Finset V}
    (hv : B.ExposedAt G label v T) (hw : B.ExposedAt G label w T) : False := by
  wlog hlt : w < v generalizing v w
  · exact this (Ne.symm hvw) hw hv (lt_of_le_of_ne (le_of_not_gt hlt) hvw)
  obtain ⟨k, hk, hkT, hwT⟩ := hw.2.1
  have hkw := B.older_lt w k hk
  have hvT := hv.2.1.choose_spec.2.2
  have hkv : k < v := hkw.trans hlt
  have hlabels : ({label k, label w, label v} : Finset V).card = 3 := by
    simp [hinj.ne (ne_of_lt hkw), hinj.ne (ne_of_lt hkv), hinj.ne (ne_of_lt hlt)]
  have hT : T = {label k, label w, label v} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hkT, hwT, hvT⟩
    · rw [hlabels, hv.1.1]
  have hcv (u : Fin N) (hu : u < v) (huT : label u ∈ T) : u ∈ B.older v := by
    have hG : G.Adj (label u) (label v) := hv.1.2 _ huT _ hvT (hinj.ne (ne_of_lt hu))
    have hh : B.graph.Adj u v := by
      by_contra hn
      exact hno u v ⟨ne_of_lt hu, hn, hG⟩
    exact (B.graph_adj_of_lt hu).mp hh
  have hold := B.older_eq_pair (ne_of_lt hkw) (hcv k hkv hkT) (hcv w hlt hwT)
  have hcard : (B.older v).card = 2 := by rw [hold, Finset.card_pair (ne_of_lt hkw)]
  apply hv.2.2 hcard
  rw [parentType, parentVertices, hold, hT]
  ext x
  simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
  aesop

theorem older_sorted_pair {v : Fin N} (hv : (B.older v).card = 2) :
    ∃ x y : Fin N, x < y ∧ B.older v = {x, y} := by
  obtain ⟨x, y, hxy, hset⟩ := Finset.card_eq_two.mp hv
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · exact ⟨x, y, hlt, hset⟩
  · exact ⟨y, x, hgt, hset.trans (Finset.pair_comm x y)⟩

theorem first_label_repeat_extra (hrules : B.SpawnRules G label)
    {v w : Fin N} (hv : (B.older v).card = 2) (hw : w < v)
    (hvw : label v = label w) :
    ∃ a b : Fin N, a < v ∧ b < v ∧ B.ExtraEdge G label a b := by
  by_contra hextra
  have hno (a b : Fin N) (ha : a < v) (hb : b < v)
      (hne : a ≠ b) (hedge : G.Adj (label a) (label b)) : B.graph.Adj a b := by
    by_contra hn
    exact hextra ⟨a, b, ha, hb, hne, hn, hedge⟩
  obtain ⟨x, y, hxy, hset⟩ := B.older_sorted_pair hv
  have hx : x ∈ B.older v := by rw [hset]; simp
  have hy : y ∈ B.older v := by rw [hset]; simp
  have hxv := B.older_lt v x hx
  have hyv := B.older_lt v y hy
  have hxwG : G.Adj (label x) (label w) := by
    rw [← hvw]
    exact hrules.edge_labels x v (Or.inl hx)
  have hywG : G.Adj (label y) (label w) := by
    rw [← hvw]
    exact hrules.edge_labels y v (Or.inl hy)
  have hxw : x ≠ w := fun hh => hxwG.ne (congrArg label hh)
  have hyw : y ≠ w := fun hh => hywG.ne (congrArg label hh)
  have hxwB := hno x w hxv hw hxw hxwG
  have hywB := hno y w hyv hw hyw hywG
  have hxyB := hrules.attachment v hv x hx y hy (ne_of_lt hxy)
  rcases lt_or_gt_of_ne (Ne.symm hyw) with hwy | hyw'
  · have hold := B.older_eq_pair hxw ((B.graph_adj_of_lt hxy).mp hxyB)
      ((B.graph_adj_of_lt hwy).mp hywB.symm)
    have hcard : (B.older y).card = 2 := by rw [hold, Finset.card_pair hxw]
    have hmax : ∀ a ∈ B.older v, a ≤ y := by
      intro a ha
      rw [hset] at ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact le_of_lt hxy
      · exact le_rfl
    apply hrules.omit_parent v y hy hmax hcard
    simp only [parentType, parentVertices, hset, hold, Finset.image_insert,
      Finset.image_singleton, hvw]
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · have hold := B.older_eq_pair (ne_of_lt hxy)
      ((B.graph_adj_of_lt (hxy.trans hyw')).mp hxwB)
      ((B.graph_adj_of_lt hyw').mp hywB)
    have heq := hrules.distinct_siblings v w hv (hset.trans hold.symm) hvw
    exact (ne_of_lt hw) heq.symm

theorem exists_first_repeat (h : ¬ Function.Injective label) :
    ∃ v w : Fin N, w < v ∧ label v = label w ∧ Set.InjOn label (Set.Iio v) := by
  classical
  let bad : Finset (Fin N) := Finset.univ.filter (fun v => ∃ w < v, label v = label w)
  have hbad (v : Fin N) : v ∈ bad ↔ ∃ w < v, label v = label w := by
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
  have hne : bad.Nonempty := by
    obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp h
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨b, (hbad b).mpr ⟨a, hlt, hab.symm⟩⟩
    · exact ⟨a, (hbad a).mpr ⟨b, hgt, hab⟩⟩
  let v := bad.min' hne
  obtain ⟨w, hw, hvw⟩ := (hbad v).mp (Finset.min'_mem bad hne)
  refine ⟨v, w, hw, hvw, ?_⟩
  intro a ha b hb hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hm := Finset.min'_le bad b ((hbad b).mpr ⟨a, hlt, hab.symm⟩)
    exact (not_le_of_gt hb) hm
  · have hm := Finset.min'_le bad a ((hbad a).mpr ⟨b, hgt, hab⟩)
    exact (not_le_of_gt ha) hm

end Labels
end BirthGraph
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_ReindexSet
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma reindexSet_inj {N : ℕ} {s e f : Finset (Fin N)} (he : e ⊆ s) (hf : f ⊆ s)
    (h : reindexSet s e = reindexSet s f) : e = f := by
  rw [← image_reindexSet he,← image_reindexSet hf,h]

lemma reindexTemplate_edges_card {N : ℕ} (s : Finset (Fin N)) (E : Graph N)
    (I : Finset (Fin N)) (hE : ∀ e ∈ E, e ⊆ s) (hsimple : ∀ e ∈ E, e.card = 2)
    (hind : ∀ e ∈ E, ¬ e ⊆ I) :
    (reindexTemplate s E I hE hsimple hind).edges.card = E.card := by
  exact Finset.card_image_of_injOn (fun e he f hf h => reindexSet_inj (hE e he) (hE f hf) h)

lemma reindexTemplate_roots_card {N : ℕ} (s : Finset (Fin N)) (E : Graph N)
    (I : Finset (Fin N)) (hE : ∀ e ∈ E, e ⊆ s) (hsimple : ∀ e ∈ E, e.card = 2)
    (hind : ∀ e ∈ E, ¬ e ⊆ I) (hI : I ⊆ s) :
    (reindexTemplate s E I hE hsimple hind).roots.card = I.card := reindexSet_card hI

lemma reindexTemplate_induced_card {N : ℕ} (s : Finset (Fin N)) (E : Graph N)
    (I : Finset (Fin N)) (hE : ∀ e ∈ E, e ⊆ s) (hsimple : ∀ e ∈ E, e.card = 2)
    (hind : ∀ e ∈ E, ¬ e ⊆ I) (U : Finset (Fin N)) :
    (((reindexTemplate s E I hE hsimple hind).edges).filter
      (fun e => e ⊆ reindexSet s U)).card = (E.filter (fun e => e ⊆ U)).card := by
  have heq : ((E.image (reindexSet s)).filter (fun e => e ⊆ reindexSet s U)) =
      (E.filter (fun e => e ⊆ U)).image (reindexSet s) := by
    ext e
    simp only [Finset.mem_filter,Finset.mem_image]
    constructor
    · rintro ⟨⟨f,hf,rfl⟩,hs⟩
      exact ⟨f,⟨hf,(reindexSet_subset_iff (hE f hf)).mp hs⟩,rfl⟩
    · rintro ⟨f,⟨hf,hs⟩,rfl⟩
      exact ⟨⟨f,hf,rfl⟩,(reindexSet_subset_iff (hE f hf)).mpr hs⟩
  change ((E.image (reindexSet s)).filter _).card = _
  rw [heq]
  exact Finset.card_image_of_injOn (fun e he f hf h =>
    reindexSet_inj (hE e (Finset.mem_filter.mp he).1) (hE f (Finset.mem_filter.mp hf).1) h)

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Embeddings_ReindexEmbedding
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

lemma reindexEdges_map {N n : ℕ} {s e : Finset (Fin N)} (he : e ⊆ s)
    (φ : Fin N ↪ Fin n) :
    (reindexSet s e).map (reindexEmbedding s φ) = e.map φ := by
  ext x
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨i,hi,rfl⟩
    exact ⟨s.orderEmbOfFin rfl i,(mem_reindexSet s e i).mp hi,rfl⟩
  · rintro ⟨v,hv,rfl⟩
    rw [← image_reindexSet he] at hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    exact ⟨i,hi,rfl⟩

theorem graphEmbedding_fiber_le_rootedCount {N n : ℕ}
    (s I P : Finset (Fin N)) (E F : Graph N) (G : Graph n)
    (hE : ∀ e ∈ E, e ⊆ s) (hsimple : ∀ e ∈ E, e.card = 2)
    (hind : ∀ e ∈ E, ¬ e ⊆ I) (hIP : I ⊆ P)
    (hcover : P ∪ s = Finset.univ) (hEF : E ⊆ F)
    (ξ : {x // x ∈ P} ↪ Fin n) :
    (((Finset.univ.filter (fun φ : Fin N ↪ Fin n =>
      (∀ x : {x // x ∈ P}, φ x = ξ x) ∧ F.image (fun e => e.map φ) ⊆ G)).card : ℕ) : ℝ) ≤
      rootedCount (reindexTemplate s E I hE hsimple hind)
        (boundaryInjection s I P hIP ξ) G := by
  classical
  let T := reindexTemplate s E I hE hsimple hind
  let ψ := boundaryInjection s I P hIP ξ
  let A := Finset.univ.filter (fun φ : Fin N ↪ Fin n =>
    (∀ x : {x // x ∈ P}, φ x = ξ x) ∧ F.image (fun e => e.map φ) ⊆ G)
  let B := Finset.univ.filter (fun φ : RootedInjection T ψ => imageEdges T φ.val ⊆ G)
  have hf (φ : Fin N ↪ Fin n) (hφ : φ ∈ A) :
      ∀ i : {i // i ∈ T.roots}, reindexEmbedding s φ i = ψ i := by
    intro i
    exact (Finset.mem_filter.mp hφ).2.1
      ⟨s.orderEmbOfFin rfl i,hIP ((mem_reindexSet s I i).mp i.property)⟩
  let f (φ : {φ // φ ∈ A}) : RootedInjection T ψ :=
    ⟨reindexEmbedding s φ.val,hf φ.val φ.property⟩
  have hfmem (φ : {φ // φ ∈ A}) : f φ ∈ B := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro e he
    obtain ⟨es,hes,rfl⟩ := Finset.mem_image.mp he
    change es ∈ E.image (reindexSet s) at hes
    obtain ⟨ef,hef,rfl⟩ := Finset.mem_image.mp hes
    change (reindexSet s ef).map (reindexEmbedding s φ.val) ∈ G
    rw [reindexEdges_map (hE ef hef)]
    exact (Finset.mem_filter.mp φ.property).2.2
      (Finset.mem_image.mpr ⟨ef,hEF hef,rfl⟩)
  have hfinj : Function.Injective f := by
    intro φ χ heq
    apply Subtype.ext
    apply Function.Embedding.ext
    intro x
    have hx : x ∈ P ∪ s := by rw [hcover]; exact Finset.mem_univ _
    rcases Finset.mem_union.mp hx with hxP | hxs
    · exact ((Finset.mem_filter.mp φ.property).2.1 ⟨x,hxP⟩).trans
        ((Finset.mem_filter.mp χ.property).2.1 ⟨x,hxP⟩).symm
    · obtain ⟨i,hi⟩ := (s.orderIsoOfFin rfl).surjective ⟨x,hxs⟩
      have hix : s.orderEmbOfFin rfl i = x := congrArg Subtype.val hi
      have hh := congrArg (fun y : RootedInjection T ψ => y.val i) heq
      change φ.val (s.orderEmbOfFin rfl i) = χ.val (s.orderEmbOfFin rfl i) at hh
      rwa [hix] at hh
  have hcard : A.card ≤ B.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective
      (fun φ : {φ // φ ∈ A} => (⟨f φ,hfmem φ⟩ : {χ // χ ∈ B}))
      (fun φ χ h => hfinj (congrArg Subtype.val h))
  have hcount : rootedCount T ψ G = (B.card : ℝ) := by
    simp [rootedCount,copyCount,intact,B]
  change (A.card : ℝ) ≤ rootedCount T ψ G
  rw [hcount]
  exact_mod_cast hcard

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_RealCardFiberBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

section FiberCount
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

omit [DecidableEq α] in
lemma real_card_le_fiber_bound (s : Finset α) (t : Finset β) (f : α → β)
    (hf : ∀ a ∈ s, f a ∈ t) (b : ℝ)
    (hb : ∀ y ∈ t, ((s.filter (fun a => f a = y)).card : ℝ) ≤ b) :
    (s.card : ℝ) ≤ b * t.card := by
  have he : s.card = ∑ y ∈ t, (s.filter (fun a => f a = y)).card :=
    Finset.card_eq_sum_card_fiberwise hf
  rw [he,Nat.cast_sum]
  calc
    _ ≤ ∑ _y ∈ t, b := Finset.sum_le_sum hb
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

end FiberCount
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Embeddings_RestrictLabel
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

theorem graphEmbeddingSet_count_glue {N n : ℕ}
    (s I P : Finset (Fin N)) (E F : Graph N) (G : Graph n)
    (hE : ∀ e ∈ E, e ⊆ s) (hsimple : ∀ e ∈ E, e.card = 2)
    (hind : ∀ e ∈ E, ¬ e ⊆ I) (hIP : I ⊆ P)
    (hcover : P ∪ s = Finset.univ) (hEF : E ⊆ F)
    (A : Finset ({x // x ∈ P} ↪ Fin n))
    (hA : ∀ φ ∈ graphEmbeddingSet F G, restrictLabel P φ ∈ A)
    (κ : ℝ) (hκ : ∀ ξ ∈ A, rootedCount (reindexTemplate s E I hE hsimple hind)
      (boundaryInjection s I P hIP ξ) G ≤ κ) :
    ((graphEmbeddingSet F G).card : ℝ) ≤ κ * A.card := by
  classical
  apply real_card_le_fiber_bound _ A (restrictLabel P) hA κ
  intro ξ hξ
  have heq : (graphEmbeddingSet F G).filter (fun φ => restrictLabel P φ = ξ) =
      Finset.univ.filter (fun φ : Fin N ↪ Fin n =>
        (∀ x : {x // x ∈ P}, φ x = ξ x) ∧ F.image (fun e => e.map φ) ⊆ G) := by
    ext φ
    simp only [graphEmbeddingSet,Finset.mem_filter,Finset.mem_univ,true_and,
      Function.Embedding.ext_iff,restrictLabel_apply,and_comm]
  rw [heq]
  exact (graphEmbedding_fiber_le_rootedCount s I P E F G hE hsimple hind hIP hcover hEF ξ).trans
    (hκ ξ hξ)

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_ReindexSetImage
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma reindexTemplate_free_card {N : ℕ} (Z I : Finset (Fin N)) (E : Graph N)
    (hE : ∀ e ∈ E, e ⊆ Z ∪ I) (hsimple : ∀ e ∈ E, e.card = 2)
    (hind : ∀ e ∈ E, ¬ e ⊆ I) (hd : Disjoint Z I) :
    (Z ∪ I).card - (reindexTemplate (Z ∪ I) E I hE hsimple hind).roots.card = Z.card := by
  rw [reindexTemplate_roots_card _ _ _ _ _ _ Finset.subset_union_right,
    Finset.card_union_of_disjoint hd]
  omega

theorem reindexTemplate_sparse_transfer {N : ℕ} (Z I : Finset (Fin N)) (E : Graph N)
    (hE : ∀ e ∈ E, e ⊆ Z ∪ I) (hsimple : ∀ e ∈ E, e.card = 2)
    (hind : ∀ e ∈ E, ¬ e ⊆ I) (hd : Disjoint Z I)
    (hsparse : ∀ U ⊆ Z, U ≠ Z → (E.filter (fun e => e ⊆ I ∪ U)).card ≤ 2 * U.card) :
    let T := reindexTemplate (Z ∪ I) E I hE hsimple hind
    ∀ J : Finset (Fin (Z ∪ I).card), T.roots ⊆ J → J ≠ Finset.univ →
      (T.edges.filter (· ⊆ J)).card ≤ 2 * (J.card - T.roots.card) := by
  intro T J hJ hproper
  let s := Z ∪ I
  let f := s.orderEmbOfFin rfl
  let Js := J.image f
  let U := Js ∩ Z
  have hJs : Js ⊆ s := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact s.orderEmbOfFin_mem rfl i
  have hI : I ⊆ Js := by
    intro x hx
    rw [← image_reindexSet (s := s) (e := I) Finset.subset_union_right] at hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨i,hJ hi,rfl⟩
  have hU : U ⊆ Z := Finset.inter_subset_right
  have hUnion : I ∪ U = Js := by
    apply Finset.Subset.antisymm
    · exact Finset.union_subset hI Finset.inter_subset_left
    · intro x hx
      rcases Finset.mem_union.mp (hJs hx) with hxZ | hxI
      · exact Finset.mem_union_right I (Finset.mem_inter.mpr ⟨hx,hxZ⟩)
      · exact Finset.mem_union_left U hxI
  have hUne : U ≠ Z := by
    intro he
    have hJall : Js = s := by rw [← hUnion,he]; exact Finset.union_comm _ _
    apply hproper
    apply Finset.eq_univ_of_forall
    intro i
    have hm : f i ∈ Js := by
      rw [hJall]
      exact s.orderEmbOfFin_mem rfl i
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hm
    exact f.injective he ▸ hj
  have hcardJs : Js.card = J.card := Finset.card_image_of_injective _ f.injective
  have hdis : Disjoint I U := hd.symm.mono_right hU
  have hcard : J.card - T.roots.card = U.card := by
    have hh := Finset.card_union_of_disjoint hdis
    rw [hUnion,hcardJs] at hh
    have hroot : T.roots.card = I.card := reindexTemplate_roots_card _ _ _ _ _ _
      Finset.subset_union_right
    rw [hroot]
    omega
  have hinduced : (T.edges.filter (· ⊆ J)).card = (E.filter (· ⊆ I ∪ U)).card := by
    have hh := reindexTemplate_induced_card s E I hE hsimple hind Js
    rw [reindexSet_image] at hh
    rw [hUnion]
    exact hh
  rw [hinduced,hcard]
  exact hsparse U hU hUne

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_SparseScalingOne
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma sparse_scaling_ge_one (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hD : 1 ≤ (n : ℝ) * p ^ 2) (v e : ℕ) (he : e ≤ 2 * v) :
    1 ≤ (n : ℝ) ^ v * p ^ e := by
  calc
    1 ≤ ((n : ℝ) * p ^ 2) ^ v := one_le_pow₀ hD
    _ = (n : ℝ) ^ v * p ^ (2 * v) := by rw [mul_pow,pow_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hp hp1 he) (by positivity)

theorem largeTemplateEligible_of_sparse {k n : ℕ} (T : RootedTemplate k)
    (hroots : T.roots = ∅) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hD : 1 ≤ (n : ℝ) * p ^ 2)
    (hs : ∀ W : Finset (Fin k), (T.edges.filter (· ⊆ W)).card ≤ 2 * W.card) :
    largeTemplateEligible T n p := by
  intro W _ F hF hFW
  have hsub : F ⊆ T.edges.filter (· ⊆ W) := by
    intro e he
    exact Finset.mem_filter.mpr ⟨hF he,hFW e he⟩
  have hcount := (Finset.card_le_card hsub).trans (hs W)
  simpa only [hroots,Finset.card_empty,Nat.sub_zero] using
    sparse_scaling_ge_one n p hp hp1 hD W.card F.card hcount

theorem smallTemplateEligible_of_sparse {k n : ℕ} (T : RootedTemplate k) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hD : 1 ≤ (n : ℝ) * p ^ 2)
    (htotal : (n : ℝ) ^ (k - T.roots.card) * p ^ T.edges.card ≤ 1)
    (hs : ∀ J : Finset (Fin k), T.roots ⊆ J → J ≠ Finset.univ →
      (T.edges.filter (· ⊆ J)).card ≤ 2 * (J.card - T.roots.card)) :
    smallTemplateEligible T n p := by
  intro J hJ
  by_cases hfull : J = Finset.univ
  · subst J
    simp only [Finset.subset_univ,Finset.filter_true,Finset.card_univ,Fintype.card_fin,
      Nat.sub_self,pow_zero,mul_one,le_refl]
  · have hI : T.roots.card ≤ J.card := Finset.card_le_card hJ
    have hJk : J.card ≤ k := by simpa only [Fintype.card_fin] using J.card_le_univ
    have hE : (T.edges.filter (· ⊆ J)).card ≤ T.edges.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hden := sparse_scaling_ge_one n p hp hp1 hD
      (J.card - T.roots.card) (T.edges.filter (· ⊆ J)).card (hs J hJ hfull)
    have hid :
        ((n : ℝ) ^ (k - J.card) * p ^ (T.edges.card - (T.edges.filter (· ⊆ J)).card)) *
          ((n : ℝ) ^ (J.card - T.roots.card) * p ^ (T.edges.filter (· ⊆ J)).card) =
        (n : ℝ) ^ (k - T.roots.card) * p ^ T.edges.card := by
      rw [mul_mul_mul_comm,← pow_add,← pow_add]
      congr 2 <;> omega
    have hnon : 0 ≤ (n : ℝ) ^ (k - J.card) *
        p ^ (T.edges.card - (T.edges.filter (· ⊆ J)).card) := by positivity
    calc
      _ ≤ ((n : ℝ) ^ (k - J.card) * p ^ (T.edges.card - (T.edges.filter (· ⊆ J)).card)) *
          ((n : ℝ) ^ (J.card - T.roots.card) * p ^ (T.edges.filter (· ⊆ J)).card) :=
        le_mul_of_one_le_right hnon hden
      _ = _ := hid
      _ ≤ 1 := htotal

end SharpTerminalLeave

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_BornEdges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.BirthGraph
open scoped BigOperators

variable {N : ℕ} (B : BirthGraph N)

theorem pair_injective_on_older (v : Fin N) :
    Set.InjOn (fun u : Fin N => ({u, v} : Finset (Fin N))) (B.older v) := by
  intro a ha b hb hab
  have hm : a ∈ ({b, v} : Finset (Fin N)) := by
    change ({a, v} : Finset (Fin N)) = {b, v} at hab
    rw [← hab]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hm | hm
  · exact hm
  · exact False.elim ((ne_of_lt (B.older_lt v a ha)) hm)

@[simp] theorem bornEdges_card (v : Fin N) : (B.bornEdges v).card = (B.older v).card :=
  Finset.card_image_of_injOn (B.pair_injective_on_older v)

theorem bornEdges_disjoint {v w : Fin N} (hvw : v ≠ w) :
    Disjoint (B.bornEdges v) (B.bornEdges w) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨b, hb, hbe⟩ := Finset.mem_image.mp hf
  have hv : v ∈ ({b, w} : Finset (Fin N)) := hbe.symm ▸ (by simp)
  have hw : w ∈ ({a, v} : Finset (Fin N)) := hbe ▸ (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv hw
  have hvb : v = b := hv.resolve_right hvw
  have hwa : w = a := hw.resolve_right hvw.symm
  have hlt := B.older_lt v a ha
  have hlt' := B.older_lt w b hb
  subst a b
  exact (not_lt_of_gt hlt) hlt'

theorem backEdges_card (Z : Finset (Fin N)) :
    (B.backEdges Z).card = ∑ v ∈ Z, (B.older v).card := by
  rw [backEdges, Finset.card_biUnion]
  · simp only [bornEdges_card]
  · intro a _ b _ hab
    exact B.bornEdges_disjoint hab

theorem backEdges_card_eq (Z : Finset (Fin N)) (h : ∀ v ∈ Z, (B.older v).card = 2) :
    (B.backEdges Z).card = 2 * Z.card := by
  rw [backEdges_card]
  simp only [Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul, mul_comm]

theorem inducedEdges_eq (U : Finset (Fin N)) : B.inducedEdges U =
    U.biUnion (fun v => ((B.older v) ∩ U).image (fun u => {u, v})) := by
  ext e
  simp only [inducedEdges, backEdges, bornEdges, Finset.mem_filter, Finset.mem_biUnion,
    Finset.mem_image, Finset.mem_inter]
  constructor
  · rintro ⟨⟨v, hv, u, hu, rfl⟩, hs⟩
    exact ⟨v, hv, u, ⟨hu, hs (by simp)⟩, rfl⟩
  · rintro ⟨v, hv, u, ⟨hu, huU⟩, rfl⟩
    refine ⟨⟨v, hv, u, hu, rfl⟩, ?_⟩
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨huU, hv⟩

theorem inducedEdges_card_le (U : Finset (Fin N)) :
    (B.inducedEdges U).card ≤ ∑ v ∈ U, ((B.older v) ∩ U).card := by
  rw [inducedEdges_eq]
  refine Finset.card_biUnion_le.trans (Finset.sum_le_sum ?_)
  intro v _
  exact Finset.card_image_le

theorem inducedEdges_sparse (U : Finset (Fin N)) (hU : U.Nonempty) :
    (B.inducedEdges U).card + 2 ≤ 2 * U.card := by
  let v := U.min' hU
  have hv : v ∈ U := Finset.min'_mem U hU
  have hzero : (B.older v) ∩ U = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    have hu' := Finset.mem_inter.mp hu
    exact (not_le_of_gt (B.older_lt v u hu'.1)) (Finset.min'_le U u hu'.2)
  have hsum : (∑ x ∈ U, ((B.older x) ∩ U).card) ≤ 2 * (U.card - 1) := by
    rw [← Finset.sum_erase_add _ _ hv, hzero, Finset.card_empty, add_zero]
    calc
      _ ≤ ∑ _x ∈ U.erase v, 2 := by
        apply Finset.sum_le_sum
        intro x _
        exact (Finset.card_le_card Finset.inter_subset_left).trans (B.older_card x)
      _ = _ := by simp [Finset.card_erase_of_mem hv, mul_comm]
  have hpos : 1 ≤ U.card := hU.card_pos
  have hh := (B.inducedEdges_card_le U).trans hsum
  omega

theorem induced_plus_one_sparse (U : Finset (Fin N)) (a b : Fin N) :
    ((insert ({a, b} : Finset (Fin N)) (B.backEdges Finset.univ)).filter
      (fun e => e ⊆ U)).card ≤ 2 * U.card := by
  by_cases hU : U.Nonempty
  · have hs : ((insert ({a, b} : Finset (Fin N)) (B.backEdges Finset.univ)).filter
        (fun e => e ⊆ U)) ⊆ insert {a, b} (B.inducedEdges U) := by
      intro e he
      obtain ⟨he, heU⟩ := Finset.mem_filter.mp he
      rcases Finset.mem_insert.mp he with he | he
      · exact Finset.mem_insert.mpr (Or.inl he)
      · obtain ⟨v, _, u, hu, heu⟩ := B.backEdges_mem_pair he
        apply Finset.mem_insert.mpr ∘ Or.inr
        apply Finset.mem_filter.mpr
        refine ⟨?_, heU⟩
        apply Finset.mem_biUnion.mpr
        refine ⟨v, heU (by rw [heu]; simp), ?_⟩
        exact Finset.mem_image.mpr ⟨u, hu, heu.symm⟩
    have hcard := (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)
    have hsp := B.inducedEdges_sparse U hU
    omega
  · have hzero : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
    subst U
    have hempty : ((insert ({a, b} : Finset (Fin N)) (B.backEdges Finset.univ)).filter
        (fun e => e ⊆ ∅)).card = 0 := by
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨he, hs⟩ := Finset.mem_filter.mp he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact Finset.notMem_empty a (hs (by simp))
      · obtain ⟨v, _, u, _, heu⟩ := B.backEdges_mem_pair he
        exact Finset.notMem_empty v (hs (by rw [heu]; simp))
    rw [hempty]
    exact Nat.zero_le _

end SharpTerminalLeave.BirthGraph

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_SuffixBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.BirthGraph
variable {N : ℕ} (B : BirthGraph N)

lemma suffixBoundary_card {Z : Finset (Fin N)} {a b : Fin N} (hmark : a ∈ Z ∨ b ∈ Z) :
    (B.suffixBoundary Z a b).card ≤ 2 * Z.card + 1 := by
  have hbase : (Z.biUnion B.older).card ≤ 2 * Z.card := by
    calc
      _ ≤ ∑ v ∈ Z, (B.older v).card := Finset.card_biUnion_le
      _ ≤ ∑ _v ∈ Z, 2 := Finset.sum_le_sum (fun v _ => B.older_card v)
      _ = _ := by simp [mul_comm]
  have hbound (x y : Fin N) (hx : x ∈ Z) :
      (((Z.biUnion B.older) ∪ {x,y}) \ Z).card ≤ 2 * Z.card + 1 := by
    have hs : ((Z.biUnion B.older) ∪ {x,y}) \ Z ⊆ insert y (Z.biUnion B.older) := by
      intro z hz
      obtain ⟨hz,hzn⟩ := Finset.mem_sdiff.mp hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact Finset.mem_insert_of_mem hz
      · rcases Finset.mem_insert.mp hz with rfl | hz
        · exact False.elim (hzn hx)
        · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hz))
    exact (Finset.card_le_card hs).trans ((Finset.card_insert_le _ _).trans (Nat.add_le_add_right hbase 1))
  rcases hmark with ha | hb
  · exact hbound a b ha
  · simpa only [suffixBoundary,Finset.pair_comm a b] using hbound b a hb

lemma suffixVertices_card {Z : Finset (Fin N)} {a b : Fin N} (hmark : a ∈ Z ∨ b ∈ Z) :
    (B.suffixVertices Z a b).card ≤ 3 * Z.card + 1 := by
  unfold suffixVertices
  have hh := (Finset.card_union_le Z (B.suffixBoundary Z a b)).trans
    (Nat.add_le_add_left (B.suffixBoundary_card hmark) Z.card)
  omega

end SharpTerminalLeave.BirthGraph

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_Within
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.BirthGraph
variable {N : ℕ} (B : BirthGraph N)

theorem within_closed {Z U : Finset (Fin N)} {x y : Fin N}
    (h : B.Within Z x y)
    (hclosed : ∀ v ∈ U, ∀ u ∈ B.older v, u ∈ Z → u ∈ U) (hy : y ∈ U) : x ∈ U := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hy
  | @head x c hxc _ ih => exact hclosed c ih x hxc.2.2 hxc.1

theorem covered_closed {Z U : Finset (Fin N)} {a b : Fin N}
    (hc : B.Covered Z a b) (ha : a ∈ Z → a ∈ U) (hb : b ∈ Z → b ∈ U)
    (hclosed : ∀ v ∈ U, ∀ u ∈ B.older v, u ∈ Z → u ∈ U) : Z ⊆ U := by
  intro z hz
  rcases hc z hz with ⟨haZ, hza⟩ | ⟨hbZ, hzb⟩
  · exact B.within_closed hza hclosed (ha haZ)
  · exact B.within_closed hzb hclosed (hb hbZ)

theorem retained_backEdges_subset {Z I U : Finset (Fin N)} (hI : Disjoint I Z) :
    ((B.backEdges Z).filter (fun e => e ⊆ I ∪ U)) ⊆ B.backEdges U := by
  intro e he
  obtain ⟨heZ, heIU⟩ := Finset.mem_filter.mp he
  obtain ⟨v, hvZ, u, hu, rfl⟩ := B.backEdges_mem_pair heZ
  have hvIU : v ∈ I ∪ U := heIU (by simp)
  have hvU : v ∈ U := (Finset.mem_union.mp hvIU).resolve_left
    (fun hvI => Finset.disjoint_left.mp hI hvI hvZ)
  exact Finset.mem_biUnion.mpr ⟨v, hvU, Finset.mem_image.mpr ⟨u, hu, rfl⟩⟩

theorem proper_suffix_sparse {Z I U : Finset (Fin N)} {a b : Fin N}
    (hI : Disjoint I Z) (hU : U ⊆ Z) (hproper : U ≠ Z)
    (hborn : ∀ v ∈ Z, (B.older v).card = 2) (hc : B.Covered Z a b) :
    ((insert ({a, b} : Finset (Fin N)) (B.backEdges Z)).filter
      (fun e => e ⊆ I ∪ U)).card ≤ 2 * U.card := by
  classical
  let S := (B.backEdges Z).filter (fun e => e ⊆ I ∪ U)
  let T := (insert ({a, b} : Finset (Fin N)) (B.backEdges Z)).filter
    (fun e => e ⊆ I ∪ U)
  have hS : S ⊆ B.backEdges U := B.retained_backEdges_subset hI
  have hUcard : (B.backEdges U).card = 2 * U.card :=
    B.backEdges_card_eq U (fun v hv => hborn v (hU hv))
  have hST : T ⊆ insert {a, b} S := by
    intro e he
    obtain ⟨he, heIU⟩ := Finset.mem_filter.mp he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨he, heIU⟩)
  by_contra hfail
  have hbig : 2 * U.card < T.card := Nat.lt_of_not_ge hfail
  have hmark : ({a, b} : Finset (Fin N)) ⊆ I ∪ U := by
    by_contra hn
    have hTS : T ⊆ S := by
      intro e he
      obtain ⟨he, heIU⟩ := Finset.mem_filter.mp he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact False.elim (hn heIU)
      · exact Finset.mem_filter.mpr ⟨he, heIU⟩
    have hh := (Finset.card_le_card hTS).trans (Finset.card_le_card hS)
    rw [hUcard] at hh
    exact (Nat.not_le_of_gt hbig) hh
  have heq : S = B.backEdges U := by
    apply Finset.eq_of_subset_of_card_le hS
    have hh := (Finset.card_le_card hST).trans (Finset.card_insert_le _ _)
    rw [hUcard]
    omega
  have hclosed : ∀ v ∈ U, ∀ u ∈ B.older v, u ∈ Z → u ∈ U := by
    intro v hv u hu huZ
    have heU : ({u, v} : Finset (Fin N)) ∈ B.backEdges U :=
      Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_image.mpr ⟨u, hu, rfl⟩⟩
    rw [← heq] at heU
    have huIU : u ∈ I ∪ U := (Finset.mem_filter.mp heU).2 (by simp)
    exact (Finset.mem_union.mp huIU).resolve_left
      (fun huI => Finset.disjoint_left.mp hI huI huZ)
  have haU : a ∈ Z → a ∈ U := by
    intro haZ
    exact (Finset.mem_union.mp (hmark (by simp))).resolve_left
      (fun haI => Finset.disjoint_left.mp hI haI haZ)
  have hbU : b ∈ Z → b ∈ U := by
    intro hbZ
    exact (Finset.mem_union.mp (hmark (by simp))).resolve_left
      (fun hbI => Finset.disjoint_left.mp hI hbI hbZ)
  exact hproper (Finset.Subset.antisymm hU (B.covered_closed hc haU hbU hclosed))

theorem suffix_edges_card {Z : Finset (Fin N)} {a b : Fin N}
    (hborn : ∀ v ∈ Z, (B.older v).card = 2)
    (hne : ¬ B.graph.Adj a b) :
    (insert ({a, b} : Finset (Fin N)) (B.backEdges Z)).card = 2 * Z.card + 1 := by
  have hn : ({a, b} : Finset (Fin N)) ∉ B.backEdges Z := by
    intro he
    obtain ⟨v, hv, u, hu, huv⟩ := B.backEdges_mem_pair he
    have huvn : u ≠ v := ne_of_lt (B.older_lt v u hu)
    have hab : a ≠ b := by
      intro h
      have hc := congrArg Finset.card huv
      simp [h, huvn] at hc
    have ha : a = u ∨ a = v := by
      have hm : a ∈ ({u, v} : Finset (Fin N)) := by rw [← huv]; simp
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
    have hb : b = u ∨ b = v := by
      have hm : b ∈ ({u, v} : Finset (Fin N)) := by rw [← huv]; simp
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact hab rfl
    · exact hne (Or.inl hu)
    · exact hne (Or.inr hu)
    · exact hab rfl
  rw [Finset.card_insert_of_notMem hn, B.backEdges_card_eq Z hborn]

end SharpTerminalLeave.BirthGraph

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Embeddings_SuffixTemplate
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.BirthGraph
variable {N : ℕ} (B : BirthGraph N)

lemma suffixTemplate_free_card (Z : Finset (Fin N)) (a b : Fin N) (hab : a ≠ b)
    (hmark : a ∈ Z ∨ b ∈ Z) :
    (B.suffixVertices Z a b).card - (B.suffixTemplate Z a b hab hmark).roots.card = Z.card :=
  reindexTemplate_free_card Z _ _ _ _ _ (B.suffixBoundary_disjoint Z a b).symm

lemma suffixTemplate_edges_card {Z : Finset (Fin N)} {a b : Fin N} (hab : a ≠ b)
    (hmark : a ∈ Z ∨ b ∈ Z) (hborn : ∀ v ∈ Z, (B.older v).card = 2)
    (hne : ¬ B.graph.Adj a b) :
    (B.suffixTemplate Z a b hab hmark).edges.card = 2 * Z.card + 1 := by
  rw [suffixTemplate,reindexTemplate_edges_card]
  exact B.suffix_edges_card hborn hne

theorem suffixTemplate_eligible {Z : Finset (Fin N)} {a b : Fin N} (hab : a ≠ b)
    (hmark : a ∈ Z ∨ b ∈ Z) (hborn : ∀ v ∈ Z, (B.older v).card = 2)
    (hne : ¬ B.graph.Adj a b) (hc : B.Covered Z a b)
    (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hD : 1 ≤ (n : ℝ) * p ^ 2)
    (hsmall : (n : ℝ) ^ Z.card * p ^ (2 * Z.card + 1) ≤ 1) :
    smallTemplateEligible (B.suffixTemplate Z a b hab hmark) n p := by
  apply smallTemplateEligible_of_sparse _ p hp hp1 hD
  · rw [B.suffixTemplate_free_card,B.suffixTemplate_edges_card hab hmark hborn hne]
    exact hsmall
  · apply reindexTemplate_sparse_transfer Z (B.suffixBoundary Z a b)
      (B.suffixEdges Z a b) _ _ _ (B.suffixBoundary_disjoint Z a b).symm
    intro U hU hproper
    exact B.proper_suffix_sparse (B.suffixBoundary_disjoint Z a b) hU hproper hborn hc

theorem suffixTemplate_count {n : ℕ} {G : Graph n} {c C : ℝ}
    (hGood : GoodPrefixGraph n c C G) {Z : Finset (Fin N)} {a b : Fin N}
    (hab : a ≠ b) (hmark : a ∈ Z ∨ b ∈ Z)
    (hborn : ∀ v ∈ Z, (B.older v).card = 2) (hne : ¬ B.graph.Adj a b)
    (hc : B.Covered Z a b) (hcap : 3 * Z.card + 1 ≤ prefixTemplateCap)
    (hp : 0 ≤ prefixDensity n) (hp1 : prefixDensity n ≤ 1) (hD : 1 ≤ prefixD n)
    (hsmall : (n : ℝ) ^ Z.card * prefixDensity n ^ (2 * Z.card + 1) ≤ 1)
    (ψ : {v // v ∈ (B.suffixTemplate Z a b hab hmark).roots} ↪ Fin n) :
    rootedCount (B.suffixTemplate Z a b hab hmark) ψ G ≤ prefixTemplateFactor n C := by
  have horder := (B.suffixVertices_card hmark).trans hcap
  have ht := (hGood.2.2.2.2.2 _ horder (B.suffixTemplate Z a b hab hmark) ψ).2
  exact ht (B.suffixTemplate_eligible hab hmark hborn hne hc n (prefixDensity n) hp hp1 hD hsmall)

end SharpTerminalLeave.BirthGraph

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixEmbeddings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave
section OrderedEmbeddings
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {N : ℕ} (J : SimpleGraph (Fin N)) (G : SimpleGraph V)
variable [DecidableRel J.Adj] [DecidableRel G.Adj]

variable {G J}

omit [DecidableEq V] in
lemma mem_prefixEmbeddings {k : ℕ} {hk : k ≤ N} (φ : Fin k ↪ V) :
    φ ∈ prefixEmbeddings J G k hk ↔ ∀ i j : Fin k,
    J.Adj (Fin.castLE hk i) (Fin.castLE hk j) → G.Adj (φ i) (φ j) := by
  simp only [prefixEmbeddings,Finset.mem_filter,Finset.mem_univ,true_and]

omit [DecidableEq V] in
lemma dropLastEmbedding_mem {k : ℕ} (hk : k+1 ≤ N) {φ : Fin (k+1) ↪ V}
    (hφ : φ ∈ prefixEmbeddings J G (k+1) hk) :
    dropLastEmbedding φ ∈ prefixEmbeddings J G k (by omega) := by
  apply (mem_prefixEmbeddings _).mpr
  intro i j hij
  apply (mem_prefixEmbeddings φ).mp hφ i.castSucc j.castSucc
  exact hij

lemma embedding_fiber_le {k : ℕ} (hk : k+1 ≤ N) (ψ : Fin k ↪ V) :
    ((prefixEmbeddings J G (k+1) hk).filter (fun φ => dropLastEmbedding φ = ψ)).card ≤
      (compatibleNext J G hk ψ).card := by
  let s := (prefixEmbeddings J G (k+1) hk).filter (fun φ => dropLastEmbedding φ = ψ)
  have hinj : Set.InjOn (fun φ : Fin (k+1) ↪ V => φ (Fin.last k)) s := by
    intro φ hφ χ hχ he
    have hφr := (Finset.mem_filter.mp hφ).2
    have hχr := (Finset.mem_filter.mp hχ).2
    apply Function.Embedding.ext
    intro i
    refine Fin.lastCases he (fun j => ?_) i
    change dropLastEmbedding φ j = dropLastEmbedding χ j
    rw [hφr,hχr]
  calc
    s.card = (s.image (fun φ => φ (Fin.last k))).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ _ := Finset.card_le_card (by
      intro z hz
      obtain ⟨φ,hφ,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hφ,hψ⟩ := Finset.mem_filter.mp hφ
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      intro i hi
      have hh := (mem_prefixEmbeddings φ).mp hφ i.castSucc (Fin.last k) hi
      change G.Adj (dropLastEmbedding φ i) _ at hh
      rw [hψ] at hh
      exact hh)

theorem prefixEmbeddings_succ_bound {k : ℕ} (hk : k+1 ≤ N) (b : ℝ)
    (hb : ∀ ψ ∈ prefixEmbeddings J G k (by omega),
      ((compatibleNext J G hk ψ).card : ℝ) ≤ b) :
    ((prefixEmbeddings J G (k+1) hk).card : ℝ) ≤
      b * (prefixEmbeddings J G k (by omega)).card := by
  apply real_card_le_fiber_bound _ _ dropLastEmbedding
      (fun _ hφ => dropLastEmbedding_mem hk hφ) b
  intro ψ hψ
  exact (Nat.cast_le.mpr (embedding_fiber_le hk ψ)).trans (hb ψ hψ)

omit [DecidableEq V] in
lemma prefixEmbeddings_zero : (prefixEmbeddings J G 0 (Nat.zero_le N)).card = 1 := by
  have h : prefixEmbeddings J G 0 (Nat.zero_le N) = Finset.univ := by
    ext φ
    simp [prefixEmbeddings]
  rw [h,Finset.card_univ]
  exact Fintype.card_unique

theorem prefixEmbeddings_product_bound (b : ℕ → ℝ) (hb0 : ∀ k < N, 0 ≤ b k)
    (hb : ∀ k (hk : k+1 ≤ N), ∀ ψ ∈ prefixEmbeddings J G k (by omega),
      ((compatibleNext J G hk ψ).card : ℝ) ≤ b k)
    (k : ℕ) (hk : k ≤ N) :
    ((prefixEmbeddings J G k hk).card : ℝ) ≤ ∏ i ∈ Finset.range k, b i := by
  induction k with
  | zero => simp only [prefixEmbeddings_zero,Nat.cast_one,Finset.range_zero,
      Finset.prod_empty,le_refl]
  | succ k ih =>
    calc
      _ ≤ b k * (prefixEmbeddings J G k (by omega)).card :=
        prefixEmbeddings_succ_bound hk (b k) (hb k hk)
      _ ≤ b k * ∏ i ∈ Finset.range k, b i :=
        mul_le_mul_of_nonneg_left (ih (by omega)) (hb0 k (by omega))
      _ = _ := by rw [Finset.prod_range_succ,mul_comm]

omit [DecidableEq V] in

theorem compatibleNext_le_codegree {k : ℕ} (hk : k+1 ≤ N) (ψ : Fin k ↪ V)
    (i j : Fin k) (hij : i ≠ j)
    (hi : J.Adj (Fin.castLE (by omega) i) ⟨k,by omega⟩)
    (hj : J.Adj (Fin.castLE (by omega) j) ⟨k,by omega⟩)
    (D : ℝ) (hD : ∀ x y : V, x ≠ y →
      ((Finset.univ.filter (fun z => G.Adj x z ∧ G.Adj y z)).card : ℝ) ≤ D) :
    ((compatibleNext J G hk ψ).card : ℝ) ≤ D := by
  have hs : compatibleNext J G hk ψ ⊆
      Finset.univ.filter (fun z => G.Adj (ψ i) z ∧ G.Adj (ψ j) z) := by
    intro z hz
    have hh := (Finset.mem_filter.mp hz).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh i hi,hh j hj⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hs)).trans (hD _ _ (ψ.injective.ne hij))

omit [DecidableEq V] in
theorem compatibleNext_le_degree {k : ℕ} (hk : k+1 ≤ N) (ψ : Fin k ↪ V)
    (i : Fin k) (hi : J.Adj (Fin.castLE (by omega) i) ⟨k,by omega⟩)
    (Δ : ℝ) (hΔ : ∀ x : V, ((Finset.univ.filter (G.Adj x)).card : ℝ) ≤ Δ) :
    ((compatibleNext J G hk ψ).card : ℝ) ≤ Δ := by
  have hs : compatibleNext J G hk ψ ⊆ Finset.univ.filter (G.Adj (ψ i)) := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hz).2 i hi⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hs)).trans (hΔ _)

omit [DecidableEq V] in
lemma compatibleNext_le_order {k : ℕ} (hk : k+1 ≤ N) (ψ : Fin k ↪ V) :
    (compatibleNext J G hk ψ).card ≤ Fintype.card V := Finset.card_le_univ _

end OrderedEmbeddings
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_InitialAssignmentSet
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.BirthGraph
variable {N n : ℕ} (B : BirthGraph N) (G : Graph n)

lemma graph_edge_mem {i j : Fin N} (hij : B.graph.Adj i j) :
    ({i,j} : Finset (Fin N)) ∈ B.backEdges Finset.univ := by
  rcases hij with h | h
  · exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_image.mpr ⟨i,h,rfl⟩⟩
  · rw [Finset.pair_comm]
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨j,h,rfl⟩⟩

open Classical in

lemma initialAssignmentSet_card (k : ℕ) (hk : k ≤ N) :
    (B.initialAssignmentSet G k hk).card ≤
      (prefixEmbeddings B.graph (lookupGraph G) k hk).card := by
  classical
  exact Finset.card_image_le

theorem initialLabel_mem {a b : Fin N} {φ : Fin N ↪ Fin n}
    (hφ : φ ∈ graphEmbeddingSet
      (insert ({a,b} : Finset (Fin N)) (B.backEdges Finset.univ)) G)
    (k : ℕ) (hk : k ≤ N) :
    restrictLabel (initialVertices N k) φ ∈ B.initialAssignmentSet G k hk := by
  classical
  refine Finset.mem_image.mpr ⟨initialLabel hk φ,?_,initialSubtypeLabel_initialLabel hk φ⟩
  apply (mem_prefixEmbeddings _).mpr
  intro i j hij
  refine ⟨φ.injective.ne (B.graph.ne_of_adj hij),?_⟩
  have he := B.graph_edge_mem hij
  have hm := (Finset.mem_filter.mp hφ).2 (Finset.mem_image.mpr
    ⟨_,Finset.mem_insert_of_mem he,rfl⟩)
  change ({φ (Fin.castLE hk i), φ (Fin.castLE hk j)} : Finset (Fin n)) ∈ G
  simpa only [Finset.map_insert,Finset.map_singleton] using hm

theorem two_preceding_neighbors (R : ℕ)
    (hb : ∀ v : Fin N, R ≤ v.val → (B.older v).card = 2)
    (k : ℕ) (hR : R ≤ k) (hk : k+1 ≤ N) :
    ∃ u v : Fin k, u ≠ v ∧
      B.graph.Adj (Fin.castLE (by omega) u) ⟨k,by omega⟩ ∧
      B.graph.Adj (Fin.castLE (by omega) v) ⟨k,by omega⟩ := by
  obtain ⟨u,v,huv,he⟩ := Finset.card_eq_two.mp (hb ⟨k,by omega⟩ hR)
  have hu : u ∈ B.older ⟨k,by omega⟩ := by rw [he]; simp
  have hv : v ∈ B.older ⟨k,by omega⟩ := by rw [he]; simp
  have huk : u.val < k := B.older_lt _ u hu
  have hvk : v.val < k := B.older_lt _ v hv
  refine ⟨⟨u.val,huk⟩,⟨v.val,hvk⟩,?_,Or.inl hu,Or.inl hv⟩
  intro hh
  exact huv (Fin.ext (congrArg (fun z : Fin k => z.val) hh))

end SharpTerminalLeave.BirthGraph

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_LookupGraphDegree
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

open Classical in

lemma lookupGraph_degree_le {n : ℕ} (G : Graph n) (x : Fin n) :
    (Finset.univ.filter (fun z => (lookupGraph G).Adj x z)).card ≤ currentDegree G x := by
  apply Finset.card_le_card
  intro z hz
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ z,(Finset.mem_filter.mp hz).2.2⟩

open Classical in

lemma lookupGraph_codegree_le {n : ℕ} (G : Graph n) (x y : Fin n) :
    (Finset.univ.filter (fun z => (lookupGraph G).Adj x z ∧ (lookupGraph G).Adj y z)).card ≤
      currentCodegree G x y := by
  apply Finset.card_le_card
  intro z hz
  have hh := (Finset.mem_filter.mp hz).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ z,hh.1.2,hh.2.2⟩

open Classical in

lemma goodPrefix_degree_bound {n : ℕ} {G : Graph n} {c C : ℝ}
    (hGood : GoodPrefixGraph n c C G) (hc : (n : ℝ)^(-c) ≤ 1)
    (hp : 0 ≤ prefixDensity n) (x : Fin n) :
    ((Finset.univ.filter (fun z => (lookupGraph G).Adj x z)).card : ℝ) ≤
      2 * (n * prefixDensity n) := by
  have h := (abs_le.mp (hGood.2.2.1 x)).2
  have hm := mul_le_mul_of_nonneg_right hc (mul_nonneg (Nat.cast_nonneg n) hp)
  have hl : ((Finset.univ.filter (fun z => (lookupGraph G).Adj x z)).card : ℝ) ≤
      currentDegree G x := by exact_mod_cast lookupGraph_degree_le G x
  linarith

open Classical in

lemma goodPrefix_codegree_bound {n : ℕ} {G : Graph n} {c C : ℝ}
    (hGood : GoodPrefixGraph n c C G) (hc : (n : ℝ)^(-c) ≤ 1)
    (x y : Fin n) (hxy : x ≠ y) :
    ((Finset.univ.filter (fun z => (lookupGraph G).Adj x z ∧ (lookupGraph G).Adj y z)).card : ℝ) ≤
      2 * prefixD n := by
  have h := (abs_le.mp (hGood.2.2.2.1 x y hxy)).2
  have hD : 0 ≤ prefixD n := mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _)
  have hm := mul_le_mul_of_nonneg_right hc hD
  have hl : ((Finset.univ.filter (fun z => (lookupGraph G).Adj x z ∧ (lookupGraph G).Adj y z)).card : ℝ) ≤
      currentCodegree G x y := by exact_mod_cast lookupGraph_codegree_le G x y
  linarith

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_RootClosers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

lemma product_two_values (R : ℕ) (T : Finset ℕ) (hT : T ⊆ Finset.range R) (x y : ℝ) :
    (∏ i ∈ Finset.range R, if i ∈ T then x else y) = x^T.card * y^(R-T.card) := by
  classical
  have ht : (Finset.range R).filter (fun i => i ∈ T) = T := by
    ext i
    simp only [Finset.mem_filter]
    exact ⟨And.right,fun hi => ⟨hT hi,hi⟩⟩
  have hc := Finset.card_filter_add_card_filter_not (s := Finset.range R) (fun i => i ∈ T)
  rw [ht,Finset.card_range] at hc
  have hn : ((Finset.range R).filter (fun i => i ∉ T)).card = R-T.card := by omega
  rw [Finset.prod_ite]
  simp only [Finset.prod_const,ht,hn]

namespace BirthGraph
variable {N : ℕ} (B : BirthGraph N)

lemma rootClosers_subset (R : ℕ) : B.rootClosers R ⊆ Finset.range R := by
  intro i hi
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hi
  exact Finset.mem_range.mpr ((mem_initialVertices N R v).mp (Finset.mem_filter.mp hv).1)

lemma rootClosers_card (R : ℕ)
    (hs : ∀ v : Fin N, v.val < R → (B.older v).card ≤ 1) :
    (B.rootClosers R).card = (B.backEdges (initialVertices N R)).card := by
  classical
  rw [rootClosers,Finset.card_image_of_injective _ Fin.val_injective,
    B.backEdges_card,Finset.card_filter]
  apply Finset.sum_congr rfl
  intro v hv
  have hs' := hs v ((mem_initialVertices N R v).mp hv)
  by_cases hn : (B.older v).Nonempty
  · rw [ite_eq_left hn]
    have hp := Finset.card_pos.mpr hn
    omega
  · rw [ite_eq_right hn,Finset.not_nonempty_iff_eq_empty.mp hn,Finset.card_empty]

lemma rootClosers_predecessor (R : ℕ) (i : ℕ) (hi : i ∈ B.rootClosers R)
    (hN : i+1 ≤ N) : ∃ u : Fin i,
      B.graph.Adj (Fin.castLE (show i ≤ N by omega) u) ⟨i,by omega⟩ := by
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨u,hu⟩ := (Finset.mem_filter.mp hv).2
  have hlt := B.older_lt v u hu
  refine ⟨⟨u.val,hlt⟩,?_⟩
  exact Or.inl hu

theorem prefixEmbeddings_unordered_roots {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (R : ℕ) (hR : R ≤ N) (Δ : ℝ)
    (hΔ0 : 0 ≤ Δ)
    (hΔ : ∀ x : V, ((Finset.univ.filter (G.Adj x)).card : ℝ) ≤ Δ) :
    letI : DecidableRel B.graph.Adj := Classical.decRel _
    ((prefixEmbeddings B.graph G R hR).card : ℝ) ≤
      (Fintype.card V : ℝ)^(R-(B.rootClosers R).card) * Δ^(B.rootClosers R).card := by
  classical
  let b : ℕ → ℝ := fun i => if i ∈ B.rootClosers R then Δ else Fintype.card V
  have hb0 : ∀ i < N, 0 ≤ b i := by
    intro i _
    dsimp only [b]
    split_ifs <;> first | exact hΔ0 | positivity
  have hb : ∀ i (hi : i+1 ≤ N), ∀ ψ ∈ prefixEmbeddings B.graph G i (by omega),
      ((compatibleNext B.graph G hi ψ).card : ℝ) ≤ b i := by
    intro i hi ψ _
    dsimp only [b]
    by_cases hclose : i ∈ B.rootClosers R
    · rw [ite_eq_left hclose]
      obtain ⟨u,hu⟩ := B.rootClosers_predecessor R i hclose hi
      exact compatibleNext_le_degree hi ψ u hu Δ hΔ
    · rw [ite_eq_right hclose]
      exact_mod_cast compatibleNext_le_order hi ψ
  have h := prefixEmbeddings_product_bound (J := B.graph) (G := G) b hb0 hb R hR
  change _ ≤ ∏ i ∈ Finset.range R, if i ∈ B.rootClosers R then Δ else (Fintype.card V : ℝ) at h
  rw [product_two_values R (B.rootClosers R) (B.rootClosers_subset R)] at h
  simpa only [mul_comm] using h

end BirthGraph
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixEmbeddingsAfterRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave
section OrderedBirthCounts
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {N : ℕ} (J : SimpleGraph (Fin N)) (G : SimpleGraph V)
variable [DecidableRel J.Adj] [DecidableRel G.Adj]

theorem prefixEmbeddings_after_roots (R k : ℕ) (hR : R ≤ k) (hk : k ≤ N)
    (D : ℝ) (hD0 : 0 ≤ D)
    (hD : ∀ x y : V, x ≠ y →
      ((Finset.univ.filter (fun z => G.Adj x z ∧ G.Adj y z)).card : ℝ) ≤ D)
    (hborn : ∀ i, R ≤ i → (hi : i+1 ≤ N) → ∃ u v : Fin i,
      u ≠ v ∧ J.Adj (Fin.castLE (by omega) u) ⟨i,by omega⟩ ∧
        J.Adj (Fin.castLE (by omega) v) ⟨i,by omega⟩) :
    ((prefixEmbeddings J G k hk).card : ℝ) ≤
      ((prefixEmbeddings J G R (hR.trans hk)).card : ℝ) * D ^ (k-R) := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hR
  induction d with
  | zero => simp
  | succ d ih =>
    have hrec := prefixEmbeddings_succ_bound (J := J) (G := G) hk D (by
      intro ψ _
      obtain ⟨u,v,huv,hu,hv⟩ := hborn (R+d) (by omega) hk
      exact compatibleNext_le_codegree hk ψ u v huv hu hv D hD)
    have hm := mul_le_mul_of_nonneg_left (ih (by omega) (by omega) hborn) hD0
    calc
      _ ≤ D * (prefixEmbeddings J G (R+d) (by omega)).card := hrec
      _ ≤ D * ((prefixEmbeddings J G R (by omega)).card * D ^ (R+d-R)) := hm
      _ = _ := by simp only [Nat.add_sub_cancel_left]; ring

end OrderedBirthCounts
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Coupling_InitialAssignmentSetBound
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.BirthGraph
variable {N n : ℕ} (B : BirthGraph N)

theorem initialAssignmentSet_bound_unordered {G : Graph n} {c C : ℝ}
    (hGood : GoodPrefixGraph n c C G) (hsmall : (n : ℝ)^(-c) ≤ 1)
    (hp : 0 ≤ prefixDensity n) (r k : ℕ) (hrk : 2*r ≤ k) (hk : k ≤ N)
    (hroot : (B.rootClosers (2*r)).card = r)
    (hborn : ∀ v : Fin N, 2*r ≤ v.val → (B.older v).card = 2) :
    ((B.initialAssignmentSet G k hk).card : ℝ) ≤
      (4 * prefixM n)^r * (2 * prefixD n)^(k-2*r) := by
  classical
  have hD0 : 0 ≤ 2 * prefixD n := by unfold prefixD; positivity
  have hΔ0 : 0 ≤ 2 * (n : ℝ) * prefixDensity n := by positivity
  have hgrow := prefixEmbeddings_after_roots B.graph (lookupGraph G) (2*r) k hrk hk
    (2 * prefixD n) hD0 (goodPrefix_codegree_bound hGood hsmall)
    (fun i hi hN => B.two_preceding_neighbors (2*r) hborn i hi hN)
  have hroots := B.prefixEmbeddings_unordered_roots (lookupGraph G) (2*r) (hrk.trans hk)
    (2 * ((n : ℝ) * prefixDensity n)) (by nlinarith)
    (goodPrefix_degree_bound hGood hsmall hp)
  have hid : (n : ℝ) * (2 * ((n : ℝ) * prefixDensity n)) = 4 * prefixM n := by
    unfold prefixM
    ring
  have hrsub : 2*r-r = r := by omega
  simp only [Fintype.card_fin,hroot,hrsub] at hroots
  rw [← mul_pow,hid] at hroots
  exact (Nat.cast_le.mpr (B.initialAssignmentSet_card G k hk)).trans
    (hgrow.trans (mul_le_mul_of_nonneg_right hroots (pow_nonneg hD0 _)))

theorem long_witness_count_unordered {G : Graph n} {c C : ℝ}
    (hGood : GoodPrefixGraph n c C G) (hsmall : (n : ℝ)^(-c) ≤ 1)
    (r k : ℕ) (hrk : 2*r ≤ k) (hk : k ≤ N)
    (hroot : (B.rootClosers (2*r)).card = r)
    (hborn : ∀ v : Fin N, 2*r ≤ v.val → (B.older v).card = 2)
    {a b : Fin N} (hab : a ≠ b) (hne : ¬ B.graph.Adj a b)
    (hmark : k ≤ a.val ∨ k ≤ b.val)
    (hc : B.Covered (Finset.univ.filter (fun x => k ≤ x.val)) a b)
    (hcap : 3 * (N-k) + 1 ≤ prefixTemplateCap)
    (hp : 0 ≤ prefixDensity n) (hp1 : prefixDensity n ≤ 1) (hD : 1 ≤ prefixD n)
    (hscale : (n : ℝ)^(N-k) * prefixDensity n ^ (2*(N-k)+1) ≤ 1) :
    ((graphEmbeddingSet (insert ({a,b} : Finset (Fin N)) (B.backEdges Finset.univ)) G).card : ℝ) ≤
      prefixTemplateFactor n C * ((4 * prefixM n)^r * (2 * prefixD n)^(k-2*r)) := by
  classical
  let Z : Finset (Fin N) := Finset.univ.filter (fun x => k ≤ x.val)
  have hZ : Z.card = N-k := by
    have heq : Z = Finset.univ \ (Finset.univ.filter (fun x : Fin N => x.val < k)) := by
      ext x
      simp only [Z,Finset.mem_filter,Finset.mem_sdiff,Finset.mem_univ,true_and,not_lt]
    rw [heq,Finset.card_sdiff_of_subset (Finset.filter_subset _ _),Finset.card_univ,
      Fintype.card_fin,Fin.card_filter_val_lt,Nat.min_eq_right hk]
  have hm : a ∈ Z ∨ b ∈ Z := by simpa only [Z,Finset.mem_filter,Finset.mem_univ,true_and] using hmark
  have hb : ∀ v ∈ Z, (B.older v).card = 2 := by
    intro v hv
    exact hborn v (hrk.trans (Finset.mem_filter.mp hv).2)
  have hIP : B.suffixBoundary Z a b ⊆ initialVertices N k := by
    intro x hx
    have hnZ := (B.mem_suffixBoundary Z a b x).mp hx |>.2
    simp only [Z,Finset.mem_filter,Finset.mem_univ,true_and,not_le] at hnZ
    exact (mem_initialVertices N k x).mpr hnZ
  have hcover : initialVertices N k ∪ B.suffixVertices Z a b = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro x
    by_cases hx : x.val < k
    · exact Finset.mem_union_left _ ((mem_initialVertices N k x).mpr hx)
    · exact Finset.mem_union_right _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩))
  have hEF : B.suffixEdges Z a b ⊆
      insert ({a,b} : Finset (Fin N)) (B.backEdges Finset.univ) := by
    apply Finset.insert_subset_insert
    exact Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.subset_univ Z)
  have hf := graphEmbeddingSet_count_glue (B.suffixVertices Z a b) (B.suffixBoundary Z a b)
    (initialVertices N k) (B.suffixEdges Z a b) _ G B.suffixEdges_subset_vertices
    (B.suffixEdges_simple hab) (B.suffixBoundary_independent hm) hIP hcover hEF
    (B.initialAssignmentSet G k hk) (fun φ hφ => B.initialLabel_mem G hφ k hk)
    (prefixTemplateFactor n C) (by
      intro ξ _
      exact B.suffixTemplate_count hGood hab hm hb hne hc (hZ ▸ hcap) hp hp1 hD
        (hZ ▸ hscale) _)
  have hκ : 0 ≤ prefixTemplateFactor n C := by
    unfold prefixTemplateFactor
    positivity
  exact hf.trans (mul_le_mul_of_nonneg_left
    (B.initialAssignmentSet_bound_unordered hGood hsmall hp r k hrk hk hroot hborn) hκ)

end SharpTerminalLeave.BirthGraph

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Coupling_OrderEmbRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

lemma roots_le_card {N R : ℕ} (s : Finset (Fin N)) (hR : R ≤ N)
    (hroot : ∀ x : Fin N, x.val < R → x ∈ s) : R ≤ s.card := by
  have hsub : Finset.univ.filter (fun z : Fin N => z.val < R) ⊆ s := by
    intro z hz
    exact hroot z (Finset.mem_filter.mp hz).2
  have h := Finset.card_le_card hsub
  rwa [Fin.card_filter_val_lt,Nat.min_eq_right hR] at h

lemma orderEmb_initial {N R : ℕ} (s : Finset (Fin N)) (hR : R ≤ N)
    (hroot : ∀ x : Fin N, x.val < R → x ∈ s)
    (i : Fin s.card) (hi : i.val < R) : (s.orderEmbOfFin rfl i).val = i.val := by
  let x : Fin N := ⟨i.val,hi.trans_le hR⟩
  let j := (s.orderIsoOfFin rfl).symm ⟨x,hroot x hi⟩
  have hj : j = i := Fin.ext (initial_rank s hroot x hi)
  have he := congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨x,hroot x hi⟩)
  change s.orderEmbOfFin rfl j = x at he
  rw [hj] at he
  exact congrArg Fin.val he

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Probability_ProductPMFMeanProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

theorem productPMF_mean_product {K V : Type*} [Fintype K] [DecidableEq K] [Fintype V]
    (ρ : K → PMF V) (w : K → V → ℝ) :
    pmfMean (productPMF ρ) (fun ω => ∏ k, w k (ω k)) =
      ∏ k, pmfMean (ρ k) (w k) := by
  simp only [pmfMean, productPMF_apply, ENNReal.toReal_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun k v => (ρ k v).toReal * w k v)).symm

theorem uniform_prospective_failure (N : ℕ) [NeZero N] (t : ℕ) (q : Fin N → ℝ) :
    pmfMean (PMF.uniformOfFintype (Fin N))
      (fun u => if u.val < t then 1 - q u else 1) =
      1 - (∑ u : Fin N, if u.val < t then q u else 0) / (N : ℝ) := by
  have hpt : (fun u : Fin N => if u.val < t then 1 - q u else 1) =
      (fun u : Fin N => 1 - (if u.val < t then q u else 0)) := by
    funext u
    split_ifs <;> simp
  rw [hpt, pmfMean_sub, pmfMean_const]
  congr 1
  simp only [pmfMean, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, Fintype.card_fin, ← Finset.mul_sum, div_eq_mul_inv, mul_comm]

theorem offpattern_product_bound {K : Type*} [DecidableEq K]
    (C S : Finset K) (hSC : S ⊆ C) (hS : S.card ≤ 2) (f : K → ℝ) (b : ℝ)
    (hf : ∀ k ∈ C, (7 / 8 : ℝ) ≤ f k) (hfull : ∏ k ∈ C, f k ≤ (9 / 8 : ℝ) * b) :
    ∏ k ∈ C \ S, f k ≤ 2 * b := by
  have hn : ∀ k ∈ C, 0 ≤ f k := fun k hk => le_trans (by norm_num) (hf k hk)
  have hp : (7 / 8 : ℝ) ^ S.card ≤ ∏ k ∈ S, f k := by
    simpa only [Finset.prod_const] using Finset.prod_le_prod
      (fun k (_ : k ∈ S) => by norm_num : ∀ k ∈ S, (0 : ℝ) ≤ 7 / 8)
      (fun k hk => hf k (hSC hk))
  have hp' : (49 / 64 : ℝ) ≤ ∏ k ∈ S, f k := by
    have hc : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by omega
    rcases hc with h | h | h <;> rw [h] at hp <;> norm_num at hp ⊢ <;> linarith
  have ho : 0 ≤ ∏ k ∈ C \ S, f k := Finset.prod_nonneg
    (fun k hk => hn k (Finset.mem_sdiff.mp hk).1)
  have he : (∏ k ∈ S, f k) * (∏ k ∈ C \ S, f k) = ∏ k ∈ C, f k := by
    rw [mul_comm, Finset.prod_sdiff hSC]
  have hb : 0 ≤ b := by
    have hh : 0 ≤ ∏ k ∈ C, f k := Finset.prod_nonneg hn
    linarith
  have hm := mul_le_mul_of_nonneg_right hp' ho
  rw [he] at hm
  linarith

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_MarkedChild
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

theorem markedGood_nonneg (p : PMF (Bool × Bool)) : 0 ≤ markedGood p := by
  apply pmfMean_nonneg
  intro z _
  split <;> norm_num

theorem markedGood_le_one (p : PMF (Bool × Bool)) : markedGood p ≤ 1 := by
  rw [← pmfMean_const p 1]
  apply pmfMean_mono
  intro z _
  split <;> norm_num

theorem markedFailure_nonneg (p : PMF (Bool × Bool)) : 0 ≤ markedFailure p := by
  apply pmfMean_nonneg
  intro z _
  split <;> norm_num

theorem markedBound_nonneg (as : List MarkedChild) : 0 ≤ markedBound as := by
  induction as with
  | nil => exact zero_le_one
  | cons a as ih =>
    apply mul_nonneg _ ih
    split
    · exact markedGood_nonneg _
    · split
      · exact markedFailure_nonneg _
      · exact zero_le_one

theorem markedBound_of_no_demand (as : List MarkedChild) (h : markedDemand as = false) :
    markedBound as = 1 := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    have hh : a.required = false ∧ markedDemand as = false := by
      simpa only [markedDemand, Bool.or_eq_false_iff] using h
    simp [markedBound, hh.1, hh.2, ih hh.2]

theorem marked_visitation_bound (as : List MarkedChild) :
    markedGood (markedCheck as) ≤ markedBound as := by
  induction as with
  | nil => simp [markedGood, markedCheck, markedBound]
  | cons a as ih =>
    let f : Bool × Bool → ℝ := fun z =>
      if a.required then (if z.2 then 1 else 0)
      else if markedDemand as then (if z.1 then 0 else 1) else 1
    have hf : pmfMean a.law f =
        if a.required then markedGood a.law
        else if markedDemand as then markedFailure a.law else 1 := by
      cases hr : a.required <;> cases hd : markedDemand as <;>
        simp [f, hr, hd, markedGood, markedFailure]
    change pmfMean (a.law.bind _) _ ≤ _
    rw [pmfMean_bind]
    calc
      _ ≤ pmfMean a.law (fun z => f z * markedBound as) := by
        apply pmfMean_mono
        rintro ⟨b, g⟩ _
        have hb := markedBound_nonneg as
        have hg := markedGood_nonneg (markedCheck as)
        have hu := markedGood_le_one (markedCheck as)
        cases hr : a.required <;> cases hd : markedDemand as <;>
          cases b <;> cases g <;>
          simp only [hr, hd, Bool.not_false, Bool.not_true, Bool.false_or,
            Bool.true_or, Bool.false_and, Bool.true_and, Bool.and_false,
            Bool.and_true, Bool.false_eq_true, ↓reduceIte,
            pmfMean_pure, pmfMean_map, f, pmfMean_const,
            zero_mul, one_mul]
        all_goals first
          | exact ih
          | exact hb
          | exact le_refl _
          | simpa only [markedBound_of_no_demand as hd] using hu
          | simp only [markedBound_of_no_demand as hd, le_refl]
      _ = markedBound (a :: as) := by
        rw [pmfMean_mul_const, hf]
        rfl

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_ChargesCovered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

theorem markedFailure_le_one (p : PMF (Bool × Bool)) : markedFailure p ≤ 1 := by
  rw [← pmfMean_const p 1]
  apply pmfMean_mono
  intro z _
  split <;> norm_num

theorem chargedFactor_nonneg (c : MarkedChild → Bool) (a : MarkedChild) :
    0 ≤ chargedFactor c a := by
  unfold chargedFactor
  split
  · exact markedGood_nonneg _
  · split
    · exact markedFailure_nonneg _
    · exact zero_le_one

theorem markedBound_le_charged (charge : MarkedChild → Bool) (as : List MarkedChild)
    (hc : ChargesCovered charge as) :
    markedBound as ≤ (as.map (chargedFactor charge)).prod := by
  induction as with
  | nil => exact le_refl _
  | cons a as ih =>
    have hc' : ChargesCovered charge as := by
      intro pre b post hh hb hch
      apply hc (a :: pre) b post
      · simp only [List.cons_append, hh]
      · exact hb
      · exact hch
    have hpoint :
        (if a.required then markedGood a.law
          else if markedDemand as then markedFailure a.law else 1) ≤
        chargedFactor charge a := by
      by_cases hr : a.required = true
      · simp [chargedFactor, hr]
      · have hr' : a.required = false := Bool.eq_false_iff.mpr hr
        by_cases hq : charge a = true
        · have hd := hc [] a as rfl hr' hq
          simp [chargedFactor, hr', hq, hd]
        · simp only [chargedFactor, hr', Bool.false_eq_true, ↓reduceIte, hq]
          split
          · exact markedFailure_le_one _
          · exact le_refl _
    change _ * _ ≤ _ * _
    exact mul_le_mul hpoint (ih hc') (markedBound_nonneg as) (chargedFactor_nonneg _ _)

theorem marked_visitation_charged (charge : MarkedChild → Bool) (as : List MarkedChild)
    (hc : ChargesCovered charge as) :
    markedGood (markedCheck as) ≤ (as.map (chargedFactor charge)).prod :=
  (marked_visitation_bound as).trans (markedBound_le_charged charge as hc)

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_MarkedDemand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

theorem markedDemand_iff (as : List MarkedChild) :
    markedDemand as = true ↔ ∃ a ∈ as, a.required = true := by
  induction as with
  | nil => simp [markedDemand]
  | cons a as ih => simp [markedDemand, ih, or_and_right, exists_or]

theorem priority_charges_covered (as : List MarkedChild) (t : ℕ)
    (hs : as.Pairwise (fun a b => a.priority ≤ b.priority))
    (ht : ∃ b ∈ as, b.required = true ∧ t ≤ b.priority) :
    ChargesCovered (fun a => decide (a.priority < t)) as := by
  intro pre a post heq _ hcharge
  have ha : a.priority < t := of_decide_eq_true hcharge
  rcases ht with ⟨b, hb, hbr, hbt⟩
  rw [heq, List.mem_append] at hb
  have hp := List.pairwise_append.mp (heq ▸ hs)
  have hbp : b ∈ post := by
    rcases hb with hb | hb
    · have hle := hp.2.2 b hb a (by simp)
      omega
    · simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · omega
      · exact hb
  exact (markedDemand_iff post).mpr ⟨b, hbp, hbr⟩

theorem marked_visitation_priority (as : List MarkedChild) (t : ℕ)
    (hs : as.Pairwise (fun a b => a.priority ≤ b.priority))
    (ht : ∃ b ∈ as, b.required = true ∧ t ≤ b.priority) :
    markedGood (markedCheck as) ≤
      (as.map (chargedFactor (fun a => decide (a.priority < t)))).prod :=
  marked_visitation_charged _ _ (priority_charges_covered as t hs ht)

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_MarkedSuccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

@[simp] theorem markedFailure_eq_one_sub (p : PMF (Bool × Bool)) :
    markedFailure p = 1 - markedSuccess p := by
  unfold markedFailure markedSuccess
  rw [← pmfMean_const p 1, ← pmfMean_sub]
  apply pmfMean_congr
  intro z _
  cases z.1 <;> simp

theorem selectedClockLaw_support {K : Type*} [Fintype K] [DecidableEq K]
    (N : ℕ) [NeZero N] (S : Finset K) (σ ω : K → Fin N)
    (hω : ω ∈ (productPMF (selectedClockLaw N S σ)).support) :
    ∀ k ∈ S, ω k = σ k := by
  intro k hk
  have h := (productPMF_support _ ω).mp hω k
  simpa [selectedClockLaw,hk] using h

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_ProspectiveFailure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

@[simp] theorem markedGood_bind {α : Type*} [Fintype α] (π : PMF α)
    (p : α → PMF (Bool × Bool)) :
    markedGood (π.bind p) = pmfMean π (fun a => markedGood (p a)) :=
  pmfMean_bind π p _

@[simp] theorem markedGood_no_marks (p : PMF Bool) :
    markedGood (p.map (fun b => (b,true))) = 1 := by
  rw [markedGood,pmfMean_map]
  simp only [↓reduceIte,pmfMean_const]

@[simp] theorem markedSuccess_no_marks (p : PMF Bool) :
    markedSuccess (p.map (fun b => (b,true))) = (p true).toReal := by
  rw [markedSuccess,pmfMean_map]
  simp [pmfMean]

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_OrderedMarkedRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

theorem orderedMarkedRow_sorted {K : Type*} [DecidableEq K] {N : ℕ}
    (order : List K) (S : Finset K) (p : K → Fin N → PMF (Bool × Bool))
    (deadline : ℕ) (ω : K → Fin N) :
    (orderedMarkedRow order S p deadline ω).Pairwise (fun a b => a.priority ≤ b.priority) := by
  unfold orderedMarkedRow
  simpa only [decide_eq_true_eq] using List.pairwise_mergeSort
    (le := fun a b : MarkedChild => decide (a.priority ≤ b.priority))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true,decide_eq_true_eq]; omega) _

theorem orderedMarkedRow_factor_product {K : Type*} [Fintype K] [DecidableEq K] {N : ℕ}
    (order : List K) (horder : order.Perm Finset.univ.toList)
    (S : Finset K) (p : K → Fin N → PMF (Bool × Bool))
    (deadline t : ℕ) (ω : K → Fin N) :
    ((orderedMarkedRow order S p deadline ω).map
      (chargedFactor (fun a => decide (a.priority < t)))).prod =
    ∏ k, chargedFactor (fun a => decide (a.priority < t)) (rowChild S p deadline ω k) := by
  unfold orderedMarkedRow
  rw [(List.mergeSort_perm _ _).map _ |>.prod_eq,List.map_map]
  rw [(horder.map _).prod_eq]
  exact Finset.prod_map_toList _ _

theorem orderedMarkedRow_pointwise {K : Type*} [Fintype K] [DecidableEq K] {N : ℕ}
    (order : List K) (horder : order.Perm Finset.univ.toList)
    (S : Finset K) (p : K → Fin N → PMF (Bool × Bool))
    (deadline t : ℕ) (htd : t ≤ deadline) (ω : K → Fin N)
    (hsel : ∀ k ∈ S, (ω k).val < deadline)
    (ht : ∃ k ∈ S, t ≤ (ω k).val) :
    markedGood (markedCheck (orderedMarkedRow order S p deadline ω)) ≤
      ∏ k, if k ∈ S then markedGood (p k (ω k))
        else if (ω k).val < t then markedFailure (p k (ω k)) else 1 := by
  have hw : ∃ a ∈ orderedMarkedRow order S p deadline ω,
      a.required = true ∧ t ≤ a.priority := by
    obtain ⟨k,hk,hkt⟩ := ht
    refine ⟨rowChild S p deadline ω k, ?_, ?_, hkt⟩
    · simp only [orderedMarkedRow,List.mem_mergeSort,List.mem_map]
      exact ⟨k,horder.mem_iff.mpr (by simp),rfl⟩
    · simpa only [rowChild,decide_eq_true_eq] using hk
  have hb := marked_visitation_priority _ t (orderedMarkedRow_sorted order S p deadline ω) hw
  rw [orderedMarkedRow_factor_product order horder] at hb
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.prod_congr rfl
  intro k _
  by_cases hk : k ∈ S
  · simp [chargedFactor,rowChild,hk,hsel k hk]
  · by_cases hkt : (ω k).val < t
    · have hkd : (ω k).val < deadline := lt_of_lt_of_le hkt htd
      simp [chargedFactor,rowChild,hk,hkt,hkd]
    · simp [chargedFactor,rowChild,hk,hkt]

theorem orderedMarkedRow_integrated {K : Type*} [Fintype K] [DecidableEq K]
    (N : ℕ) [NeZero N] (order : List K) (horder : order.Perm Finset.univ.toList)
    (S : Finset K) (σ : K → Fin N)
    (p : K → Fin N → PMF (Bool × Bool)) (deadline t : ℕ)
    (htd : t ≤ deadline) (hsel : ∀ k ∈ S, (σ k).val < deadline)
    (ht : ∃ k ∈ S, t ≤ (σ k).val) :
    pmfMean (productPMF (selectedClockLaw N S σ))
      (fun ω => markedGood (markedCheck (orderedMarkedRow order S p deadline ω))) ≤
    ∏ k, if k ∈ S then markedGood (p k (σ k)) else
      1 - (∑ u : Fin N, if u.val < t then markedSuccess (p k u) else 0) / (N : ℝ) := by
  calc
    _ ≤ pmfMean (productPMF (selectedClockLaw N S σ))
        (fun ω => ∏ k, if k ∈ S then markedGood (p k (ω k))
          else if (ω k).val < t then markedFailure (p k (ω k)) else 1) := by
      apply pmfMean_mono
      intro ω hω
      have he := selectedClockLaw_support N S σ ω hω
      apply orderedMarkedRow_pointwise order horder S p deadline t htd ω
      · intro k hk
        simpa only [he k hk] using hsel k hk
      · obtain ⟨k,hk,htk⟩ := ht
        exact ⟨k,hk,by rwa [he k hk]⟩
    _ = _ := by
      rw [productPMF_mean_product (selectedClockLaw N S σ)
        (fun k u => if k ∈ S then markedGood (p k u)
          else if u.val < t then markedFailure (p k u) else 1)]
      apply Finset.prod_congr rfl
      intro k _
      by_cases hk : k ∈ S
      · simp [selectedClockLaw,hk]
      · simp only [selectedClockLaw,hk,↓reduceIte,markedFailure_eq_one_sub]
        exact uniform_prospective_failure N t (fun u => markedSuccess (p k u))

theorem orderedMarkedRow_cavity_bound {K : Type*} [Fintype K] [DecidableEq K]
    (N : ℕ) [NeZero N] (order : List K) (horder : order.Perm Finset.univ.toList)
    (S : Finset K) (σ : K → Fin N)
    (p : K → Fin N → PMF (Bool × Bool)) (q : K → Fin N → ℝ)
    (deadline t : ℕ) (htd : t ≤ deadline) (hsel : ∀ k ∈ S, (σ k).val < deadline)
    (ht : ∃ k ∈ S, t ≤ (σ k).val) (hS : S.card ≤ 2)
    (hmarg : ∀ k ∉ S, ∀ u, markedSuccess (p k u) = q k u)
    (b : ℝ) (hfactor : ∀ k, (7 / 8 : ℝ) ≤ prospectiveFailure N t (q k))
    (hfull : ∏ k, prospectiveFailure N t (q k) ≤ (9 / 8 : ℝ) * b) :
    markedGood ((productPMF (selectedClockLaw N S σ)).bind
      (fun ω => markedCheck (orderedMarkedRow order S p deadline ω))) ≤
      (∏ k ∈ S, markedGood (p k (σ k))) * (2 * b) := by
  rw [markedGood_bind]
  have h := orderedMarkedRow_integrated N order horder S σ p deadline t htd hsel ht
  let f : K → ℝ := fun k => prospectiveFailure N t (q k)
  have he : (∏ k, if k ∈ S then markedGood (p k (σ k)) else
      1 - (∑ u : Fin N, if u.val < t then markedSuccess (p k u) else 0) / (N : ℝ)) =
      (∏ k ∈ S, markedGood (p k (σ k))) * (∏ k ∈ Finset.univ \ S, f k) := by
    have hp : (fun k => if k ∈ S then markedGood (p k (σ k)) else
        1 - (∑ u : Fin N, if u.val < t then markedSuccess (p k u) else 0) / (N : ℝ)) =
        (fun k => if k ∈ S then markedGood (p k (σ k)) else f k) := by
      funext k
      by_cases hk : k ∈ S
      · simp only [hk,↓reduceIte]
      · simp only [hk,↓reduceIte,f,prospectiveFailure,hmarg k hk]
    rw [hp,Finset.prod_ite]
    congr 1
    · congr 1
      ext k
      simp
    · congr 1
      ext k
      simp
  rw [he] at h
  have hf := offpattern_product_bound Finset.univ S (Finset.subset_univ S) hS f b
    (fun k _ => hfactor k) hfull
  exact h.trans (mul_le_mul_of_nonneg_left hf (Finset.prod_nonneg
    (fun k _ => markedGood_nonneg (p k (σ k)))))

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_OrderedMarkedRowUnweighted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

theorem orderedMarkedRow_unweighted {K : Type*} [Fintype K] [DecidableEq K] {N : ℕ}
    (order : List K) (horder : order.Perm Finset.univ.toList)
    (S : Finset K) (p : K → Fin N → PMF (Bool × Bool)) (deadline : ℕ) (ω : K → Fin N) :
    markedGood (markedCheck (orderedMarkedRow order S p deadline ω)) ≤
      ∏ k ∈ S, if (ω k).val < deadline then markedGood (p k (ω k)) else 0 := by
  have hc : ChargesCovered (fun _ => false) (orderedMarkedRow order S p deadline ω) := by
    intro pre a post hh ha hb
    simp at hb
  have hb := marked_visitation_charged _ _ hc
  refine hb.trans_eq ?_
  unfold orderedMarkedRow
  rw [(List.mergeSort_perm _ _).map _ |>.prod_eq,List.map_map,(horder.map _).prod_eq,
    Finset.prod_map_toList]
  calc
    _ = ∏ k, if k ∈ S then
        (if (ω k).val < deadline then markedGood (p k (ω k)) else 0) else 1 := by
      apply Finset.prod_congr rfl
      intro k _
      by_cases hk : k ∈ S
      · by_cases hu : (ω k).val < deadline
        · simp [chargedFactor,rowChild,hk,hu]
        · simp [chargedFactor,rowChild,hk,hu,markedGood]
      · simp [chargedFactor,rowChild,hk]
    _ = _ := by
      rw [Finset.prod_ite]
      simp only [Finset.prod_const_one,mul_one]
      congr 1
      ext k
      simp

theorem orderedMarkedRow_forbidden {K : Type*} [Fintype K] [DecidableEq K] {N : ℕ}
    (order : List K) (horder : order.Perm Finset.univ.toList)
    (S : Finset K) (p : K → Fin N → PMF (Bool × Bool)) (deadline : ℕ) (ω : K → Fin N)
    (k : K) (hk : k ∈ S) (hu : deadline ≤ (ω k).val) :
    markedGood (markedCheck (orderedMarkedRow order S p deadline ω)) = 0 := by
  apply le_antisymm _ (markedGood_nonneg _)
  have hb := orderedMarkedRow_unweighted order horder S p deadline ω
  have hz : (∏ a ∈ S, if (ω a).val < deadline then markedGood (p a (ω a)) else 0) = 0 := by
    apply Finset.prod_eq_zero hk
    simp only [not_lt_of_ge hu,↓reduceIte]
  rwa [hz] at hb

theorem selectedClockLaw_singleton {K : Type*} [DecidableEq K]
    (N : ℕ) [NeZero N] (a : K) (u : Fin N) :
    selectedClockLaw N {a} (fun _ => u) =
      Function.update (fun _ : K => PMF.uniformOfFintype (Fin N)) a (PMF.pure u) := by
  funext k
  by_cases hk : k = a
  · subst k
    simp [selectedClockLaw]
  · simp [selectedClockLaw,hk]

theorem marked_row_single_path {K : Type*} [Fintype K] [DecidableEq K]
    (N : ℕ) [NeZero N] (order : List K) (horder : order.Perm Finset.univ.toList)
    (a : K) (p : K → Fin N → PMF (Bool × Bool)) (q : K → Fin N → ℝ)
    (deadline : ℕ) (b : ℕ → ℝ)
    (hmarg : ∀ k ≠ a, ∀ u, markedSuccess (p k u) = q k u)
    (hfactor : ∀ t < deadline, ∀ k, (7 / 8 : ℝ) ≤ prospectiveFailure N t (q k))
    (hfull : ∀ t < deadline, ∏ k, prospectiveFailure N t (q k) ≤ (9 / 8 : ℝ) * b t) :
    markedGood ((productPMF (fun _ : K => PMF.uniformOfFintype (Fin N))).bind
      (fun ω => markedCheck (orderedMarkedRow order {a} p deadline ω))) ≤
      (1 / (N : ℝ)) * ∑ u : Fin N,
        if u.val < deadline then markedGood (p a u) * (2 * b u.val) else 0 := by
  rw [productPMF_split (fun _ : K => PMF.uniformOfFintype (Fin N)) a,
    PMF.bind_bind,markedGood_bind]
  have hpoint : ∀ u : Fin N,
      markedGood ((productPMF (Function.update (fun _ : K => PMF.uniformOfFintype (Fin N))
        a (PMF.pure u))).bind
        (fun ω => markedCheck (orderedMarkedRow order {a} p deadline ω))) ≤
      if u.val < deadline then markedGood (p a u) * (2 * b u.val) else 0 := by
    intro u
    rw [← selectedClockLaw_singleton N a u]
    by_cases hu : u.val < deadline
    · simp only [hu,↓reduceIte]
      have hs : ∀ k ∈ ({a} : Finset K), ((fun _ => u) k).val < deadline := by
        intro k _
        exact hu
      have ht : ∃ k ∈ ({a} : Finset K), u.val ≤ ((fun _ => u) k).val := ⟨a,by simp,le_rfl⟩
      simpa only [Finset.prod_singleton] using orderedMarkedRow_cavity_bound N order horder {a}
        (fun _ => u) p q deadline u.val (Nat.le_of_lt hu) hs ht (by simp)
        (fun k hk v => hmarg k (by simpa only [Finset.mem_singleton] using hk) v)
        (b u.val) (hfactor u.val hu) (hfull u.val hu)
    · simp only [hu,↓reduceIte]
      rw [markedGood_bind]
      apply le_trans (pmfMean_mono _ (g := fun _ => 0) ?_) (by simp)
      intro ω hω
      have he := selectedClockLaw_support N {a} (fun _ => u) ω hω a (by simp)
      rw [orderedMarkedRow_forbidden order horder {a} p deadline ω a (by simp)
        (by simpa only [he] using Nat.le_of_not_gt hu)]
  calc
    _ ≤ pmfMean (PMF.uniformOfFintype (Fin N))
        (fun u => if u.val < deadline then markedGood (p a u) * (2 * b u.val) else 0) :=
      pmfMean_mono _ (fun u _ => hpoint u)
    _ = _ := by
      simp only [pmfMean,PMF.uniformOfFintype_apply,ENNReal.toReal_inv,
        ENNReal.toReal_natCast,Fintype.card_fin,one_div,Finset.mul_sum]

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Coupling_SelectedClockLawPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

theorem selectedClockLaw_pair {K : Type*} [DecidableEq K]
    (N : ℕ) [NeZero N] (a b : K) (hab : a ≠ b) (u v : Fin N) :
    selectedClockLaw N {a,b} (Function.update (fun _ => v) a u) =
      Function.update (Function.update (fun _ : K => PMF.uniformOfFintype (Fin N))
        a (PMF.pure u)) b (PMF.pure v) := by
  funext k
  by_cases hka : k = a
  · subst k
    simp [selectedClockLaw,hab]
  · by_cases hkb : k = b
    · subst k
      simp [selectedClockLaw,hka]
    · simp [selectedClockLaw,hka,hkb]

theorem productPMF_split_two_uniform {K : Type*} [Fintype K] [DecidableEq K]
    (N : ℕ) [NeZero N] (a b : K) (hab : a ≠ b) :
    productPMF (fun _ : K => PMF.uniformOfFintype (Fin N)) =
      (PMF.uniformOfFintype (Fin N)).bind (fun u =>
        (PMF.uniformOfFintype (Fin N)).bind (fun v =>
          productPMF (selectedClockLaw N {a,b} (Function.update (fun _ => v) a u)))) := by
  rw [productPMF_split (fun _ : K => PMF.uniformOfFintype (Fin N)) a]
  congr 1
  funext u
  rw [productPMF_split (Function.update (fun _ : K => PMF.uniformOfFintype (Fin N))
    a (PMF.pure u)) b,Function.update_of_ne hab.symm]
  congr 1
  funext v
  rw [selectedClockLaw_pair N a b hab u v]

theorem marked_row_two_paths {K : Type*} [Fintype K] [DecidableEq K]
    (N : ℕ) [NeZero N] (order : List K) (horder : order.Perm Finset.univ.toList)
    (a b : K) (hab : a ≠ b) (p : K → Fin N → PMF (Bool × Bool))
    (q : K → Fin N → ℝ) (deadline : ℕ) (w : ℕ → ℝ)
    (hmarg : ∀ k ∉ ({a,b} : Finset K), ∀ u, markedSuccess (p k u) = q k u)
    (hfactor : ∀ t < deadline, ∀ k, (7 / 8 : ℝ) ≤ prospectiveFailure N t (q k))
    (hfull : ∀ t < deadline, ∏ k, prospectiveFailure N t (q k) ≤ (9 / 8 : ℝ) * w t) :
    markedGood ((productPMF (fun _ : K => PMF.uniformOfFintype (Fin N))).bind
      (fun ω => markedCheck (orderedMarkedRow order {a,b} p deadline ω))) ≤
      (1 / (N : ℝ)) * ∑ u : Fin N, (1 / (N : ℝ)) * ∑ v : Fin N,
        if u.val < deadline ∧ v.val < deadline then
          (markedGood (p a u) * markedGood (p b v)) * (2 * w (max u.val v.val))
        else 0 := by
  rw [productPMF_split_two_uniform N a b hab,PMF.bind_bind,markedGood_bind]
  have hpoint : ∀ u v : Fin N,
      markedGood ((productPMF (selectedClockLaw N {a,b}
        (Function.update (fun _ => v) a u))).bind
        (fun ω => markedCheck (orderedMarkedRow order {a,b} p deadline ω))) ≤
      if u.val < deadline ∧ v.val < deadline then
        (markedGood (p a u) * markedGood (p b v)) * (2 * w (max u.val v.val)) else 0 := by
    intro u v
    let σ : K → Fin N := Function.update (fun _ => v) a u
    have hσa : σ a = u := Function.update_self ..
    have hσb : σ b = v := Function.update_of_ne hab.symm ..
    by_cases huv : u.val < deadline ∧ v.val < deadline
    · rw [ite_eq_left huv]
      have htd : max u.val v.val < deadline := max_lt huv.1 huv.2
      have hsel : ∀ k ∈ ({a,b} : Finset K), (σ k).val < deadline := by
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · simpa only [hσa] using huv.1
        · have he : k = b := Finset.mem_singleton.mp hk
          simpa only [he,hσb] using huv.2
      have ht : ∃ k ∈ ({a,b} : Finset K), max u.val v.val ≤ (σ k).val := by
        by_cases h : u.val ≤ v.val
        · exact ⟨b,by simp,by simp only [hσb,max_eq_right h,le_refl]⟩
        · exact ⟨a,by simp,by simp only [hσa,max_eq_left (le_of_not_ge h),le_refl]⟩
      have hh := orderedMarkedRow_cavity_bound N order horder {a,b} σ p q deadline
        (max u.val v.val) (Nat.le_of_lt htd) hsel ht (by simp [hab]) hmarg
        (w (max u.val v.val)) (hfactor _ htd) (hfull _ htd)
      simpa only [Finset.prod_pair hab,hσa,hσb] using hh
    · rw [ite_eq_right huv]
      rw [markedGood_bind]
      apply le_trans (pmfMean_mono _ (g := fun _ => 0) ?_) (by simp)
      intro ω hω
      have hsa := selectedClockLaw_support N {a,b} σ ω hω a (by simp)
      have hsb := selectedClockLaw_support N {a,b} σ ω hω b (by simp)
      by_cases hu : u.val < deadline
      · have hv : deadline ≤ v.val := by omega
        rw [orderedMarkedRow_forbidden order horder {a,b} p deadline ω b (by simp)
          (by simpa only [hsb,hσb] using hv)]
      · rw [orderedMarkedRow_forbidden order horder {a,b} p deadline ω a (by simp)
          (by simpa only [hsa,hσa] using Nat.le_of_not_gt hu)]
  calc
    _ ≤ pmfMean (PMF.uniformOfFintype (Fin N)) (fun u =>
        pmfMean (PMF.uniformOfFintype (Fin N)) (fun v =>
          if u.val < deadline ∧ v.val < deadline then
            (markedGood (p a u) * markedGood (p b v)) * (2 * w (max u.val v.val)) else 0)) := by
      apply pmfMean_mono
      intro u _
      rw [PMF.bind_bind,markedGood_bind]
      exact pmfMean_mono _ (fun v _ => hpoint u v)
    _ = _ := by
      simp only [pmfMean,PMF.uniformOfFintype_apply,ENNReal.toReal_inv,
        ENNReal.toReal_natCast,Fintype.card_fin,one_div,Finset.mul_sum]

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_ProgramDemand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave
namespace ExposureTree
variable {K V O A : Type*}

theorem fresh_checkMarked (ν : K → PMF V)
    (as : List (Bool × ExposureTree K V (Bool × Bool))) :
    fresh ν (checkMarked as) =
      markedCheck (as.map (fun a => (⟨a.1,fresh ν a.2,0⟩ : MarkedChild))) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [checkMarked,fresh_bind,List.map_cons,markedCheck]
    congr 1
    funext z
    cases z.1 <;> simp only [Bool.false_eq_true,↓reduceIte,fresh,fresh_mapOutput,
      ih,programDemand_law]

theorem checkMarked_outcome
    (as : List (Bool × ExposureTree K V (Bool × Bool))) :
    mapOutput Prod.fst (checkMarked as) =
      checkNone (as.map (fun a => mapOutput Prod.fst a.2)) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [checkMarked,mapOutput_bind,List.map_cons,checkNone,bind_mapOutput]
    congr 1
    funext z
    cases z.1 <;> simp only [Bool.false_eq_true,↓reduceIte,mapOutput_done,mapOutput_comp]
    exact ih

theorem exposeLabeled_table [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]
    (ν : K → PMF V) (key : A → K) (as : List A) (ha : as.Nodup)
    (ρ : A → PMF V) (hρ : ∀ a ∈ as, ρ a = ν (key a)) :
    (productPMF ρ).map (fun ω => as.map (fun a => (a,ω a))) =
      fresh ν (exposeLabeled key as) := by
  induction as generalizing ρ with
  | nil => exact PMF.map_const (productPMF ρ) []
  | cons a as ih =>
    obtain ⟨hna,hn⟩ := List.nodup_cons.mp ha
    rw [productPMF_split ρ a,PMF.map_bind,hρ a (List.mem_cons_self)]
    simp only [exposeLabeled,fresh,fresh_bind]
    congr 1
    funext v
    have hx : (productPMF (Function.update ρ a (PMF.pure v))).map
        (fun ω => (a,ω a) :: as.map (fun b => (b,ω b))) =
        (productPMF (Function.update ρ a (PMF.pure v))).map
        (fun ω => (a,v) :: as.map (fun b => (b,ω b))) := by
      apply pmf_bind_congr_on_support
      intro ω hω
      have hw := (productPMF_support _ ω).mp hω a
      have hv : ω a = v := by simpa using hw
      dsimp only [Function.comp_def]
      rw [hv]
    change (productPMF (Function.update ρ a (PMF.pure v))).map
      (fun ω => (a,ω a) :: as.map (fun b => (b,ω b))) = _
    rw [hx]
    have hh := ih hn (Function.update ρ a (PMF.pure v)) (by
      intro b hb
      have hba : b ≠ a := fun he => hna (he ▸ hb)
      rw [Function.update_of_ne hba]
      exact hρ b (List.mem_cons_of_mem _ hb))
    change (productPMF (Function.update ρ a (PMF.pure v))).map
      ((fun xs => (a,v) :: xs) ∘ (fun ω => as.map (fun b => (b,ω b)))) = _
    rw [← PMF.map_comp,hh]
    rfl

end ExposureTree

section MarkedGrid
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem markedGridQueryDepth_outcome (H : τ → Finset ι) (N : ℕ)
    (required : List (ι × τ) → Bool) (d k : ℕ) (address : List (ι × τ))
    (focus : Finset ι) (parent : Option τ) :
    ExposureTree.mapOutput Prod.fst
      (markedGridQueryDepth H N required d k address focus parent) =
      gridQueryDepth H N d k focus parent := by
  induction d generalizing k address focus parent with
  | zero => simp only [markedGridQueryDepth,gridQueryDepth,ExposureTree.mapOutput_bind,
      ExposureTree.mapOutput_done]
  | succ d ih =>
    simp only [markedGridQueryDepth,gridQueryDepth,ExposureTree.mapOutput_bind]
    congr 1
    funext values
    rw [ExposureTree.checkMarked_outcome,List.map_map]
    congr 1
    apply List.map_congr_left
    intro p _
    dsimp only [Function.comp_def]
    split
    · exact ih _ _ _ _
    · rfl

end MarkedGrid
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_MarkedRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

theorem markedDemand_map_priority {A : Type*} (as : List A)
    (req : A → Bool) (law : A → PMF (Bool × Bool)) (s t : A → ℕ) :
    markedDemand (as.map (fun a => (⟨req a,law a,s a⟩ : MarkedChild))) =
      markedDemand (as.map (fun a => (⟨req a,law a,t a⟩ : MarkedChild))) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons,markedDemand,ih]

theorem markedCheck_map_priority {A : Type*} (as : List A)
    (req : A → Bool) (law : A → PMF (Bool × Bool)) (s t : A → ℕ) :
    markedCheck (as.map (fun a => (⟨req a,law a,s a⟩ : MarkedChild))) =
      markedCheck (as.map (fun a => (⟨req a,law a,t a⟩ : MarkedChild))) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons,markedCheck,ih,
      markedDemand_map_priority as req law s t]

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_FinsetCandidateOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

lemma finsetCandidateOrder_map {A : Type*} [DecidableEq A] (C : Finset A) :
    (finsetCandidateOrder C).map Subtype.val = C.toList := by
  simp only [finsetCandidateOrder,List.map_map,Function.comp_def]
  simp

lemma finsetCandidateOrder_perm {A : Type*} [DecidableEq A] (C : Finset A) :
    (finsetCandidateOrder C).Perm (Finset.univ : Finset C).toList := by
  have hn : (finsetCandidateOrder C).Nodup := List.Nodup.of_map Subtype.val (by
    rw [finsetCandidateOrder_map]
    exact Finset.nodup_toList _)
  apply (List.perm_ext_iff_of_nodup hn (Finset.nodup_toList _)).mpr
  intro a
  simp only [Finset.mem_toList,Finset.mem_univ,iff_true]
  apply List.mem_map.mpr
  exact ⟨⟨a.val,Finset.mem_toList.mpr a.property⟩,List.mem_attach _ _,by apply Subtype.ext; rfl⟩

namespace ExposureTree
variable {K A B V : Type*}
lemma exposeLabeled_relabel (key : B → K) (f : A → B) (as : List A) :
    mapOutput (List.map (fun p : A × V => (f p.1,p.2)))
      (exposeLabeled (key ∘ f) as) = exposeLabeled key (as.map f) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [exposeLabeled,List.map_cons,mapOutput,mapOutput_bind]
    congr 1
    funext v
    rw [← ih]
    rw [bind_mapOutput]
end ExposureTree

section CandidateKernel
variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

omit [Fintype ι] in
lemma candidate_clock_table (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (focus : Finset ι) (parent : Option τ) :
    (productPMF (fun _ : gridCandidates H focus parent => PMF.uniformOfFintype (Fin N))).map
      (fun ω => (finsetCandidateOrder (gridCandidates H focus parent)).map
        (fun a => (a.val,ω a))) =
    ExposureTree.fresh (fun _ : τ => PMF.uniformOfFintype (Fin N))
      (ExposureTree.exposeLabeled Prod.snd (gridCandidates H focus parent).toList) := by
  let C := gridCandidates H focus parent
  let order := finsetCandidateOrder C
  have ho : order.Nodup := (finsetCandidateOrder_perm C).nodup_iff.mpr (Finset.nodup_toList _)
  have htable := ExposureTree.exposeLabeled_table
    (fun _ : τ => PMF.uniformOfFintype (Fin N)) (fun a : C => a.val.2)
    order ho (fun _ : C => PMF.uniformOfFintype (Fin N)) (by intros; rfl)
  have hm := congrArg (PMF.map (List.map (fun p : C × Fin N => (p.1.val,p.2)))) htable
  rw [PMF.map_comp,← ExposureTree.fresh_mapOutput] at hm
  simp only [Function.comp_def,List.map_map] at hm
  have he := ExposureTree.exposeLabeled_relabel (V := Fin N) Prod.snd
    (Subtype.val : C → ι × τ) order
  dsimp only [Function.comp_def] at he
  rw [he] at hm
  simpa only [order,C,finsetCandidateOrder_map] using hm

omit [Fintype ι] in

theorem markedGridQueryDepth_candidate_kernel (H : τ → Finset ι)
    (N : ℕ) [NeZero N] (required : List (ι × τ) → Bool)
    (d k : ℕ) (address : List (ι × τ)) (focus : Finset ι) (parent : Option τ) :
    ExposureTree.fresh (fun _ : τ => PMF.uniformOfFintype (Fin N))
      (markedGridQueryDepth H N required (d+1) k address focus parent) =
    (productPMF (fun _ : gridCandidates H focus parent => PMF.uniformOfFintype (Fin N))).bind
      (fun ω => markedCheck (orderedMarkedRow
        (finsetCandidateOrder (gridCandidates H focus parent))
        (requiredCandidates H required address focus parent)
        (markedChildKernel H N required d address focus parent) k ω)) := by
  classical
  rw [markedGridQueryDepth,ExposureTree.fresh_bind,← candidate_clock_table H N focus parent,
    PMF.bind_map]
  congr 1
  funext ω
  dsimp only [Function.comp_def]
  rw [ExposureTree.fresh_checkMarked]
  simp only [List.map_map,Function.comp_def]
  let order := finsetCandidateOrder (gridCandidates H focus parent)
  let as := (order.map (fun a => (a.val,ω a))).mergeSort (fun a b => a.2.val ≤ b.2.val)
  have hp := markedCheck_map_priority as
    (fun p => required (p.1 :: address))
    (fun p => if p.2.val < k then ExposureTree.fresh (fun _ : τ => PMF.uniformOfFintype (Fin N))
      (markedGridQueryDepth H N required d p.2.val (p.1 :: address)
        ((H p.1.2).erase p.1.1) (some p.1.2)) else PMF.pure (false,false))
    (fun _ => 0) (fun p => p.2.val)
  calc
    _ = markedCheck (as.map (fun p => (⟨required (p.1 :: address),
        if p.2.val < k then ExposureTree.fresh (fun _ : τ => PMF.uniformOfFintype (Fin N))
          (markedGridQueryDepth H N required d p.2.val (p.1 :: address)
            ((H p.1.2).erase p.1.1) (some p.1.2)) else PMF.pure (false,false),0⟩ : MarkedChild))) := by
      congr 1
      apply List.map_congr_left
      intro p _
      split <;> rfl
    _ = _ := by
      rw [hp]
      congr 1
      dsimp only [as]
      rw [List.map_mergeSort (s := fun a b : MarkedChild => decide (a.priority ≤ b.priority))
        (by intros; rfl),List.map_map]
      unfold orderedMarkedRow
      congr 1
      apply List.map_congr_left
      intro a _
      dsimp [rowChild,markedChildKernel]
      simp only [requiredCandidates,Finset.mem_filter,Finset.mem_univ,true_and]
      cases required (a.val :: address) <;> rfl

end CandidateKernel
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Probability_MarkedSuccessTrueProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

lemma markedSuccess_eq_trueProbability_fst (p : PMF (Bool × Bool)) :
    markedSuccess p = trueProbability (p.map Prod.fst) := by
  have hp := pmfMean_map p Prod.fst (fun b : Bool => if b then (1:ℝ) else 0)
  rw [← markedSuccess] at hp
  rw [← hp]
  simp [pmfMean,trueProbability]

section CandidateMarginal
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem markedChildKernel_success (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (required : List (ι × τ) → Bool) (d : ℕ) (address : List (ι × τ))
    (focus : Finset ι) (parent : Option τ)
    (a : gridCandidates H focus parent) (u : Fin N) :
    markedSuccess (markedChildKernel H N required d address focus parent a u) =
      gridAnswerProbability H N d u.val ((H a.val.2).erase a.val.1) (some a.val.2) := by
  rw [markedSuccess_eq_trueProbability_fst]
  unfold markedChildKernel
  rw [← ExposureTree.fresh_mapOutput,markedGridQueryDepth_outcome]
  rfl

theorem markedChildKernel_success_complete (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (required : List (ι × τ) → Bool) (d : ℕ) (address : List (ι × τ))
    (focus : Finset ι) (parent : Option τ)
    (a : gridCandidates H focus parent) (u : Fin N) (hu : u.val ≤ d) :
    markedSuccess (markedChildKernel H N required d address focus parent a u) =
      ∏ f ∈ (H a.val.2).erase a.val.1, gridMessage H N N u.val f (some a.val.2) := by
  rw [markedChildKernel_success,gridAnswerProbability_factor]
  apply Finset.prod_congr rfl
  intro f _
  exact gridMessage_stable H N u.val d N hu u.isLt.le f (some a.val.2)

end CandidateMarginal
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_MarkedChildKernelProspective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave
section ActualMarkedRows
variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

omit [Fintype ι] in

lemma markedChildKernel_prospective (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (required : List (ι × τ) → Bool) (d t : ℕ) (htd : t ≤ d+1) (htN : t ≤ N)
    (address : List (ι × τ)) (focus : Finset ι) (parent : Option τ)
    (a : gridCandidates H focus parent) :
    prospectiveFailure N t (fun u => markedSuccess
      (markedChildKernel H N required d address focus parent a u)) =
        gridCandidateFailure H N t a.val.1 a.val.2 := by
  have hsum : (∑ u : Fin N, if u.val < t then markedSuccess
      (markedChildKernel H N required d address focus parent a u) else 0) =
      ∑ j ∈ Finset.range t, ∏ f ∈ (H a.val.2).erase a.val.1,
        gridMessage H N N j f (some a.val.2) := by
    calc
      _ = ∑ u : Fin N, if u.val < t then
          ∏ f ∈ (H a.val.2).erase a.val.1, gridMessage H N N u.val f (some a.val.2)
          else 0 := by
        apply Finset.sum_congr rfl
        intro u _
        by_cases hu : u.val < t
        · simp only [hu,↓reduceIte]
          exact markedChildKernel_success_complete H N required d address focus parent a u (by omega)
        · simp only [hu,↓reduceIte]
      _ = _ := by
        simpa only [Finset.sum_filter] using sum_fin_filter_lt_eq_range N t htN
          (fun j => ∏ f ∈ (H a.val.2).erase a.val.1, gridMessage H N N j f (some a.val.2))
  unfold prospectiveFailure gridCandidateFailure
  rw [hsum]
  ring

omit [Fintype ι] in

theorem markedQuery_single_path (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (required : List (ι × τ) → Bool) (d k : ℕ) (hkd : k ≤ d+1) (hkN : k ≤ N)
    (address : List (ι × τ)) (focus : Finset ι) (parent : Option τ)
    (a : gridCandidates H focus parent)
    (hreq : requiredCandidates H required address focus parent = {a}) (b : ℕ → ℝ)
    (hfactor : ∀ t < k, ∀ (e : ι) (T : τ), e ∈ H T →
      (7/8 : ℝ) ≤ gridCandidateFailure H N t e T)
    (hfull : ∀ t < k, gridAnswerProbability H N N t focus parent ≤ (9/8 : ℝ)*b t) :
    markedGood (ExposureTree.fresh (fun _ : τ => PMF.uniformOfFintype (Fin N))
      (markedGridQueryDepth H N required (d+1) k address focus parent)) ≤
      (1/(N : ℝ))*∑ u : Fin N, if u.val < k then
        markedGood (markedChildKernel H N required d address focus parent a u)*(2*b u.val)
        else 0 := by
  rw [markedGridQueryDepth_candidate_kernel,hreq]
  apply marked_row_single_path N _ (finsetCandidateOrder_perm _) a _
    (fun a u => markedSuccess (markedChildKernel H N required d address focus parent a u))
    k b (by intros; rfl)
  · intro t ht a
    rw [markedChildKernel_prospective H N required d t (by omega) (by omega)]
    exact hfactor t ht a.val.1 a.val.2 (by
      have ha := a.property
      simp only [gridCandidates,Finset.mem_filter] at ha
      exact ha.2.1)
  · intro t ht
    simp_rw [markedChildKernel_prospective H N required d t (by omega) (by omega)]
    rw [gridCandidateFailure_product H N t (by omega)]
    exact hfull t ht

omit [Fintype ι] in

theorem markedQuery_two_paths (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (required : List (ι × τ) → Bool) (d k : ℕ) (hkd : k ≤ d+1) (hkN : k ≤ N)
    (address : List (ι × τ)) (focus : Finset ι) (parent : Option τ)
    (a b : gridCandidates H focus parent) (hab : a ≠ b)
    (hreq : requiredCandidates H required address focus parent = {a,b}) (w : ℕ → ℝ)
    (hfactor : ∀ t < k, ∀ (e : ι) (T : τ), e ∈ H T →
      (7/8 : ℝ) ≤ gridCandidateFailure H N t e T)
    (hfull : ∀ t < k, gridAnswerProbability H N N t focus parent ≤ (9/8 : ℝ)*w t) :
    markedGood (ExposureTree.fresh (fun _ : τ => PMF.uniformOfFintype (Fin N))
      (markedGridQueryDepth H N required (d+1) k address focus parent)) ≤
      (1/(N : ℝ))*∑ u : Fin N, (1/(N : ℝ))*∑ v : Fin N,
        if u.val < k ∧ v.val < k then
          (markedGood (markedChildKernel H N required d address focus parent a u)*
            markedGood (markedChildKernel H N required d address focus parent b v))*
              (2*w (max u.val v.val)) else 0 := by
  rw [markedGridQueryDepth_candidate_kernel,hreq]
  apply marked_row_two_paths N _ (finsetCandidateOrder_perm _) a b hab _
    (fun a u => markedSuccess (markedChildKernel H N required d address focus parent a u))
    k w (by intros; rfl)
  · intro t ht a
    rw [markedChildKernel_prospective H N required d t (by omega) (by omega)]
    exact hfactor t ht a.val.1 a.val.2 (by
      have ha := a.property
      simp only [gridCandidates,Finset.mem_filter] at ha
      exact ha.2.1)
  · intro t ht
    simp_rw [markedChildKernel_prospective H N required d t (by omega) (by omega)]
    rw [gridCandidateFailure_product H N t (by omega)]
    exact hfull t ht

end ActualMarkedRows
end SharpTerminalLeave

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave

theorem prefixWeight_nonneg {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) (t : ℕ) :
    0 ≤ prefixWeight w t := Finset.sum_nonneg (fun i _ => hw i)

theorem orderedWeight_nonneg {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) (j t : ℕ) :
    0 ≤ orderedWeight w j t := by
  induction j generalizing t with
  | zero => exact zero_le_one
  | succ j ih => exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (ih i))

theorem power_increment_lower (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (j : ℕ) :
    ((j + 1 : ℕ) : ℝ) * y * x ^ j ≤ (x + y) ^ (j + 1) - x ^ (j + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hmul := mul_le_mul_of_nonneg_left ih hx
    have hpow := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hx (le_add_of_nonneg_right hy) (j + 1)) hy
    simp only [Nat.cast_add, Nat.cast_one] at ih hmul ⊢
    rw [pow_succ (x + y) (j + 1), pow_succ x (j + 1)]
    rw [pow_succ x j] at hpow hmul ⊢
    nlinarith

theorem orderedWeight_factorial {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) (j t : ℕ) :
    (j.factorial : ℝ) * orderedWeight w j t ≤ prefixWeight w t ^ j := by
  induction j generalizing t with
  | zero => simp [orderedWeight]
  | succ j ih =>
    rw [orderedWeight, Nat.factorial_succ, Nat.cast_mul, Finset.mul_sum]
    calc
      _ ≤ ∑ i ∈ Finset.range t,
          ((j + 1 : ℕ) : ℝ) * w i * prefixWeight w i ^ j := by
        apply Finset.sum_le_sum
        intro i _
        have hh := mul_le_mul_of_nonneg_left (ih i)
          (mul_nonneg (Nat.cast_nonneg (j + 1)) (hw i))
        convert hh using 1 <;> first | rfl | ring
      _ ≤ ∑ i ∈ Finset.range t,
          (prefixWeight w (i + 1) ^ (j + 1) - prefixWeight w i ^ (j + 1)) := by
        apply Finset.sum_le_sum
        intro i _
        rw [prefixWeight_succ]
        exact power_increment_lower _ _ (prefixWeight_nonneg hw i) (hw i) j
      _ = prefixWeight w t ^ (j + 1) := by
        rw [Finset.sum_range_sub (fun i => prefixWeight w i ^ (j + 1))]
        simp

theorem orderedWeight_le {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) (j t : ℕ) :
    orderedWeight w j t ≤ prefixWeight w t ^ j / (j.factorial : ℝ) := by
  apply (le_div_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos j))).mpr
  simpa only [mul_comm] using orderedWeight_factorial hw j t

theorem three_segment_weight_le {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (h a b t : ℕ) :
    orderedWeight w h t * orderedWeight w a t * orderedWeight w b t ≤
      prefixWeight w t ^ (h + a + b) /
        ((h.factorial : ℝ) * (a.factorial : ℝ) * (b.factorial : ℝ)) := by
  have hh := orderedWeight_le hw h t
  have ha := orderedWeight_le hw a t
  have hb := orderedWeight_le hw b t
  have hp := mul_le_mul hh ha (orderedWeight_nonneg hw a t)
    (div_nonneg (pow_nonneg (prefixWeight_nonneg hw t) _) (Nat.cast_nonneg _))
  have hp' := mul_le_mul hp hb (orderedWeight_nonneg hw b t)
    (mul_nonneg
      (div_nonneg (pow_nonneg (prefixWeight_nonneg hw t) _) (Nat.cast_nonneg _))
      (div_nonneg (pow_nonneg (prefixWeight_nonneg hw t) _) (Nat.cast_nonneg _)))
  calc
    _ ≤ _ := hp'
    _ = _ := by rw [pow_add, pow_add, div_mul_div_comm, div_mul_div_comm]

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_PathRequired
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave

lemma pathRequired_singleton {A : Type*} [DecidableEq A] (a b : A) (as : List A) :
    pathRequired (a :: as) [b] = decide (b = a) := by
  simp [pathRequired,List.cons_prefix_cons]

lemma pathRequired_shift {A : Type*} [DecidableEq A] (a : A) (as address : List A) :
    pathRequired (a :: as) (address ++ [a]) = pathRequired as address := by
  simp [pathRequired,List.reverse_append]

section PathVisitation
variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

omit [Fintype ι] in
lemma path_required_candidates (H : τ → Finset ι) (focus : Finset ι) (parent : Option τ)
    (a : gridCandidates H focus parent) (as : List (ι × τ)) :
    requiredCandidates H (pathRequired (a.val :: as)) [] focus parent = {a} := by
  ext b
  simp only [requiredCandidates,Finset.mem_filter,Finset.mem_univ,true_and,
    pathRequired_singleton,decide_eq_true_eq,Finset.mem_singleton]
  exact Subtype.val_injective.eq_iff

omit [Fintype ι] in

lemma markedGridQueryDepth_readdress (H : τ → Finset ι) (N : ℕ)
    (required : List (ι × τ) → Bool) (d k : ℕ)
    (address base : List (ι × τ)) (focus : Finset ι) (parent : Option τ) :
    markedGridQueryDepth H N required d k (address ++ base) focus parent =
      markedGridQueryDepth H N (fun l => required (l ++ base)) d k address focus parent := by
  induction d generalizing k address focus parent with
  | zero => rfl
  | succ d ih =>
    simp only [markedGridQueryDepth]
    congr 1
    funext values
    congr 1
    apply List.map_congr_left
    intro p _
    congr 1
    split
    · simpa only [List.cons_append] using
        ih p.2.val (p.1 :: address) ((H p.1.2).erase p.1.1) (some p.1.2)
    · rfl

omit [Fintype ι] in
lemma marked_path_child (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d : ℕ) (focus : Finset ι) (parent : Option τ)
    (a : gridCandidates H focus parent) (as : List (ι × τ)) (u : Fin N) :
    markedChildKernel H N (pathRequired (a.val :: as)) d [] focus parent a u =
      ExposureTree.fresh (fun _ : τ => PMF.uniformOfFintype (Fin N))
        (markedGridQueryDepth H N (pathRequired as) d u.val []
          ((H a.val.2).erase a.val.1) (some a.val.2)) := by
  unfold markedChildKernel
  change ExposureTree.fresh _ (markedGridQueryDepth H N _ d u.val ([] ++ [a.val]) _ _) = _
  rw [markedGridQueryDepth_readdress]
  have he : (fun l => pathRequired (a.val :: as) (l ++ [a.val])) = pathRequired as := by
    funext l
    exact pathRequired_shift _ _ _
  rw [he]

omit [Fintype ι] in

theorem pathVisitProbability_ordered (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (b : ℕ → ℝ) (hb : ∀ t, 0 ≤ b t) (hq : GridRowQuality H N b)
    (path : List (ι × τ)) (d k : ℕ) (hkd : k ≤ d) (hkN : k ≤ N)
    (hlen : path.length ≤ d) (e : ι) (T : τ) (he : e ∈ H T)
    (hpath : LegalQueryPath H ((H T).erase e) (some T) path) :
    pathVisitProbability H N d k ((H T).erase e) (some T) path ≤
      orderedWeight (fun t => (2/(N : ℝ))*b t) path.length k := by
  induction path generalizing d k e T with
  | nil =>
    simpa only [List.length_nil,orderedWeight,pathVisitProbability] using markedGood_le_one _
  | cons a as ih =>
    cases d with
    | zero => simp only [List.length_cons] at hlen; omega
    | succ d =>
      obtain ⟨ha,htail⟩ := hpath
      let a' : gridCandidates H ((H T).erase e) (some T) := ⟨a,ha⟩
      have haT : a.1 ∈ H a.2 := (Finset.mem_filter.mp ha).2.1
      have hstep := markedQuery_single_path H N (pathRequired (a :: as)) d k hkd hkN []
        ((H T).erase e) (some T) a' (path_required_candidates H _ _ a' as) b
        (fun t ht => hq.1 t (by omega))
        (fun t ht => hq.2 t (by omega) e T he)
      change pathVisitProbability H N (d+1) k ((H T).erase e) (some T) (a :: as) ≤ _ at hstep
      calc
        _ ≤ (1/(N : ℝ))*∑ u : Fin N, if u.val < k then
            markedGood (markedChildKernel H N (pathRequired (a :: as)) d []
              ((H T).erase e) (some T) a' u)*(2*b u.val) else 0 := hstep
        _ ≤ (1/(N : ℝ))*∑ u : Fin N, if u.val < k then
            orderedWeight (fun t => (2/(N : ℝ))*b t) as.length u.val*(2*b u.val) else 0 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum
          intro u _
          by_cases hu : u.val < k
          · simp only [hu,↓reduceIte]
            apply mul_le_mul_of_nonneg_right _ (mul_nonneg (by norm_num) (hb _))
            rw [marked_path_child H N d ((H T).erase e) (some T) a' as u]
            apply ih d u.val (by omega) u.isLt.le (by simpa only [List.length_cons] using Nat.le_of_succ_le_succ hlen)
              a.1 a.2 haT htail
          · simp only [hu,↓reduceIte,le_refl]
        _ = _ := by
          rw [Finset.mul_sum]
          simp only [List.length_cons,orderedWeight]
          have hsum := sum_fin_filter_lt_eq_range N k hkN
            (fun j => (2/(N : ℝ))*b j*orderedWeight (fun t => (2/(N : ℝ))*b t) as.length j)
          rw [Finset.sum_filter] at hsum
          rw [← hsum]
          apply Finset.sum_congr rfl
          intro u _
          by_cases hu : u.val < k <;> simp only [hu,↓reduceIte] <;> ring

end PathVisitation
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_PairRequired
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave

lemma pairRequired_shift_left {A : Type*} [DecidableEq A] (a b : A)
    (as bs address : List A) (hab : a ≠ b) :
    pairRequired (a :: as) (b :: bs) (address ++ [a]) = pathRequired as address := by
  simp [pairRequired,pathRequired,List.reverse_append,List.cons_prefix_cons,hab]

lemma pairRequired_shift_right {A : Type*} [DecidableEq A] (a b : A)
    (as bs address : List A) (hab : a ≠ b) :
    pairRequired (a :: as) (b :: bs) (address ++ [b]) = pathRequired bs address := by
  simp [pairRequired,pathRequired,List.reverse_append,List.cons_prefix_cons,hab.symm]

section ForkVisitation
variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

omit [Fintype ι] in
lemma pair_required_candidates (H : τ → Finset ι) (focus : Finset ι) (parent : Option τ)
    (a b : gridCandidates H focus parent) (as bs : List (ι × τ)) :
    requiredCandidates H (pairRequired (a.val :: as) (b.val :: bs)) [] focus parent =
      {a,b} := by
  ext c
  simp only [requiredCandidates,Finset.mem_filter,Finset.mem_univ,true_and,pairRequired,
    pathRequired_singleton,Bool.or_eq_true,decide_eq_true_eq,Finset.mem_insert,
    Finset.mem_singleton,Subtype.val_injective.eq_iff]

omit [Fintype ι] in
lemma marked_pair_child_left (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d : ℕ) (focus : Finset ι) (parent : Option τ)
    (a b : gridCandidates H focus parent) (hab : a ≠ b)
    (as bs : List (ι × τ)) (u : Fin N) :
    markedChildKernel H N (pairRequired (a.val :: as) (b.val :: bs)) d [] focus parent a u =
      ExposureTree.fresh (fun _ : τ => PMF.uniformOfFintype (Fin N))
        (markedGridQueryDepth H N (pathRequired as) d u.val []
          ((H a.val.2).erase a.val.1) (some a.val.2)) := by
  unfold markedChildKernel
  change ExposureTree.fresh _ (markedGridQueryDepth H N _ d u.val ([] ++ [a.val]) _ _) = _
  rw [markedGridQueryDepth_readdress]
  have he : (fun l => pairRequired (a.val :: as) (b.val :: bs) (l ++ [a.val])) =
      pathRequired as := by
    funext l
    exact pairRequired_shift_left _ _ _ _ _ (fun h => hab (Subtype.ext h))
  rw [he]

omit [Fintype ι] in
lemma marked_pair_child_right (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d : ℕ) (focus : Finset ι) (parent : Option τ)
    (a b : gridCandidates H focus parent) (hab : a ≠ b)
    (as bs : List (ι × τ)) (u : Fin N) :
    markedChildKernel H N (pairRequired (a.val :: as) (b.val :: bs)) d [] focus parent b u =
      ExposureTree.fresh (fun _ : τ => PMF.uniformOfFintype (Fin N))
        (markedGridQueryDepth H N (pathRequired bs) d u.val []
          ((H b.val.2).erase b.val.1) (some b.val.2)) := by
  unfold markedChildKernel
  change ExposureTree.fresh _ (markedGridQueryDepth H N _ d u.val ([] ++ [b.val]) _ _) = _
  rw [markedGridQueryDepth_readdress]
  have he : (fun l => pairRequired (a.val :: as) (b.val :: bs) (l ++ [b.val])) =
      pathRequired bs := by
    funext l
    exact pairRequired_shift_right _ _ _ _ _ (fun h => hab (Subtype.ext h))
  rw [he]

lemma discrete_ordered_step (N k : ℕ) (hk : k ≤ N) (b : ℕ → ℝ) (j : ℕ) :
    (1/(N : ℝ))*(∑ u : Fin N, if u.val < k then
      orderedWeight (fun t => (2/(N : ℝ))*b t) j u.val*(2*b u.val) else 0) =
      orderedWeight (fun t => (2/(N : ℝ))*b t) (j+1) k := by
  rw [Finset.mul_sum,orderedWeight]
  have hs := sum_fin_filter_lt_eq_range N k hk
    (fun t => (2/(N : ℝ))*b t*orderedWeight (fun t => (2/(N : ℝ))*b t) j t)
  rw [Finset.sum_filter] at hs
  rw [← hs]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : u.val < k <;> simp only [hu,↓reduceIte] <;> ring

omit [Fintype ι] in

theorem pairVisitProbability_fork (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (b : ℕ → ℝ) (hb : ∀ t, 0 ≤ b t) (hq : GridRowQuality H N b)
    (C : ℝ) (hC : 0 ≤ C) (hlower : ∀ t ≤ N, 1 ≤ C*b t)
    (d k : ℕ) (hkd : k ≤ d+1) (hkN : k ≤ N)
    (e : ι) (T : τ) (he : e ∈ H T)
    (a b' : gridCandidates H ((H T).erase e) (some T)) (hab : a ≠ b')
    (as bs : List (ι × τ)) (ha : LegalQueryPath H ((H a.val.2).erase a.val.1) (some a.val.2) as)
    (hb' : LegalQueryPath H ((H b'.val.2).erase b'.val.1) (some b'.val.2) bs)
    (halen : as.length ≤ d) (hblen : bs.length ≤ d) :
    pairVisitProbability H N (d+1) k ((H T).erase e) (some T) (a.val :: as) (b'.val :: bs) ≤
      C * orderedWeight (fun t => (2/(N : ℝ))*b t) (as.length+1) k *
        orderedWeight (fun t => (2/(N : ℝ))*b t) (bs.length+1) k := by
  let A := fun t => orderedWeight (fun t => (2/(N : ℝ))*b t) as.length t
  let B := fun t => orderedWeight (fun t => (2/(N : ℝ))*b t) bs.length t
  have hA : ∀ t, 0 ≤ A t := fun t => orderedWeight_nonneg (fun t => mul_nonneg (by positivity) (hb t)) _ t
  have hB : ∀ t, 0 ≤ B t := fun t => orderedWeight_nonneg (fun t => mul_nonneg (by positivity) (hb t)) _ t
  have hstep := markedQuery_two_paths H N (pairRequired (a.val :: as) (b'.val :: bs)) d k hkd hkN []
    ((H T).erase e) (some T) a b' hab (pair_required_candidates H _ _ a b' as bs) b
    (fun t ht => hq.1 t (by omega)) (fun t ht => hq.2 t (by omega) e T he)
  have hac := (Finset.mem_filter.mp a.property).2.1
  have hbc := (Finset.mem_filter.mp b'.property).2.1
  calc
    _ ≤ (1/(N : ℝ))*∑ u : Fin N, (1/(N : ℝ))*∑ v : Fin N,
        if u.val < k ∧ v.val < k then
          (markedGood (markedChildKernel H N (pairRequired (a.val :: as) (b'.val :: bs)) d []
            ((H T).erase e) (some T) a u)*
          markedGood (markedChildKernel H N (pairRequired (a.val :: as) (b'.val :: bs)) d []
            ((H T).erase e) (some T) b' v))*(2*b (max u.val v.val)) else 0 := hstep
    _ ≤ (1/(N : ℝ))*∑ u : Fin N, (1/(N : ℝ))*∑ v : Fin N,
        C*((if u.val < k then A u.val*(2*b u.val) else 0)*
          (if v.val < k then B v.val*(2*b v.val) else 0)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro u _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro v _
      by_cases hu : u.val < k <;> by_cases hv : v.val < k
      · simp only [hu,hv,and_self,↓reduceIte]
        rw [marked_pair_child_left H N d _ _ a b' hab as bs u,
          marked_pair_child_right H N d _ _ a b' hab as bs v]
        have hau := pathVisitProbability_ordered H N b hb hq as d u.val (by omega) u.isLt.le
          halen a.val.1 a.val.2 hac ha
        have hbv := pathVisitProbability_ordered H N b hb hq bs d v.val (by omega) v.isLt.le
          hblen b'.val.1 b'.val.2 hbc hb'
        have hm : b (max u.val v.val) ≤ C*(b u.val*b v.val) := by
          rcases le_total u.val v.val with h | h
          · rw [max_eq_right h]
            simpa only [one_mul,mul_assoc] using
              mul_le_mul_of_nonneg_right (hlower u.val u.isLt.le) (hb v.val)
          · rw [max_eq_left h]
            have hh := mul_le_mul_of_nonneg_right (hlower v.val v.isLt.le) (hb u.val)
            nlinarith
        have hp := mul_le_mul hau hbv (markedGood_nonneg _) (hA _)
        have hprod := mul_le_mul_of_nonneg_right hp
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hb (max u.val v.val)))
        have hwm := mul_le_mul_of_nonneg_left hm (mul_nonneg (hA u.val) (hB v.val))
        dsimp only [pathVisitProbability] at hprod
        calc
          _ ≤ A u.val*B v.val*(2*b (max u.val v.val)) := hprod
          _ ≤ _ := by
            have hn := mul_nonneg (mul_nonneg (hA u.val) (hB v.val))
              (mul_nonneg hC (mul_nonneg (hb u.val) (hb v.val)))
            nlinarith
      · simp only [hu,hv,and_false,↓reduceIte,mul_zero,le_refl]
      · simp only [hu,hv,false_and,↓reduceIte,zero_mul,mul_zero,le_refl]
      · simp only [hu,hv,false_and,↓reduceIte,mul_zero,le_refl]
    _ = C*((1/(N : ℝ))*∑ u : Fin N, if u.val < k then A u.val*(2*b u.val) else 0)*
        ((1/(N : ℝ))*∑ v : Fin N, if v.val < k then B v.val*(2*b v.val) else 0) := by
      simp only [← Finset.mul_sum,← Finset.sum_mul]
      ring
    _ = _ := by
      rw [discrete_ordered_step N k hkN b as.length,discrete_ordered_step N k hkN b bs.length]

end ForkVisitation
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Coupling_OrderedWeightMono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave

lemma orderedWeight_mono {w : ℕ → ℝ} (hw : ∀ t, 0 ≤ w t) (j : ℕ) :
    Monotone (orderedWeight w j) := by
  cases j with
  | zero => intro a b _; rfl
  | succ j =>
    intro a b hab
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
      (fun t _ _ => mul_nonneg (hw t) (orderedWeight_nonneg hw _ _))

lemma pairRequired_common_shift {A : Type*} [DecidableEq A] (a : A)
    (p q address : List A) :
    pairRequired (a :: p) (a :: q) (address ++ [a]) = pairRequired p q address := by
  simp only [pairRequired,pathRequired_shift]

section SpineVisitation
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

lemma pair_common_required_candidates (H : τ → Finset ι) (focus : Finset ι)
    (parent : Option τ) (a : gridCandidates H focus parent) (p q : List (ι × τ)) :
    requiredCandidates H (pairRequired (a.val :: p) (a.val :: q)) [] focus parent = {a} := by
  rw [pair_required_candidates]
  exact Finset.pair_eq_singleton a

lemma marked_pair_common_child (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d : ℕ) (focus : Finset ι) (parent : Option τ)
    (a : gridCandidates H focus parent) (p q : List (ι × τ)) (u : Fin N) :
    markedChildKernel H N (pairRequired (a.val :: p) (a.val :: q)) d [] focus parent a u =
      ExposureTree.fresh (fun _ : τ => PMF.uniformOfFintype (Fin N))
        (markedGridQueryDepth H N (pairRequired p q) d u.val []
          ((H a.val.2).erase a.val.1) (some a.val.2)) := by
  unfold markedChildKernel
  change ExposureTree.fresh _ (markedGridQueryDepth H N _ d u.val ([] ++ [a.val]) _ _) = _
  rw [markedGridQueryDepth_readdress]
  have he : (fun l => pairRequired (a.val :: p) (a.val :: q) (l ++ [a.val])) =
      pairRequired p q := by
    funext l
    exact pairRequired_common_shift _ _ _ _
  rw [he]

theorem pairVisitProbability_spine (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (b : ℕ → ℝ) (hb : ∀ t, 0 ≤ b t) (hq : GridRowQuality H N b)
    (C : ℝ) (hC : 0 ≤ C) (hlower : ∀ t ≤ N, 1 ≤ C*b t)
    (spine : List (ι × τ)) (a b' : ι × τ) (hab : a ≠ b') (as bs : List (ι × τ))
    (d k : ℕ) (hkd : k ≤ d) (hkN : k ≤ N)
    (e : ι) (T : τ) (he : e ∈ H T)
    (ha : LegalQueryPath H ((H T).erase e) (some T) (spine ++ a :: as))
    (hb' : LegalQueryPath H ((H T).erase e) (some T) (spine ++ b' :: bs))
    (halen : spine.length + (as.length+1) ≤ d) (hblen : spine.length + (bs.length+1) ≤ d) :
    pairVisitProbability H N d k ((H T).erase e) (some T)
      (spine ++ a :: as) (spine ++ b' :: bs) ≤
      C * orderedWeight (fun t => (2/(N : ℝ))*b t) spine.length k *
        orderedWeight (fun t => (2/(N : ℝ))*b t) (as.length+1) k *
        orderedWeight (fun t => (2/(N : ℝ))*b t) (bs.length+1) k := by
  have hw : ∀ t, 0 ≤ (2/(N : ℝ))*b t := fun t => mul_nonneg (by positivity) (hb t)
  induction spine generalizing d k e T with
  | nil =>
    cases d with
    | zero => simp only [List.length_nil] at halen; omega
    | succ d =>
      obtain ⟨ha,hat⟩ := ha
      obtain ⟨hb',hbt⟩ := hb'
      let aa : gridCandidates H ((H T).erase e) (some T) := ⟨a,ha⟩
      let bb : gridCandidates H ((H T).erase e) (some T) := ⟨b',hb'⟩
      have hne : aa ≠ bb := fun h => hab (congrArg Subtype.val h)
      simpa only [List.nil_append,List.length_nil,orderedWeight,mul_one] using
        pairVisitProbability_fork H N b hb hq C hC hlower d k hkd hkN e T he aa bb hne as bs
          hat hbt (by simp only [List.length_nil] at halen; omega)
          (by simp only [List.length_nil] at hblen; omega)
  | cons z zs ih =>
    cases d with
    | zero => simp only [List.length_cons] at halen; omega
    | succ d =>
      obtain ⟨hz,haz⟩ := ha
      obtain ⟨_,hbz⟩ := hb'
      let zz : gridCandidates H ((H T).erase e) (some T) := ⟨z,hz⟩
      have hzc := (Finset.mem_filter.mp hz).2.1
      have hs := markedQuery_single_path H N
        (pairRequired (z :: (zs ++ a :: as)) (z :: (zs ++ b' :: bs))) d k hkd hkN []
        ((H T).erase e) (some T) zz (pair_common_required_candidates H _ _ zz _ _) b
        (fun t ht => hq.1 t (by omega)) (fun t ht => hq.2 t (by omega) e T he)
      let A := orderedWeight (fun t => (2/(N : ℝ))*b t) (as.length+1) k
      let B := orderedWeight (fun t => (2/(N : ℝ))*b t) (bs.length+1) k
      have hA : 0 ≤ A := orderedWeight_nonneg hw _ _
      have hB : 0 ≤ B := orderedWeight_nonneg hw _ _
      calc
        _ ≤ (1/(N : ℝ))*∑ u : Fin N, if u.val < k then
            markedGood (markedChildKernel H N
              (pairRequired (z :: (zs ++ a :: as)) (z :: (zs ++ b' :: bs))) d []
              ((H T).erase e) (some T) zz u)*(2*b u.val) else 0 := hs
        _ ≤ (1/(N : ℝ))*∑ u : Fin N, if u.val < k then
            (C*orderedWeight (fun t => (2/(N : ℝ))*b t) zs.length u.val*A*B)*(2*b u.val)
            else 0 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum
          intro u _
          by_cases hu : u.val < k
          · simp only [hu,↓reduceIte]
            apply mul_le_mul_of_nonneg_right _ (mul_nonneg (by norm_num) (hb _))
            rw [marked_pair_common_child H N d _ _ zz _ _ u]
            have hi := ih d u.val (by omega) u.isLt.le z.1 z.2 hzc haz hbz
              (by simp only [List.length_cons] at halen; omega)
              (by simp only [List.length_cons] at hblen; omega)
            apply hi.trans
            apply mul_le_mul
            · apply mul_le_mul_of_nonneg_left
              · exact orderedWeight_mono hw _ hu.le
              · exact mul_nonneg hC (orderedWeight_nonneg hw _ _)
            · exact orderedWeight_mono hw _ hu.le
            · exact orderedWeight_nonneg hw _ _
            · exact mul_nonneg (mul_nonneg hC (orderedWeight_nonneg hw _ _)) hA
          · simp only [hu,↓reduceIte,le_refl]
        _ = C*((1/(N : ℝ))*∑ u : Fin N, if u.val < k then
            orderedWeight (fun t => (2/(N : ℝ))*b t) zs.length u.val*(2*b u.val) else 0)*A*B := by
          simp only [Finset.mul_sum,Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro u _
          by_cases hu : u.val < k <;> simp only [hu,↓reduceIte] <;> ring
        _ = _ := by
          rw [discrete_ordered_step N k hkN b zs.length]
          rfl

end SpineVisitation
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Coupling_UniformRootAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave
section FixedRoots
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma uniform_root_atom (G : Finset α) (hne : G.Nonempty) (e : α) :
    pmfMean (PMF.uniformOfFinset G hne) (fun x => if x = e then 1 else 0) =
      if e ∈ G then 1/(G.card : ℝ) else 0 := by
  rw [pmfMean_uniformOfFinset]
  by_cases he : e ∈ G
  · simp only [he,ite_true]
    rw [Finset.sum_ite_eq']
    simp [he]
  · simp [he]

lemma uniform_ordered_root_atoms (G : Finset α) (hne : G.Nonempty) (e f : α) :
    pmfMean (PMF.uniformOfFinset G hne) (fun x =>
      pmfMean (PMF.uniformOfFinset G hne) (fun y => if x = e ∧ y = f then 1 else 0)) =
      if e ∈ G ∧ f ∈ G then 1/(G.card : ℝ)^2 else 0 := by
  have h (x : α) :
      pmfMean (PMF.uniformOfFinset G hne) (fun y => if x = e ∧ y = f then 1 else 0) =
        (if x = e then 1 else 0)*(if f ∈ G then 1/(G.card : ℝ) else 0) := by
    by_cases hx : x = e
    · simp only [hx,true_and,ite_true,one_mul]
      exact uniform_root_atom G hne f
    · simp [hx]
  simp_rw [h]
  rw [pmfMean_mul_const,uniform_root_atom]
  by_cases he : e ∈ G <;> by_cases hf : f ∈ G <;> simp only [he,hf,ite_true,ite_false,true_and,false_and,zero_mul,mul_zero]
  ring

theorem uniform_root_set_probability_le (G : Finset α) (hne : G.Nonempty)
    (E : Finset α) (hE : E.card = 2) :
    pmfMean (PMF.uniformOfFinset G hne) (fun x =>
      pmfMean (PMF.uniformOfFinset G hne) (fun y => if ({x,y} : Finset α) = E then 1 else 0)) ≤
        2/(G.card : ℝ)^2 := by
  obtain ⟨e,f,hef,rfl⟩ := Finset.card_eq_two.mp hE
  have hpt (x y : α) : (if ({x,y} : Finset α) = {e,f} then (1 : ℝ) else 0) ≤
      (if x=e ∧ y=f then 1 else 0) + (if x=f ∧ y=e then 1 else 0) := by
    by_cases h : ({x,y} : Finset α) = {e,f}
    · have hm : x ∈ ({e,f} : Finset α) := h ▸ Finset.mem_insert_self _ _
      have hn : y ∈ ({e,f} : Finset α) := h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      have hxy : x ≠ y := by
        intro heq
        subst y
        have hh := congrArg Finset.card h
        simp only [Finset.insert_eq_of_mem (Finset.mem_singleton_self _),Finset.card_singleton,
          Finset.card_pair hef] at hh
        omega
      have hx : x = e ∨ x = f := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hm
      have hy : y = e ∨ y = f := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hn
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact False.elim (hxy (hx.trans hy.symm))
      · simp [hx,hy,hef]
      · simp [hx,hy,hef,Finset.pair_comm]
      · exact False.elim (hxy (hx.trans hy.symm))
    · simp only [h,ite_false]
      split_ifs <;> norm_num
  have hh : pmfMean (PMF.uniformOfFinset G hne) (fun x =>
      pmfMean (PMF.uniformOfFinset G hne) (fun y => if ({x,y} : Finset α) = {e,f} then 1 else 0)) ≤
      pmfMean (PMF.uniformOfFinset G hne) (fun x =>
      pmfMean (PMF.uniformOfFinset G hne) (fun y =>
        (if x=e ∧ y=f then 1 else 0)+(if x=f ∧ y=e then 1 else 0))) := by
    apply pmfMean_mono
    intro x _
    apply pmfMean_mono
    intro y _
    exact hpt x y
  simp_rw [pmfMean_add] at hh
  rw [uniform_ordered_root_atoms,uniform_ordered_root_atoms] at hh
  have hnon : 0 ≤ 1/(G.card : ℝ)^2 := by positivity
  have htwo : 2/(G.card : ℝ)^2 = 2*(1/(G.card : ℝ)^2) := by ring
  exact hh.trans (by rw [htwo]; split_ifs <;> linarith)

end FixedRoots
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_OlderSeed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.TriangleGrowth
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {N R : ℕ}
variable (A : TriangleGrowth G N R)

lemma nonroot_of_card_two {v : Fin N} (hv : (A.older v).card = 2) : R ≤ v.val := by
  by_contra hn
  have hh := A.seed_small v (Nat.lt_of_not_ge hn)
  rw [← A.older_eq_seed (Nat.lt_of_not_ge hn),hv] at hh
  omega

lemma older_le_parent {v p x : Fin N} (hv : R ≤ v.val) (hp : A.parent v = some p)
    (hx : x ∈ A.older v) : x ≤ p := by
  rw [older,dite_eq_left hv,hp] at hx
  rcases Finset.mem_insert.mp (Finset.mem_filter.mp hx).1 with h | h
  · exact le_of_eq h
  · exact le_of_lt ((A.older_invariants p).1 x h)

lemma parent_of_max {v p : Fin N} (hv : R ≤ v.val) (hp : R ≤ p.val)
    (hpm : p ∈ A.older v) (hmax : ∀ x ∈ A.older v, x ≤ p) : A.parent v = some p := by
  cases hpar : A.parent v with
  | none =>
    have hh := A.older_root_of_none hv hpar hpm
    omega
  | some q =>
    have hq := hmax q (A.parent_mem_older hv hpar)
    have hqp := A.older_le_parent hv hpar hpm
    exact congrArg some (le_antisymm hq hqp)

lemma root_graph {x y : Fin N} (hx : x.val < R) (hy : y.val < R) :
    A.birthGraph.graph.Adj x y ↔ A.seed.graph.Adj x y := by
  change (x ∈ A.older y ∨ y ∈ A.older x) ↔ _
  rw [A.older_eq_seed hx,A.older_eq_seed hy]
  rfl

theorem spawnRules : A.birthGraph.SpawnRules G A.label := by
  constructor
  · have hold (u v : Fin N) (h : u ∈ A.older v) : G.Adj (A.label u) (A.label v) := by
      by_cases hv : R ≤ v.val
      · have hm : A.label u ∈ A.attach v := by
          rw [← ((A.older_invariants v).2 hv).2.1]
          exact Finset.mem_image.mpr ⟨u,h,rfl⟩
        exact (A.triangle v hv).2 _ (Finset.mem_insert_of_mem hm) _
          (Finset.mem_insert_self _ _) (fun he => A.new_label v hv (he ▸ hm))
      · rw [A.older_eq_seed (Nat.lt_of_not_ge hv)] at h
        exact A.seed_labels v (Nat.lt_of_not_ge hv) u h
    intro a b h
    rcases h with h | h
    · exact hold a b h
    · exact (hold b a h).symm
  · intro v hvc a ha b hb hab
    have hv := A.nonroot_of_card_two hvc
    cases hp : A.parent v with
    | none =>
      obtain ⟨x,y,hx,hy,hxy,he⟩ := A.older_pair_of_root hv hp
      have hg := (A.root_graph hx hy).mpr hxy
      change a ∈ A.older v at ha
      change b ∈ A.older v at hb
      rw [he] at ha hb
      simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact False.elim (hab rfl)
      · exact hg
      · exact hg.symm
      · exact False.elim (hab rfl)
    | some p =>
      have he := A.birthGraph.older_eq_pair hab ha hb
      have hpm := A.parent_mem_older hv hp
      change p ∈ A.birthGraph.older v at hpm
      rw [he] at hpm
      simp only [Finset.mem_insert,Finset.mem_singleton] at hpm
      have hsub : A.older v ⊆ insert p (A.older p) := by
        rw [older,dite_eq_left hv,hp]
        exact Finset.filter_subset _ _
      rcases hpm with hpa | hpb
      · subst a
        exact Or.inr ((Finset.mem_insert.mp (hsub hb)).resolve_left hab.symm)
      · subst b
        exact Or.inl ((Finset.mem_insert.mp (hsub ha)).resolve_left hab)
  · intro v p hpm hmax hpc
    have hp := A.nonroot_of_card_two hpc
    have hv : R ≤ v.val := le_trans hp (le_of_lt (A.birthGraph.older_lt v p hpm))
    have hpar := A.parent_of_max hv hp hpm hmax
    rw [A.parentType_eq v hv,A.parentType_eq p hp]
    exact A.omission v p hv hpar
  · intro v w hvc he hl
    change A.older v = A.older w at he
    change (A.older v).card = 2 at hvc
    have hv := A.nonroot_of_card_two hvc
    have hw := A.nonroot_of_card_two (he ▸ hvc)
    have hp : A.parent v = A.parent w := by
      cases hpv : A.parent v with
      | none =>
        cases hpw : A.parent w with
        | none => rfl
        | some p =>
          have hm := A.parent_mem_older hw hpw
          rw [← he] at hm
          have hpr := A.older_root_of_none hv hpv hm
          have hpn := A.parent_nonroot w p hw hpw
          omega
      | some p =>
        have hpm := A.parent_mem_older hv hpv
        have hmax := fun x (hx : x ∈ A.older v) => A.older_le_parent hv hpv hx
        have hpm' : p ∈ A.older w := he ▸ hpm
        have hmax' : ∀ x ∈ A.older w, x ≤ p := by
          intro x hx
          exact hmax x (he.symm ▸ hx)
        exact (A.parent_of_max hw (A.parent_nonroot v p hv hpv) hpm' hmax').symm
    apply A.distinct_children v w hv hw hp _ hl
    rw [← ((A.older_invariants v).2 hv).2.1,← ((A.older_invariants w).2 hw).2.1]
    exact congrArg (Finset.image A.label) he

end SharpTerminalLeave.TriangleGrowth

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_Parent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.TriangleGrowth
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {N R : ℕ}
variable (A : TriangleGrowth G N R)

lemma parent_older {x y : Fin N} (h : A.Parent x y) : x ∈ A.older y :=
  A.parent_mem_older h.1 h.2

lemma pathUnion_subset_lower {a b : Fin N} {S : Set (Fin N)} (hS : IsLowerSet S)
    (hroots : ∀ x : Fin N, x.val < R → x ∈ S) (ha : a ∈ S) (hb : b ∈ S) :
    ↑(A.pathUnion a b) ⊆ S := by
  intro x hx
  rcases (A.mem_pathUnion a b x).mp hx with hroot | hanc | hanc
  · exact hroots x hroot
  · exact hS (A.ancestor_le hanc) ha
  · exact hS (A.ancestor_le hanc) hb

end SharpTerminalLeave.TriangleGrowth

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_RootedExposedCollisionWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.BirthGraph
variable {N : ℕ} (B : BirthGraph N)
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) (label : Fin N → V)

theorem rooted_exposed_collision_witness (hrules : B.SpawnRules G label)
    (R : ℕ) (hroots : Set.InjOn label {v : Fin N | v.val < R})
    (hnonroot : ∀ v : Fin N, R ≤ v.val → (B.older v).card = 2)
    {v w : Fin N} (hne : v ≠ w) {T : Finset V}
    (hv : B.ExposedAt G label v T) (hw : B.ExposedAt G label w T) :
    ∃ S : Set (Fin N), IsLowerSet S ∧ Set.InjOn label S ∧
      (∀ x : Fin N, x.val < R → x ∈ S) ∧
      ∃ a ∈ S, ∃ b ∈ S, B.ExtraEdge G label a b := by
  classical
  by_cases hinj : Function.Injective label
  · have hex : ∃ a b, B.ExtraEdge G label a b := by
      by_contra hn
      have hno : ∀ a b, ¬ B.ExtraEdge G label a b := by simpa only [not_exists] using hn
      exact B.no_repeated_exposure G label hinj hno hne hv hw
    obtain ⟨a,b,he⟩ := hex
    exact ⟨Set.univ,isLowerSet_univ,hinj.injOn,fun _ _ => Set.mem_univ _,
      a,Set.mem_univ _,b,Set.mem_univ _,he⟩
  · obtain ⟨z,u,huz,hzu,hpre⟩ := exists_first_repeat label hinj
    have hz : R ≤ z.val := by
      by_contra hn
      have hzR : z.val < R := Nat.lt_of_not_ge hn
      have huR : u.val < R := lt_trans huz hzR
      exact (ne_of_lt huz) (hroots hzR huR hzu).symm
    obtain ⟨a,b,ha,hb,he⟩ :=
      B.first_label_repeat_extra G label hrules (hnonroot z hz) huz hzu
    exact ⟨Set.Iio z,isLowerSet_Iio z,hpre,fun x hx => lt_of_lt_of_le hx hz,
      a,ha,b,hb,he⟩

end SharpTerminalLeave.BirthGraph

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_PathSuffix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.TriangleGrowth
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {N R : ℕ}
variable (A : TriangleGrowth G N R)

lemma pathUnion_ancestor_closed {a b x y : Fin N} (hxy : A.Ancestor x y)
    (hy : y ∈ A.pathUnion a b) : x ∈ A.pathUnion a b := by
  apply (A.mem_pathUnion a b x).mpr
  rcases (A.mem_pathUnion a b y).mp hy with hroot | ha | hb
  · exact Or.inl (lt_of_le_of_lt (A.ancestor_le hxy) hroot)
  · exact Or.inr (Or.inl (hxy.trans ha))
  · exact Or.inr (Or.inr (hxy.trans hb))

lemma within_pathSuffix {a b x y : Fin N} {cut : ℕ} (hxy : A.Ancestor x y)
    (hy : y ∈ A.pathUnion a b) (hx : cut ≤ x.val) :
    A.birthGraph.Within (A.pathSuffix a b cut) x y := by
  induction hxy using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head x c hxc hcy ih =>
    have hc : cut ≤ c.val := hx.trans (A.parent_le hxc)
    have hxP : x ∈ A.pathUnion a b := A.pathUnion_ancestor_closed
      (Relation.ReflTransGen.head hxc hcy) hy
    have hcP : c ∈ A.pathUnion a b := A.pathUnion_ancestor_closed hcy hy
    exact Relation.ReflTransGen.head
      ⟨(A.mem_pathSuffix a b x cut).mpr ⟨hxP,hx⟩,
        (A.mem_pathSuffix a b c cut).mpr ⟨hcP,hc⟩,A.parent_older hxc⟩ (ih hc)

theorem pathSuffix_covered (a b : Fin N) (cut : ℕ) (hcut : R ≤ cut) :
    A.birthGraph.Covered (A.pathSuffix a b cut) a b := by
  intro x hx
  obtain ⟨hxP,hxc⟩ := (A.mem_pathSuffix a b x cut).mp hx
  rcases (A.mem_pathUnion a b x).mp hxP with hroot | ha | hb
  · exact False.elim ((Nat.not_le_of_gt hroot) (hcut.trans hxc))
  · refine Or.inl ⟨?_,A.within_pathSuffix ha (A.left_mem_pathUnion a b) hxc⟩
    exact (A.mem_pathSuffix a b a cut).mpr
      ⟨A.left_mem_pathUnion a b,hxc.trans (A.ancestor_le ha)⟩
  · refine Or.inr ⟨?_,A.within_pathSuffix hb (A.right_mem_pathUnion a b) hxc⟩
    exact (A.mem_pathSuffix a b b cut).mpr
      ⟨A.right_mem_pathUnion a b,hxc.trans (A.ancestor_le hb)⟩

theorem injective_path_collision {v w : Fin N} (hne : v ≠ w) {T : Finset V}
    (hv : A.birthGraph.ExposedAt G A.label v T)
    (hw : A.birthGraph.ExposedAt G A.label w T) :
    ∃ a b : Fin N, A.birthGraph.ExtraEdge G A.label a b ∧
      Set.InjOn A.label (A.pathUnion a b) := by
  obtain ⟨S,hS,hi,hroots,a,ha,b,hb,he⟩ :=
    A.birthGraph.rooted_exposed_collision_witness G A.label A.spawnRules R A.roots_injective
      (fun z hz => ((A.older_invariants z).2 hz).1) hne hv hw
  exact ⟨a,b,he,hi.mono (A.pathUnion_subset_lower hS hroots ha hb)⟩

end SharpTerminalLeave.TriangleGrowth

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_PathForest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

namespace PathForest
variable {s : ℕ}

lemma step_lt (F : PathForest s) {x y : Fin s} (h : F.Step x y) : x < y := F.property y x h

lemma ancestor_le (F : PathForest s) {x y : Fin s} (h : F.Ancestor x y) : x ≤ y := by
  induction h with
  | refl => exact le_rfl
  | tail _ hp ih => exact ih.trans (F.step_lt hp).le

lemma predecessor_unique (F : PathForest s) {x y z : Fin s}
    (hx : F.Step x z) (hy : F.Step y z) : x = y := Option.some.inj (hx.symm.trans hy)

lemma ancestor_eq_or_predecessor (F : PathForest s) {x z : Fin s}
    (h : F.Ancestor x z) : x = z ∨ ∃ y, F.Step y z ∧ F.Ancestor x y := by
  cases h with
  | refl => exact Or.inl rfl
  | @tail y z hxy hyz => exact Or.inr ⟨y,hyz,hxy⟩

lemma ancestors_comparable (F : PathForest s) {x y z : Fin s}
    (hx : F.Ancestor x z) (hy : F.Ancestor y z) :
    F.Ancestor x y ∨ F.Ancestor y x := by
  induction hx generalizing y with
  | refl => exact Or.inr hy
  | @tail v z hxv hvz ih =>
    rcases F.ancestor_eq_or_predecessor hy with rfl | ⟨w,hwz,hyw⟩
    · exact Or.inl (Relation.ReflTransGen.tail hxv hvz)
    · have he := F.predecessor_unique hvz hwz
      subst w
      exact ih hyw

lemma onPath_ancestor (F : PathForest s) {a : Option (Fin s)} {x y : Fin s}
    (hx : F.Ancestor x y) (hy : F.OnPath a y) : F.OnPath a x := by
  obtain ⟨w,rfl,hyw⟩ := hy
  exact ⟨w,rfl,hx.trans hyw⟩

lemma onPath_comparable (F : PathForest s) {a : Option (Fin s)} {x y : Fin s}
    (hx : F.OnPath a x) (hy : F.OnPath a y) : F.Ancestor x y ∨ F.Ancestor y x := by
  obtain ⟨u,hu,hxu⟩ := hx
  obtain ⟨v,hv,hyv⟩ := hy
  have he := Option.some.inj (hu.symm.trans hv)
  subst v
  exact F.ancestors_comparable hxu hyv

lemma onPath_before (F : PathForest s) {a : Option (Fin s)} {x y : Fin s}
    (hx : F.OnPath a x) (hy : F.OnPath a y) (hxy : x < y) : F.Ancestor x y := by
  rcases F.onPath_comparable hx hy with h | h
  · exact h
  · exact False.elim (not_le_of_gt hxy (F.ancestor_le h))

theorem parent_determined (F H : PathForest s) (a b : Option (Fin s))
    (hcover : ∀ v, F.OnPath a v ∨ F.OnPath b v)
    (ha : ∀ v, F.OnPath a v ↔ H.OnPath a v)
    (hb : ∀ v, F.OnPath b v ↔ H.OnPath b v) : F = H := by
  have hone : ∀ (U W : PathForest s) (c : Option (Fin s)) (v p : Fin s),
      (∀ i, U.OnPath c i ↔ W.OnPath c i) → U.OnPath c v → U.Step p v →
      ∃ q, W.Step q v ∧ p ≤ q := by
    intro U W c v p he hv hp
    have hpc := U.onPath_ancestor (Relation.ReflTransGen.single hp) hv
    have hbefore := W.onPath_before ((he p).mp hpc) ((he v).mp hv) (U.step_lt hp)
    rcases W.ancestor_eq_or_predecessor hbefore with h | ⟨q,hq,hpq⟩
    · exact False.elim (ne_of_lt (U.step_lt hp) h)
    · exact ⟨q,hq,W.ancestor_le hpq⟩
  apply Subtype.ext
  funext v
  change F.parent v = H.parent v
  obtain ⟨c,hcv,he⟩ : ∃ c, F.OnPath c v ∧ ∀ i, F.OnPath c i ↔ H.OnPath c i := by
    rcases hcover v with hv | hv
    · exact ⟨a,hv,ha⟩
    · exact ⟨b,hv,hb⟩
  cases hF : F.parent v with
  | none =>
    cases hH : H.parent v with
    | none => rfl
    | some q =>
      obtain ⟨p,hp,_⟩ := hone H F c v q (fun i => (he i).symm) ((he v).mp hcv) hH
      change F.parent v = some p at hp
      rw [hF] at hp
      contradiction
  | some p =>
    obtain ⟨q,hq,hpq⟩ := hone F H c v p he hcv hF
    obtain ⟨p',hp',hqp'⟩ := hone H F c v q (fun i => (he i).symm) ((he v).mp hcv) hq
    have hpp' : p = p' := F.predecessor_unique hF hp'
    have hpq' : p = q := le_antisymm hpq (hpp' ▸ hqp')
    rw [show H.parent v = some q from hq,hpq']

lemma color_left_iff (F : PathForest s) (a b : Option (Fin s)) (v : Fin s) :
    F.color a b v ≠ .right ↔ F.OnPath a v := by
  classical
  simp only [color]
  split_ifs <;> simp_all

lemma color_right_iff (F : PathForest s) (a b : Option (Fin s)) (v : Fin s)
    (hc : F.OnPath a v ∨ F.OnPath b v) :
    F.color a b v ≠ .left ↔ F.OnPath b v := by
  classical
  simp only [color]
  split_ifs <;> simp_all

open Classical in

theorem two_path_forest_count (a b : Option (Fin s)) :
    Fintype.card {F : PathForest s // ∀ v, F.OnPath a v ∨ F.OnPath b v} ≤ 3^s := by
  classical
  let f : {F : PathForest s // ∀ v, F.OnPath a v ∨ F.OnPath b v} → (Fin s → PathColor) :=
    fun F => F.val.color a b
  have hf : Function.Injective f := by
    intro F H h
    apply Subtype.ext
    apply parent_determined F.val H.val a b F.property
    · intro v
      rw [← color_left_iff,← color_left_iff]
      exact congrArg (fun z => z ≠ PathColor.right) (congrFun h v) |>.to_iff
    · intro v
      rw [← color_right_iff _ _ _ _ (F.property v),← color_right_iff _ _ _ _ (H.property v)]
      exact congrArg (fun z => z ≠ PathColor.left) (congrFun h v) |>.to_iff
  have hh := Fintype.card_le_of_injective f hf
  simpa [Fintype.card_fun,show Fintype.card PathColor = 3 from rfl] using hh

end PathForest
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_Restrict
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.BirthGraph
variable {N : ℕ} (B : BirthGraph N)

lemma restrict_within (s : Finset (Fin N))
    (hclosed : ∀ v ∈ s, B.older v ⊆ s) (Z : Finset (Fin N)) (hZ : Z ⊆ s)
    {x y : Fin N} (h : B.Within Z x y) (hx : x ∈ s) (hy : y ∈ s) :
    (B.restrict s hclosed).Within (reindexSet s Z)
      ((s.orderIsoOfFin rfl).symm ⟨x,hx⟩) ((s.orderIsoOfFin rfl).symm ⟨y,hy⟩) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head x z hxz _ ih =>
    have hz : z ∈ s := hZ hxz.2.1
    apply Relation.ReflTransGen.head (b := (s.orderIsoOfFin rfl).symm ⟨z,hz⟩) _ (ih hz)
    have hex : s.orderEmbOfFin rfl ((s.orderIsoOfFin rfl).symm ⟨x,hx⟩) = x :=
      congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨x,hx⟩)
    have hez : s.orderEmbOfFin rfl ((s.orderIsoOfFin rfl).symm ⟨z,hz⟩) = z :=
      congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨z,hz⟩)
    simpa only [mem_reindexSet,restrict_older_mem,hex,hez] using hxz

lemma restrict_covered (s : Finset (Fin N))
    (hclosed : ∀ v ∈ s, B.older v ⊆ s) (Z : Finset (Fin N)) (hZ : Z ⊆ s)
    {a b : Fin N} (ha : a ∈ s) (hb : b ∈ s) (hc : B.Covered Z a b) :
    (B.restrict s hclosed).Covered (reindexSet s Z)
      ((s.orderIsoOfFin rfl).symm ⟨a,ha⟩) ((s.orderIsoOfFin rfl).symm ⟨b,hb⟩) := by
  intro i hi
  have hfi := (mem_reindexSet s Z i).mp hi
  have ha' : s.orderEmbOfFin rfl ((s.orderIsoOfFin rfl).symm ⟨a,ha⟩) = a :=
    congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨a,ha⟩)
  have hb' : s.orderEmbOfFin rfl ((s.orderIsoOfFin rfl).symm ⟨b,hb⟩) = b :=
    congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨b,hb⟩)
  have hi' : (s.orderIsoOfFin rfl).symm ⟨s.orderEmbOfFin rfl i,hZ hfi⟩ = i := by
    exact (s.orderIsoOfFin rfl).symm_apply_apply i
  rcases hc _ hfi with ⟨haZ,hh⟩ | ⟨hbZ,hh⟩
  · refine Or.inl ⟨(mem_reindexSet s Z _).mpr (by rw [ha']; exact haZ),?_⟩
    simpa only [hi'] using B.restrict_within s hclosed Z hZ hh (hZ hfi) ha
  · refine Or.inr ⟨(mem_reindexSet s Z _).mpr (by rw [hb']; exact hbZ),?_⟩
    simpa only [hi'] using B.restrict_within s hclosed Z hZ hh (hZ hfi) hb

end SharpTerminalLeave.BirthGraph

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_PathPattern
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.TriangleGrowth
variable {n N R : ℕ} {G : Graph n} (A : TriangleGrowth (lookupGraph G) N R)

theorem pathAssignment_mem {a b : Fin N}
    (hi : Set.InjOn A.label (A.pathUnion a b))
    (he : A.birthGraph.ExtraEdge (lookupGraph G) A.label a b) :
    A.pathAssignment a b hi ∈ graphEmbeddingSet
      (insert ({A.pathIndex a b a (A.left_mem_pathUnion a b),
        A.pathIndex a b b (A.right_mem_pathUnion a b)} : Finset _)
        ((A.pathPattern a b).backEdges Finset.univ)) G := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  intro e he'
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he'
  rcases Finset.mem_insert.mp hf with rfl | hf
  · simpa only [Finset.map_insert,Finset.map_singleton,A.pathAssignment_index] using he.2.2.2
  · obtain ⟨v,_,u,hu,rfl⟩ := (A.pathPattern a b).backEdges_mem_pair hf
    have hAdj : A.birthGraph.graph.Adj ((A.pathUnion a b).orderEmbOfFin rfl u)
        ((A.pathUnion a b).orderEmbOfFin rfl v) := by
      exact (BirthGraph.restrict_graph_adj _ _ _ _ _).mp (Or.inl hu)
    have h := A.spawnRules.edge_labels _ _ hAdj
    simp only [Finset.map_insert,Finset.map_singleton]
    change ({A.label ((A.pathUnion a b).orderEmbOfFin rfl u),
      A.label ((A.pathUnion a b).orderEmbOfFin rfl v)} : Finset (Fin n)) ∈ G
    exact h.2

lemma pathPattern_extra {a b : Fin N}
    (he : A.birthGraph.ExtraEdge (lookupGraph G) A.label a b) :
    let a' := A.pathIndex a b a (A.left_mem_pathUnion a b)
    let b' := A.pathIndex a b b (A.right_mem_pathUnion a b)
    a' ≠ b' ∧ ¬ (A.pathPattern a b).graph.Adj a' b' := by
  dsimp only
  constructor
  · intro h
    have hh := congrArg ((A.pathUnion a b).orderEmbOfFin rfl) h
    apply he.1
    simpa only [A.pathIndex_image] using hh
  · intro h
    have hh := (BirthGraph.restrict_graph_adj _ _ _ _ _).mp h
    apply he.2.1
    simpa only [A.pathIndex_image] using hh

theorem pathPattern_covered (a b : Fin N) (k : ℕ)
    (hR : R ≤ k) (hk : k < (A.pathUnion a b).card) :
    (A.pathPattern a b).Covered (Finset.univ.filter (fun x => k ≤ x.val))
      (A.pathIndex a b a (A.left_mem_pathUnion a b))
      (A.pathIndex a b b (A.right_mem_pathUnion a b)) := by
  classical
  let s := A.pathUnion a b
  let y := s.orderEmbOfFin rfl ⟨k,hk⟩
  have hRy : R ≤ y.val := orderEmb_nonroot s
    (fun x hx => (A.mem_pathUnion a b x).mpr (Or.inl hx)) ⟨k,hk⟩ hR
  have hZ : A.pathSuffix a b y.val ⊆ s := by
    intro x hx
    exact ((A.mem_pathSuffix a b x y.val).mp hx).1
  have heq : reindexSet s (A.pathSuffix a b y.val) =
      Finset.univ.filter (fun x => k ≤ x.val) := by
    ext i
    simp only [mem_reindexSet,A.mem_pathSuffix,Finset.mem_filter,Finset.mem_univ,true_and]
    have him := s.orderEmbOfFin_mem rfl i
    have hiff : y ≤ s.orderEmbOfFin rfl i ↔ (⟨k,hk⟩ : Fin s.card) ≤ i :=
      (s.orderEmbOfFin rfl).le_iff_le
    exact ⟨fun h => hiff.mp h.2,fun h => ⟨him,hiff.mpr h⟩⟩
  have h := A.birthGraph.restrict_covered s
    (fun _ hv _ hx => A.pathUnion_older_closed hv hx)
    (A.pathSuffix a b y.val) hZ (A.left_mem_pathUnion a b) (A.right_mem_pathUnion a b)
    (A.pathSuffix_covered a b y.val hRy)
  rw [heq] at h
  exact h

end SharpTerminalLeave.TriangleGrowth

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_LocalChoiceRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

lemma localChoiceRank_lt {α : Type*} (C : Finset α) (a : α) (ha : a ∈ C) :
    localChoiceRank C a < C.card := by
  classical
  simp only [localChoiceRank,dite_eq_left ha]
  simpa only [Fintype.card_coe] using (Fintype.equivFin {a // a ∈ C} ⟨a,ha⟩).isLt

lemma localChoiceRank_injective {α : Type*} (C : Finset α) {a b : α}
    (ha : a ∈ C) (hb : b ∈ C) (he : localChoiceRank C a = localChoiceRank C b) : a = b := by
  classical
  simp only [localChoiceRank,dite_eq_left ha,dite_eq_left hb] at he
  have he' := (Fintype.equivFin {a // a ∈ C}).injective (Fin.ext he)
  exact congrArg Subtype.val he'

lemma prefixChoiceValues_self {n : ℕ} {α : Type*}
    (S : Finset (Fin n → α)) (f : Fin n → α) (hf : f ∈ S) (i : Fin n) :
    f i ∈ prefixChoiceValues S f i := by
  classical
  exact Finset.mem_image.mpr ⟨f,Finset.mem_filter.mpr ⟨hf,fun _ _ => rfl⟩,rfl⟩

lemma prefixChoiceValues_eq {n : ℕ} {α : Type*}
    (S : Finset (Fin n → α)) (f g : Fin n → α) (i : Fin n)
    (he : ∀ j, j < i → f j = g j) : prefixChoiceValues S f i = prefixChoiceValues S g i := by
  classical
  unfold prefixChoiceValues
  congr 1
  apply Finset.filter_congr
  intro q _
  constructor <;> intro h j hj
  · exact (h j hj).trans (he j hj)
  · exact (h j hj).trans (he j hj).symm

theorem finite_branching_family_bound {n : ℕ} {α : Type*}
    (S : Finset (Fin n → α)) (b : ℕ)
    (hb : ∀ f ∈ S, ∀ i, (prefixChoiceValues S f i).card ≤ b) : S.card ≤ b^n := by
  classical
  let code : {f // f ∈ S} → (Fin n → Fin b) := fun f i =>
    ⟨localChoiceRank (prefixChoiceValues S f.val i) (f.val i),
      (localChoiceRank_lt _ _ (prefixChoiceValues_self S f.val f.property i)).trans_le
        (hb f.val f.property i)⟩
  have hinj : Function.Injective code := by
    intro f g hcode
    apply Subtype.ext
    funext i
    have hrec : ∀ k, ∀ hk : k < n, f.val ⟨k,hk⟩ = g.val ⟨k,hk⟩ := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
        intro hk
        let i : Fin n := ⟨k,hk⟩
        have hprev : ∀ j, j < i → f.val j = g.val j := by
          intro j hj
          exact ih j.val hj j.isLt
        have heC := prefixChoiceValues_eq S f.val g.val i hprev
        have hval := congrArg Fin.val (congrFun hcode i)
        change localChoiceRank (prefixChoiceValues S f.val i) (f.val i) =
          localChoiceRank (prefixChoiceValues S g.val i) (g.val i) at hval
        rw [← heC] at hval
        apply localChoiceRank_injective _ (prefixChoiceValues_self S f.val f.property i) _ hval
        rw [heC]
        exact prefixChoiceValues_self S g.val g.property i
    exact hrec i.val i.isLt
  have h := Fintype.card_le_of_injective code hinj
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_fin] using h

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_ValidAttachments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

lemma mem_prefixChoiceValues {n : ℕ} {α : Type*}
    (S : Finset (Fin n → α)) (f : Fin n → α) (i : Fin n) (a : α) :
    a ∈ prefixChoiceValues S f i ↔ ∃ g ∈ S, (∀ j, j < i → g j = f j) ∧ g i = a := by
  classical
  simp only [prefixChoiceValues,Finset.mem_image,Finset.mem_filter]
  aesop

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_ValidIndexedAttachments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

lemma indexed_attachment_choices_le_two {K s : ℕ} (E : Finset (Finset (Fin K))) (birth : Fin s → Fin K)
    (hE : E.card ≤ 2) (F : PathForest s) (f : Fin s → Finset (Fin K))
    (hf : f ∈ indexedAttachmentFamily E birth F) (i : Fin s) :
    (prefixChoiceValues (indexedAttachmentFamily E birth F) f i).card ≤ 2 := by
  classical
  have hf' : ValidIndexedAttachments E birth F f := (mem_indexedAttachmentFamily _ _ _ _).mp hf
  cases hp : F.parent i with
  | none =>
    apply (Finset.card_le_card (t := E) ?_).trans hE
    intro e he
    obtain ⟨g,hg,_,rfl⟩ := (mem_prefixChoiceValues _ _ _ _).mp he
    have hvalid : ValidIndexedAttachments E birth F g := (mem_indexedAttachmentFamily _ _ _ _).mp hg
    simpa only [hp] using hvalid.2 i
  | some p =>
    let C : Finset (Finset (Fin K)) :=
      (f p).image (fun u => {birth p,u})
    have hsub : prefixChoiceValues (indexedAttachmentFamily E birth F) f i ⊆ C := by
      intro e he
      obtain ⟨g,hgS,hprev,rfl⟩ := (mem_prefixChoiceValues _ _ _ _).mp he
      have hvalid : ValidIndexedAttachments E birth F g := (mem_indexedAttachmentFamily _ _ _ _).mp hgS
      have hgp : g p = f p := hprev p (F.property i p hp)
      have hgi := hvalid.2 i
      rw [hp] at hgi
      obtain ⟨u,hu,heq⟩ := hgi
      exact Finset.mem_image.mpr ⟨u,by simpa only [hgp] using hu,heq.symm⟩
    exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans (hf'.1 p))

theorem fixed_forest_indexed_attachment_count {K s : ℕ} (E : Finset (Finset (Fin K))) (birth : Fin s → Fin K)
    (hE : E.card ≤ 2) (F : PathForest s) : (indexedAttachmentFamily E birth F).card ≤ 2^s :=
  finite_branching_family_bound _ 2 (indexed_attachment_choices_le_two E birth hE F)

end SharpTerminalLeave

open Filter
open scoped BigOperators Topology
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_EdgeMatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

namespace EdgeMatching
variable {V : Type*} [DecidableEq V] {E : Finset (Finset V)}

lemma pair (e f : Finset V) (he : e.card = 2) (hf : f.card = 2)
    (hd : Disjoint e f) : EdgeMatching {e,f} := by
  constructor
  · intro g hg
    rcases Finset.mem_insert.mp hg with h | h
    · simpa only [h] using he
    · simpa only [Finset.mem_singleton.mp h] using hf
  · intro a ha b hb hab
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact False.elim (hab rfl)
    · exact hd
    · exact hd.symm
    · exact False.elim (hab rfl)

end EdgeMatching

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_IndexedPatternEdges
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

namespace TriangleGrowth
variable {n N R : ℕ} {G : Graph n} (A : TriangleGrowth (lookupGraph G) N R)

theorem pathPattern_edges (a b : Fin N) (hR : R ≤ N) :
    (A.pathPattern a b).backEdges Finset.univ =
      indexedPatternEdges (A.pathRootEdges a b) (A.pathBirthIndex a b hR)
        (A.pathAttachments a b hR) := by
  classical
  let S := A.pathUnion a b
  have hroot : ∀ x : Fin N, x.val < R → x ∈ S :=
    fun x hx => (A.mem_pathUnion a b x).mpr (Or.inl hx)
  ext e
  constructor
  · intro he
    obtain ⟨v,_,u,hu,rfl⟩ := (A.pathPattern a b).backEdges_mem_pair he
    by_cases hv : v.val < R
    · have hvR : (S.orderEmbOfFin rfl v).val < R := by
        rw [orderEmb_initial S hR hroot v hv]
        exact hv
      have hu' : S.orderEmbOfFin rfl u ∈ A.seed.older (S.orderEmbOfFin rfl v) := by
        change u ∈ reindexSet S (A.older (S.orderEmbOfFin rfl v)) at hu
        rw [mem_reindexSet] at hu
        rwa [A.older_eq_seed hvR] at hu
      have hem : ({S.orderEmbOfFin rfl u,S.orderEmbOfFin rfl v} : Finset (Fin N)) ∈
          A.seed.backEdges A.roots :=
        Finset.mem_biUnion.mpr ⟨_,(A.mem_roots _).mpr hvR,Finset.mem_image.mpr ⟨_,hu',rfl⟩⟩
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨_,hem,?_⟩
      rw [reindexSet_pair S _ _ (S.orderEmbOfFin_mem rfl u) (S.orderEmbOfFin_mem rfl v)]
      simp only [PathForest.index_embed]
    · have hs : (A.pathUnion a b).card = R + (A.pathSuffix a b R).card :=
        prefix_suffix_card S hR hroot
      let j : Fin (A.pathSuffix a b R).card := ⟨v.val-R,by omega⟩
      have hj : A.pathBirthIndex a b hR j = v := by
        apply Fin.ext
        simp only [pathBirthIndex_val,j]
        omega
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨j,Finset.mem_univ _,Finset.mem_image.mpr ⟨u,?_,?_⟩⟩
      · change u ∈ (A.pathPattern a b).older (A.pathBirthIndex a b hR j)
        rwa [hj]
      · rw [hj]
  · intro he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨v,hv,u,hu,rfl⟩ := A.seed.backEdges_mem_pair hf
      have hvR := (A.mem_roots v).mp hv
      have huR := A.seed_root v u hu hvR
      have hvP := hroot v hvR
      have huP := hroot u huR
      rw [reindexSet_pair S u v huP hvP]
      apply Finset.mem_biUnion.mpr
      refine ⟨PathForest.index S v hvP,Finset.mem_univ _,Finset.mem_image.mpr
        ⟨PathForest.index S u huP,?_,rfl⟩⟩
      change PathForest.index S u huP ∈
        reindexSet S (A.older (S.orderEmbOfFin rfl (PathForest.index S v hvP)))
      rw [mem_reindexSet]
      rw [PathForest.embed_index,PathForest.embed_index,A.older_eq_seed hvR]
      exact hu
    · obtain ⟨i,_,he⟩ := Finset.mem_biUnion.mp he
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp he
      exact Finset.mem_biUnion.mpr ⟨A.pathBirthIndex a b hR i,Finset.mem_univ _,
        Finset.mem_image.mpr ⟨u,hu,rfl⟩⟩

theorem pathAssignment_mem_decoded {a b : Fin N} (hR : R ≤ N)
    (hi : Set.InjOn A.label (A.pathUnion a b))
    (he : A.birthGraph.ExtraEdge (lookupGraph G) A.label a b) :
    A.pathAssignment a b hi ∈ graphEmbeddingSet
      (insert ({A.pathIndex a b a (A.left_mem_pathUnion a b),
        A.pathIndex a b b (A.right_mem_pathUnion a b)} : Finset _)
        (indexedPatternEdges (A.pathRootEdges a b) (A.pathBirthIndex a b hR)
          (A.pathAttachments a b hR))) G := by
  rw [← A.pathPattern_edges a b hR]
  exact A.pathAssignment_mem hi he

end TriangleGrowth
end SharpTerminalLeave

open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_MarkedIndexedAttachmentPattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave
open Classical in

theorem marked_indexed_attachment_pattern_count {K s : ℕ}
    (E : Finset (Finset (Fin K))) (birth : Fin s → Fin K) (hE : E.card ≤ 2) (a b : Option (Fin s)) :
    Fintype.card (Σ F : {F : PathForest s // ∀ v, F.OnPath a v ∨ F.OnPath b v},
      {f // f ∈ indexedAttachmentFamily E birth F.val}) ≤ 6^s := by
  classical
  rw [Fintype.card_sigma]
  calc
    ∑ F : {F : PathForest s // ∀ v, F.OnPath a v ∨ F.OnPath b v},
        Fintype.card {f // f ∈ indexedAttachmentFamily E birth F.val}
      ≤ ∑ _F : {F : PathForest s // ∀ v, F.OnPath a v ∨ F.OnPath b v}, 2^s := by
        apply Finset.sum_le_sum
        intro F _
        simpa only [Fintype.card_coe] using fixed_forest_indexed_attachment_count E birth hE F.val
    _ = Fintype.card {F : PathForest s // ∀ v, F.OnPath a v ∨ F.OnPath b v} * 2^s := by
      simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
    _ ≤ 3^s * 2^s := Nat.mul_le_mul_right _ (PathForest.two_path_forest_count a b)
    _ = 6^s := by rw [← Nat.mul_pow]

open Classical in

theorem all_marked_indexed_attachment_pattern_count {K s : ℕ} {M : Type*} [Fintype M]
    (E : Finset (Finset (Fin K))) (birth : Fin s → Fin K) (hE : E.card ≤ 2) (mark : M → Option (Fin s)) :
    Fintype.card (Σ ab : M × M,
      Σ F : {F : PathForest s // ∀ v, F.OnPath (mark ab.1) v ∨ F.OnPath (mark ab.2) v},
        {f // f ∈ indexedAttachmentFamily E birth F.val}) ≤ (Fintype.card M)^2 * 6^s := by
  classical
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _ab : M × M, 6^s := by
      apply Finset.sum_le_sum
      intro ab _
      exact marked_indexed_attachment_pattern_count E birth hE _ _
    _ = (Fintype.card M)^2 * 6^s := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,smul_eq_mul,pow_two]

end SharpTerminalLeave

open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_SuffixProjection
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

namespace TriangleGrowth
variable {n N R : ℕ} {G : Graph n} (A : TriangleGrowth (lookupGraph G) N R)

lemma pathRootEdges_count (a b : Fin N) :
    (A.pathRootEdges a b).card ≤ (A.seed.backEdges A.roots).card := Finset.card_image_le

end TriangleGrowth
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_IndexedWitnessCode
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

lemma seedPatternChoices_card {K R : ℕ} (hR : R ≤ K) (h4 : R ≤ 4) :
    (seedPatternChoices K R).card ≤ 64 := by
  have hc : (initialVertices K R).card = R := by
    simp only [initialVertices,Fin.card_filter_val_lt,Nat.min_eq_right hR]
  calc
    _ ≤ ((rootEdgeUniverse K R).powerset).card := Finset.card_filter_le _ _
    _ = 2^(R.choose 2) := by rw [Finset.card_powerset,rootEdgeUniverse,Finset.card_powersetCard,hc]
    _ ≤ 2^((4 : ℕ).choose 2) := Nat.pow_le_pow_right (by norm_num) (Nat.choose_le_choose 2 h4)
    _ = 64 := by decide

namespace TriangleGrowth
variable {n N R : ℕ} {G : Graph n} (A : TriangleGrowth (lookupGraph G) N R)

lemma pathRootEdges_mem_seedPatternChoices (a b : Fin N) (hR : R ≤ N)
    (hE : (A.seed.backEdges A.roots).card ≤ 2) :
    A.pathRootEdges a b ∈ seedPatternChoices (A.pathUnion a b).card R := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powerset.mpr ?_,(A.pathRootEdges_count a b).trans hE⟩
  intro edge hedge
  obtain ⟨seedEdge,hseedEdge,rfl⟩ := Finset.mem_image.mp hedge
  obtain ⟨later,hlater,earlier,hearlier,rfl⟩ := A.seed.backEdges_mem_pair hseedEdge
  have hlaterRoot := (A.mem_roots later).mp hlater
  have hearlierRoot := A.seed_root later earlier hearlier hlaterRoot
  have hroot : ∀ vertex : Fin N, vertex.val < R → vertex ∈ A.pathUnion a b :=
    fun vertex hvertex => (A.mem_pathUnion a b vertex).mpr (Or.inl hvertex)
  have hsubset : ({earlier,later} : Finset (Fin N)) ⊆ A.pathUnion a b := by
    intro vertex hvertex
    simp only [Finset.mem_insert,Finset.mem_singleton] at hvertex
    rcases hvertex with rfl | rfl
    · exact hroot _ hearlierRoot
    · exact hroot _ hlaterRoot
  apply Finset.mem_powersetCard.mpr
  refine ⟨?_,(reindexSet_card hsubset).trans
    (Finset.card_pair (ne_of_lt (A.seed.older_lt later earlier hearlier)))⟩
  intro vertex hvertex
  apply (mem_initialVertices _ _ _).mpr
  have hembedded := (mem_reindexSet _ _ _).mp hvertex
  have hembeddedRoot : ((A.pathUnion a b).orderEmbOfFin rfl vertex).val < R := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hembedded
    rcases hembedded with hearlierEq | hlaterEq
    · simpa only [hearlierEq] using hearlierRoot
    · simpa only [hlaterEq] using hlaterRoot
  let rootIndex : Fin (A.pathUnion a b).card :=
    ⟨((A.pathUnion a b).orderEmbOfFin rfl vertex).val,
      hembeddedRoot.trans_le (roots_le_card _ hR hroot)⟩
  have hequal : rootIndex = vertex := by
    apply ((A.pathUnion a b).orderEmbOfFin rfl).injective
    exact Fin.ext (orderEmb_initial _ hR hroot rootIndex hembeddedRoot)
  rw [← hequal]
  exact hembeddedRoot

end TriangleGrowth
end SharpTerminalLeave

open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_Address
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave
namespace PathForest
variable {s : ℕ} {α : Type*}

lemma address_none (F : PathForest s) (key : Fin s → α) (i : Fin s)
    (hp : F.parent i = none) : F.address key i = [key i] := by
  rw [address,hp]

lemma address_some (F : PathForest s) (key : Fin s → α) (i j : Fin s)
    (hp : F.parent i = some j) : F.address key i = key i :: F.address key j := by
  rw [address,hp]

lemma address_unique (F : PathForest s) (key : Fin s → α) (ρ : Fin s → List α)
    (hρ : ∀ i, ρ i = key i :: (F.parent i).elim [] ρ) (i : Fin s) :
    F.address key i = ρ i := by
  induction i using (measure (fun i : Fin s => i.val)).wf.induction with
  | h i ih =>
    cases hp : F.parent i with
    | none => rw [F.address_none key i hp,hρ i,hp]; rfl
    | some j =>
      rw [F.address_some key i j hp,ih j (F.property i j hp),hρ i,hp]
      rfl

end PathForest

namespace TriangleGrowth
variable {n N R : ℕ} {G : Graph n} (A : TriangleGrowth (lookupGraph G) N R)

lemma pathAttachments_image (a b : Fin N) (hR : R ≤ N)
    (hi : Set.InjOn A.label (A.pathUnion a b)) (i : Fin (A.pathSuffix a b R).card) :
    (A.pathAttachments a b hR i).image (A.pathAssignment a b hi) =
      A.attach ((A.pathSuffix a b R).orderEmbOfFin rfl i) := by
  rw [A.pathAttachments_eq]
  change (reindexSet (A.pathUnion a b) _).image
    (A.label ∘ (A.pathUnion a b).orderEmbOfFin rfl) = _
  rw [← Finset.image_image,image_reindexSet]
  · exact ((A.older_invariants _).2 ((A.mem_pathSuffix a b _ R).mp
      ((A.pathSuffix a b R).orderEmbOfFin_mem rfl i)).2).2.1
  · intro x hx
    exact A.pathUnion_older_closed ((A.mem_pathSuffix a b _ R).mp
      ((A.pathSuffix a b R).orderEmbOfFin_mem rfl i)).1 hx

lemma indexedTriangleKey_actual (a b : Fin N) (hR : R ≤ N)
    (hi : Set.InjOn A.label (A.pathUnion a b)) (i : Fin (A.pathSuffix a b R).card) :
    indexedTriangleKey (A.pathBirthIndex a b hR) (A.pathAttachments a b hR)
      (A.pathAssignment a b hi) i =
      (A.attach ((A.pathSuffix a b R).orderEmbOfFin rfl i),
        insert (A.label ((A.pathSuffix a b R).orderEmbOfFin rfl i))
          (A.attach ((A.pathSuffix a b R).orderEmbOfFin rfl i))) := by
  unfold indexedTriangleKey
  rw [A.pathAttachments_image]
  change (_,insert (A.label ((A.pathUnion a b).orderEmbOfFin rfl _)) _) = _
  rw [A.pathBirthIndex_embedding]

end TriangleGrowth
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_IndexedAttachmentOlder
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

lemma indexed_attachment_older {K s R : ℕ} {E : Graph K}
    {birth : Fin s → Fin K} (hb : ∀ i, (birth i).val = R+i.val)
    (hE : E ∈ seedPatternChoices K R) (F : PathForest s)
    (f : Fin s → Finset (Fin K)) (hf : f ∈ indexedAttachmentFamily E birth F) :
    ∀ i, ∀ x ∈ f i, x.val < (birth i).val := by
  have hvalid := (mem_indexedAttachmentFamily E birth F f).mp hf
  intro i
  induction i using (measure (fun i : Fin s => i.val)).wf.induction with
  | h i ih =>
    intro x hx
    have hi := hvalid.2 i
    cases hp : F.parent i with
    | none =>
      rw [hp] at hi
      have he : f i ∈ rootEdgeUniverse K R := (Finset.mem_powerset.mp (Finset.mem_filter.mp hE).1) hi
      have hxr := (mem_initialVertices K R x).mp ((Finset.mem_powersetCard.mp he).1 hx)
      rw [hb]
      omega
    | some p =>
      rw [hp] at hi
      obtain ⟨u,hu,he⟩ := hi
      rw [he] at hx
      have hpi := F.property i p hp
      have hu' := ih p hpi u hu
      have hbirth : (birth p).val < (birth i).val := by
        rw [hb p,hb i]
        omega
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hbirth
      · have he := Finset.mem_singleton.mp hx
        subst x
        exact lt_trans hu' hbirth

lemma indexed_triangle_key_injective {n K s R : ℕ} {E : Graph K}
    {birth : Fin s → Fin K} (hb : ∀ i, (birth i).val = R+i.val)
    (hE : E ∈ seedPatternChoices K R) (F : PathForest s)
    (f : Fin s → Finset (Fin K)) (hf : f ∈ indexedAttachmentFamily E birth F)
    (ψ : Fin K ↪ Fin n) : Function.Injective (indexedTriangleKey birth f ψ) := by
  intro i j he
  have hi : ψ (birth i) ∈ (indexedTriangleKey birth f ψ j).2 := by
    rw [← he]
    exact Finset.mem_insert_self _ _
  have hj : ψ (birth j) ∈ (indexedTriangleKey birth f ψ i).2 := by
    rw [he]
    exact Finset.mem_insert_self _ _
  have hle (a b : Fin s) (h : ψ (birth a) ∈ (indexedTriangleKey birth f ψ b).2) :
      a.val ≤ b.val := by
    change ψ (birth a) ∈ insert (ψ (birth b)) ((f b).image ψ) at h
    rcases Finset.mem_insert.mp h with h | h
    · have hh := congrArg Fin.val (ψ.injective h)
      rw [hb a,hb b] at hh
      omega
    · obtain ⟨x,hx,hxe⟩ := Finset.mem_image.mp h
      have hxe' := ψ.injective hxe
      subst x
      have hh := indexed_attachment_older hb hE F f hf b (birth a) hx
      rw [hb a,hb b] at hh
      omega
  exact Fin.ext (Nat.le_antisymm (hle i j hi) (hle j i hj))

end SharpTerminalLeave

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_ThreeChooseBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

lemma three_choose_bound (h a b : ℕ) :
    (h+a+b).choose h * (a+b).choose a ≤ 3^(h+a+b) := by
  have hb := Nat.choose_le_two_pow (a+b) a
  have hh := Nat.mul_le_mul_left ((h+a+b).choose h) hb
  have ht := Finset.single_le_sum (s := Finset.range (h+a+b+1))
    (f := fun j => (1 : ℕ)^j*2^(h+a+b-j)*(h+a+b).choose j)
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (show h < h+a+b+1 by omega))
  have he : h+a+b-h = a+b := by omega
  have hsum : (∑ j ∈ Finset.range (h+a+b+1),
      (1 : ℕ)^j*2^(h+a+b-j)*(h+a+b).choose j) = 3^(h+a+b) := by
    simpa only [Nat.cast_id] using (add_pow (1 : ℕ) 2 (h+a+b)).symm
  rw [hsum,he] at ht
  exact hh.trans (by simpa only [one_pow,one_mul,Nat.mul_comm] using ht)

lemma three_factorial_bound (h a b : ℕ) :
    (h+a+b).factorial ≤ 3^(h+a+b) * (h.factorial*a.factorial*b.factorial) := by
  have hbc := Nat.choose_mul_factorial_mul_factorial (show a ≤ a+b by omega)
  have hha := Nat.choose_mul_factorial_mul_factorial (show h ≤ h+a+b by omega)
  have hsub1 : a+b-a = b := by omega
  have hsub2 : h+a+b-h = a+b := by omega
  rw [hsub1] at hbc
  rw [hsub2] at hha
  have hi : (h+a+b).choose h * (a+b).choose a *
      (h.factorial*a.factorial*b.factorial) = (h+a+b).factorial := by
    calc
      _ = (h+a+b).choose h * h.factorial *
          ((a+b).choose a * a.factorial * b.factorial) := by ring
      _ = _ := by rw [hbc,hha]
  rw [← hi]
  exact Nat.mul_le_mul_right _ (three_choose_bound h a b)

theorem total_three_segment_weight_le {x : ℝ} (hx : 0 ≤ x) (h a b : ℕ) :
    x^(h+a+b) / ((h.factorial : ℝ)*(a.factorial : ℝ)*(b.factorial : ℝ)) ≤
      (3*x)^(h+a+b) / ((h+a+b).factorial : ℝ) := by
  have hf : ((h+a+b).factorial : ℝ) ≤
      (3 : ℝ)^(h+a+b)*((h.factorial : ℝ)*(a.factorial : ℝ)*(b.factorial : ℝ)) := by
    exact_mod_cast three_factorial_bound h a b
  have hh := mul_le_mul_of_nonneg_left hf (pow_nonneg hx (h+a+b))
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  rw [mul_pow]
  nlinarith only [hh]

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Probability_TrueProbabilityMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave
open scoped BigOperators

theorem pmf_map_congr_support {A B : Type*} (p : PMF A) (f g : A → B)
    (h : ∀ x ∈ p.support, f x = g x) : p.map f = p.map g := by
  unfold PMF.map
  apply pmf_bind_congr_on_support
  intro x hx
  rw [Function.comp_apply, Function.comp_apply, h x hx]

end SharpTerminalLeave

open scoped BigOperators ENNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_MatchingSeedEdgeRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

section MatchingSeedEdgeCount
variable {V : Type*} [DecidableEq V] {N R : ℕ}
variable (label : Fin N → V) (E : Finset (Finset V)) (hE : EdgeMatching E)
variable (hi : Set.InjOn label {v | v.val < R})

lemma matchingSeed_edge_roots (Z : Finset (Fin N)) {e : Finset (Fin N)}
    (he : e ∈ (matchingSeed label E hE hi).backEdges Z) :
    ∀ x ∈ e, x.val < R := by
  obtain ⟨v,_,u,hu,rfl⟩ := BirthGraph.backEdges_mem_pair _ he
  obtain ⟨hv,huv,_⟩ := (matchingSeed_mem_older label E hE hi v u).mp hu
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact lt_trans huv hv
  · simpa only [Finset.mem_singleton] using (Finset.mem_singleton.mp hx ▸ hv)

lemma matchingSeed_edge_image (Z : Finset (Fin N)) {e : Finset (Fin N)}
    (he : e ∈ (matchingSeed label E hE hi).backEdges Z) : e.image label ∈ E := by
  obtain ⟨v,_,u,hu,rfl⟩ := BirthGraph.backEdges_mem_pair _ he
  simpa only [Finset.image_insert,Finset.image_singleton] using
    ((matchingSeed_mem_older label E hE hi v u).mp hu).2.2

theorem matchingSeed_edge_count (Z : Finset (Fin N)) :
    ((matchingSeed label E hE hi).backEdges Z).card ≤ E.card := by
  classical
  let S := (matchingSeed label E hE hi).backEdges Z
  have hinj : Set.InjOn (Finset.image label) S := by
    intro e he f hf hEq
    have heR := matchingSeed_edge_roots label E hE hi Z he
    have hfR := matchingSeed_edge_roots label E hE hi Z hf
    apply Finset.Subset.antisymm
    · intro x hx
      have hxI : label x ∈ f.image label := hEq ▸ Finset.mem_image_of_mem label hx
      obtain ⟨y,hy,hxy⟩ := Finset.mem_image.mp hxI
      exact hi (hfR y hy) (heR x hx) hxy ▸ hy
    · intro y hy
      have hyI : label y ∈ e.image label := hEq.symm ▸ Finset.mem_image_of_mem label hy
      obtain ⟨x,hx,hxy⟩ := Finset.mem_image.mp hyI
      exact hi (heR x hx) (hfR y hy) hxy ▸ hx
  rw [← Finset.card_image_of_injOn hinj]
  apply Finset.card_le_card
  intro e he
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
  exact matchingSeed_edge_image label E hE hi Z hf

end MatchingSeedEdgeCount

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_MatchingSeedFullEdge
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

theorem matchingSeed_full_edge_count {V : Type*} [DecidableEq V] {N R : ℕ}
    (label : Fin N → V) (E : Finset (Finset V)) (hE : EdgeMatching E)
    (hi : Set.InjOn label {v | v.val < R})
    (hc : ∀ e ∈ E, ∀ x ∈ e, ∃ v : Fin N, v.val < R ∧ label v = x) :
    ((matchingSeed label E hE hi).backEdges (Finset.univ.filter (fun v => v.val < R))).card = E.card := by
  classical
  apply Nat.le_antisymm (matchingSeed_edge_count label E hE hi _)
  let S := (matchingSeed label E hE hi).backEdges (Finset.univ.filter (fun v => v.val < R))
  have hsub : E ⊆ S.image (Finset.image label) := by
    intro e he
    obtain ⟨x,y,hx,hy,hxy,rfl⟩ := matchingSeed_covers label E hE hi hc e he
    have hp : ({x,y} : Finset (Fin N)) ∈ S := by
      rcases hxy with hxy | hyx
      · exact Finset.mem_biUnion.mpr ⟨y,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy⟩,
          Finset.mem_image.mpr ⟨x,hxy,rfl⟩⟩
      · have hh : ({y,x} : Finset (Fin N)) ∈ S := Finset.mem_biUnion.mpr
          ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩,Finset.mem_image.mpr ⟨y,hyx,rfl⟩⟩
        simpa only [Finset.pair_comm] using hh
    exact Finset.mem_image.mpr ⟨{x,y},hp,by simp only [Finset.image_insert,Finset.image_singleton]⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

namespace RecordedCallForest
variable {n : ℕ} {G : Graph n} {c : QueryCall (Finset (Fin n)) (Finset (Fin n))}
variable (F : RecordedCallForest (triangleHypergraph G) c)

lemma growth_seed_card (hM : EdgeMatching c.focus) (hG : c.focus ⊆ G) :
    ((F.toTriangleGrowth hM hG).seed.backEdges (F.toTriangleGrowth hM hG).roots).card = c.focus.card :=
  matchingSeed_full_edge_count F.vertexLabel c.focus hM F.vertexLabel_injective_roots F.vertexLabel_covers

lemma rootCount_focus_card (hM : EdgeMatching c.focus) : F.rootCount = 2*c.focus.card := by
  classical
  rw [rootCount,rootSet,Finset.card_biUnion]
  · calc
      ∑ e ∈ c.focus, e.card = ∑ _e ∈ c.focus, 2 := Finset.sum_congr rfl (fun e he => hM.1 e he)
      _ = 2*c.focus.card := by simp only [Finset.sum_const,smul_eq_mul,Nat.mul_comm]
  · exact hM.2

end RecordedCallForest
end SharpTerminalLeave

open Filter
open scoped BigOperators Topology
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_CallPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave
section LegalPathCover
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

omit [Fintype τ] [DecidableEq τ] in
lemma callAtPath_address (H : τ → Finset ι) (c : QueryCall ι τ) (p : List (ι × τ)) :
    (callAtPath H c p).address = p.reverse ++ c.address := by
  induction p generalizing c with
  | nil => simp [callAtPath]
  | cons a as ih => simp only [callAtPath,ih,List.reverse_cons,List.append_assoc,List.singleton_append]

lemma mem_legalPaths (H : τ → Finset ι) (d : ℕ) (focus : Finset ι) (parent : Option τ)
    (p : List (ι × τ)) : p ∈ legalPaths H d focus parent ↔
      LegalQueryPath H focus parent p ∧ p.length ≤ d := by
  induction d generalizing focus parent p with
  | zero => cases p <;> simp [legalPaths,LegalQueryPath]
  | succ d ih =>
    cases p with
    | nil => simp [legalPaths,LegalQueryPath]
    | cons a as =>
      simp only [legalPaths,Finset.mem_insert,List.cons_ne_nil,Finset.mem_biUnion,
        Finset.mem_image,false_or,List.cons.injEq,LegalQueryPath,List.length_cons]
      constructor
      · rintro ⟨b,hb,t,ht,hba,rfl⟩
        subst b
        obtain ⟨hl,hn⟩ := (ih _ _ _).mp ht
        exact ⟨⟨hb,hl⟩,by omega⟩
      · rintro ⟨⟨ha,hl⟩,hn⟩
        exact ⟨a,ha,as,(ih _ _ _).mpr ⟨hl,by omega⟩,rfl,rfl⟩

theorem tracedGridQuery_legal_path (H : τ → Finset ι) (N d k : ℕ) (c : QueryCall ι τ)
    (ν : τ → PMF (Fin N)) {z : (Bool × List (QueryCall ι τ)) × List τ}
    (hz : z ∈ (ExposureTree.freshLog ν (tracedGridQuery H N d k c)).support) :
    ∀ a ∈ z.1.2, ∃ p ∈ legalPaths H d c.focus c.parent, a = callAtPath H c p := by
  induction d generalizing k c z with
  | zero =>
    rw [tracedGridQuery,ExposureTree.freshLog_bind] at hz
    obtain ⟨x,_,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    have he : y = ((true,[c]),[]) := by simpa [ExposureTree.freshLog] using hy
    subst y
    intro a ha
    have he : a = c := by simpa using ha
    subst a
    exact ⟨[],by simp [legalPaths],rfl⟩
  | succ d ih =>
    rw [tracedGridQuery,ExposureTree.freshLog_bind] at hz
    obtain ⟨x,hx,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    rw [ExposureTree.freshLog_mapOutput] at hy
    obtain ⟨w,hw,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
    have hxv := (ExposureTree.freshLog_exposeLabeled_support ν Prod.snd _ hx).1
    have hh := ExposureTree.freshLog_checkNoneTrace_forall ν
      (fun a : QueryCall ι τ => ∃ p ∈ legalPaths H (d+1) c.focus c.parent,
        a = callAtPath H c p) _ (by
          intro A hA z hz
          obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hA
          have hq' : q ∈ x.1 := (List.mergeSort_perm _ _).mem_iff.mp hq
          have hcand : q.1 ∈ gridCandidates H c.focus c.parent := by
            have hm : q.1 ∈ x.1.map Prod.fst := List.mem_map.mpr ⟨q,hq',rfl⟩
            rw [hxv] at hm
            exact Finset.mem_toList.mp hm
          split_ifs at hz with hqk
          · intro a ha
            obtain ⟨p,hp,he⟩ := ih _ _ hz a ha
            refine ⟨q.1 :: p,?_,he⟩
            apply Finset.mem_insert_of_mem
            apply Finset.mem_biUnion.mpr
            exact ⟨q.1,hcand,Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩
          · have he : z = ((false,[]),[]) := by simpa [ExposureTree.freshLog] using hz
            simp [he]) hw
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨[],Finset.mem_insert_self _ _,rfl⟩
    · exact hh a ha

end LegalPathCover
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_Separated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave
section CandidateUniqueness
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

lemma gridCandidates_key_injective (H : τ → Finset ι) (c : QueryCall ι τ)
    (hc : c.Separated H) :
    Set.InjOn Prod.snd (↑(gridCandidates H c.focus c.parent) : Set (ι × τ)) := by
  intro a ha b hb hab
  obtain ⟨haF,haT,haP⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbF,hbT,_⟩ := Finset.mem_filter.mp hb
  have haF := (Finset.mem_product.mp haF).1
  have hbF := (Finset.mem_product.mp hbF).1
  apply Prod.ext _ hab
  have haI : a.1 ∈ H a.2 ∩ c.focus := Finset.mem_inter.mpr ⟨haT,haF⟩
  have hbI : b.1 ∈ H a.2 ∩ c.focus := Finset.mem_inter.mpr ⟨hab ▸ hbT,hbF⟩
  exact (Finset.card_le_one.mp (hc a.2 haP)) _ haI _ hbI

theorem QueryCall.keys_nodup (H : τ → Finset ι) (c : QueryCall ι τ)
    (hc : c.Separated H) : (c.keys H).Nodup := by
  apply List.Nodup.map_on _ (Finset.nodup_toList _)
  intro a ha b hb hab
  exact gridCandidates_key_injective H c hc
    (Finset.mem_toList.mp ha) (Finset.mem_toList.mp hb) hab

omit [Fintype τ] [DecidableEq τ] in

lemma separated_child (H : τ → Finset ι)
    (hlin : ∀ T S, T ≠ S → (H T ∩ H S).card ≤ 1)
    (address : List (ι × τ)) (e : ι) (T : τ) :
    (QueryCall.mk ((e,T)::address) ((H T).erase e) (some T)).Separated H := by
  intro S hS
  have hne : S ≠ T := by simpa using hS
  change (H S ∩ (H T).erase e).card ≤ 1
  apply (Finset.card_le_card (show H S ∩ (H T).erase e ⊆ H S ∩ H T from
    fun x hx => Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
      Finset.erase_subset _ _ (Finset.mem_inter.mp hx).2⟩)).trans
  exact hlin S T hne

end CandidateUniqueness
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_TracedGridQueryLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave
section TraceAccounting
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem tracedGridQuery_log (H : τ → Finset ι) (N d k : ℕ) (c : QueryCall ι τ)
    (ν : τ → PMF (Fin N)) {z : (Bool × List (QueryCall ι τ)) × List τ}
    (hz : z ∈ (ExposureTree.freshLog ν (tracedGridQuery H N d k c)).support) :
    z.2 = z.1.2.flatMap (QueryCall.keys H) := by
  induction d generalizing k c z with
  | zero =>
    rw [tracedGridQuery, ExposureTree.freshLog_bind] at hz
    obtain ⟨x,hx,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    have heq : y = ((true,[c]),[]) := by
      simpa [ExposureTree.freshLog] using hy
    have hkeys := (ExposureTree.freshLog_exposeLabeled_support ν Prod.snd _ hx).2
    simp [heq, hkeys, QueryCall.keys]
  | succ d ih =>
    rw [tracedGridQuery, ExposureTree.freshLog_bind] at hz
    obtain ⟨x,hx,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    rw [ExposureTree.freshLog_mapOutput] at hy
    obtain ⟨w,hw,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
    have hxkeys := (ExposureTree.freshLog_exposeLabeled_support ν Prod.snd _ hx).2
    have hwkeys := ExposureTree.freshLog_checkNoneTrace_support ν (QueryCall.keys H) _
      (by
        intro A hA a ha
        obtain ⟨p,_,rfl⟩ := List.mem_map.mp hA
        split_ifs at ha with hp
        · exact ih _ _ ha
        · have heq : a = ((false,[]),[]) := by
            simpa [ExposureTree.freshLog] using ha
          simp [heq]) hw
    simp only [List.flatMap_cons, hxkeys, hwkeys, QueryCall.keys]

end TraceAccounting
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_TracedGridQuerySeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave
section TrueRepeatedCall
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem tracedGridQuery_separated (H : τ → Finset ι)
    (hlin : ∀ T S, T ≠ S → (H T ∩ H S).card ≤ 1)
    (N d k : ℕ) (c : QueryCall ι τ) (hc : c.Separated H)
    (ν : τ → PMF (Fin N)) {z : (Bool × List (QueryCall ι τ)) × List τ}
    (hz : z ∈ (ExposureTree.freshLog ν (tracedGridQuery H N d k c)).support) :
    ∀ a ∈ z.1.2, a.Separated H := by
  induction d generalizing k c z with
  | zero =>
    rw [tracedGridQuery, ExposureTree.freshLog_bind] at hz
    obtain ⟨x,_,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    have heq : y = ((true,[c]),[]) := by simpa [ExposureTree.freshLog] using hy
    simpa [heq] using hc
  | succ d ih =>
    rw [tracedGridQuery, ExposureTree.freshLog_bind] at hz
    obtain ⟨x,_,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    rw [ExposureTree.freshLog_mapOutput] at hy
    obtain ⟨w,hw,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
    have hwP := ExposureTree.freshLog_checkNoneTrace_forall ν (fun a => a.Separated H) _
      (by
        intro A hA a ha
        obtain ⟨p,_,rfl⟩ := List.mem_map.mp hA
        split_ifs at ha with hp
        · exact ih _ _ (separated_child H hlin _ _ _) ha
        · have heq : a = ((false,[]),[]) := by simpa [ExposureTree.freshLog] using ha
          simp [heq]) hw
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hc
    · exact hwP a ha

theorem repeated_flatMap_calls {R K : Type*} [DecidableEq K]
    (calls : List R) (keys : R → List K)
    (hc : ∀ c ∈ calls, (keys c).Nodup)
    (hr : ExposureTree.repeats ∅ (calls.flatMap keys) = true) :
    ∃ i j : Fin calls.length, i < j ∧ ∃ T,
      T ∈ keys (calls.get i) ∧ T ∈ keys (calls.get j) := by
  by_contra hn
  have hnd : (calls.flatMap keys).Nodup := by
    apply List.nodup_flatMap.mpr
    refine ⟨hc, List.pairwise_iff_get.mpr ?_⟩
    intro i j hij
    apply List.disjoint_left.mpr
    intro T hTi hTj
    exact hn ⟨i,j,hij,T,hTi,hTj⟩
  have hf := (ExposureTree.repeats_empty_false_iff _).mpr hnd
  rw [hr] at hf
  contradiction

theorem tracedGridQuery_repeat_calls (H : τ → Finset ι)
    (hlin : ∀ T S, T ≠ S → (H T ∩ H S).card ≤ 1)
    (N d k : ℕ) (c : QueryCall ι τ) (hc : c.Separated H)
    (ν : τ → PMF (Fin N)) {z : (Bool × List (QueryCall ι τ)) × List τ}
    (hz : z ∈ (ExposureTree.freshLog ν (tracedGridQuery H N d k c)).support)
    (hr : ExposureTree.repeats ∅ z.2 = true) :
    ∃ i j : Fin z.1.2.length, i < j ∧ ∃ T,
      T ∈ (z.1.2.get i).keys H ∧ T ∈ (z.1.2.get j).keys H := by
  have hp := tracedGridQuery_separated H hlin N d k c hc ν hz
  rw [tracedGridQuery_log H N d k c ν hz] at hr
  exact repeated_flatMap_calls _ _ (fun a ha => a.keys_nodup H (hp a ha)) hr

end TrueRepeatedCall
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_TriangleHypergraphLinear
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

theorem triangleHypergraph_linear {n : ℕ} (G : Graph n)
    (T S : Finset (Fin n)) (hTS : T ≠ S) :
    (triangleHypergraph G T ∩ triangleHypergraph G S).card ≤ 1 := by
  by_cases hT : T ∈ triangles G
  · by_cases hS : S ∈ triangles G
    · simp only [triangleHypergraph, hT, hS, ↓reduceIte]
      apply Finset.card_le_one.mpr
      intro e he f hf
      by_contra hef
      obtain ⟨heT,heS⟩ := Finset.mem_inter.mp he
      obtain ⟨hfT,hfS⟩ := Finset.mem_inter.mp hf
      obtain ⟨heT,hce⟩ := Finset.mem_powersetCard.mp heT
      obtain ⟨hfT,hcf⟩ := Finset.mem_powersetCard.mp hfT
      have heS := (Finset.mem_powersetCard.mp heS).1
      have hfS := (Finset.mem_powersetCard.mp hfS).1
      exact hTS (triangle_eq_of_two_edges (mem_triangles.mp hT).1
        (mem_triangles.mp hS).1 hce hcf hef heT hfT heS hfS)
    · simp [triangleHypergraph, hS]
  · simp [triangleHypergraph, hT]

lemma disjoint_edges_not_same_triangle {α : Type*} [DecidableEq α]
    {T e f : Finset α} (hT : T.card = 3)
    (he : e ∈ T.powersetCard 2) (hf : f ∈ T.powersetCard 2)
    (hd : Disjoint e f) : False := by
  obtain ⟨he,hce⟩ := Finset.mem_powersetCard.mp he
  obtain ⟨hf,hcf⟩ := Finset.mem_powersetCard.mp hf
  have hh := Finset.card_le_card (Finset.union_subset he hf)
  rw [Finset.card_union_of_disjoint hd,hce,hcf,hT] at hh
  omega

theorem triangleHypergraph_separated_disjoint_roots {n : ℕ} (G : Graph n)
    (e f : Finset (Fin n)) (hd : Disjoint e f) :
    (QueryCall.mk [] {e,f} none).Separated (triangleHypergraph G) := by
  intro T _
  by_cases hT : T ∈ triangles G
  · change (triangleHypergraph G T ∩ {e,f}).card ≤ 1
    simp only [triangleHypergraph,hT,↓reduceIte]
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨haT,haR⟩ := Finset.mem_inter.mp ha
    obtain ⟨hbT,hbR⟩ := Finset.mem_inter.mp hb
    simp only [Finset.mem_insert,Finset.mem_singleton] at haR hbR
    rcases haR with rfl | rfl <;> rcases hbR with rfl | rfl
    · rfl
    · exact False.elim (disjoint_edges_not_same_triangle (mem_triangles.mp hT).1 haT hbT hd)
    · exact False.elim (disjoint_edges_not_same_triangle (mem_triangles.mp hT).1 hbT haT hd)
    · rfl
  · simp [triangleHypergraph,hT]

theorem graph_query_repeat_addresses {n : ℕ} (G : Graph n) (N d k : ℕ)
    (c : QueryCall (Finset (Fin n)) (Finset (Fin n)))
    (hc : c.Separated (triangleHypergraph G))
    (ν : Finset (Fin n) → PMF (Fin N))
    {z : (Bool × List (QueryCall (Finset (Fin n)) (Finset (Fin n)))) × List (Finset (Fin n))}
    (hz : z ∈ (ExposureTree.freshLog ν
      (tracedGridQuery (triangleHypergraph G) N d k c)).support)
    (hr : ExposureTree.repeats ∅ z.2 = true) :
    ∃ a ∈ z.1.2, ∃ b ∈ z.1.2, a.address ≠ b.address ∧ ∃ T,
      T ∈ a.keys (triangleHypergraph G) ∧ T ∈ b.keys (triangleHypergraph G) := by
  obtain ⟨i,j,hij,T,hi,hj⟩ := tracedGridQuery_repeat_calls _
    (triangleHypergraph_linear G) N d k c hc ν hz hr
  have hnd := tracedGridQuery_address_nodup _ N d k c ν hz
  have hpair : z.1.2.Pairwise (fun a b => a.address ≠ b.address) := by
    simpa only [List.Nodup,List.pairwise_map] using hnd
  exact ⟨z.1.2.get i, List.get_mem _ _, z.1.2.get j, List.get_mem _ _,
    List.pairwise_iff_get.mp hpair i j hij, T, hi, hj⟩

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_FreshMemSelected
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.RecordedCallForest
variable {n : ℕ} {G : Graph n} {c : QueryCall (Finset (Fin n)) (Finset (Fin n))}
variable (F : RecordedCallForest (triangleHypergraph G) c)
variable (hM : EdgeMatching c.focus) (hG : c.focus ⊆ G)

lemma fresh_mem_selected {V : Type*} [DecidableEq V] {e a : Finset V} {x : V}
    (he : e.card = 2) (ha : a.card = 2) (hs : e ⊆ insert x a) (hne : e ≠ a) : x ∈ e := by
  by_contra hx
  have hh : e ⊆ a := by
    intro z hz
    exact (Finset.mem_insert.mp (hs hz)).resolve_left (fun he => hx (he ▸ hz))
  exact hne (Finset.eq_of_subset_of_card_le hh (by rw [he,ha]))

lemma pair_has_other {V : Type*} [DecidableEq V] {e : Finset V} (he : e.card = 2) (x : V) :
    ∃ z ∈ e, z ≠ x := by
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp he
  by_cases ha : a = x
  · exact ⟨b,by simp,ha ▸ hab.symm⟩
  · exact ⟨a,by simp,ha⟩

lemma candidate_nonroot_exposed (i : Fin F.size) (hi : i ≠ F.root)
    (p : Finset (Fin n) × Finset (Fin n))
    (hp : p ∈ gridCandidates (triangleHypergraph G) (F.call i).focus (F.call i).parent) :
    (F.toTriangleGrowth hM hG).birthGraph.ExposedAt (lookupGraph G) F.vertexLabel
      (F.birthIndex i hi) p.2 := by
  let A := F.toTriangleGrowth hM hG
  have hc := (graphCandidate_iff G _ _ _).mp hp
  have hf := hc.1
  rw [F.incoming_focus i hi] at hf
  obtain ⟨hediff,hepow⟩ := Finset.mem_erase.mp hf
  obtain ⟨hes,hec⟩ := Finset.mem_powersetCard.mp hepow
  have hes' : p.1 ⊆ insert (F.newVertex i hi) (F.incoming i hi).1 := by
    rw [← (F.newVertex_spec i hi).2]
    exact hes
  have hnew := fresh_mem_selected hec (F.incoming_card i hi) hes' hediff
  obtain ⟨z,hze,hzn⟩ := pair_has_other hec (F.newVertex i hi)
  have hza : z ∈ (F.incoming i hi).1 := (Finset.mem_insert.mp (hes' hze)).resolve_left hzn
  have hv := F.birthIndex_nonroot i hi
  have him : (A.older (F.birthIndex i hi)).image F.vertexLabel = (F.incoming i hi).1 := by
    have hh := ((A.older_invariants (F.birthIndex i hi)).2 hv).2.1
    change (A.older (F.birthIndex i hi)).image F.vertexLabel = F.attachment (F.birthIndex i hi) at hh
    exact hh.trans (F.attachment_birth i hi)
  have hfT := (Finset.mem_powersetCard.mp hc.2.2.1).1
  obtain ⟨u,hum,huz⟩ := Finset.mem_image.mp (him.symm ▸ hza)
  refine ⟨lookupGraph_triangle hc.2.1,⟨u,hum,?_,?_⟩,?_⟩
  · exact huz.symm ▸ hfT hze
  · rw [F.vertexLabel_birth]
    exact hfT hnew
  · intro _ heq
    have hpar := hc.2.2.2
    rw [F.incoming_parent i hi] at hpar
    apply hpar
    apply congrArg some
    have hh := A.parentType_eq (F.birthIndex i hi) hv
    change A.birthGraph.parentType F.vertexLabel (F.birthIndex i hi) =
      insert (F.vertexLabel (F.birthIndex i hi)) (F.attachment (F.birthIndex i hi)) at hh
    rw [F.vertexLabel_birth,F.attachment_birth,← (F.newVertex_spec i hi).2] at hh
    exact heq.trans hh

lemma candidate_root_exposed (p : Finset (Fin n) × Finset (Fin n))
    (hp : p ∈ gridCandidates (triangleHypergraph G) c.focus c.parent) :
    ∃ v : Fin F.vertexCount, v.val < F.rootCount ∧
      (F.toTriangleGrowth hM hG).birthGraph.ExposedAt (lookupGraph G) F.vertexLabel v p.2 := by
  let A := F.toTriangleGrowth hM hG
  have hc := (graphCandidate_iff G _ _ _).mp hp
  obtain ⟨x,y,hx,hy,hxy,he⟩ := matchingSeed_covers F.vertexLabel c.focus hM
    F.vertexLabel_injective_roots (F.vertexLabel_covers) p.1 hc.1
  have hB : A.birthGraph.graph.Adj x y := (A.root_graph hx hy).mpr hxy
  have hfT := (Finset.mem_powersetCard.mp hc.2.2.1).1
  have hxT : F.vertexLabel x ∈ p.2 := hfT (he ▸ by simp)
  have hyT : F.vertexLabel y ∈ p.2 := hfT (he ▸ by simp)
  have hsmall (v : Fin F.vertexCount) (hv : v.val < F.rootCount) : (A.older v).card ≤ 1 := by
    rw [A.older_eq_seed hv]
    exact A.seed_small v hv
  rcases lt_or_gt_of_ne hB.ne with hlt | hgt
  · refine ⟨y,hy,lookupGraph_triangle hc.2.1,⟨x,(A.birthGraph.graph_adj_of_lt hlt).mp hB,hxT,hyT⟩,?_⟩
    intro hc2 _
    have hh := hsmall y hy
    change (A.older y).card = 2 at hc2
    omega
  · refine ⟨x,hx,lookupGraph_triangle hc.2.1,⟨y,(A.birthGraph.graph_adj_of_lt hgt).mp hB.symm,hyT,hxT⟩,?_⟩
    intro hc2 _
    have hh := hsmall x hx
    change (A.older x).card = 2 at hc2
    omega

end SharpTerminalLeave.RecordedCallForest

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_KeyCandidate
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

lemma QueryCall.key_has_candidate {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]
    (H : τ → Finset ι) (c : QueryCall ι τ) (T : τ) (h : T ∈ c.keys H) :
    ∃ e, (e,T) ∈ gridCandidates H c.focus c.parent := by
  obtain ⟨p,hp,he⟩ := List.mem_map.mp h
  exact ⟨p.1,he ▸ Finset.mem_toList.mp hp⟩

namespace RecordedCallForest
variable {n : ℕ} {G : Graph n} {c : QueryCall (Finset (Fin n)) (Finset (Fin n))}
variable (F : RecordedCallForest (triangleHypergraph G) c)
variable (hM : EdgeMatching c.focus) (hG : c.focus ⊆ G)

lemma key_exposed (i : Fin F.size) (T : Finset (Fin n))
    (hT : T ∈ (F.call i).keys (triangleHypergraph G)) :
    ∃ v : Fin F.vertexCount,
      ((i = F.root ∧ v.val < F.rootCount) ∨ (∃ hi : i ≠ F.root, v = F.birthIndex i hi)) ∧
      (F.toTriangleGrowth hM hG).birthGraph.ExposedAt (lookupGraph G) F.vertexLabel v T := by
  obtain ⟨e,he⟩ := (F.call i).key_has_candidate (triangleHypergraph G) T hT
  by_cases hi : i = F.root
  · subst i
    rw [F.root_eq] at he
    obtain ⟨v,hv,hve⟩ := F.candidate_root_exposed hM hG (e,T) he
    exact ⟨v,Or.inl ⟨rfl,hv⟩,hve⟩
  · exact ⟨F.birthIndex i hi,Or.inr ⟨hi,rfl⟩,F.candidate_nonroot_exposed hM hG i hi (e,T) he⟩

end RecordedCallForest

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_CallPathCollisionWitness
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

namespace RecordedCallForest
variable {n : ℕ} {G : Graph n} {c : QueryCall (Finset (Fin n)) (Finset (Fin n))}
variable (F : RecordedCallForest (triangleHypergraph G) c)
variable (hM : EdgeMatching c.focus) (hG : c.focus ⊆ G)

theorem call_path_collision_witness (i j : Fin F.size) (hne : i ≠ j) (T : Finset (Fin n))
    (hi : T ∈ (F.call i).keys (triangleHypergraph G))
    (hj : T ∈ (F.call j).keys (triangleHypergraph G)) :
    ∃ a b : Fin F.vertexCount,
      (F.toTriangleGrowth hM hG).birthGraph.ExtraEdge (lookupGraph G) F.vertexLabel a b ∧
      Set.InjOn F.vertexLabel ((F.toTriangleGrowth hM hG).pathUnion a b) := by
  let A := F.toTriangleGrowth hM hG
  obtain ⟨v,hv,hve⟩ := F.key_exposed hM hG i T hi
  obtain ⟨w,hw,hwe⟩ := F.key_exposed hM hG j T hj
  have hvw : v ≠ w := by
    rcases hv with ⟨hiv,hvr⟩ | ⟨hiv,rfl⟩ <;> rcases hw with ⟨hjw,hwr⟩ | ⟨hjw,rfl⟩
    · exact False.elim (hne (hiv.trans hjw.symm))
    · intro he
      have hh := F.birthIndex_nonroot j hjw
      rw [← he] at hh
      omega
    · intro he
      have hh := F.birthIndex_nonroot i hiv
      rw [he] at hh
      omega
    · exact fun he => hne (F.birthIndex_injective i j hiv hjw he)
  exact A.injective_path_collision hvw hve hwe

end RecordedCallForest

theorem traced_graph_path_collision_witness {n : ℕ} (G : Graph n) (N d k : ℕ)
    (c : QueryCall (Finset (Fin n)) (Finset (Fin n)))
    (hM : EdgeMatching c.focus) (hG : c.focus ⊆ G)
    (hc : c.Separated (triangleHypergraph G))
    (ν : Finset (Fin n) → PMF (Fin N))
    (z : (Bool × List (QueryCall (Finset (Fin n)) (Finset (Fin n)))) × List (Finset (Fin n)))
    (hz : z ∈ (ExposureTree.freshLog ν
      (tracedGridQuery (triangleHypergraph G) N d k c)).support)
    (hr : ExposureTree.repeats ∅ z.2 = true) :
    let F := extractCallForest (triangleHypergraph G) N d k c ν z hz
    ∃ a b : Fin F.vertexCount,
      (F.toTriangleGrowth hM hG).birthGraph.ExtraEdge (lookupGraph G) F.vertexLabel a b ∧
      Set.InjOn F.vertexLabel ((F.toTriangleGrowth hM hG).pathUnion a b) := by
  let F := extractCallForest (triangleHypergraph G) N d k c ν z hz
  obtain ⟨a,ha,b,hb,hab,T,haT,hbT⟩ := graph_query_repeat_addresses G N d k c hc ν hz hr
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp ha
  obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hb
  have hij : i ≠ j := fun he => hab (he ▸ rfl)
  exact F.call_path_collision_witness hM hG i j hij T haT hbT

end SharpTerminalLeave

open Filter
open scoped BigOperators Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_MemAddressId
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.PathForest
variable {s : ℕ} {α : Type*}

lemma mem_address_id (F : PathForest s) (i j : Fin s) :
    i ∈ F.address id j ↔ F.Ancestor i j := by
  induction j using (measure (fun j : Fin s => j.val)).wf.induction with
  | h j ih =>
    cases hp : F.parent j with
    | none =>
      rw [F.address_none id j hp,List.mem_singleton]
      constructor
      · rintro rfl
        exact Relation.ReflTransGen.refl
      · intro h
        rcases F.ancestor_eq_or_predecessor h with he | ⟨k,hk,_⟩
        · exact he
        · exact False.elim (by change F.parent j = some k at hk; rw [hp] at hk; cases hk)
    | some k =>
      rw [F.address_some id j k hp,List.mem_cons,ih k (F.property j k hp)]
      constructor
      · rintro (rfl | hik)
        · exact Relation.ReflTransGen.refl
        · exact hik.tail hp
      · intro h
        rcases F.ancestor_eq_or_predecessor h with he | ⟨l,hl,hil⟩
        · exact Or.inl he
        · have he := F.predecessor_unique hl hp
          subst l
          exact Or.inr hil

lemma address_map (F : PathForest s) (key : Fin s → α) (i : Fin s) :
    F.address key i = (F.address id i).map key := by
  induction i using (measure (fun i : Fin s => i.val)).wf.induction with
  | h i ih =>
    cases hp : F.parent i with
    | none => rw [F.address_none key i hp,F.address_none id i hp]; rfl
    | some j =>
      rw [F.address_some key i j hp,F.address_some id i j hp,
        ih j (F.property i j hp)]
      rfl

lemma option_address_length (F : PathForest s) (key : Fin s → α) (a : Option (Fin s)) :
    (a.elim [] (F.address key)).length = (a.elim [] (F.address id)).length := by
  cases a with
  | none => rfl
  | some i => simp only [Option.elim_some,F.address_map key,List.length_map]

lemma mem_option_address (F : PathForest s) (a : Option (Fin s)) (i : Fin s) :
    i ∈ a.elim [] (F.address id) ↔ F.OnPath a i := by
  cases a with
  | none => simp [OnPath]
  | some j =>
    simp only [Option.elim_some,F.mem_address_id,OnPath,Option.some.injEq]
    exact ⟨fun h => ⟨j,rfl,h⟩,fun ⟨w,hw,h⟩ => hw ▸ h⟩

lemma two_mark_size (F : PathForest s) (key : Fin s → α) (a b : Option (Fin s))
    (hcover : ∀ i, F.OnPath a i ∨ F.OnPath b i) :
    s ≤ (a.elim [] (F.address key)).length + (b.elim [] (F.address key)).length := by
  classical
  rw [F.option_address_length key a,F.option_address_length key b]
  have hsub : (Finset.univ : Finset (Fin s)) ⊆
      (a.elim [] (F.address id)).toFinset ∪ (b.elim [] (F.address id)).toFinset := by
    intro i _
    rcases hcover i with h | h
    · exact Finset.mem_union_left _ (List.mem_toFinset.mpr ((F.mem_option_address a i).mpr h))
    · exact Finset.mem_union_right _ (List.mem_toFinset.mpr ((F.mem_option_address b i).mpr h))
  calc
    s = (Finset.univ : Finset (Fin s)).card := (Finset.card_fin s).symm
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add (List.toFinset_card_le _) (List.toFinset_card_le _)

end SharpTerminalLeave.PathForest

open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_VertexCall
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.RecordedCallForest
variable {n : ℕ} {G : Graph n} {c : QueryCall (Finset (Fin n)) (Finset (Fin n))}
variable (F : RecordedCallForest (triangleHypergraph G) c)

lemma vertexCall_nonroot (v : Fin F.vertexCount) (hv : F.rootCount ≤ v.val) :
    F.vertexCall v = F.callIndex v hv := dite_eq_left hv

lemma vertexCall_root (v : Fin F.vertexCount) (hv : v.val < F.rootCount) :
    F.vertexCall v = F.root := dite_eq_right (Nat.not_le.mpr hv)

lemma birthParent_vertexCall (v : Fin F.vertexCount) (hv : F.rootCount ≤ v.val) :
    (F.birthParent v).elim F.root F.vertexCall =
      F.parent (F.callIndex v hv) (F.callIndex_nonroot v hv) := by
  rw [F.birthParent_nonroot v hv]
  split_ifs with hp
  · simp only [Option.elim_some,vertexCall,dite_eq_left (F.birthIndex_nonroot _ hp),F.callIndex_birthIndex]
  · simpa only [Option.elim_none] using (not_ne_iff.mp hp).symm

lemma vertexCall_address (v : Fin F.vertexCount) (hv : F.rootCount ≤ v.val) :
    (F.call (F.vertexCall v)).address =
      (F.attachment v,insert (F.vertexLabel v) (F.attachment v)) ::
        (F.call ((F.birthParent v).elim F.root F.vertexCall)).address := by
  rw [F.vertexCall_nonroot v hv,F.birthParent_vertexCall v hv,
    F.newTriangle v hv,F.attachment_nonroot v hv]
  exact congrArg QueryCall.address (F.incoming_spec _ _).2

lemma vertexCall_address_empty_root (hc : c.address = [])
    (v : Fin F.vertexCount) (hv : F.rootCount ≤ v.val) :
    (F.call (F.vertexCall v)).address =
      (F.attachment v,insert (F.vertexLabel v) (F.attachment v)) ::
        (F.birthParent v).elim [] (fun p => (F.call (F.vertexCall p)).address) := by
  rw [F.vertexCall_address v hv]
  cases F.birthParent v <;> simp only [Option.elim_none,Option.elim_some,F.root_eq,hc]

lemma decoded_path_address (hM : EdgeMatching c.focus) (hG : c.focus ⊆ G)
    (hc : c.address = []) (a b : Fin F.vertexCount)
    (hR : F.rootCount ≤ F.vertexCount)
    (hi : Set.InjOn F.vertexLabel ((F.toTriangleGrowth hM hG).pathUnion a b))
    (i : Fin ((F.toTriangleGrowth hM hG).pathSuffix a b F.rootCount).card) :
    let A := F.toTriangleGrowth hM hG
    (A.pathForest a b).address
      (indexedTriangleKey (A.pathBirthIndex a b hR) (A.pathAttachments a b hR)
        (A.pathAssignment a b hi)) i =
      (F.call (F.vertexCall ((A.pathSuffix a b F.rootCount).orderEmbOfFin rfl i))).address := by
  dsimp only
  let A := F.toTriangleGrowth hM hG
  apply PathForest.address_unique
  intro j
  rw [A.indexedTriangleKey_actual a b hR hi j]
  have hv : F.rootCount ≤ ((A.pathSuffix a b F.rootCount).orderEmbOfFin rfl j).val :=
    ((A.mem_pathSuffix a b _ F.rootCount).mp
      ((A.pathSuffix a b F.rootCount).orderEmbOfFin_mem rfl j)).2
  rw [F.vertexCall_address_empty_root hc _ hv]
  congr 1
  cases hp : (A.pathForest a b).parent j with
  | none =>
    have he := (A.pathForest_parent_none a b j).mp hp
    change F.birthParent _ = none at he
    rw [he]
    rfl
  | some k =>
    have he := (A.pathForest_parent_some a b j k).mp hp
    change F.birthParent _ = some _ at he
    rw [he]
    rfl

lemma decoded_mark_address (hM : EdgeMatching c.focus) (hG : c.focus ⊆ G)
    (hc : c.address = []) (a b : Fin F.vertexCount)
    (hR : F.rootCount ≤ F.vertexCount)
    (hi : Set.InjOn F.vertexLabel ((F.toTriangleGrowth hM hG).pathUnion a b))
    (x : Fin F.vertexCount) (hx : x ∈ (F.toTriangleGrowth hM hG).pathUnion a b) :
    let A := F.toTriangleGrowth hM hG
    (suffixProjection (A.path_card_split a b hR) (A.pathIndex a b x hx)).elim []
      ((A.pathForest a b).address
        (indexedTriangleKey (A.pathBirthIndex a b hR) (A.pathAttachments a b hR)
          (A.pathAssignment a b hi))) = (F.call (F.vertexCall x)).address := by
  dsimp only
  let A := F.toTriangleGrowth hM hG
  rw [A.path_mark_projection a b hR x hx,PathForest.restrictMark]
  split_ifs with hn
  · simp only [Option.elim_some]
    rw [F.decoded_path_address hM hG hc a b hR hi]
    rw [PathForest.embed_index]
  · have hv : x.val < F.rootCount := by
      by_contra h
      exact hn ((A.mem_pathSuffix a b x F.rootCount).mpr ⟨hx,by omega⟩)
    rw [F.vertexCall_root x hv,F.root_eq,hc]
    rfl

end SharpTerminalLeave.RecordedCallForest

open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_CheckMarkedTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave.ExposureTree
variable {K V R : Type*}

lemma programDemand_marked_trace (as : List (Bool × ExposureTree K V (Bool × Bool × List R))) :
    programDemand (as.map (fun a => (a.1,mapOutput (fun z => (z.1,z.2.1)) a.2))) =
      as.any Prod.fst := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons,programDemand,List.any_cons,ih]

lemma checkMarkedTrace_marked (as : List (Bool × ExposureTree K V (Bool × Bool × List R))) :
    mapOutput (fun z => (z.1,z.2.1)) (checkMarkedTrace as) =
      checkMarked (as.map (fun a => (a.1,mapOutput (fun z => (z.1,z.2.1)) a.2))) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [checkMarkedTrace,mapOutput_bind,List.map_cons,checkMarked,bind_mapOutput]
    congr 1
    funext z
    cases z.1 <;> simp only [Bool.false_eq_true,↓reduceIte,mapOutput_done,
      mapOutput_comp,programDemand_marked_trace]
    rw [← ih]
    rw [mapOutput_comp]
    rfl

lemma checkMarkedTrace_trace (as : List (Bool × ExposureTree K V (Bool × Bool × List R))) :
    mapOutput (fun z => (z.1,z.2.2)) (checkMarkedTrace as) =
      checkNoneTrace (as.map (fun a => mapOutput (fun z => (z.1,z.2.2)) a.2)) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [checkMarkedTrace,mapOutput_bind,List.map_cons,checkNoneTrace,bind_mapOutput]
    congr 1
    funext z
    cases z.1 <;> simp only [Bool.false_eq_true,↓reduceIte,mapOutput_done,mapOutput_comp]
    rw [← ih]
    rw [mapOutput_comp]
    rfl

lemma any_fst_false (as : List (Bool × ExposureTree K V (Bool × Bool × List R))) :
    as.any Prod.fst = false ↔ ∀ a ∈ as, a.1 = false := by
  induction as with
  | nil => simp
  | cons a as ih => simp only [List.any_cons,Bool.or_eq_false_iff,ih,List.forall_mem_cons]

theorem checkMarkedTrace_no_demands (ν : K → PMF V)
    (as : List (Bool × ExposureTree K V (Bool × Bool × List R)))
    (ha : as.any Prod.fst = false)
    {z : Bool × Bool × List R} (hz : z ∈ (fresh ν (checkMarkedTrace as)).support) :
    z.2.1 = true := by
  induction as generalizing z with
  | nil =>
    have he : z = (true,true,[]) := by
      simpa only [checkMarkedTrace,fresh,PMF.mem_support_pure_iff] using hz
    subst z
    rfl
  | cons a as ih =>
    have haa := Bool.or_eq_false_iff.mp ha
    rw [checkMarkedTrace,fresh_bind] at hz
    obtain ⟨x,_,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    by_cases hx : x.1 = true
    · simp only [hx,↓reduceIte,fresh,PMF.mem_support_pure_iff] at hz
      subst z
      simp only [haa.1,haa.2,Bool.not_false,Bool.true_or,Bool.and_self]
    · simp only [hx,Bool.false_eq_true,↓reduceIte,fresh_mapOutput] at hz
      obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
      simp only [haa.1,Bool.not_false,Bool.true_or,Bool.true_and]
      exact ih haa.2 hy

theorem checkMarkedTrace_one_hit (ν : K → PMF V) (P : R → Prop)
    (as : List (Bool × ExposureTree K V (Bool × Bool × List R)))
    (hunique : as.Pairwise (fun a b => a.1 = true → b.1 = false))
    (hchild : ∀ a ∈ as, ∀ z ∈ (fresh ν a.2).support,
      (∃ r ∈ z.2.2, P r) → a.1 = true ∧ z.2.1 = true)
    {z : Bool × Bool × List R} (hz : z ∈ (fresh ν (checkMarkedTrace as)).support)
    (hhit : ∃ r ∈ z.2.2, P r) : as.any Prod.fst = true ∧ z.2.1 = true := by
  induction as generalizing z with
  | nil =>
    have he : z = (true,true,[]) := by simpa only [checkMarkedTrace,fresh,
      PMF.mem_support_pure_iff] using hz
    subst z
    simp only [List.not_mem_nil,false_and,exists_false] at hhit
  | cons a as ih =>
    obtain ⟨hun,hup⟩ := List.pairwise_cons.mp hunique
    rw [checkMarkedTrace,fresh_bind] at hz
    obtain ⟨x,hx,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    have haresult := hchild a (List.mem_cons_self) x hx
    have htail := fun a ha => hchild a (List.mem_cons_of_mem _ ha)
    have hnodemand (ha : a.1 = true) : as.any Prod.fst = false :=
      (any_fst_false as).mpr (fun b hb => hun b hb ha)
    by_cases hxv : x.1 = true
    · simp only [hxv,↓reduceIte,fresh,PMF.mem_support_pure_iff] at hz
      subst z
      obtain ⟨ha,hgood⟩ := haresult hhit
      simp only [List.any_cons,ha,hgood,hnodemand ha,Bool.true_or,Bool.not_false,
        Bool.or_true,Bool.and_self,and_self]
    · simp only [hxv,Bool.false_eq_true,↓reduceIte,fresh_mapOutput] at hz
      obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
      obtain ⟨r,hr,hPr⟩ := hhit
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨ha,hgood⟩ := haresult ⟨r,hr,hPr⟩
        have hygood := checkMarkedTrace_no_demands ν as (hnodemand ha) hy
        simp only [List.any_cons,ha,hgood,hygood,Bool.true_or,Bool.or_true,
          Bool.and_self,and_self]
      · obtain ⟨hd,hgood⟩ := ih hup htail hy ⟨r,hr,hPr⟩
        have ha : a.1 = false := by
          cases hh : a.1
          · rfl
          · have hh' := hnodemand hh
            rw [hh'] at hd
            contradiction
        simp only [List.any_cons,ha,hgood,hd,Bool.false_or,Bool.not_false,
          Bool.true_or,Bool.and_self,and_self]

end SharpTerminalLeave.ExposureTree

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_JointMarkedQuery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave
section MarkedTrace
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem jointMarkedQuery_marked (H : τ → Finset ι) (N : ℕ)
    (required : List (ι × τ) → Bool) (d k : ℕ) (c : QueryCall ι τ) :
    ExposureTree.mapOutput (fun z => (z.1,z.2.1)) (jointMarkedQuery H N required d k c) =
      markedGridQueryDepth H N required d k c.address c.focus c.parent := by
  induction d generalizing k c with
  | zero => simp only [jointMarkedQuery,markedGridQueryDepth,
      ExposureTree.mapOutput_bind,ExposureTree.mapOutput_done]
  | succ d ih =>
    simp only [jointMarkedQuery,markedGridQueryDepth,ExposureTree.mapOutput_bind,
      ExposureTree.mapOutput_comp]
    congr 1
    funext values
    rw [show (fun x : Bool × Bool × List (QueryCall ι τ) => (x.1,x.2.1)) ∘
        (fun z : Bool × Bool × List (QueryCall ι τ) => (z.1,z.2.1,c :: z.2.2)) =
        (fun z : Bool × Bool × List (QueryCall ι τ) => (z.1,z.2.1)) from rfl,
      ExposureTree.checkMarkedTrace_marked,List.map_map]
    congr 1
    apply List.map_congr_left
    intro p _
    dsimp only [Function.comp_def]
    congr 1
    split
    · exact ih _ _
    · rfl

theorem jointMarkedQuery_trace (H : τ → Finset ι) (N : ℕ)
    (required : List (ι × τ) → Bool) (d k : ℕ) (c : QueryCall ι τ) :
    ExposureTree.mapOutput (fun z => (z.1,z.2.2)) (jointMarkedQuery H N required d k c) =
      tracedGridQuery H N d k c := by
  induction d generalizing k c with
  | zero => simp only [jointMarkedQuery,tracedGridQuery,
      ExposureTree.mapOutput_bind,ExposureTree.mapOutput_done]
  | succ d ih =>
    simp only [jointMarkedQuery,tracedGridQuery,ExposureTree.mapOutput_bind,
      ExposureTree.mapOutput_comp]
    congr 1
    funext values
    rw [show (fun x : Bool × Bool × List (QueryCall ι τ) => (x.1,x.2.2)) ∘
        (fun z : Bool × Bool × List (QueryCall ι τ) => (z.1,z.2.1,c :: z.2.2)) =
        (fun z : Bool × List (QueryCall ι τ) => (z.1,c :: z.2)) ∘
          (fun z : Bool × Bool × List (QueryCall ι τ) => (z.1,z.2.2)) from rfl,
      ← ExposureTree.mapOutput_comp,ExposureTree.checkMarkedTrace_trace,List.map_map]
    congr 2
    apply List.map_congr_left
    intro p _
    dsimp only [Function.comp_def]
    split
    · exact ih _ _
    · rfl

theorem jointMarkedQuery_address (H : τ → Finset ι) (N : ℕ)
    (required : List (ι × τ) → Bool) (d k : ℕ) (c : QueryCall ι τ)
    (ν : τ → PMF (Fin N)) {z : Bool × Bool × List (QueryCall ι τ)}
    (hz : z ∈ (ExposureTree.fresh ν (jointMarkedQuery H N required d k c)).support) :
    ∀ a ∈ z.2.2, c.address <:+ a.address := by
  have ht : (z.1,z.2.2) ∈ (ExposureTree.fresh ν (tracedGridQuery H N d k c)).support := by
    rw [← jointMarkedQuery_trace H N required d k c,ExposureTree.fresh_mapOutput]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨z,hz,rfl⟩
  rw [← ExposureTree.freshLog_outcome] at ht
  obtain ⟨x,hx,hxe⟩ := (PMF.mem_support_map_iff _ _ _).mp ht
  have hh := tracedGridQuery_address H N d k c ν hx
  rw [hxe] at hh
  exact hh

end MarkedTrace
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_PathRequiredBaseChild
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave

lemma pathRequired_base_child {A : Type*} [DecidableEq A]
    (base : List A) (a p : A) (as : List A) :
    pathRequired (base.reverse ++ a :: as) (p :: base) = decide (p = a) := by
  simp [pathRequired,List.reverse_cons,List.prefix_append_right_inj]

lemma pathRequired_base_nil {A : Type*} [DecidableEq A]
    (base : List A) (p : A) : pathRequired base.reverse (p :: base) = false := by
  simp only [pathRequired,decide_eq_false_iff_not]
  intro h
  have hl := h.length_le
  simp only [List.length_reverse,List.length_cons] at hl
  omega

section MarkedTraceHit
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem jointMarkedQuery_hit (H : τ → Finset ι) (N d k : ℕ)
    (c : QueryCall ι τ) (path : List (ι × τ)) (ν : τ → PMF (Fin N))
    {z : Bool × Bool × List (QueryCall ι τ)}
    (hz : z ∈ (ExposureTree.fresh ν
      (jointMarkedQuery H N (pathRequired (c.address.reverse ++ path)) d k c)).support)
    (hhit : ∃ a ∈ z.2.2, a.address = path.reverse ++ c.address) : z.2.1 = true := by
  induction d generalizing k c path z with
  | zero =>
    rw [jointMarkedQuery,ExposureTree.fresh_bind] at hz
    obtain ⟨_,_,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    have he : z = (true,true,[c]) := by
      simpa only [ExposureTree.fresh,PMF.mem_support_pure_iff] using hz
    rw [he]
  | succ d ih =>
    rw [jointMarkedQuery,ExposureTree.fresh_bind] at hz
    obtain ⟨values,hvalues,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    rw [ExposureTree.fresh_mapOutput] at hz
    obtain ⟨w,hw,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    cases path with
    | nil =>
      apply ExposureTree.checkMarkedTrace_no_demands ν _ _ hw
      apply List.any_eq_false.mpr
      intro x hx
      obtain ⟨p,_,rfl⟩ := List.mem_map.mp hx
      simp only [List.append_nil,pathRequired_base_nil,Bool.false_eq_true,not_false_eq_true]
    | cons a as =>
      have hhit' : ∃ q ∈ w.2.2, q.address = (a :: as).reverse ++ c.address := by
        obtain ⟨q,hq,he⟩ := hhit
        rcases List.mem_cons.mp hq with rfl | hq
        · have hl := congrArg List.length he
          simp only [List.length_append,List.length_reverse,List.length_cons] at hl
          omega
        · exact ⟨q,hq,he⟩
      have hvals : (values.map Prod.fst).Nodup := by
        rw [← ExposureTree.freshLog_outcome] at hvalues
        obtain ⟨x,hx,hxe⟩ := (PMF.mem_support_map_iff _ _ _).mp hvalues
        have he := (ExposureTree.freshLog_exposeLabeled_support ν Prod.snd _ hx).1
        rw [hxe] at he
        rw [he]
        exact Finset.nodup_toList _
      have hsorted := ((List.mergeSort_perm values
        (fun a b => a.2.val ≤ b.2.val)).map Prod.fst).nodup_iff.mpr hvals
      have hpair : (values.mergeSort (fun a b => a.2.val ≤ b.2.val)).Pairwise
          (fun p q => p.1 ≠ q.1) := by
        simpa only [List.Nodup,List.pairwise_map] using hsorted
      apply (ExposureTree.checkMarkedTrace_one_hit ν
        (fun q : QueryCall ι τ => q.address = (a :: as).reverse ++ c.address) _ _ _ hw hhit').2
      · apply List.pairwise_map.mpr
        apply hpair.imp
        intro p q hpq hp
        simp only [pathRequired_base_child,decide_eq_true_eq] at hp
        simp only [pathRequired_base_child,decide_eq_false_iff_not]
        exact fun hq => hpq (hp.trans hq.symm)
      · intro child hchild y hy hhit
        obtain ⟨p,_,rfl⟩ := List.mem_map.mp hchild
        split_ifs at hy with hp
        · obtain ⟨q,hq,he⟩ := hhit
          have had := jointMarkedQuery_address H N _ d p.2.val
            ⟨p.1 :: c.address,(H p.1.2).erase p.1.1,some p.1.2⟩ ν hy q hq
          rw [he] at had
          have haa : a :: c.address <:+ (a :: as).reverse ++ c.address := by
            simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
            exact List.suffix_append _ _
          have hpa : p.1 = a := List.cons.inj
            ((List.suffix_of_suffix_length_le had haa (by simp)).eq_of_length (by simp)) |>.1
          refine ⟨?_,?_⟩
          · simp only [pathRequired_base_child,hpa,decide_true]
          · have hi := ih p.2.val
              ⟨p.1 :: c.address,(H p.1.2).erase p.1.1,some p.1.2⟩ as
              (by simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,hpa] using hy)
              (by simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,hpa] using
                (show ∃ q ∈ y.2.2, q.address = (a :: as).reverse ++ c.address from ⟨q,hq,he⟩))
            exact hi
        · have he : y = (false,false,[]) := by
            simpa only [ExposureTree.fresh,PMF.mem_support_pure_iff] using hy
          simp only [he,List.not_mem_nil,false_and,exists_false] at hhit

end MarkedTraceHit
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Probability_PathVisitProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave

lemma pmf_boolean_map_le {A : Type*} (P : PMF A) (f g : A → Bool)
    (h : ∀ a ∈ P.support, f a = true → g a = true) :
    ((P.map f) true).toReal ≤ ((P.map g) true).toReal := by
  apply ENNReal.toReal_mono (PMF.apply_ne_top _ _)
  simp only [PMF.map_apply]
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases ha : P a = 0
  · simp only [ha,ite_self,le_refl]
  · by_cases hf : f a = true
    · have hg := h a ((PMF.mem_support_iff _ _).mpr ha) hf
      simp only [hf,hg,↓reduceIte,le_refl]
    · simp only [Ne.symm hf,↓reduceIte,zero_le]

lemma markedGood_map_true (p : PMF (Bool × Bool)) :
    markedGood p = ((p.map Prod.snd) true).toReal := by
  unfold markedGood
  rw [← pmfMean_map p Prod.snd (fun b => if b then 1 else 0)]
  simp [pmfMean]

section TracePathProbability
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem actualPathVisitProbability_le_marked (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (focus : Finset ι) (parent : Option τ) (path : List (ι × τ)) :
    actualPathVisitProbability H N d k focus parent path ≤
      pathVisitProbability H N d k focus parent path := by
  let c : QueryCall ι τ := ⟨[],focus,parent⟩
  let ν := fun _ : τ => PMF.uniformOfFintype (Fin N)
  let P := ExposureTree.fresh ν (jointMarkedQuery H N (pathRequired path) d k c)
  have ht : P.map (fun z => (z.1,z.2.2)) =
      ExposureTree.fresh ν (tracedGridQuery H N d k c) := by
    rw [← ExposureTree.fresh_mapOutput,jointMarkedQuery_trace]
  have hm : P.map (fun z => (z.1,z.2.1)) =
      ExposureTree.fresh ν (markedGridQueryDepth H N (pathRequired path) d k [] focus parent) := by
    rw [← ExposureTree.fresh_mapOutput,jointMarkedQuery_marked]
  unfold actualPathVisitProbability pathVisitProbability
  rw [markedGood_map_true]
  rw [← ht,← hm,PMF.map_comp,PMF.map_comp]
  apply pmf_boolean_map_le
  intro z hz hh
  obtain ⟨a,ha,hea⟩ := List.any_eq_true.mp hh
  have hit : ∃ a ∈ z.2.2, a.address = path.reverse ++ c.address := by
    exact ⟨a,ha,by simpa only [c,List.append_nil] using of_decide_eq_true hea⟩
  exact jointMarkedQuery_hit H N d k c path ν hz hit

end TracePathProbability
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_PathRequiredBaseAppend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave

lemma pathRequired_base_append {A : Type*} [DecidableEq A]
    (base path ex : List A) :
    pathRequired (base.reverse ++ path) (ex ++ base) = pathRequired path ex := by
  simp [pathRequired,List.reverse_append,List.prefix_append_right_inj]

lemma pairRequired_base_child {A : Type*} [DecidableEq A]
    (base : List A) (a b p : A) (as bs : List A) :
    pairRequired (base.reverse ++ a :: as) (base.reverse ++ b :: bs) (p :: base) =
      decide (p = a ∨ p = b) := by
  simp only [pairRequired,pathRequired_base_child]
  by_cases ha : p = a <;> by_cases hb : p = b <;> simp [ha,hb]

section JointPairHelpers
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem jointMarkedQuery_congr_required (H : τ → Finset ι) (N d k : ℕ)
    (c : QueryCall ι τ) (r s : List (ι × τ) → Bool)
    (hrs : ∀ ex : List (ι × τ), ex ≠ [] → r (ex ++ c.address) = s (ex ++ c.address)) :
    jointMarkedQuery H N r d k c = jointMarkedQuery H N s d k c := by
  induction d generalizing k c with
  | zero => rfl
  | succ d ih =>
    simp only [jointMarkedQuery]
    congr 1
    funext values
    congr 2
    apply List.map_congr_left
    intro p _
    have he := hrs [p.1] (by simp)
    simp only [List.singleton_append] at he
    rw [he]
    congr 1
    split
    · apply ih
      intro ex hex
      simpa only [List.append_assoc,List.singleton_append] using
        hrs (ex ++ [p.1]) (by simp)
    · rfl

theorem jointMarkedQuery_pair_nil (H : τ → Finset ι) (N d k : ℕ)
    (c : QueryCall ι τ) (path : List (ι × τ)) :
    jointMarkedQuery H N (pairRequired c.address.reverse (c.address.reverse ++ path)) d k c =
      jointMarkedQuery H N (pathRequired (c.address.reverse ++ path)) d k c := by
  apply jointMarkedQuery_congr_required
  intro ex hex
  have hh : pathRequired c.address.reverse (ex ++ c.address) = false := by
    have he := pathRequired_base_append c.address [] ex
    simp only [List.append_nil] at he
    rw [he]
    simp [pathRequired,hex]
  simp only [pairRequired,hh,Bool.false_or]

theorem jointMarkedQuery_pair_child (H : τ → Finset ι) (N d k : ℕ)
    (base : List (ι × τ)) (a b : ι × τ) (as bs : List (ι × τ)) (hab : a ≠ b)
    (focus : Finset ι) (parent : Option τ) :
    jointMarkedQuery H N
        (pairRequired (base.reverse ++ a :: as) (base.reverse ++ b :: bs))
        d k ⟨a :: base,focus,parent⟩ =
      jointMarkedQuery H N (pathRequired ((a :: base).reverse ++ as))
        d k ⟨a :: base,focus,parent⟩ := by
  apply jointMarkedQuery_congr_required
  intro ex _
  simp [pairRequired,pathRequired,List.reverse_append,List.reverse_cons,
    List.append_assoc,List.prefix_append_right_inj,List.cons_prefix_cons,hab]

theorem jointMarkedQuery_hit_head (H : τ → Finset ι) (N d k : ℕ)
    (r : List (ι × τ) → Bool) (ν : τ → PMF (Fin N))
    (base : List (ι × τ)) (p a : ι × τ) (as : List (ι × τ))
    (focus : Finset ι) (parent : Option τ)
    {z : Bool × Bool × List (QueryCall ι τ)}
    (hz : z ∈ (ExposureTree.fresh ν
      (jointMarkedQuery H N r d k ⟨p :: base,focus,parent⟩)).support)
    (hh : ∃ q ∈ z.2.2, q.address = (a :: as).reverse ++ base) : p = a := by
  obtain ⟨q,hq,he⟩ := hh
  have had := jointMarkedQuery_address H N r d k ⟨p :: base,focus,parent⟩ ν hz q hq
  rw [he] at had
  have haa : a :: base <:+ (a :: as).reverse ++ base := by
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
    exact List.suffix_append _ _
  exact (List.cons.inj
    ((List.suffix_of_suffix_length_le had haa (by simp)).eq_of_length (by simp))).1

omit [Fintype τ] in
lemma query_trace_cons_hit_tail (c : QueryCall ι τ) (l : List (QueryCall ι τ))
    (a : ι × τ) (as : List (ι × τ))
    (h : ∃ q ∈ c :: l, q.address = (a :: as).reverse ++ c.address) :
    ∃ q ∈ l, q.address = (a :: as).reverse ++ c.address := by
  obtain ⟨q,hq,he⟩ := h
  rcases List.mem_cons.mp hq with rfl | hq
  · have hl := congrArg List.length he
    simp only [List.length_append,List.length_reverse,List.length_cons] at hl
    omega
  · exact ⟨q,hq,he⟩

end JointPairHelpers
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_CheckMarkedTraceHit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave.ExposureTree
variable {K V R A C : Type*}

theorem checkMarkedTrace_hit_source (ν : K → PMF V) (P : R → Prop)
    (as : List (Bool × ExposureTree K V (Bool × Bool × List R)))
    {z : Bool × Bool × List R} (hz : z ∈ (fresh ν (checkMarkedTrace as)).support)
    (hh : ∃ r ∈ z.2.2, P r) :
    ∃ a ∈ as, ∃ x ∈ (fresh ν a.2).support, ∃ r ∈ x.2.2, P r := by
  induction as generalizing z with
  | nil =>
    have he : z = (true,true,[]) := by
      simpa only [checkMarkedTrace,fresh,PMF.mem_support_pure_iff] using hz
    simp only [he,List.not_mem_nil,false_and,exists_false] at hh
  | cons a as ih =>
    rw [checkMarkedTrace,fresh_bind] at hz
    obtain ⟨x,hx,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    by_cases hv : x.1 = true
    · simp only [hv,↓reduceIte,fresh,PMF.mem_support_pure_iff] at hz
      subst z
      exact ⟨a,List.mem_cons_self,x,hx,hh⟩
    · simp only [hv,Bool.false_eq_true,↓reduceIte,fresh_mapOutput] at hz
      obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
      obtain ⟨r,hr,hP⟩ := hh
      rcases List.mem_append.mp hr with hr | hr
      · exact ⟨a,List.mem_cons_self,x,hx,r,hr,hP⟩
      · obtain ⟨b,hb,w,hw,r,hr,hP⟩ := ih hy ⟨r,hr,hP⟩
        exact ⟨b,List.mem_cons_of_mem _ hb,w,hw,r,hr,hP⟩

theorem checkMarkedTrace_two_hit [DecidableEq A] (ν : K → PMF V)
    (P Q : R → Prop) (key : C → A) (program : C → ExposureTree K V (Bool × Bool × List R))
    (a b : A) (hab : a ≠ b) (cs : List C) (hnd : (cs.map key).Nodup)
    (hP : ∀ c ∈ cs, ∀ z ∈ (fresh ν (program c)).support,
      (∃ r ∈ z.2.2, P r) → key c = a ∧ z.2.1 = true)
    (hQ : ∀ c ∈ cs, ∀ z ∈ (fresh ν (program c)).support,
      (∃ r ∈ z.2.2, Q r) → key c = b ∧ z.2.1 = true)
    {z : Bool × Bool × List R}
    (hz : z ∈ (fresh ν (checkMarkedTrace
      (cs.map (fun c => (decide (key c = a ∨ key c = b),program c))))).support)
    (hp : ∃ r ∈ z.2.2, P r) (hq : ∃ r ∈ z.2.2, Q r) : z.2.1 = true := by
  induction cs generalizing z with
  | nil =>
    have he : z = (true,true,[]) := by
      simpa only [List.map_nil,checkMarkedTrace,fresh,PMF.mem_support_pure_iff] using hz
    rw [he]
  | cons c cs ih =>
    obtain ⟨hc,hnd⟩ := List.nodup_cons.mp hnd
    have hcne : ∀ c' ∈ cs, key c ≠ key c' := by
      intro c' hc' he
      exact hc (List.mem_map.mpr ⟨c',hc',he.symm⟩)
    have hPt := fun c' hc' => hP c' (List.mem_cons_of_mem _ hc')
    have hQt := fun c' hc' => hQ c' (List.mem_cons_of_mem _ hc')
    have hsrc (U : R → Prop) (v : A)
        (hu : ∀ c' ∈ cs, ∀ x ∈ (fresh ν (program c')).support,
          (∃ r ∈ x.2.2, U r) → key c' = v ∧ x.2.1 = true)
        {w : Bool × Bool × List R}
        (hw : w ∈ (fresh ν (checkMarkedTrace
          (cs.map (fun c => (decide (key c = a ∨ key c = b),program c))))).support)
        (hh : ∃ r ∈ w.2.2, U r) : key c ≠ v := by
      obtain ⟨d,hd,x,hx,hh⟩ := checkMarkedTrace_hit_source ν U _ hw hh
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hd
      have he := (hu c' hc' x hx hh).1
      intro hv
      exact hcne c' hc' (hv.trans he.symm)
    rw [List.map_cons,checkMarkedTrace,fresh_bind] at hz
    obtain ⟨x,hx,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    have hpx := hP c List.mem_cons_self x hx
    have hqx := hQ c List.mem_cons_self x hx
    by_cases hv : x.1 = true
    · simp only [hv,↓reduceIte,fresh,PMF.mem_support_pure_iff] at hz
      subst z
      exact (hab ((hpx hp).1.symm.trans (hqx hq).1)).elim
    · simp only [hv,Bool.false_eq_true,↓reduceIte,fresh_mapOutput] at hz
      obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
      have hp' : (∃ r ∈ x.2.2, P r) ∨ (∃ r ∈ y.2.2, P r) := by
        simpa only [List.mem_append,or_and_right,exists_or] using hp
      have hq' : (∃ r ∈ x.2.2, Q r) ∨ (∃ r ∈ y.2.2, Q r) := by
        simpa only [List.mem_append,or_and_right,exists_or] using hq
      have hone (v other : A) (hvother : v ≠ other) (hcv : key c = other)
          (heq : ∀ c' ∈ cs, (key c' = a ∨ key c' = b) ↔ key c' = v)
          (U : R → Prop)
          (hu : ∀ c' ∈ cs, ∀ x ∈ (fresh ν (program c')).support,
            (∃ r ∈ x.2.2, U r) → key c' = v ∧ x.2.1 = true)
          (hh : ∃ r ∈ y.2.2, U r) : y.2.1 = true := by
        apply (checkMarkedTrace_one_hit ν U _ _ _ hy hh).2
        · apply List.pairwise_map.mpr
          have hpw : cs.Pairwise (fun x y => key x ≠ key y) := by
            simpa only [List.Nodup,List.pairwise_map] using hnd
          apply List.pairwise_iff_get.mpr
          intro i j hij
          have hi := (List.pairwise_iff_get.mp hpw) i j hij
          intro hd
          simp only [decide_eq_true_eq] at hd
          simp only [decide_eq_false_iff_not]
          intro he
          exact hi (((heq _ (List.get_mem ..)).mp hd).trans
            ((heq _ (List.get_mem ..)).mp he).symm)
        · intro d hd w hw hh'
          obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hd
          obtain ⟨he,hg⟩ := hu c' hc' w hw hh'
          exact ⟨decide_eq_true ((heq c' hc').mpr he),hg⟩
      rcases hp' with hp' | hp' <;> rcases hq' with hq' | hq'
      · exact (hab ((hpx hp').1.symm.trans (hqx hq').1)).elim
      · obtain ⟨hca,hgood⟩ := hpx hp'
        have heq : ∀ c' ∈ cs, (key c' = a ∨ key c' = b) ↔ key c' = b := by
          intro c' hc'
          have hh : key c' ≠ a := fun he => hcne c' hc' (hca.trans he.symm)
          simp only [hh,false_or]
        have hygood := hone b a (Ne.symm hab) hca heq Q hQt hq'
        simp only [hgood,hygood,Bool.or_true,Bool.and_self]
      · obtain ⟨hcb,hgood⟩ := hqx hq'
        have heq : ∀ c' ∈ cs, (key c' = a ∨ key c' = b) ↔ key c' = a := by
          intro c' hc'
          have hh : key c' ≠ b := fun he => hcne c' hc' (hcb.trans he.symm)
          simp only [hh,or_false]
        have hygood := hone a b hab hcb heq P hPt hp'
        simp only [hgood,hygood,Bool.or_true,Bool.and_self]
      · have hca := hsrc P a hPt hy hp'
        have hcb := hsrc Q b hQt hy hq'
        have hgood := ih hnd hPt hQt hy hp' hq'
        simp only [hca,hcb,false_or,decide_false,Bool.not_false,
          Bool.true_or,Bool.true_and,hgood]

end SharpTerminalLeave.ExposureTree

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Spectral_CheckMarkedTraceCommon
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave.ExposureTree
variable {K V R A C : Type*}

theorem checkMarkedTrace_common_hit [DecidableEq A] (ν : K → PMF V)
    (P Q : R → Prop) (key : C → A) (program : C → ExposureTree K V (Bool × Bool × List R))
    (a : A) (cs : List C) (hnd : (cs.map key).Nodup)
    (hP : ∀ c ∈ cs, ∀ z ∈ (fresh ν (program c)).support,
      (∃ r ∈ z.2.2, P r) → key c = a)
    (hQ : ∀ c ∈ cs, ∀ z ∈ (fresh ν (program c)).support,
      (∃ r ∈ z.2.2, Q r) → key c = a)
    (hG : ∀ c ∈ cs, ∀ z ∈ (fresh ν (program c)).support,
      (∃ r ∈ z.2.2, P r) → (∃ r ∈ z.2.2, Q r) → z.2.1 = true)
    {z : Bool × Bool × List R}
    (hz : z ∈ (fresh ν (checkMarkedTrace
      (cs.map (fun c => (decide (key c = a),program c))))).support)
    (hp : ∃ r ∈ z.2.2, P r) (hq : ∃ r ∈ z.2.2, Q r) : z.2.1 = true := by
  induction cs generalizing z with
  | nil =>
    have he : z = (true,true,[]) := by
      simpa only [List.map_nil,checkMarkedTrace,fresh,PMF.mem_support_pure_iff] using hz
    rw [he]
  | cons c cs ih =>
    obtain ⟨hc,hnd⟩ := List.nodup_cons.mp hnd
    have hcne : ∀ c' ∈ cs, key c ≠ key c' := by
      intro c' hc' he
      exact hc (List.mem_map.mpr ⟨c',hc',he.symm⟩)
    have hPt := fun c' hc' => hP c' (List.mem_cons_of_mem _ hc')
    have hQt := fun c' hc' => hQ c' (List.mem_cons_of_mem _ hc')
    have hGt := fun c' hc' => hG c' (List.mem_cons_of_mem _ hc')
    have hnone (he : key c = a) :
        (cs.map (fun c => (decide (key c = a),program c))).any Prod.fst = false := by
      apply List.any_eq_false.mpr
      intro d hd
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hd
      simp only [decide_eq_true_eq]
      exact fun h => hcne c' hc' (he.trans h.symm)
    have hsrc (U : R → Prop)
        (hu : ∀ c' ∈ cs, ∀ x ∈ (fresh ν (program c')).support,
          (∃ r ∈ x.2.2, U r) → key c' = a)
        {w : Bool × Bool × List R}
        (hw : w ∈ (fresh ν (checkMarkedTrace
          (cs.map (fun c => (decide (key c = a),program c))))).support)
        (hh : ∃ r ∈ w.2.2, U r) : key c ≠ a := by
      obtain ⟨d,hd,x,hx,hh⟩ := checkMarkedTrace_hit_source ν U _ hw hh
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hd
      have he := hu c' hc' x hx hh
      intro hv
      exact hcne c' hc' (hv.trans he.symm)
    rw [List.map_cons,checkMarkedTrace,fresh_bind] at hz
    obtain ⟨x,hx,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    by_cases hv : x.1 = true
    · simp only [hv,↓reduceIte,fresh,PMF.mem_support_pure_iff] at hz
      subst z
      have hgood := hG c List.mem_cons_self x hx hp hq
      have he := hP c List.mem_cons_self x hx hp
      simp only [hgood,hnone he,Bool.or_true,Bool.not_false,Bool.and_self]
    · simp only [hv,Bool.false_eq_true,↓reduceIte,fresh_mapOutput] at hz
      obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
      have hp' : (∃ r ∈ x.2.2, P r) ∨ (∃ r ∈ y.2.2, P r) := by
        simpa only [List.mem_append,or_and_right,exists_or] using hp
      have hq' : (∃ r ∈ x.2.2, Q r) ∨ (∃ r ∈ y.2.2, Q r) := by
        simpa only [List.mem_append,or_and_right,exists_or] using hq
      rcases hp' with hp' | hp' <;> rcases hq' with hq' | hq'
      · have hgood := hG c List.mem_cons_self x hx hp' hq'
        have he := hP c List.mem_cons_self x hx hp'
        have hygood := checkMarkedTrace_no_demands ν _ (hnone he) hy
        simp only [hgood,hygood,Bool.or_true,Bool.and_self]
      · exact ((hsrc Q hQt hy hq') (hP c List.mem_cons_self x hx hp')).elim
      · exact ((hsrc P hPt hy hp') (hQ c List.mem_cons_self x hx hq')).elim
      · have hca := hsrc P hPt hy hp'
        have hgood := ih hnd hPt hQt hGt hy hp' hq'
        simp only [hca,decide_false,Bool.not_false,Bool.true_or,Bool.true_and,hgood]

end SharpTerminalLeave.ExposureTree

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_JointMarkedQueryPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave
section JointPairHit
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem jointMarkedQuery_pair_hit (H : τ → Finset ι) (N d k : ℕ)
    (c : QueryCall ι τ) (path₁ path₂ : List (ι × τ)) (ν : τ → PMF (Fin N))
    {z : Bool × Bool × List (QueryCall ι τ)}
    (hz : z ∈ (ExposureTree.fresh ν
      (jointMarkedQuery H N
        (pairRequired (c.address.reverse ++ path₁) (c.address.reverse ++ path₂)) d k c)).support)
    (hp : ∃ a ∈ z.2.2, a.address = path₁.reverse ++ c.address)
    (hq : ∃ a ∈ z.2.2, a.address = path₂.reverse ++ c.address) : z.2.1 = true := by
  induction d generalizing k c path₁ path₂ z with
  | zero =>
    rw [jointMarkedQuery,ExposureTree.fresh_bind] at hz
    obtain ⟨_,_,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
    have he : z = (true,true,[c]) := by
      simpa only [ExposureTree.fresh,PMF.mem_support_pure_iff] using hz
    rw [he]
  | succ d ih =>
    cases path₁ with
    | nil =>
      simp only [List.append_nil] at hz
      rw [jointMarkedQuery_pair_nil] at hz
      exact jointMarkedQuery_hit H N (d+1) k c path₂ ν hz hq
    | cons a as =>
      cases path₂ with
      | nil =>
        simp only [List.append_nil] at hz
        have he : pairRequired (c.address.reverse ++ a :: as) c.address.reverse =
            pairRequired c.address.reverse (c.address.reverse ++ a :: as) := by
          funext l
          exact Bool.or_comm _ _
        rw [he,jointMarkedQuery_pair_nil] at hz
        exact jointMarkedQuery_hit H N (d+1) k c (a :: as) ν hz hp
      | cons b bs =>
        rw [jointMarkedQuery,ExposureTree.fresh_bind] at hz
        obtain ⟨values,hvalues,hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
        rw [ExposureTree.fresh_mapOutput] at hz
        obtain ⟨w,hw,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
        have hp' := query_trace_cons_hit_tail c w.2.2 a as hp
        have hq' := query_trace_cons_hit_tail c w.2.2 b bs hq
        let cs := values.mergeSort (fun a b => a.2.val ≤ b.2.val)
        let req := pairRequired (c.address.reverse ++ a :: as) (c.address.reverse ++ b :: bs)
        let program (p : (ι × τ) × Fin N) := if p.2.val < k then
          jointMarkedQuery H N req d p.2.val
            ⟨p.1 :: c.address,(H p.1.2).erase p.1.1,some p.1.2⟩
          else ExposureTree.done (false,false,[])
        have hnd : (cs.map Prod.fst).Nodup := by
          rw [← ExposureTree.freshLog_outcome] at hvalues
          obtain ⟨x,hx,hxe⟩ := (PMF.mem_support_map_iff _ _ _).mp hvalues
          have he := (ExposureTree.freshLog_exposeLabeled_support ν Prod.snd _ hx).1
          rw [hxe] at he
          apply ((List.mergeSort_perm values (fun a b => a.2.val ≤ b.2.val)).map Prod.fst).nodup_iff.mpr
          rw [he]
          exact Finset.nodup_toList _
        have hhead (v : ι × τ) (vs : List (ι × τ))
            (p : (ι × τ) × Fin N) (_ : p ∈ cs)
            (y : Bool × Bool × List (QueryCall ι τ))
            (hy : y ∈ (ExposureTree.fresh ν (program p)).support)
            (hh : ∃ q ∈ y.2.2, q.address = (v :: vs).reverse ++ c.address) : p.1 = v := by
          dsimp only [program] at hy
          split_ifs at hy with hk
          · exact jointMarkedQuery_hit_head H N d p.2.val req ν c.address p.1 v vs _ _ hy hh
          · have he : y = (false,false,[]) := by
              simpa only [ExposureTree.fresh,PMF.mem_support_pure_iff] using hy
            simp only [he,List.not_mem_nil,false_and,exists_false] at hh
        change w ∈ (ExposureTree.fresh ν (ExposureTree.checkMarkedTrace
          (cs.map (fun p => (req (p.1 :: c.address),program p))))).support at hw
        by_cases hab : a = b
        · subst b
          have hrow : cs.map (fun p => (req (p.1 :: c.address),program p)) =
              cs.map (fun p => (decide (p.1 = a),program p)) := by
            apply List.map_congr_left
            intro p _
            simp only [req,pairRequired_base_child,or_self]
          rw [hrow] at hw
          apply ExposureTree.checkMarkedTrace_common_hit ν
            (fun q : QueryCall ι τ => q.address = (a :: as).reverse ++ c.address)
            (fun q : QueryCall ι τ => q.address = (a :: bs).reverse ++ c.address)
            Prod.fst program a cs hnd (hhead a as) (hhead a bs) _ hw hp' hq'
          intro p hp y hy hpy hqy
          have hpa := hhead a as p hp y hy hpy
          dsimp only [program] at hy
          split_ifs at hy with hk
          · apply ih p.2.val
              ⟨p.1 :: c.address,(H p.1.2).erase p.1.1,some p.1.2⟩ as bs
            · simpa only [req,List.reverse_cons,List.append_assoc,List.singleton_append,hpa] using hy
            · simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,hpa] using hpy
            · simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,hpa] using hqy
          · have he : y = (false,false,[]) := by
              simpa only [ExposureTree.fresh,PMF.mem_support_pure_iff] using hy
            simp only [he,List.not_mem_nil,false_and,exists_false] at hpy
        · have hrow : cs.map (fun p => (req (p.1 :: c.address),program p)) =
              cs.map (fun p => (decide (p.1 = a ∨ p.1 = b),program p)) := by
            apply List.map_congr_left
            intro p _
            rw [show req (p.1 :: c.address) = decide (p.1 = a ∨ p.1 = b) from
              pairRequired_base_child c.address a b p.1 as bs]
          rw [hrow] at hw
          apply ExposureTree.checkMarkedTrace_two_hit ν
            (fun q : QueryCall ι τ => q.address = (a :: as).reverse ++ c.address)
            (fun q : QueryCall ι τ => q.address = (b :: bs).reverse ++ c.address)
            Prod.fst program a b hab cs hnd _ _ hw hp' hq'
          · intro p hp y hy hh
            have hpa := hhead a as p hp y hy hh
            refine ⟨hpa,?_⟩
            dsimp only [program,req] at hy
            split_ifs at hy with hk
            · simp only [hpa] at hy
              rw [jointMarkedQuery_pair_child H N d p.2.val c.address a b as bs hab] at hy
              apply jointMarkedQuery_hit H N d p.2.val
                ⟨a :: c.address,(H a.2).erase a.1,some a.2⟩ as ν hy
              simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using hh
            · have he : y = (false,false,[]) := by
                simpa only [ExposureTree.fresh,PMF.mem_support_pure_iff] using hy
              simp only [he,List.not_mem_nil,false_and,exists_false] at hh
          · intro p hp y hy hh
            have hpb := hhead b bs p hp y hy hh
            refine ⟨hpb,?_⟩
            dsimp only [program,req] at hy
            split_ifs at hy with hk
            · simp only [hpb] at hy
              have he : pairRequired (c.address.reverse ++ a :: as) (c.address.reverse ++ b :: bs) =
                  pairRequired (c.address.reverse ++ b :: bs) (c.address.reverse ++ a :: as) := by
                funext l
                exact Bool.or_comm _ _
              rw [he,jointMarkedQuery_pair_child H N d p.2.val c.address b a bs as (Ne.symm hab)] at hy
              apply jointMarkedQuery_hit H N d p.2.val
                ⟨b :: c.address,(H b.2).erase b.1,some b.2⟩ bs ν hy
              simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using hh
            · have he : y = (false,false,[]) := by
                simpa only [ExposureTree.fresh,PMF.mem_support_pure_iff] using hy
              simp only [he,List.not_mem_nil,false_and,exists_false] at hh

end JointPairHit
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Probability_PairVisitProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave
section TracePairProbability
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem actualPairVisitProbability_le_marked (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (focus : Finset ι) (parent : Option τ) (path₁ path₂ : List (ι × τ)) :
    actualPairVisitProbability H N d k focus parent path₁ path₂ ≤
      pairVisitProbability H N d k focus parent path₁ path₂ := by
  let c : QueryCall ι τ := ⟨[],focus,parent⟩
  let ν := fun _ : τ => PMF.uniformOfFintype (Fin N)
  let P := ExposureTree.fresh ν (jointMarkedQuery H N (pairRequired path₁ path₂) d k c)
  have ht : P.map (fun z => (z.1,z.2.2)) =
      ExposureTree.fresh ν (tracedGridQuery H N d k c) := by
    rw [← ExposureTree.fresh_mapOutput,jointMarkedQuery_trace]
  have hm : P.map (fun z => (z.1,z.2.1)) =
      ExposureTree.fresh ν (markedGridQueryDepth H N (pairRequired path₁ path₂) d k [] focus parent) := by
    rw [← ExposureTree.fresh_mapOutput,jointMarkedQuery_marked]
  unfold actualPairVisitProbability pairVisitProbability
  rw [markedGood_map_true,← ht,← hm,PMF.map_comp,PMF.map_comp]
  apply pmf_boolean_map_le
  intro z hz hh
  obtain ⟨hp,hq⟩ := Bool.and_eq_true_iff.mp hh
  obtain ⟨a,ha,hea⟩ := List.any_eq_true.mp hp
  obtain ⟨b,hb,heb⟩ := List.any_eq_true.mp hq
  apply jointMarkedQuery_pair_hit H N d k c path₁ path₂ ν hz
  · exact ⟨a,ha,by simpa only [c,List.append_nil] using of_decide_eq_true hea⟩
  · exact ⟨b,hb,by simpa only [c,List.append_nil] using of_decide_eq_true heb⟩

end TracePairProbability
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Probability_RootPairVisitProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave
section RootForkVisitation
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem rootPairVisitProbability_fork (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (b : ℕ → ℝ) (hb : ∀ t, 0 ≤ b t) (hq : GridRowQuality H N b)
    (C : ℝ) (hC : 0 ≤ C) (hlower : ∀ t ≤ N, 1 ≤ C*b t)
    (d k : ℕ) (hkd : k ≤ d+1) (hkN : k ≤ N)
    (focus : Finset ι) (parent : Option τ)
    (a b' : gridCandidates H focus parent) (hab : a ≠ b')
    (as bs : List (ι × τ)) (ha : LegalQueryPath H ((H a.val.2).erase a.val.1) (some a.val.2) as)
    (hb' : LegalQueryPath H ((H b'.val.2).erase b'.val.1) (some b'.val.2) bs)
    (halen : as.length ≤ d) (hblen : bs.length ≤ d) :
    pairVisitProbability H N (d+1) k focus parent (a.val :: as) (b'.val :: bs) ≤
      C^2 * orderedWeight (fun t => (2/(N : ℝ))*b t) (as.length+1) k *
        orderedWeight (fun t => (2/(N : ℝ))*b t) (bs.length+1) k := by
  let A := fun t => orderedWeight (fun t => (2/(N : ℝ))*b t) as.length t
  let B := fun t => orderedWeight (fun t => (2/(N : ℝ))*b t) bs.length t
  have hA : ∀ t, 0 ≤ A t := fun t => orderedWeight_nonneg (fun t => mul_nonneg (by positivity) (hb t)) _ t
  have hB : ∀ t, 0 ≤ B t := fun t => orderedWeight_nonneg (fun t => mul_nonneg (by positivity) (hb t)) _ t
  have hstep := markedQuery_two_paths H N (pairRequired (a.val :: as) (b'.val :: bs)) d k hkd hkN []
    focus parent a b' hab (pair_required_candidates H _ _ a b' as bs) (fun _ => 1)
    (fun t ht => hq.1 t (by omega))
    (fun t _ => (gridAnswerProbability_mem_unit H N N t focus parent).2.trans (by norm_num))
  have hac := (Finset.mem_filter.mp a.property).2.1
  have hbc := (Finset.mem_filter.mp b'.property).2.1
  calc
    _ ≤ (1/(N : ℝ))*∑ u : Fin N, (1/(N : ℝ))*∑ v : Fin N,
        if u.val < k ∧ v.val < k then
          (markedGood (markedChildKernel H N (pairRequired (a.val :: as) (b'.val :: bs)) d []
            focus parent a u)*
          markedGood (markedChildKernel H N (pairRequired (a.val :: as) (b'.val :: bs)) d []
            focus parent b' v))*(2*1) else 0 := hstep
    _ ≤ (1/(N : ℝ))*∑ u : Fin N, (1/(N : ℝ))*∑ v : Fin N,
        C^2*((if u.val < k then A u.val*(2*b u.val) else 0)*
          (if v.val < k then B v.val*(2*b v.val) else 0)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro u _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro v _
      by_cases hu : u.val < k <;> by_cases hv : v.val < k
      · simp only [hu,hv,and_self,↓reduceIte]
        rw [marked_pair_child_left H N d _ _ a b' hab as bs u,
          marked_pair_child_right H N d _ _ a b' hab as bs v]
        have hau := pathVisitProbability_ordered H N b hb hq as d u.val (by omega) u.isLt.le
          halen a.val.1 a.val.2 hac ha
        have hbv := pathVisitProbability_ordered H N b hb hq bs d v.val (by omega) v.isLt.le
          hblen b'.val.1 b'.val.2 hbc hb'
        have hp := mul_le_mul hau hbv (markedGood_nonneg _) (hA _)
        dsimp only [pathVisitProbability] at hp
        have hm : 1 ≤ C^2*(b u.val*b v.val) := by
          have hh := mul_le_mul (hlower u.val u.isLt.le) (hlower v.val v.isLt.le)
            (by norm_num : (0 : ℝ) ≤ 1) (mul_nonneg hC (hb _))
          nlinarith
        have hw := mul_le_mul_of_nonneg_left hm (mul_nonneg (hA u.val) (hB v.val))
        have hab0 := mul_nonneg (hA u.val) (hB v.val)
        nlinarith
      · simp only [hu,hv,and_false,↓reduceIte,mul_zero,le_refl]
      · simp only [hu,hv,false_and,↓reduceIte,zero_mul,mul_zero,le_refl]
      · simp only [hu,hv,false_and,↓reduceIte,mul_zero,le_refl]
    _ = C^2*((1/(N : ℝ))*∑ u : Fin N, if u.val < k then A u.val*(2*b u.val) else 0)*
        ((1/(N : ℝ))*∑ v : Fin N, if v.val < k then B v.val*(2*b v.val) else 0) := by
      simp only [← Finset.mul_sum,← Finset.sum_mul]
      ring
    _ = _ := by
      rw [discrete_ordered_step N k hkN b as.length,discrete_ordered_step N k hkN b bs.length]

end RootForkVisitation
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Probability_RootPairVisitProbability2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave
section RootSpineVisitation
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem rootPairVisitProbability_spine (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (b : ℕ → ℝ) (hb : ∀ t, 0 ≤ b t) (hq : GridRowQuality H N b)
    (C : ℝ) (hC : 0 ≤ C) (hlower : ∀ t ≤ N, 1 ≤ C*b t)
    (spine : List (ι × τ)) (a b' : ι × τ) (hab : a ≠ b') (as bs : List (ι × τ))
    (d k : ℕ) (hkd : k ≤ d) (hkN : k ≤ N)
    (focus : Finset ι) (parent : Option τ)
    (ha : LegalQueryPath H focus parent (spine ++ a :: as))
    (hb' : LegalQueryPath H focus parent (spine ++ b' :: bs))
    (halen : spine.length + (as.length+1) ≤ d) (hblen : spine.length + (bs.length+1) ≤ d) :
    pairVisitProbability H N d k focus parent
      (spine ++ a :: as) (spine ++ b' :: bs) ≤
      C^2 * orderedWeight (fun t => (2/(N : ℝ))*b t) spine.length k *
        orderedWeight (fun t => (2/(N : ℝ))*b t) (as.length+1) k *
        orderedWeight (fun t => (2/(N : ℝ))*b t) (bs.length+1) k := by
  have hw : ∀ t, 0 ≤ (2/(N : ℝ))*b t := fun t => mul_nonneg (by positivity) (hb t)
  cases spine with
  | nil =>
    cases d with
    | zero => simp only [List.length_nil] at halen; omega
    | succ d =>
      obtain ⟨ha,hat⟩ := ha
      obtain ⟨hb',hbt⟩ := hb'
      let aa : gridCandidates H focus parent := ⟨a,ha⟩
      let bb : gridCandidates H focus parent := ⟨b',hb'⟩
      have hne : aa ≠ bb := fun h => hab (congrArg Subtype.val h)
      simpa only [List.nil_append,List.length_nil,orderedWeight,mul_one] using
        rootPairVisitProbability_fork H N b hb hq C hC hlower d k hkd hkN focus parent aa bb hne as bs
          hat hbt (by simp only [List.length_nil] at halen; omega)
          (by simp only [List.length_nil] at hblen; omega)
  | cons z zs =>
    cases d with
    | zero => simp only [List.length_cons] at halen; omega
    | succ d =>
      obtain ⟨hz,haz⟩ := ha
      obtain ⟨_,hbz⟩ := hb'
      let zz : gridCandidates H focus parent := ⟨z,hz⟩
      have hzc := (Finset.mem_filter.mp hz).2.1
      have hs := markedQuery_single_path H N
        (pairRequired (z :: (zs ++ a :: as)) (z :: (zs ++ b' :: bs))) d k hkd hkN []
        focus parent zz (pair_common_required_candidates H _ _ zz _ _) (fun _ => 1)
        (fun t ht => hq.1 t (by omega))
        (fun t _ => (gridAnswerProbability_mem_unit H N N t focus parent).2.trans (by norm_num))
      let A := orderedWeight (fun t => (2/(N : ℝ))*b t) (as.length+1) k
      let B := orderedWeight (fun t => (2/(N : ℝ))*b t) (bs.length+1) k
      have hA : 0 ≤ A := orderedWeight_nonneg hw _ _
      have hB : 0 ≤ B := orderedWeight_nonneg hw _ _
      calc
        _ ≤ (1/(N : ℝ))*∑ u : Fin N, if u.val < k then
            markedGood (markedChildKernel H N
              (pairRequired (z :: (zs ++ a :: as)) (z :: (zs ++ b' :: bs))) d []
              focus parent zz u)*(2*1) else 0 := hs
        _ ≤ (1/(N : ℝ))*∑ u : Fin N, if u.val < k then
            (C^2*orderedWeight (fun t => (2/(N : ℝ))*b t) zs.length u.val*A*B)*(2*b u.val)
            else 0 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum
          intro u _
          by_cases hu : u.val < k
          · simp only [hu,↓reduceIte]
            rw [marked_pair_common_child H N d _ _ zz _ _ u]
            have hi := pairVisitProbability_spine H N b hb hq C hC hlower zs a b' hab as bs
              d u.val (by omega) u.isLt.le z.1 z.2 hzc haz hbz
              (by simp only [List.length_cons] at halen; omega)
              (by simp only [List.length_cons] at hblen; omega)
            have hj : pairVisitProbability H N d u.val ((H z.2).erase z.1) (some z.2)
                (zs ++ a :: as) (zs ++ b' :: bs) ≤
                C*orderedWeight (fun t => (2/(N : ℝ))*b t) zs.length u.val*A*B := by
              apply hi.trans
              apply mul_le_mul
              · apply mul_le_mul_of_nonneg_left
                · exact orderedWeight_mono hw _ hu.le
                · exact mul_nonneg hC (orderedWeight_nonneg hw _ _)
              · exact orderedWeight_mono hw _ hu.le
              · exact orderedWeight_nonneg hw _ _
              · exact mul_nonneg (mul_nonneg hC (orderedWeight_nonneg hw _ _)) hA
            have hz0 := orderedWeight_nonneg hw zs.length u.val
            have hcharge := mul_le_mul_of_nonneg_left (hlower u.val u.isLt.le)
              (mul_nonneg (mul_nonneg (mul_nonneg hC hz0) hA) hB)
            dsimp only [pairVisitProbability] at hj
            nlinarith
          · simp only [hu,↓reduceIte,le_refl]
        _ = C^2*((1/(N : ℝ))*∑ u : Fin N, if u.val < k then
            orderedWeight (fun t => (2/(N : ℝ))*b t) zs.length u.val*(2*b u.val) else 0)*A*B := by
          simp only [Finset.mul_sum,Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro u _
          by_cases hu : u.val < k <;> simp only [hu,↓reduceIte] <;> ring
        _ = _ := by
          rw [discrete_ordered_step N k hkN b zs.length]
          rfl

end RootSpineVisitation
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Probability_RootPathVisitProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave
section RootPathVisitation
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem rootPathVisitProbability_ordered (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (b : ℕ → ℝ) (hb : ∀ t, 0 ≤ b t) (hq : GridRowQuality H N b)
    (C : ℝ) (hC : 1 ≤ C) (hlower : ∀ t ≤ N, 1 ≤ C*b t)
    (path : List (ι × τ)) (d k : ℕ) (hkd : k ≤ d) (hkN : k ≤ N)
    (hlen : path.length ≤ d) (focus : Finset ι) (parent : Option τ)
    (hpath : LegalQueryPath H focus parent path) :
    pathVisitProbability H N d k focus parent path ≤
      C*orderedWeight (fun t => (2/(N : ℝ))*b t) path.length k := by
  cases path with
  | nil =>
    simpa only [List.length_nil,orderedWeight,mul_one,pathVisitProbability] using
      (markedGood_le_one (ExposureTree.fresh (fun _ : τ => PMF.uniformOfFintype (Fin N))
        (markedGridQueryDepth H N (pathRequired []) d k [] focus parent))).trans hC
  | cons a as =>
    cases d with
    | zero => simp only [List.length_cons] at hlen; omega
    | succ d =>
      obtain ⟨ha,htail⟩ := hpath
      let aa : gridCandidates H focus parent := ⟨a,ha⟩
      have haT : a.1 ∈ H a.2 := (Finset.mem_filter.mp ha).2.1
      have hstep := markedQuery_single_path H N (pathRequired (a :: as)) d k hkd hkN []
        focus parent aa (path_required_candidates H _ _ aa as) (fun _ => 1)
        (fun t ht => hq.1 t (by omega))
        (fun t _ => (gridAnswerProbability_mem_unit H N N t focus parent).2.trans (by norm_num))
      change pathVisitProbability H N (d+1) k focus parent (a :: as) ≤ _ at hstep
      calc
        _ ≤ (1/(N : ℝ))*∑ u : Fin N, if u.val < k then
            markedGood (markedChildKernel H N (pathRequired (a :: as)) d []
              focus parent aa u)*(2*1) else 0 := hstep
        _ ≤ C*((1/(N : ℝ))*∑ u : Fin N, if u.val < k then
            orderedWeight (fun t => (2/(N : ℝ))*b t) as.length u.val*(2*b u.val)
            else 0) := by
          rw [mul_left_comm C (1/(N : ℝ))]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro u _
          by_cases hu : u.val < k
          · simp only [hu,↓reduceIte]
            rw [marked_path_child H N d focus parent aa as u]
            have hi := pathVisitProbability_ordered H N b hb hq as d u.val (by omega)
              u.isLt.le (by simp only [List.length_cons] at hlen; omega) a.1 a.2 haT htail
            have ho := orderedWeight_nonneg (fun t => mul_nonneg (by positivity : (0 : ℝ) ≤ 2/(N : ℝ)) (hb t)) as.length u.val
            have hl := hlower u.val u.isLt.le
            change pathVisitProbability H N d u.val ((H a.2).erase a.1) (some a.2) as * (2*1) ≤ _
            nlinarith [mul_nonneg ho (sub_nonneg.mpr hl)]
          · simp only [hu,↓reduceIte,mul_zero,le_refl]
        _ = _ := by
          rw [discrete_ordered_step N k hkN b as.length]
          rfl

theorem actualRootPathVisitProbability_factorial (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (b : ℕ → ℝ) (hb : ∀ t, 0 ≤ b t) (hq : GridRowQuality H N b)
    (C : ℝ) (hC : 1 ≤ C) (hlower : ∀ t ≤ N, 1 ≤ C*b t)
    (path : List (ι × τ)) (d k : ℕ) (hkd : k ≤ d) (hkN : k ≤ N)
    (hlen : path.length ≤ d) (focus : Finset ι) (parent : Option τ)
    (hpath : LegalQueryPath H focus parent path) :
    actualPathVisitProbability H N d k focus parent path ≤
      C*(prefixWeight (fun t => (2/(N : ℝ))*b t) k ^ path.length /
        (path.length.factorial : ℝ)) := by
  apply (actualPathVisitProbability_le_marked H N d k focus parent path).trans
  apply (rootPathVisitProbability_ordered H N b hb hq C hC hlower path d k hkd hkN hlen
    focus parent hpath).trans
  exact mul_le_mul_of_nonneg_left
    (orderedWeight_le (fun t => mul_nonneg (by positivity) (hb t)) _ _) (by linarith)

end RootPathVisitation
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_DivergentArms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave

lemma factorial_weight_add_le {x : ℝ} (hx : 0 ≤ x) (i j : ℕ) :
    x^(i+j)/(Nat.factorial (i+j) : ℝ) ≤
      (x^i/(i.factorial : ℝ))*(x^j/(j.factorial : ℝ)) := by
  have hf : (i.factorial : ℝ)*(j.factorial : ℝ) ≤ ((i+j).factorial : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos (i+j))
      (Nat.factorial_mul_factorial_dvd_factorial_add i j)
  rw [pow_add,div_mul_div_comm]
  exact div_le_div_of_nonneg_left (mul_nonneg (pow_nonneg hx _) (pow_nonneg hx _))
    (mul_pos (by positivity) (by positivity)) hf

lemma cube_ge_self {C : ℝ} (hC : 1 ≤ C) : C ≤ C^3 := by nlinarith [sq_nonneg (C-1)]
lemma cube_ge_sq {C : ℝ} (hC : 1 ≤ C) : C^2 ≤ C^3 := by
  have h := mul_le_mul_of_nonneg_left hC (sq_nonneg C)
  nlinarith

section ActualPairFactorial
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

lemma actualPairVisitProbability_le_left (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (focus : Finset ι) (parent : Option τ) (p q : List (ι × τ)) :
    actualPairVisitProbability H N d k focus parent p q ≤
      actualPathVisitProbability H N d k focus parent p := by
  unfold actualPairVisitProbability actualPathVisitProbability
  apply pmf_boolean_map_le
  intro z _ h
  exact (Bool.and_eq_true_iff.mp h).1

lemma actualPairVisitProbability_le_right (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (focus : Finset ι) (parent : Option τ) (p q : List (ι × τ)) :
    actualPairVisitProbability H N d k focus parent p q ≤
      actualPathVisitProbability H N d k focus parent q := by
  unfold actualPairVisitProbability actualPathVisitProbability
  apply pmf_boolean_map_le
  intro z _ h
  exact (Bool.and_eq_true_iff.mp h).2

theorem actualPairVisitProbability_pattern_factorial (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (b : ℕ → ℝ) (hb : ∀ t, 0 ≤ b t) (hq : GridRowQuality H N b)
    (C : ℝ) (hC : 1 ≤ C) (hlower : ∀ t ≤ N, 1 ≤ C*b t)
    (spine left right : List (ι × τ)) (hdiv : DivergentArms left right)
    (d k : ℕ) (hkd : k ≤ d) (hkN : k ≤ N)
    (focus : Finset ι) (parent : Option τ)
    (ha : LegalQueryPath H focus parent (spine ++ left))
    (hb' : LegalQueryPath H focus parent (spine ++ right))
    (halen : (spine ++ left).length ≤ d) (hblen : (spine ++ right).length ≤ d) :
    actualPairVisitProbability H N d k focus parent (spine ++ left) (spine ++ right) ≤
      C^3 * (prefixWeight (fun t => (2/(N : ℝ))*b t) k ^
        (spine.length+left.length+right.length) /
        ((spine.length.factorial : ℝ)*(left.length.factorial : ℝ)*(right.length.factorial : ℝ))) := by
  let w := fun t => (2/(N : ℝ))*b t
  let x := prefixWeight w k
  have hw : ∀ t, 0 ≤ w t := fun t => mul_nonneg (by positivity) (hb t)
  have hx : 0 ≤ x := prefixWeight_nonneg hw k
  have hc0 : 0 ≤ C := by linarith
  have hc3 : 0 ≤ C^3 := pow_nonneg hc0 _
  cases left with
  | nil =>
    have ht := (actualPairVisitProbability_le_right H N d k focus parent (spine ++ []) (spine ++ right)).trans
      (actualRootPathVisitProbability_factorial H N b hb hq C hC hlower (spine ++ right)
        d k hkd hkN hblen focus parent hb')
    have hsplit := factorial_weight_add_le hx spine.length right.length
    have hg := mul_le_mul_of_nonneg_left hsplit hc3
    have hf : C*(x^(spine.length+right.length)/((spine.length+right.length).factorial : ℝ)) ≤
        C^3*(x^(spine.length+right.length)/((spine.length+right.length).factorial : ℝ)) :=
      mul_le_mul_of_nonneg_right (cube_ge_self hC) (by positivity)
    apply ht.trans
    change C*(x^((spine ++ right).length)/(((spine ++ right).length).factorial : ℝ)) ≤ _
    simp only [List.length_append,List.length_nil,Nat.add_zero,Nat.factorial_zero,Nat.cast_one,mul_one]
    apply hf.trans
    simpa only [div_mul_div_comm,← pow_add] using hg
  | cons a as =>
    cases right with
    | nil =>
      have ht := (actualPairVisitProbability_le_left H N d k focus parent (spine ++ a :: as) (spine ++ [])).trans
        (actualRootPathVisitProbability_factorial H N b hb hq C hC hlower (spine ++ a :: as)
          d k hkd hkN halen focus parent ha)
      have hsplit := factorial_weight_add_le hx spine.length (a :: as).length
      have hg := mul_le_mul_of_nonneg_left hsplit hc3
      have hf : C*(x^(spine.length+(a :: as).length)/((spine.length+(a :: as).length).factorial : ℝ)) ≤
          C^3*(x^(spine.length+(a :: as).length)/((spine.length+(a :: as).length).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_right (cube_ge_self hC) (by positivity)
      apply ht.trans
      change C*(x^((spine ++ a :: as).length)/(((spine ++ a :: as).length).factorial : ℝ)) ≤ _
      simp only [List.length_append,List.length_nil,Nat.add_zero,Nat.factorial_zero,Nat.cast_one,mul_one]
      apply hf.trans
      simpa only [div_mul_div_comm,← pow_add] using hg
    | cons a' as' =>
      have ht := (actualPairVisitProbability_le_marked H N d k focus parent _ _).trans
        (rootPairVisitProbability_spine H N b hb hq C hc0 hlower spine a a' hdiv as as'
          d k hkd hkN focus parent ha hb'
          (by simpa only [List.length_append,List.length_cons] using halen)
          (by simpa only [List.length_append,List.length_cons] using hblen))
      have hs := three_segment_weight_le hw spine.length (as.length+1) (as'.length+1) k
      have hp := mul_le_mul_of_nonneg_left hs (sq_nonneg C)
      have he : C^2 * orderedWeight w spine.length k * orderedWeight w (as.length+1) k *
          orderedWeight w (as'.length+1) k =
          C^2*(orderedWeight w spine.length k * orderedWeight w (as.length+1) k *
            orderedWeight w (as'.length+1) k) := by ring
      apply ht.trans
      change C^2 * orderedWeight w spine.length k * orderedWeight w (as.length+1) k *
        orderedWeight w (as'.length+1) k ≤ _
      rw [he]
      apply hp.trans
      apply mul_le_mul_of_nonneg_right (cube_ge_sq hC)
      exact div_nonneg (pow_nonneg (prefixWeight_nonneg hw k) _) (by positivity)

end ActualPairFactorial
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_SplitQueryPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave

lemma pmf_boolean_finite_cover {A J : Type*} (P : PMF A) (s : Finset J)
    (f : A → Bool) (g : J → A → Bool)
    (hcover : ∀ a ∈ P.support, f a = true → ∃ j ∈ s, g j a = true) :
    ((P.map f) true).toReal ≤ ∑ j ∈ s, ((P.map (g j)) true).toReal := by
  classical
  have hc (q : J → A → ℝ≥0∞) :
      (∑' a, ∑ j ∈ s, q j a) = ∑ j ∈ s, ∑' a, q j a := by
    clear hcover
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih => simp only [Finset.sum_insert hj,ENNReal.tsum_add,ih]
  have hp : (P.map f) true ≤ ∑ j ∈ s, (P.map (g j)) true := by
    simp only [PMF.map_apply]
    rw [← hc]
    apply ENNReal.tsum_le_tsum
    intro a
    by_cases h0 : P a = 0
    · simp only [h0,ite_self,Finset.sum_const_zero,le_refl]
    by_cases hf : f a = true
    · obtain ⟨j,hj,hg⟩ := hcover a ((PMF.mem_support_iff _ _).mpr h0) hf
      simp only [hf,↓reduceIte]
      have hterm : (if true = g j a then P a else 0) ≤
          ∑ j ∈ s, if true = g j a then P a else 0 :=
        Finset.single_le_sum (f := fun j => (if true = g j a then P a else 0))
          (fun _ _ => by positivity) hj
      convert hterm using 1 <;> simp [hg]
    · simp only [Ne.symm hf,↓reduceIte,zero_le]
  have hf : ∀ j ∈ s, (P.map (g j)) true ≠ ⊤ := fun j _ => PMF.apply_ne_top _ _
  have hh := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr hf) hp
  rwa [ENNReal.toReal_sum hf] at hh

theorem splitQueryPaths_spec {A : Type*} [DecidableEq A] (p q : List A) :
    p = (splitQueryPaths p q).1 ++ (splitQueryPaths p q).2.1 ∧
    q = (splitQueryPaths p q).1 ++ (splitQueryPaths p q).2.2 ∧
    DivergentArms (splitQueryPaths p q).2.1 (splitQueryPaths p q).2.2 := by
  induction p generalizing q with
  | nil => simp [splitQueryPaths,DivergentArms]
  | cons a p ih =>
    cases q with
    | nil => simp [splitQueryPaths,DivergentArms]
    | cons b q =>
      by_cases hab : a = b
      · subst b
        obtain ⟨hp,hq,hd⟩ := ih q
        simpa only [splitQueryPaths,↓reduceIte,List.cons_append,List.cons.injEq,true_and] using
          And.intro hp (And.intro hq hd)
      · simp [splitQueryPaths,hab,DivergentArms]

lemma pairFactorialWeight_nonneg {A : Type*} [DecidableEq A] {x : ℝ}
    (hx : 0 ≤ x) (p q : List A) : 0 ≤ pairFactorialWeight x p q := by
  unfold pairFactorialWeight
  positivity

section PairWeight
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem actualPairVisitProbability_weight (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (b : ℕ → ℝ) (hb : ∀ t, 0 ≤ b t) (hq : GridRowQuality H N b)
    (C : ℝ) (hC : 1 ≤ C) (hlower : ∀ t ≤ N, 1 ≤ C*b t)
    (d k : ℕ) (hkd : k ≤ d) (hkN : k ≤ N) (focus : Finset ι) (parent : Option τ)
    (p q : List (ι × τ))
    (hp : p ∈ legalPaths H d focus parent) (hqp : q ∈ legalPaths H d focus parent) :
    actualPairVisitProbability H N d k focus parent p q ≤
      C^3 * pairFactorialWeight (prefixWeight (fun t => (2/(N : ℝ))*b t) k) p q := by
  obtain ⟨hpl,hplen⟩ := (mem_legalPaths H d focus parent p).mp hp
  obtain ⟨hql,hqlen⟩ := (mem_legalPaths H d focus parent q).mp hqp
  obtain ⟨he₁,he₂,hd⟩ := splitQueryPaths_spec p q
  unfold pairFactorialWeight
  have ht := actualPairVisitProbability_pattern_factorial H N b hb hq C hC hlower
    (splitQueryPaths p q).1 (splitQueryPaths p q).2.1 (splitQueryPaths p q).2.2 hd
    d k hkd hkN focus parent (he₁ ▸ hpl) (he₂ ▸ hql) (he₁ ▸ hplen) (he₂ ▸ hqlen)
  rwa [← he₁,← he₂] at ht

end PairWeight
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_PrefixCodeSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

lemma nil_not_mem_prefixCodeSet {A : Type*} [DecidableEq A] (p : List A) :
    [] ∉ prefixCodeSet p := by
  cases p with
  | nil => simp [prefixCodeSet]
  | cons a p => simp [prefixCodeSet]

lemma prefixCodeSet_card {A : Type*} [DecidableEq A] (p : List A) :
    (prefixCodeSet p).card = p.length := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [prefixCodeSet,Finset.card_insert_of_notMem,Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2),ih,List.length_cons]
    intro h
    obtain ⟨q,hq,h⟩ := Finset.mem_image.mp h
    have he : q = [] := List.cons.inj h |>.2
    subst q
    exact nil_not_mem_prefixCodeSet p hq

lemma prefixCodeSet_cons_disjoint {A : Type*} [DecidableEq A] {a b : A}
    (hab : a ≠ b) (p q : List A) :
    Disjoint (prefixCodeSet (a::p)) (prefixCodeSet (b::q)) := by
  apply Finset.disjoint_left.mpr
  intro l hl hr
  have hhead {x : A} {t : List A} (h : l ∈ prefixCodeSet (x::t)) : l.head? = some x := by
    rw [prefixCodeSet] at h
    rcases Finset.mem_insert.mp h with rfl | h
    · rfl
    · obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp h
      rfl
  exact hab (Option.some.inj ((hhead hl).symm.trans (hhead hr)))

lemma prefixCodeSet_union_card {A : Type*} [DecidableEq A] (p q : List A) :
    (prefixCodeSet p ∪ prefixCodeSet q).card =
      (splitQueryPaths p q).1.length + (splitQueryPaths p q).2.1.length +
        (splitQueryPaths p q).2.2.length := by
  induction p generalizing q with
  | nil => simp [prefixCodeSet,splitQueryPaths,prefixCodeSet_card]
  | cons a p ih =>
    cases q with
    | nil => simpa only [prefixCodeSet,Finset.union_empty,splitQueryPaths,List.length_nil,zero_add,Nat.add_zero] using prefixCodeSet_card (a::p)
    | cons b q =>
      by_cases hab : a = b
      · subst b
        have he : prefixCodeSet (a::p) ∪ prefixCodeSet (a::q) =
            insert [a] ((prefixCodeSet p ∪ prefixCodeSet q).image (List.cons a)) := by
          simp only [prefixCodeSet,Finset.image_union,Finset.insert_union,Finset.union_insert,Finset.insert_idem]
        rw [he,Finset.card_insert_of_notMem,Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2),ih]
        · simp only [splitQueryPaths,↓reduceIte,List.length_cons]
          omega
        · intro h
          obtain ⟨t,ht,ht0⟩ := Finset.mem_image.mp h
          have he : t = [] := List.cons.inj ht0 |>.2
          subst t
          rcases Finset.mem_union.mp ht with h | h
          · exact nil_not_mem_prefixCodeSet p h
          · exact nil_not_mem_prefixCodeSet q h
      · rw [Finset.card_union_of_disjoint (prefixCodeSet_cons_disjoint hab p q),
          prefixCodeSet_card,prefixCodeSet_card]
        simp only [splitQueryPaths,hab,↓reduceIte,List.length_nil,zero_add]

lemma prefixCodeSet_append_singleton {A : Type*} [DecidableEq A] (p : List A) (a : A) :
    prefixCodeSet (p++[a]) = insert (p++[a]) (prefixCodeSet p) := by
  induction p with
  | nil => simp [prefixCodeSet]
  | cons b p ih =>
    simp only [List.cons_append,prefixCodeSet,ih,Finset.image_insert]
    exact Finset.insert_comm _ _ _

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_AddressHead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.PathForest
variable {s : ℕ} {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
lemma address_head (F : PathForest s) (key : Fin s → α) (i : Fin s) :
    (F.address key i).head? = some (key i) := by
  cases hp : F.parent i with
  | none => rw [F.address_none key i hp]; rfl
  | some j => rw [F.address_some key i j hp]; rfl

omit [DecidableEq α] in
lemma address_injective (F : PathForest s) {key : Fin s → α}
    (hk : Function.Injective key) : Function.Injective (F.address key) := by
  intro i j h
  apply hk
  exact Option.some.inj (by simpa only [F.address_head] using congrArg List.head? h)

lemma prefix_address_mem (F : PathForest s) (key : Fin s → α) (i : Fin s) (p : List α) :
    p ∈ prefixCodeSet (F.address key i).reverse ↔
      ∃ j, F.Ancestor j i ∧ p = (F.address key j).reverse := by
  induction i using (measure (fun i : Fin s => i.val)).wf.induction with
  | h i ih =>
    cases hp : F.parent i with
    | none =>
      rw [F.address_none key i hp]
      simp only [List.reverse_singleton,prefixCodeSet,Finset.image_empty,Finset.mem_insert,
        Finset.notMem_empty,or_false]
      constructor
      · intro h
        exact ⟨i,Relation.ReflTransGen.refl,by rw [F.address_none key i hp]; exact h⟩
      · rintro ⟨j,hj,rfl⟩
        rcases F.ancestor_eq_or_predecessor hj with he | ⟨k,hk,_⟩
        · subst j
          rw [F.address_none key i hp]; rfl
        · exact False.elim (by change F.parent i = some k at hk; rw [hp] at hk; cases hk)
    | some k =>
      have hi : (F.address key i).reverse = (F.address key k).reverse ++ [key i] := by
        rw [F.address_some key i k hp,List.reverse_cons]
      rw [hi,prefixCodeSet_append_singleton,Finset.mem_insert,ih k (F.property i k hp)]
      constructor
      · rintro (h | ⟨j,hj,h⟩)
        · exact ⟨i,Relation.ReflTransGen.refl,h.trans hi.symm⟩
        · exact ⟨j,hj.tail hp,h⟩
      · rintro ⟨j,hj,rfl⟩
        rcases F.ancestor_eq_or_predecessor hj with rfl | ⟨l,hl,hjl⟩
        · exact Or.inl hi
        · have he := F.predecessor_unique hl hp
          subst l
          exact Or.inr ⟨j,hjl,rfl⟩

lemma prefix_option_address_mem (F : PathForest s) (key : Fin s → α)
    (a : Option (Fin s)) (p : List α) :
    p ∈ prefixCodeSet (a.elim [] (F.address key)).reverse ↔
      ∃ j, F.OnPath a j ∧ p = (F.address key j).reverse := by
  cases a with
  | none => simp [prefixCodeSet,OnPath]
  | some i =>
    simp only [Option.elim_some,F.prefix_address_mem,OnPath,Option.some.injEq]
    constructor
    · rintro ⟨j,hj,hp⟩
      exact ⟨j,⟨i,rfl,hj⟩,hp⟩
    · rintro ⟨j,⟨i',rfl,hj⟩,hp⟩
      exact ⟨j,hj,hp⟩

lemma two_mark_exact_size (F : PathForest s) {key : Fin s → α}
    (hk : Function.Injective key) (a b : Option (Fin s))
    (hcover : ∀ i, F.OnPath a i ∨ F.OnPath b i) :
    let p := (a.elim [] (F.address key)).reverse
    let q := (b.elim [] (F.address key)).reverse
    (splitQueryPaths p q).1.length + (splitQueryPaths p q).2.1.length +
      (splitQueryPaths p q).2.2.length = s := by
  dsimp only
  rw [← prefixCodeSet_union_card]
  have he : prefixCodeSet (a.elim [] (F.address key)).reverse ∪
      prefixCodeSet (b.elim [] (F.address key)).reverse =
        Finset.univ.image (fun i => (F.address key i).reverse) := by
    ext p
    simp only [Finset.mem_union,F.prefix_option_address_mem,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro (⟨j,_,rfl⟩ | ⟨j,_,rfl⟩) <;> exact ⟨j,rfl⟩
    · rintro ⟨j,rfl⟩
      rcases hcover j with h | h
      · exact Or.inl ⟨j,h,rfl⟩
      · exact Or.inr ⟨j,h,rfl⟩
  rw [he,Finset.card_image_of_injective]
  · exact Finset.card_fin s
  · exact List.reverse_injective.comp (F.address_injective hk)

end SharpTerminalLeave.PathForest

open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_LegalCollisionPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave
section CollisionPathSum
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

lemma log_pair_probability (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (focus : Finset ι) (parent : Option τ) (p q : List (ι × τ)) :
    (((ExposureTree.freshLog (gridPriorities N)
      (tracedGridQuery H N d k ⟨[],focus,parent⟩)).map (fun z =>
        z.1.2.any (fun c => decide (c.address = p.reverse)) &&
        z.1.2.any (fun c => decide (c.address = q.reverse)))) true).toReal =
      actualPairVisitProbability H N d k focus parent p q := by
  unfold actualPairVisitProbability
  change _ = (((ExposureTree.fresh (gridPriorities N)
    (tracedGridQuery H N d k ⟨[],focus,parent⟩)).map _) true).toReal
  rw [← ExposureTree.freshLog_outcome,PMF.map_comp]
  rfl

end CollisionPathSum

end SharpTerminalLeave

open Filter
open scoped BigOperators Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Embeddings_EmbeddedWitnessPathSize
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

lemma embeddedWitness_path_size {n R d : ℕ} {G : Graph n}
    (W : BoundedEmbeddedWitness G R d) :
    let p := (embeddedWitnessPaths W).1
    let q := (embeddedWitnessPaths W).2
    (splitQueryPaths p q).1.length + (splitQueryPaths p q).2.1.length +
      (splitQueryPaths p q).2.2.length = W.1.val.2.val := by
  let q := W.1
  let w := W.2.2.1
  let ψ := W.2.2.2.val
  let key := indexedTriangleKey (dimensionBirth q) w.2.2.val ψ
  have hk : Function.Injective key := indexed_triangle_key_injective (fun _ => rfl)
    W.2.1.property w.2.1.val w.2.2.val w.2.2.property ψ
  exact w.2.1.val.two_mark_exact_size hk _ _ w.2.1.property

lemma embeddedWitness_factorial_weight {n R d : ℕ} {G : Graph n}
    (W : BoundedEmbeddedWitness G R d) {x : ℝ} (hx : 0 ≤ x) :
    pairFactorialWeight x (embeddedWitnessPaths W).1 (embeddedWitnessPaths W).2 ≤
      (3*x)^W.1.val.2.val / (W.1.val.2.val.factorial : ℝ) := by
  unfold pairFactorialWeight
  have hh := total_three_segment_weight_le hx
    (splitQueryPaths (embeddedWitnessPaths W).1 (embeddedWitnessPaths W).2).1.length
    (splitQueryPaths (embeddedWitnessPaths W).1 (embeddedWitnessPaths W).2).2.1.length
    (splitQueryPaths (embeddedWitnessPaths W).1 (embeddedWitnessPaths W).2).2.2.length
  dsimp only
  rw [embeddedWitness_path_size W] at hh ⊢
  exact hh

section AnyPaths
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

lemma actualPairVisitProbability_zero_of_illegal (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (focus : Finset ι) (parent : Option τ) (p q : List (ι × τ))
    (hbad : ¬ (p ∈ legalPaths H d focus parent ∧ q ∈ legalPaths H d focus parent)) :
    actualPairVisitProbability H N d k focus parent p q = 0 := by
  classical
  rw [← log_pair_probability]
  let P := ExposureTree.freshLog (gridPriorities N) (tracedGridQuery H N d k ⟨[],focus,parent⟩)
  let ev := fun (z : (Bool × List (QueryCall ι τ)) × List τ) =>
    z.1.2.any (fun c => decide (c.address = p.reverse)) &&
      z.1.2.any (fun c => decide (c.address = q.reverse))
  have hnone : ∀ z ∈ P.support, ev z = false := by
    intro z hz
    apply Bool.eq_false_iff.mpr
    intro he
    obtain ⟨hp,hq⟩ := Bool.and_eq_true_iff.mp he
    have hlegal (path : List (ι × τ)) (h : z.1.2.any (fun c => decide (c.address = path.reverse)) = true) :
        path ∈ legalPaths H d focus parent := by
      obtain ⟨a,ha,heq⟩ := List.any_eq_true.mp h
      have haeq : a.address = path.reverse := of_decide_eq_true heq
      obtain ⟨path',hp',ha'⟩ := tracedGridQuery_legal_path H N d k ⟨[],focus,parent⟩
        (gridPriorities N) hz a ha
      rw [ha',callAtPath_address,List.append_nil] at haeq
      have hh : path' = path := List.reverse_injective haeq
      exact hh ▸ hp'
    exact hbad ⟨hlegal p hp,hlegal q hq⟩
  have heq := pmf_map_congr_support P ev (fun _ => false) hnone
  change ((P.map ev) true).toReal = 0
  rw [heq]
  change ((P.map (Function.const _ false)) true).toReal = 0
  rw [PMF.map_const]
  simp

theorem actualPairVisitProbability_weight_any (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (b : ℕ → ℝ) (hb : ∀ t, 0 ≤ b t) (hq : GridRowQuality H N b)
    (C : ℝ) (hC : 1 ≤ C) (hlower : ∀ t ≤ N, 1 ≤ C*b t)
    (d k : ℕ) (hkd : k ≤ d) (hkN : k ≤ N) (focus : Finset ι) (parent : Option τ)
    (p q : List (ι × τ)) :
    actualPairVisitProbability H N d k focus parent p q ≤
      C^3 * pairFactorialWeight (prefixWeight (fun t => (2/(N : ℝ))*b t) k) p q := by
  by_cases h : p ∈ legalPaths H d focus parent ∧ q ∈ legalPaths H d focus parent
  · exact actualPairVisitProbability_weight H N b hb hq C hC hlower d k hkd hkN focus parent p q h.1 h.2
  · rw [actualPairVisitProbability_zero_of_illegal H N d k focus parent p q h]
    apply mul_nonneg (pow_nonneg (by linarith) _)
    apply pairFactorialWeight_nonneg
    apply Finset.sum_nonneg
    intro t _
    exact mul_nonneg (by positivity) (hb t)

end AnyPaths
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Embeddings_EmbeddedWitnessRoots
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave

lemma matchingSeed_full_image {V : Type*} [DecidableEq V] {N R : ℕ}
    (label : Fin N → V) (E : Finset (Finset V)) (hE : EdgeMatching E)
    (hi : Set.InjOn label {v | v.val < R})
    (hc : ∀ e ∈ E, ∀ x ∈ e, ∃ v : Fin N, v.val < R ∧ label v = x) :
    ((matchingSeed label E hE hi).backEdges (Finset.univ.filter (fun v => v.val < R))).image
      (Finset.image label) = E := by
  classical
  apply Finset.Subset.antisymm
  · intro e he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
    exact matchingSeed_edge_image label E hE hi _ hf
  · intro e he
    obtain ⟨x,y,hx,hy,hxy,rfl⟩ := matchingSeed_covers label E hE hi hc e he
    have hp : ({x,y} : Finset (Fin N)) ∈
        (matchingSeed label E hE hi).backEdges (Finset.univ.filter (fun v => v.val < R)) := by
      rcases hxy with hxy | hyx
      · exact Finset.mem_biUnion.mpr ⟨y,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy⟩,
          Finset.mem_image.mpr ⟨x,hxy,rfl⟩⟩
      · have hh : ({y,x} : Finset (Fin N)) ∈
            (matchingSeed label E hE hi).backEdges (Finset.univ.filter (fun v => v.val < R)) :=
          Finset.mem_biUnion.mpr ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩,
            Finset.mem_image.mpr ⟨y,hyx,rfl⟩⟩
        simpa only [Finset.pair_comm] using hh
    exact Finset.mem_image.mpr ⟨{x,y},hp,by simp only [Finset.image_insert,Finset.image_singleton]⟩

namespace TriangleGrowth
variable {n N R : ℕ} {G : Graph n} (A : TriangleGrowth (lookupGraph G) N R)

lemma pathRootEdges_image (a b : Fin N) (hi : Set.InjOn A.label (A.pathUnion a b)) :
    (A.pathRootEdges a b).image (Finset.image (A.pathAssignment a b hi)) =
      (A.seed.backEdges A.roots).image (Finset.image A.label) := by
  classical
  unfold pathRootEdges
  rw [Finset.image_image]
  apply Finset.image_congr
  intro e he
  have hs : e ⊆ A.pathUnion a b := by
    obtain ⟨v,hv,u,hu,rfl⟩ := A.seed.backEdges_mem_pair he
    have hvR : v.val < R := (Finset.mem_filter.mp hv).2
    have hul : u.val < v.val := A.seed.older_lt v u hu
    have huR : u.val < R := hul.trans hvR
    intro x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · subst x
      exact (A.mem_pathUnion a b u).mpr (Or.inl huR)
    · have hx' := Finset.mem_singleton.mp hx
      subst x
      exact (A.mem_pathUnion a b v).mpr (Or.inl hvR)
  change (reindexSet (A.pathUnion a b) e).image
    (fun i => A.label ((A.pathUnion a b).orderEmbOfFin rfl i)) = e.image A.label
  change (reindexSet (A.pathUnion a b) e).image
    (A.label ∘ (A.pathUnion a b).orderEmbOfFin rfl) = e.image A.label
  rw [← Finset.image_image,image_reindexSet hs]

end TriangleGrowth
namespace RecordedCallForest
variable {n : ℕ} {G : Graph n} {c : QueryCall (Finset (Fin n)) (Finset (Fin n))}
variable (F : RecordedCallForest (triangleHypergraph G) c)

lemma growth_seed_image (hM : EdgeMatching c.focus) (hG : c.focus ⊆ G) :
    ((F.toTriangleGrowth hM hG).seed.backEdges (F.toTriangleGrowth hM hG).roots).image
      (Finset.image (F.toTriangleGrowth hM hG).label) = c.focus :=
  matchingSeed_full_image F.vertexLabel c.focus hM F.vertexLabel_injective_roots F.vertexLabel_covers

end RecordedCallForest

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Embeddings_EmptyRootInjection
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

theorem rootedCount_empty_roots {k n : ℕ} (T : RootedTemplate k) (hT : T.roots = ∅)
    (ψ : {x // x ∈ T.roots} ↪ Fin n) (G : Graph n) :
    rootedCount T ψ G = ((graphEmbeddingSet T.edges G).card : ℝ) := by
  classical
  let e : RootedInjection T ψ ≃ (Fin k ↪ Fin n) :=
    { toFun := Subtype.val
      invFun := fun φ => ⟨φ,fun x => False.elim (by simpa [hT] using x.property)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold rootedCount copyCount
  calc
    _ = ∑ φ : Fin k ↪ Fin n, intact (T.edges.image (fun e => e.map φ)) G :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = _ := by simp [graphEmbeddingSet,intact]

theorem graphEmbeddingSet_large_count {n N : ℕ} {G : Graph n} {c C : ℝ}
    (hGood : GoodPrefixGraph n c C G) (E : Graph N) (hE : ∀ e ∈ E, e.card = 2)
    (hcap : N ≤ prefixTemplateCap)
    (hsparse : ∀ U : Finset (Fin N), (E.filter (· ⊆ U)).card ≤ 2 * U.card)
    (hp : 0 ≤ prefixDensity n) (hp1 : prefixDensity n ≤ 1) (hD : 1 ≤ prefixD n) :
    ((graphEmbeddingSet E G).card : ℝ) ≤
      prefixTemplateFactor n C * ((n : ℝ)^N * prefixDensity n ^ E.card) := by
  let T := unrootedTemplate E hE
  let ψ := emptyRootInjection (n := n) T rfl
  have h := (hGood.2.2.2.2.2 N hcap T ψ).1
    (largeTemplateEligible_of_sparse T rfl (prefixDensity n) hp hp1 hD hsparse)
  rw [rootedCount_empty_roots T rfl ψ G] at h
  simpa only [T,unrootedTemplate,rootedScaling,Finset.card_empty,Nat.sub_zero] using h

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_PlusEdgesSimple
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.BirthGraph
variable {N : ℕ} (B : BirthGraph N)

lemma plusEdges_simple {a b : Fin N} (hab : a ≠ b) :
    ∀ e ∈ insert ({a,b} : Finset (Fin N)) (B.backEdges Finset.univ), e.card = 2 := by
  intro e he
  rcases Finset.mem_insert.mp he with rfl | he
  · exact Finset.card_pair hab
  · obtain ⟨v,_,u,hu,rfl⟩ := B.backEdges_mem_pair he
    exact Finset.card_pair (ne_of_lt (B.older_lt v u hu))

lemma extra_not_mem_backEdges {a b : Fin N} (hne : ¬ B.graph.Adj a b) :
    ({a,b} : Finset (Fin N)) ∉ B.backEdges Finset.univ := by
  intro he
  obtain ⟨v,_,u,hu,he⟩ := B.backEdges_mem_pair he
  have ha : a = u ∨ a = v := by
    have hm : a ∈ ({u,v} : Finset (Fin N)) := he ▸ (by simp)
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hm
  have hb : b = u ∨ b = v := by
    have hm : b ∈ ({u,v} : Finset (Fin N)) := he ▸ (by simp)
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hm
  have hc := congrArg Finset.card he
  have hab : a ≠ b := by
    intro hh
    rw [hh,Finset.pair_eq_singleton,Finset.card_singleton,
      Finset.card_pair (ne_of_lt (B.older_lt v u hu))] at hc
    omega
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact hab rfl
  · exact hne (Or.inl hu)
  · exact hne (Or.inr hu)
  · exact hab rfl

theorem short_witness_count {n : ℕ} {G : Graph n} {c C : ℝ}
    (hGood : GoodPrefixGraph n c C G) {a b : Fin N} (hab : a ≠ b)
    (hne : ¬ B.graph.Adj a b) (hcap : N ≤ prefixTemplateCap)
    (hp : 0 ≤ prefixDensity n) (hp1 : prefixDensity n ≤ 1) (hD : 1 ≤ prefixD n) :
    ((graphEmbeddingSet (insert ({a,b} : Finset (Fin N)) (B.backEdges Finset.univ)) G).card : ℝ) ≤
      prefixTemplateFactor n C * ((n : ℝ)^N *
        prefixDensity n ^ ((B.backEdges Finset.univ).card + 1)) := by
  have h := graphEmbeddingSet_large_count hGood _ (B.plusEdges_simple hab) hcap
    (fun U => B.induced_plus_one_sparse U a b) hp hp1 hD
  rw [Finset.card_insert_of_notMem (B.extra_not_mem_backEdges hne)] at h
  exact h

end SharpTerminalLeave.BirthGraph

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_SeedEdgeSubsetPath
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.TriangleGrowth
variable {n N R : ℕ} {G : Graph n} (A : TriangleGrowth (lookupGraph G) N R)

lemma seed_edge_subset_pathUnion (a b : Fin N) {e : Finset (Fin N)}
    (he : e ∈ A.seed.backEdges A.roots) : e ⊆ A.pathUnion a b := by
  obtain ⟨v,hv,u,hu,rfl⟩ := A.seed.backEdges_mem_pair he
  have hvR := (A.mem_roots v).mp hv
  have huR := A.seed_root v u hu hvR
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact (A.mem_pathUnion a b x).mpr (Or.inl huR)
  · have h := Finset.mem_singleton.mp hx
    subst x
    exact (A.mem_pathUnion a b v).mpr (Or.inl hvR)

lemma pathRootEdges_card (a b : Fin N) :
    (A.pathRootEdges a b).card = (A.seed.backEdges A.roots).card := by
  classical
  apply Finset.card_image_of_injOn
  intro e he f hf h
  exact reindexSet_inj (A.seed_edge_subset_pathUnion a b he)
    (A.seed_edge_subset_pathUnion a b hf) h

lemma pathPattern_rootEdges (a b : Fin N) (hR : R ≤ N) :
    (A.pathPattern a b).backEdges (initialVertices (A.pathUnion a b).card R) =
      A.pathRootEdges a b := by
  classical
  let S := A.pathUnion a b
  have hroot : ∀ x : Fin N, x.val < R → x ∈ S :=
    fun x hx => (A.mem_pathUnion a b x).mpr (Or.inl hx)
  ext e
  constructor
  · intro he
    obtain ⟨v,hv,u,hu,rfl⟩ := (A.pathPattern a b).backEdges_mem_pair he
    have hv' := (mem_initialVertices _ _ _).mp hv
    have hvR : (S.orderEmbOfFin rfl v).val < R := by
      rw [orderEmb_initial S hR hroot v hv']
      exact hv'
    have hu' : S.orderEmbOfFin rfl u ∈ A.seed.older (S.orderEmbOfFin rfl v) := by
      change u ∈ reindexSet S (A.older (S.orderEmbOfFin rfl v)) at hu
      rw [mem_reindexSet] at hu
      rwa [A.older_eq_seed hvR] at hu
    have hem : ({S.orderEmbOfFin rfl u,S.orderEmbOfFin rfl v} : Finset (Fin N)) ∈
        A.seed.backEdges A.roots :=
      Finset.mem_biUnion.mpr ⟨_,(A.mem_roots _).mpr hvR,Finset.mem_image.mpr ⟨_,hu',rfl⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨_,hem,?_⟩
    rw [reindexSet_pair S _ _ (S.orderEmbOfFin_mem rfl u) (S.orderEmbOfFin_mem rfl v)]
    simp only [PathForest.index_embed]
  · intro he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨v,hv,u,hu,rfl⟩ := A.seed.backEdges_mem_pair hf
    have hvR := (A.mem_roots v).mp hv
    have huR := A.seed_root v u hu hvR
    have hvP := hroot v hvR
    have huP := hroot u huR
    rw [reindexSet_pair S u v huP hvP]
    apply Finset.mem_biUnion.mpr
    refine ⟨PathForest.index S v hvP,?_,Finset.mem_image.mpr
      ⟨PathForest.index S u huP,?_,rfl⟩⟩
    · apply (mem_initialVertices _ _ _).mpr
      change ((S.orderIsoOfFin rfl).symm ⟨v,hvP⟩).val < R
      rw [initial_rank S hroot v hvR]
      exact hvR
    · change PathForest.index S u huP ∈
        reindexSet S (A.older (S.orderEmbOfFin rfl (PathForest.index S v hvP)))
      rw [mem_reindexSet]
      rw [PathForest.embed_index,PathForest.embed_index,A.older_eq_seed hvR]
      exact hu

lemma pathPattern_root_small (a b : Fin N) (hR : R ≤ N)
    (v : Fin (A.pathUnion a b).card) (hv : v.val < R) :
    ((A.pathPattern a b).older v).card ≤ 1 := by
  rw [pathPattern,BirthGraph.restrict_older_card]
  have hvR : ((A.pathUnion a b).orderEmbOfFin rfl v).val < R := by
    rw [orderEmb_initial _ hR (fun x hx => (A.mem_pathUnion a b x).mpr (Or.inl hx)) v hv]
    exact hv
  change (A.older _).card ≤ 1
  rw [A.older_eq_seed hvR]
  exact A.seed_small _ hvR

lemma pathPattern_rootClosers (a b : Fin N) (hR : R ≤ N) :
    ((A.pathPattern a b).rootClosers R).card = (A.seed.backEdges A.roots).card := by
  rw [(A.pathPattern a b).rootClosers_card R (A.pathPattern_root_small a b hR),
    A.pathPattern_rootEdges a b hR,A.pathRootEdges_card]

lemma path_mark_reaches_suffix (a b : Fin N) (k : ℕ)
    (hR : R ≤ k) (hk : k < (A.pathUnion a b).card) :
    k ≤ (A.pathIndex a b a (A.left_mem_pathUnion a b)).val ∨
      k ≤ (A.pathIndex a b b (A.right_mem_pathUnion a b)).val := by
  have hc := A.pathPattern_covered a b k hR hk ⟨k,hk⟩
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,le_refl _⟩)
  rcases hc with ⟨ha,_⟩ | ⟨hb,_⟩
  · exact Or.inl (Finset.mem_filter.mp ha).2
  · exact Or.inr (Finset.mem_filter.mp hb).2

end SharpTerminalLeave.TriangleGrowth

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_BackEdgesCardSplit
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave
namespace BirthGraph
variable {N : ℕ} (B : BirthGraph N)

lemma backEdges_card_split (R : ℕ) (hR : R ≤ N)
    (hborn : ∀ v : Fin N, R ≤ v.val → (B.older v).card = 2) :
    (B.backEdges Finset.univ).card =
      (B.backEdges (initialVertices N R)).card + 2*(N-R) := by
  classical
  rw [B.backEdges_card,B.backEdges_card]
  have hsum := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin N)))
    (fun v => v.val < R) (fun v => (B.older v).card)
  have hborn' : (∑ v ∈ Finset.univ.filter (fun v : Fin N => ¬v.val < R), (B.older v).card) =
      2*(N-R) := by
    have he : (∑ v ∈ Finset.univ.filter (fun v : Fin N => ¬v.val < R), (B.older v).card) =
        ∑ _v ∈ Finset.univ.filter (fun v : Fin N => ¬v.val < R), 2 := by
      apply Finset.sum_congr rfl
      intro v hv
      exact hborn v (Nat.le_of_not_gt (Finset.mem_filter.mp hv).2)
    rw [he,Finset.sum_const,smul_eq_mul]
    have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
      (fun v => v.val < R)
    rw [Fin.card_filter_val_lt,Nat.min_eq_right hR,Finset.card_univ,Fintype.card_fin] at hc
    have hf : (Finset.univ.filter (fun v : Fin N => ¬v.val < R)).card = N-R := by omega
    rw [hf,Nat.mul_comm]
  rw [hborn'] at hsum
  exact hsum.symm

end BirthGraph

lemma witness_scale_identity (n r s : ℕ) :
    (n : ℝ)^(2*r+s) * prefixDensity n^(r+2*s+1) =
      (2*prefixM n)^r * prefixD n^s * prefixDensity n := by
  unfold prefixM prefixD
  have he : 2*((n : ℝ)^2 * prefixDensity n / 2) = (n : ℝ)^2 * prefixDensity n := by ring
  rw [he,pow_add,pow_add,pow_add,mul_pow,mul_pow]
  rw [pow_mul,pow_mul]
  ring

namespace TriangleGrowth
variable {n N r : ℕ} {G : Graph n} (A : TriangleGrowth (lookupGraph G) N (2*r))

lemma pathPattern_edge_card (a b : Fin N) (hR : 2*r ≤ N)
    (hseed : (A.seed.backEdges A.roots).card = r) :
    ((A.pathPattern a b).backEdges Finset.univ).card = r+2*(A.pathSuffix a b (2*r)).card := by
  rw [(A.pathPattern a b).backEdges_card_split (2*r)
    (roots_le_card _ hR (fun x hx => (A.mem_pathUnion a b x).mpr (Or.inl hx)))
    (A.pathPattern_nonroot a b)]
  rw [A.pathPattern_rootEdges a b hR,A.pathRootEdges_card,hseed,A.path_card_split a b hR]
  omega

theorem actual_short_witness_count {c C : ℝ} (hGood : GoodPrefixGraph n c C G)
    (a b : Fin N) (hR : 2*r ≤ N) (hseed : (A.seed.backEdges A.roots).card = r)
    (he : A.birthGraph.ExtraEdge (lookupGraph G) A.label a b)
    (hcap : (A.pathUnion a b).card ≤ prefixTemplateCap)
    (hp : 0 ≤ prefixDensity n) (hp1 : prefixDensity n ≤ 1) (hD : 1 ≤ prefixD n) :
    ((graphEmbeddingSet (insert ({A.pathIndex a b a (A.left_mem_pathUnion a b),
      A.pathIndex a b b (A.right_mem_pathUnion a b)} : Finset _)
      ((A.pathPattern a b).backEdges Finset.univ)) G).card : ℝ) ≤
      prefixTemplateFactor n C * ((2*prefixM n)^r *
        prefixD n^(A.pathSuffix a b (2*r)).card * prefixDensity n) := by
  have hex := A.pathPattern_extra he
  have h := (A.pathPattern a b).short_witness_count hGood hex.1 hex.2 hcap hp hp1 hD
  rw [A.pathPattern_edge_card a b hR hseed] at h
  conv at h => rhs; rw [A.path_card_split a b hR,witness_scale_identity]
  exact h

theorem actual_long_witness_count {c C : ℝ} (hGood : GoodPrefixGraph n c C G)
    (hsmall : (n : ℝ)^(-c) ≤ 1) (a b : Fin N) (hR : 2*r ≤ N)
    (hseed : (A.seed.backEdges A.roots).card = r)
    (he : A.birthGraph.ExtraEdge (lookupGraph G) A.label a b)
    (k : ℕ) (hrk : 2*r ≤ k) (hk : k < (A.pathUnion a b).card)
    (hcap : 3*((A.pathUnion a b).card-k)+1 ≤ prefixTemplateCap)
    (hp : 0 ≤ prefixDensity n) (hp1 : prefixDensity n ≤ 1) (hD : 1 ≤ prefixD n)
    (hscale : (n : ℝ)^((A.pathUnion a b).card-k) *
      prefixDensity n^(2*((A.pathUnion a b).card-k)+1) ≤ 1) :
    ((graphEmbeddingSet (insert ({A.pathIndex a b a (A.left_mem_pathUnion a b),
      A.pathIndex a b b (A.right_mem_pathUnion a b)} : Finset _)
      ((A.pathPattern a b).backEdges Finset.univ)) G).card : ℝ) ≤
      prefixTemplateFactor n C * ((4*prefixM n)^r * (2*prefixD n)^(k-2*r)) := by
  have hex := A.pathPattern_extra he
  apply (A.pathPattern a b).long_witness_count_unordered hGood hsmall r k hrk hk.le
  · rw [A.pathPattern_rootClosers a b hR,hseed]
  · exact A.pathPattern_nonroot a b
  · exact hex.1
  · exact hex.2
  · exact A.path_mark_reaches_suffix a b k hrk hk
  · exact A.pathPattern_covered a b k hrk hk
  · exact hcap
  · exact hp
  · exact hp1
  · exact hD
  · exact hscale

end TriangleGrowth
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_WitnessCountEventually
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.instFintypeBoundedEmbeddedWitness _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCode _root_.OAI.SharpTerminalLeave.instFintypeIndexedWitnessCodeEmbeddingBound _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem actual_witness_count_eventually (c C : ℝ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : Graph n), GoodPrefixGraph n c C G →
    ∀ r : ℕ, r ≤ 2 → ∀ N : ℕ, ∀ (A : TriangleGrowth (lookupGraph G) N (2*r)),
      2*r ≤ N → (A.seed.backEdges A.roots).card = r →
    ∀ a b : Fin N, A.birthGraph.ExtraEdge (lookupGraph G) A.label a b →
    ((graphEmbeddingSet (insert ({A.pathIndex a b a (A.left_mem_pathUnion a b),
      A.pathIndex a b b (A.right_mem_pathUnion a b)} : Finset _)
      ((A.pathPattern a b).backEdges Finset.univ)) G).card : ℝ) ≤
      (4*prefixM n)^r * (2*prefixD n)^(A.pathSuffix a b (2*r)).card / prefixD n^50 := by
  filter_upwards [prefix_short_suppression C,prefix_long_suppression C,
    prefix_suffix_scaling,prefix_scales_eventually_pos,eventually_ge_atTop (1 : ℕ)]
    with n hshort hlong hscale hpos hn
  intro G hGood r hr N A hR hseed a b he
  let s := (A.pathSuffix a b (2*r)).card
  have hcard : (A.pathUnion a b).card = 2*r+s := A.path_card_split a b hR
  have hm0 : 0 ≤ prefixM n := by
    unfold prefixM
    exact div_nonneg (mul_nonneg (sq_nonneg _) hpos.1.le) (by norm_num)
  have hD0 : 0 < prefixD n := lt_of_lt_of_le zero_lt_one hpos.2
  have hden : 0 < prefixD n^50 := pow_pos hD0 _
  have hκ0 : 0 ≤ prefixTemplateFactor n C := by unfold prefixTemplateFactor; positivity
  have hsmall : (n : ℝ)^(-c) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (neg_nonpos.mpr hc.le)
  by_cases hs : s < 100
  · have hcap : (A.pathUnion a b).card ≤ prefixTemplateCap := by
      rw [hcard]
      unfold prefixTemplateCap
      omega
    have h := A.actual_short_witness_count hGood a b hR hseed he hcap hpos.1.le
      (prefixDensity_le_one n) hpos.2
    change _ ≤ prefixTemplateFactor n C * ((2*prefixM n)^r * prefixD n^s * prefixDensity n) at h
    have hbase : (2*prefixM n)^r * prefixD n^s ≤ (4*prefixM n)^r * (2*prefixD n)^s :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) (by nlinarith) r)
        (pow_le_pow_left₀ hD0.le (by linarith) s) (by positivity) (by positivity)
    calc
      _ ≤ prefixTemplateFactor n C * ((2*prefixM n)^r * prefixD n^s * prefixDensity n) := h
      _ = (prefixTemplateFactor n C * prefixDensity n) * ((2*prefixM n)^r * prefixD n^s) := by ring
      _ ≤ (prefixD n^50)⁻¹ * ((4*prefixM n)^r * (2*prefixD n)^s) :=
        mul_le_mul hshort hbase (by positivity) (by positivity)
      _ = _ := by rw [div_eq_mul_inv]; ring
  · have hs100 : 100 ≤ s := Nat.le_of_not_gt hs
    let k := 2*r+(s-100)
    have hkr : 2*r ≤ k := by dsimp [k]; omega
    have hk : k < (A.pathUnion a b).card := by rw [hcard]; dsimp [k]; omega
    have hdiff : (A.pathUnion a b).card-k = 100 := by rw [hcard]; dsimp [k]; omega
    have hscale' : (n : ℝ)^((A.pathUnion a b).card-k) *
        prefixDensity n^(2*((A.pathUnion a b).card-k)+1) ≤ 1 := by
      simpa only [hdiff] using hscale
    have h := A.actual_long_witness_count hGood hsmall a b hR hseed he k hkr hk
      (by rw [hdiff]; norm_num [prefixTemplateCap]) hpos.1.le (prefixDensity_le_one n) hpos.2 hscale'
    have hks : k-2*r = s-100 := by dsimp [k]; omega
    rw [hks] at h
    calc
      _ ≤ prefixTemplateFactor n C * ((4*prefixM n)^r * (2*prefixD n)^(s-100)) := h
      _ ≤ ((2*prefixD n)^100 / prefixD n^50) * ((4*prefixM n)^r * (2*prefixD n)^(s-100)) :=
        mul_le_mul_of_nonneg_right hlong (by positivity)
      _ = _ := by
        have hp : (2*prefixD n)^100 * (2*prefixD n)^(s-100) = (2*prefixD n)^s := by
          rw [← pow_add,Nat.add_sub_of_le hs100]
        rw [div_mul_eq_mul_div]
        congr 1
        calc
          _ = (4*prefixM n)^r * ((2*prefixD n)^100 * (2*prefixD n)^(s-100)) := by ring
          _ = _ := by rw [hp]

end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Embeddings_WitnessEmbeddingBound
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma actual_witness_count_roots_eventually (c C : ℝ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : Graph n), GoodPrefixGraph n c C G →
    ∀ r : ℕ, r ≤ 2 → ∀ N R : ℕ, ∀ (A : TriangleGrowth (lookupGraph G) N R),
      R ≤ N → R = 2*r → (A.seed.backEdges A.roots).card = r →
    ∀ a b : Fin N, A.birthGraph.ExtraEdge (lookupGraph G) A.label a b →
    ((graphEmbeddingSet (insert ({A.pathIndex a b a (A.left_mem_pathUnion a b),
      A.pathIndex a b b (A.right_mem_pathUnion a b)} : Finset _)
      ((A.pathPattern a b).backEdges Finset.univ)) G).card : ℝ) ≤
      (4*prefixM n)^r * (2*prefixD n)^(A.pathSuffix a b R).card / prefixD n^50 := by
  filter_upwards [actual_witness_count_eventually c C hc] with n hn
  intro G hG r hr N R A hR hRr hseed a b he
  subst R
  exact hn G hG r hr N A hR hseed a b he

end SharpTerminalLeave

open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Probability_UniformDistinctRootSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave
section RootAverage
variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]

lemma uniform_distinct_root_set_probability_le (G : Finset α) (hne : G.Nonempty)
    (E : Finset α) :
    pmfMean (PMF.uniformOfFinset G hne) (fun x =>
      pmfMean (PMF.uniformOfFinset G hne) (fun y =>
        if x ≠ y ∧ ({x,y} : Finset α) = E then 1 else 0)) ≤
      2/(G.card : ℝ)^2 := by
  by_cases hE : E.card = 2
  · apply le_trans _ (uniform_root_set_probability_le G hne E hE)
    apply pmfMean_mono
    intro x _
    apply pmfMean_mono
    intro y _
    by_cases h : x ≠ y ∧ ({x,y} : Finset α) = E
    · simp [h]
    · simp only [h,ite_false]
      split_ifs <;> norm_num
  · have hz (x y : α) : ¬ (x ≠ y ∧ ({x,y} : Finset α) = E) := by
      rintro ⟨hxy,h⟩
      apply hE
      rw [← h,Finset.card_pair hxy]
    simp only [hz,ite_false,pmfMean_const]
    positivity

theorem uniform_two_root_weighted_sum (G : Finset α) (hne : G.Nonempty)
    (roots : ι → Finset α) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    pmfMean (PMF.uniformOfFinset G hne) (fun x =>
      pmfMean (PMF.uniformOfFinset G hne) (fun y =>
        ∑ i, if x ≠ y ∧ roots i = ({x,y} : Finset α) then w i else 0)) ≤
      (2/(G.card : ℝ)^2) * ∑ i, w i := by
  let p := PMF.uniformOfFinset G hne
  have hpt (x y : α) (i : ι) :
      (if x ≠ y ∧ roots i = ({x,y} : Finset α) then w i else 0) =
        (if x ≠ y ∧ ({x,y} : Finset α) = roots i then 1 else 0)*w i := by
    simp only [eq_comm (a := roots i)]
    split_ifs <;> simp
  simp_rw [hpt,pmfMean_sum,pmfMean_mul_const]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_right (uniform_distinct_root_set_probability_le G hne (roots i)) (hw i)

end RootAverage
end SharpTerminalLeave

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_IndexedWitnessCodeCard
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedCountedTracedRepeatIndexedWitnessCodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

lemma indexedWitnessCode_card_bound {K s : ℕ} (E : Graph K) (birth : Fin s → Fin K)
    (hE : E.card ≤ 2) (mark : Fin K → Option (Fin s)) :
    Fintype.card (IndexedWitnessCode E birth mark) ≤ K^2*6^s := by
  simpa only [Fintype.card_fin] using all_marked_indexed_attachment_pattern_count E birth hE mark

lemma boundedEmbeddedWitness_weight_sum {n R d : ℕ} (G : Graph n) (r : ℕ)
    (hR : R ≤ 4) (hm : 0 ≤ prefixM n) (v : WitnessDimensions R d → ℝ)
    (hv : ∀ q, 0 ≤ v q) :
    (∑ W : BoundedEmbeddedWitness G R d, if WitnessEmbeddingBound r W then v W.1 else 0) ≤
      ∑ q : WitnessDimensions R d,
        64*(q.val.1.val^2*6^q.val.2.val : ℕ) *
          ((4*prefixM n)^r*(2*prefixD n)^q.val.2.val/prefixD n^50)*v q := by
  classical
  have hD : 0 ≤ prefixD n := by unfold prefixD; positivity
  let B (q : WitnessDimensions R d) :=
    (4*prefixM n)^r*(2*prefixD n)^q.val.2.val/prefixD n^50
  have hB (q : WitnessDimensions R d) : 0 ≤ B q := by dsimp only [B]; positivity
  rw [Fintype.sum_sigma]
  apply Finset.sum_le_sum
  intro q _
  rw [Fintype.sum_sigma]
  have hqR : R ≤ q.val.1.val := by have h := q.property; omega
  calc
    _ ≤ ∑ E : {E : Graph q.val.1 // E ∈ seedPatternChoices q.val.1 R},
        (q.val.1.val^2*6^q.val.2.val : ℕ)*B q*v q := by
      apply Finset.sum_le_sum
      intro E _
      let Code := IndexedWitnessCode E.val (dimensionBirth q) (suffixProjection q.property)
      have hc := indexedWitnessCode_card_bound E.val (dimensionBirth q)
        (Finset.mem_filter.mp E.property).2 (suffixProjection q.property)
      rw [Fintype.sum_sigma]
      calc
        _ ≤ ∑ _w : Code, B q*v q := by
          apply Finset.sum_le_sum
          intro w _
          change (∑ _ψ : {ψ : Fin q.val.1 ↪ Fin n //
            ψ ∈ graphEmbeddingSet (decodeWitnessPattern w).2 G},
            if ((graphEmbeddingSet (decodeWitnessPattern w).2 G).card : ℝ) ≤ B q
              then v q else 0) ≤ B q*v q
          by_cases hh : ((graphEmbeddingSet (decodeWitnessPattern w).2 G).card : ℝ) ≤ B q
          · simp only [hh,ite_true,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
            exact mul_le_mul_of_nonneg_right hh (hv q)
          · simp only [hh,ite_false,Finset.sum_const_zero]
            exact mul_nonneg (hB q) (hv q)
        _ = (Fintype.card Code : ℝ)*B q*v q := by
          simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc]
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (hB q)) (hv q)
    _ = (seedPatternChoices q.val.1 R).card *
        ((q.val.1.val^2*6^q.val.2.val : ℕ)*B q*v q) := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
    _ ≤ 64*((q.val.1.val^2*6^q.val.2.val : ℕ)*B q*v q) := by
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (seedPatternChoices_card hqR hR))
        (mul_nonneg (mul_nonneg (by positivity) (hB q)) (hv q))
    _ = _ := by dsimp only [B]; ring

end SharpTerminalLeave

open scoped BigOperators Topology
open Filter

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_WitnessDimensionEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

lemma witness_dimensions_sum {R d : ℕ} (f : ℕ → ℝ) :
    (∑ q : WitnessDimensions R d, f q.val.2.val) =
      ∑ s ∈ Finset.range (2*d+1), f s := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Fintype.sum_equiv (witnessDimensionEquiv R d) _ _ (fun _ => rfl)

lemma finite_exp_series_le {x : ℝ} (hx : 0 ≤ x) (L : ℕ) :
    (∑ s ∈ Finset.range L, x^s/(s.factorial : ℝ)) ≤ Real.exp x := by
  exact sum_le_hasSum _ (fun s _ => by positivity) (witness_exp_series x)

theorem witness_dimensions_weight_sum {R d r : ℕ} {m D C x : ℝ}
    (hR : R ≤ 4) (hm : 0 ≤ m) (hD : 0 ≤ D) (hC : 0 ≤ C) (hx : 0 ≤ x) :
    (∑ q : WitnessDimensions R d,
      64*(q.val.1.val^2*6^q.val.2.val : ℕ)*
        ((4*m)^r*(2*D)^q.val.2.val/D^50)*
          (C^3*((3*x)^q.val.2.val/(q.val.2.val.factorial : ℝ)))) ≤
      (2048*(4*m)^r*C^3/D^50)*Real.exp (45*D*x) := by
  have hnon : 0 ≤ (2048*(4*m)^r*C^3/D^50) := by positivity
  calc
    _ ≤ ∑ q : WitnessDimensions R d,
        (2048*(4*m)^r*C^3/D^50)*((45*D*x)^q.val.2.val/(q.val.2.val.factorial : ℝ)) := by
      apply Finset.sum_le_sum
      intro q _
      have hmark := pattern_marks_exponential (s := q.val.2.val) hR
      rw [← q.property] at hmark
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmark (by norm_num : (0 : ℝ) ≤ 64))
          (show 0 ≤ (4*m)^r*(2*D)^q.val.2.val/D^50 by positivity))
        (show 0 ≤ C^3*((3*x)^q.val.2.val/(q.val.2.val.factorial : ℝ)) by positivity)
      apply hh.trans_eq
      have hp : (15/2 : ℝ)^q.val.2.val*(2*D)^q.val.2.val*(3*x)^q.val.2.val =
          (45*D*x)^q.val.2.val := by
        rw [← mul_pow,← mul_pow]
        congr 1
        ring
      calc
        _ = (2048*(4*m)^r*C^3/D^50)*
            (((15/2 : ℝ)^q.val.2.val*(2*D)^q.val.2.val*(3*x)^q.val.2.val)/
              (q.val.2.val.factorial : ℝ)) := by ring
        _ = _ := by rw [hp]
    _ = (2048*(4*m)^r*C^3/D^50)*
        (∑ s ∈ Finset.range (2*d+1), (45*D*x)^s/(s.factorial : ℝ)) := by
      rw [← Finset.mul_sum, witness_dimensions_sum (R := R) (d := d)
        (fun s => (45*D*x)^s/(s.factorial : ℝ))]
    _ ≤ _ := mul_le_mul_of_nonneg_left (finite_exp_series_le (by positivity) _) hnon

end SharpTerminalLeave

open Filter
open scoped BigOperators Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Tracking_RootedCountedTracedRepeat
attribute [-instance] _root_.OAI.SharpTerminalLeave.canonicalCollisionSumIndexedWitnessCodeFintype _root_.OAI.SharpTerminalLeave.indexedWitnessCodeAddressFintype _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave

theorem rooted_counted_traced_repeat_cover (c₀ C₀ : ℝ) (hc₀ : 0 < c₀) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : Graph n), GoodPrefixGraph n c₀ C₀ G →
    ∀ (focus : Graph n)
    (parent : Option (Finset (Fin n))) (_hM : EdgeMatching focus) (_hG : focus ⊆ G)
    (_hr : focus.card ≤ 2)
    (_hc : (QueryCall.mk [] focus parent).Separated (triangleHypergraph G))
    (N d k : ℕ) (ν : Finset (Fin n) → PMF (Fin N))
    (z : (Bool × List (QueryCall (Finset (Fin n)) (Finset (Fin n)))) × List (Finset (Fin n)))
    (_hz : z ∈ (ExposureTree.freshLog ν
      (tracedGridQuery (triangleHypergraph G) N d k ⟨[],focus,parent⟩)).support)
    (_hrep : ExposureTree.repeats ∅ z.2 = true),
    ∃ W : BoundedEmbeddedWitness G (focus.biUnion id).card d,
      WitnessEmbeddingBound focus.card W ∧ embeddedWitnessRoots W = focus ∧
      (∃ a ∈ z.1.2, a.address = (embeddedWitnessPaths W).1.reverse) ∧
      (∃ b ∈ z.1.2, b.address = (embeddedWitnessPaths W).2.reverse) := by
  classical
  filter_upwards [actual_witness_count_roots_eventually c₀ C₀ hc₀] with n hn
  intro G hGood focus parent hM hG hr hc N d k ν z hz hrep
  let c : QueryCall (Finset (Fin n)) (Finset (Fin n)) := ⟨[],focus,parent⟩
  let F := extractCallForest (triangleHypergraph G) N d k c ν z hz
  let A := F.toTriangleGrowth hM hG
  have hR : F.rootCount ≤ F.vertexCount := Nat.le_add_right _ _
  obtain ⟨a,b,he,hi⟩ := traced_graph_path_collision_witness G N d k c hM hG hc ν z hz hrep
  have hdepth (i : Fin F.size) : (F.call i).address.length ≤ d := by
    obtain ⟨p,hp,he⟩ := tracedGridQuery_legal_path (triangleHypergraph G) N d k c ν hz
      (F.call i) (List.get_mem z.1.2 i)
    rw [he,callAtPath_address]
    simpa only [c,List.append_nil,List.length_reverse] using
      (mem_legalPaths (triangleHypergraph G) d focus parent p).mp hp |>.2
  let key := indexedTriangleKey (A.pathBirthIndex a b hR) (A.pathAttachments a b hR)
    (A.pathAssignment a b hi)
  have hs : (A.pathSuffix a b F.rootCount).card ≤ 2*d := by
    have h := (A.pathForest a b).two_mark_size key
      (suffixProjection (A.path_card_split a b hR) (A.pathIndex a b a (A.left_mem_pathUnion a b)))
      (suffixProjection (A.path_card_split a b hR) (A.pathIndex a b b (A.right_mem_pathUnion a b)))
      (A.pathWitnessCode a b hR).2.1.property
    rw [F.decoded_mark_address hM hG rfl a b hR hi a (A.left_mem_pathUnion a b),
      F.decoded_mark_address hM hG rfl a b hR hi b (A.right_mem_pathUnion a b)] at h
    have ha := hdepth (F.vertexCall a)
    have hb := hdepth (F.vertexCall b)
    omega
  let q : WitnessDimensions F.rootCount d :=
    ⟨(⟨(A.pathUnion a b).card,by rw [A.path_card_split a b hR]; omega⟩,
      ⟨(A.pathSuffix a b F.rootCount).card,by omega⟩),A.path_card_split a b hR⟩
  have hseed : (A.seed.backEdges A.roots).card ≤ 2 := by
    rw [F.growth_seed_card hM hG]
    exact hr
  let E : {E : Graph (A.pathUnion a b).card // E ∈ seedPatternChoices (A.pathUnion a b).card F.rootCount} :=
    ⟨A.pathRootEdges a b,A.pathRootEdges_mem_seedPatternChoices a b hR hseed⟩
  let W : BoundedEmbeddedWitness G F.rootCount d :=
    ⟨q,E,A.pathWitnessCode a b hR,A.pathAssignment a b hi,A.pathAssignment_mem_decoded hR hi he⟩
  have hleft : (embeddedWitnessPaths W).1.reverse = (F.call (F.vertexCall a)).address := by
    change (((suffixProjection (A.path_card_split a b hR)
      (A.pathIndex a b a (A.left_mem_pathUnion a b))).elim []
      ((A.pathForest a b).address key)).reverse).reverse = _
    rw [List.reverse_reverse]
    exact F.decoded_mark_address hM hG rfl a b hR hi a (A.left_mem_pathUnion a b)
  have hright : (embeddedWitnessPaths W).2.reverse = (F.call (F.vertexCall b)).address := by
    change (((suffixProjection (A.path_card_split a b hR)
      (A.pathIndex a b b (A.right_mem_pathUnion a b))).elim []
      ((A.pathForest a b).address key)).reverse).reverse = _
    rw [List.reverse_reverse]
    exact F.decoded_mark_address hM hG rfl a b hR hi b (A.right_mem_pathUnion a b)
  have hbound : WitnessEmbeddingBound focus.card W := by
    have hh := hn G hGood focus.card hr F.vertexCount F.rootCount A hR
      (F.rootCount_focus_card hM) (F.growth_seed_card hM hG) a b he
    change ((graphEmbeddingSet (decodeWitnessPattern (A.pathWitnessCode a b hR)).2 G).card : ℝ) ≤
      (4*prefixM n)^focus.card*(2*prefixD n)^(A.pathSuffix a b F.rootCount).card/prefixD n^50
    change ((graphEmbeddingSet (insert {A.pathIndex a b a (A.left_mem_pathUnion a b),
      A.pathIndex a b b (A.right_mem_pathUnion a b)}
      (indexedPatternEdges (A.pathRootEdges a b) (A.pathBirthIndex a b hR)
        (A.pathAttachments a b hR))) G).card : ℝ) ≤ _
    rw [← A.pathPattern_edges a b hR]
    exact hh
  have hroots : embeddedWitnessRoots W = focus := by
    change (A.pathRootEdges a b).image (Finset.image (A.pathAssignment a b hi)) = c.focus
    exact (A.pathRootEdges_image a b hi).trans (F.growth_seed_image hM hG)
  exact ⟨W,hbound,hroots,⟨F.call (F.vertexCall a),List.get_mem z.1.2 _,hleft.symm⟩,
    ⟨F.call (F.vertexCall b),List.get_mem z.1.2 _,hright.symm⟩⟩

end SharpTerminalLeave

open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Queries_CanonicalCollisionSum
attribute [-instance] _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

theorem canonical_collision_sum (c₀ C₀ : ℝ) (hc₀ : 0 < c₀) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : Graph n), GoodPrefixGraph n c₀ C₀ G →
    ∀ (focus : Graph n) (parent : Option (Finset (Fin n)))
    (_hM : EdgeMatching focus) (_hG : focus ⊆ G) (_hr : focus.card ≤ 2)
    (_hc : (QueryCall.mk [] focus parent).Separated (triangleHypergraph G))
    (N : ℕ) [NeZero N] (b : ℕ → ℝ) (_hb : ∀ t, 0 ≤ b t)
    (_hq : GridRowQuality (triangleHypergraph G) N b)
    (C : ℝ) (_hC : 1 ≤ C) (_hlower : ∀ t ≤ N, 1 ≤ C*b t)
    (d k : ℕ) (_hkd : k ≤ d) (_hkN : k ≤ N),
    tracedCollisionProbability (triangleHypergraph G) N d k focus parent ≤
      ∑ W : BoundedEmbeddedWitness G (focus.biUnion id).card d,
        if WitnessEmbeddingBound focus.card W ∧ embeddedWitnessRoots W = focus then
          C^3 * ((3*prefixWeight (fun t => (2/(N : ℝ))*b t) k)^W.1.val.2.val /
            (W.1.val.2.val.factorial : ℝ)) else 0 := by
  classical
  filter_upwards [rooted_counted_traced_repeat_cover c₀ C₀ hc₀] with n hn
  intro G hGood focus parent hM hG hr hc N _ b hb hq C hC hlower d k hkd hkN
  let H := triangleHypergraph G
  let P := ExposureTree.freshLog (gridPriorities N)
    (tracedGridQuery H N d k ⟨[],focus,parent⟩)
  let S : Finset (BoundedEmbeddedWitness G (focus.biUnion id).card d) :=
    Finset.univ.filter (fun W => WitnessEmbeddingBound focus.card W ∧ embeddedWitnessRoots W = focus)
  let ev := fun (W : BoundedEmbeddedWitness G (focus.biUnion id).card d)
      (z : (Bool × List (QueryCall (Finset (Fin n)) (Finset (Fin n)))) × List (Finset (Fin n))) =>
    z.1.2.any (fun a => decide (a.address = (embeddedWitnessPaths W).1.reverse)) &&
      z.1.2.any (fun a => decide (a.address = (embeddedWitnessPaths W).2.reverse))
  have hcov : ∀ z ∈ P.support, ExposureTree.repeats ∅ z.2 = true →
      ∃ W ∈ S, ev W z = true := by
    intro z hz hzrep
    obtain ⟨W,hW,hroots,⟨a,ha,hae⟩,⟨b,hb',hbe⟩⟩ :=
      hn G hGood focus parent hM hG hr hc N d k (gridPriorities N) z hz hzrep
    refine ⟨W,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hW,hroots⟩,?_⟩
    apply Bool.and_eq_true_iff.mpr
    exact ⟨List.any_eq_true.mpr ⟨a,ha,decide_eq_true hae⟩,
      List.any_eq_true.mpr ⟨b,hb',decide_eq_true hbe⟩⟩
  have hh := pmf_boolean_finite_cover P S (fun z => ExposureTree.repeats ∅ z.2) ev hcov
  change tracedCollisionProbability H N d k focus parent ≤ _ at hh
  apply hh.trans
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum
  intro W _
  change (((ExposureTree.freshLog (gridPriorities N)
    (tracedGridQuery H N d k ⟨[],focus,parent⟩)).map (fun z =>
      z.1.2.any (fun a => decide (a.address = (embeddedWitnessPaths W).1.reverse)) &&
      z.1.2.any (fun a => decide (a.address = (embeddedWitnessPaths W).2.reverse)))) true).toReal ≤ _
  rw [log_pair_probability]
  apply (actualPairVisitProbability_weight_any H N b hb hq C hC hlower
    d k hkd hkN focus parent (embeddedWitnessPaths W).1 (embeddedWitnessPaths W).2).trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith) _)
  apply embeddedWitness_factorial_weight W
  apply Finset.sum_nonneg
  intro t _
  exact mul_nonneg (by positivity) (hb t)

end SharpTerminalLeave

open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Tr.TriangleRemoval_Process_CardBiUnion
attribute [-instance] _root_.OAI.SharpTerminalLeave.linkSimpleGraph_decidable _root_.OAI.SharpTerminalLeave.rootedTemplateFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma EdgeMatching.card_biUnion {V : Type*} [DecidableEq V]
    {E : Finset (Finset V)} (h : EdgeMatching E) :
    (E.biUnion id).card = 2*E.card := by
  change (E.biUnion (fun e => e)).card = _
  rw [Finset.card_biUnion h.2]
  calc
    _ = ∑ _e ∈ E, 2 := Finset.sum_congr rfl (fun e he => h.1 e he)
    _ = _ := by simp only [Finset.sum_const,smul_eq_mul,Nat.mul_comm]

lemma disjoint_valid_edge_ne {n : ℕ} {e f : Finset (Fin n)}
    (he : e.card = 2) (hd : Disjoint e f) : e ≠ f := by
  rintro rfl
  have h : e = ∅ := disjoint_self.mp hd
  rw [h,Finset.card_empty] at he
  omega

theorem canonical_collision_pair_sum (c₀ C₀ : ℝ) (hc₀ : 0 < c₀) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : Graph n), GoodPrefixGraph n c₀ C₀ G →
    ∀ (e f : Finset (Fin n)), e ∈ G → f ∈ G → Disjoint e f →
    ∀ (N : ℕ) [NeZero N] (b : ℕ → ℝ) (_hb : ∀ t, 0 ≤ b t)
    (_hq : GridRowQuality (triangleHypergraph G) N b)
    (C : ℝ) (_hC : 1 ≤ C) (_hlower : ∀ t ≤ N, 1 ≤ C*b t)
    (d k : ℕ) (_hkd : k ≤ d) (_hkN : k ≤ N),
    tracedCollisionProbability (triangleHypergraph G) N d k {e,f} none ≤
      ∑ W : BoundedEmbeddedWitness G 4 d,
        if WitnessEmbeddingBound 2 W ∧ embeddedWitnessRoots W = {e,f} then
          C^3 * ((3*prefixWeight (fun t => (2/(N : ℝ))*b t) k)^W.1.val.2.val /
            (W.1.val.2.val.factorial : ℝ)) else 0 := by
  classical
  filter_upwards [canonical_collision_sum c₀ C₀ hc₀] with n hn
  intro G hGood e f he hf hd N _ b hb hq C hC hlower d k hkd hkN
  have he2 := mem_completeGraph.mp (hGood.1 he)
  have hf2 := mem_completeGraph.mp (hGood.1 hf)
  have hm := EdgeMatching.pair e f he2 hf2 hd
  have hef : e ≠ f := disjoint_valid_edge_ne he2 hd
  have hcard : ({e,f} : Graph n).card = 2 := Finset.card_pair hef
  have hbi : (({e,f} : Graph n).biUnion id).card = 4 := by
    rw [hm.card_biUnion,hcard]
  have hh := hn G hGood {e,f} none hm (by intro a ha; simp only [Finset.mem_insert,Finset.mem_singleton] at ha; rcases ha with rfl | rfl <;> assumption)
    (by rw [hcard]) (triangleHypergraph_separated_disjoint_roots G e f hd)
    N b hb hq C hC hlower d k hkd hkN
  rw [hbi] at hh
  simpa only [hcard] using hh

lemma witness_total_weight_bound {n R d r : ℕ} (G : Graph n) (hR : R ≤ 4)
    (hm : 0 ≤ prefixM n) {C x : ℝ} (hC : 0 ≤ C) (hx : 0 ≤ x) :
    (∑ W : BoundedEmbeddedWitness G R d, if WitnessEmbeddingBound r W then
      C^3*((3*x)^W.1.val.2.val/(W.1.val.2.val.factorial : ℝ)) else 0) ≤
      (2048*(4*prefixM n)^r*C^3/prefixD n^50)*Real.exp (45*prefixD n*x) := by
  have hD : 0 ≤ prefixD n := by unfold prefixD; positivity
  apply (boundedEmbeddedWitness_weight_sum G r hR hm
    (fun q => C^3*((3*x)^q.val.2.val/(q.val.2.val.factorial : ℝ)))
    (fun _ => by positivity)).trans
  exact witness_dimensions_weight_sum hR hm hD hC hx

theorem averaged_disjoint_grid_collision_oai (c₀ C₀ : ℝ) (hc₀ : 0 < c₀) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : Graph n), GoodPrefixGraph n c₀ C₀ G →
    ∀ (hne : G.Nonempty) (N : ℕ) [NeZero N]
    (b : ℕ → ℝ) (_hb : ∀ t, 0 ≤ b t) (_hq : GridRowQuality (triangleHypergraph G) N b)
    (C : ℝ) (_hC : 1 ≤ C) (_hlower : ∀ t ≤ N, 1 ≤ C*b t)
    (d k : ℕ) (_hkd : k ≤ d) (_hkN : k ≤ N),
    pmfMean (PMF.uniformOfFinset G hne) (fun e =>
      pmfMean (PMF.uniformOfFinset G hne) (fun f => if Disjoint e f then
        tracedCollisionProbability (triangleHypergraph G) N d k {e,f} none else 0)) ≤
      (65536*C^3/prefixD n^50)*
        Real.exp (45*prefixD n*prefixWeight (fun t => (2/(N : ℝ))*b t) k) := by
  classical
  filter_upwards [canonical_collision_pair_sum c₀ C₀ hc₀] with n hn
  intro G hGood hne N _ b hb hq C hC hlower d k hkd hkN
  let x := prefixWeight (fun t => (2/(N : ℝ))*b t) k
  have hx : 0 ≤ x := by
    apply Finset.sum_nonneg
    intro t _
    exact mul_nonneg (by positivity) (hb t)
  let w (W : BoundedEmbeddedWitness G 4 d) : ℝ :=
    if WitnessEmbeddingBound 2 W then C^3*((3*x)^W.1.val.2.val/(W.1.val.2.val.factorial : ℝ)) else 0
  have hw (W : BoundedEmbeddedWitness G 4 d) : 0 ≤ w W := by
    dsimp only [w]
    split_ifs <;> positivity
  have hcover : pmfMean (PMF.uniformOfFinset G hne) (fun e =>
      pmfMean (PMF.uniformOfFinset G hne) (fun f => if Disjoint e f then
        tracedCollisionProbability (triangleHypergraph G) N d k {e,f} none else 0)) ≤
      pmfMean (PMF.uniformOfFinset G hne) (fun e =>
      pmfMean (PMF.uniformOfFinset G hne) (fun f =>
        ∑ W : BoundedEmbeddedWitness G 4 d,
          if e ≠ f ∧ embeddedWitnessRoots W = {e,f} then w W else 0)) := by
    apply pmfMean_mono
    intro e he
    apply pmfMean_mono
    intro f hf
    have heG := (PMF.mem_support_uniformOfFinset_iff hne e).mp he
    have hfG := (PMF.mem_support_uniformOfFinset_iff hne f).mp hf
    by_cases hd : Disjoint e f
    · rw [ite_eq_left hd]
      have hef : e ≠ f := disjoint_valid_edge_ne (mem_completeGraph.mp (hGood.1 heG)) hd
      have hh := hn G hGood e f heG hfG hd N b hb hq C hC hlower d k hkd hkN
      apply hh.trans_eq
      apply Finset.sum_congr rfl
      intro W _
      by_cases hW : WitnessEmbeddingBound 2 W <;>
        by_cases hroot : embeddedWitnessRoots W = {e,f} <;>
          simp [w,x,hef,hW,hroot]
    · rw [ite_eq_right hd]
      apply Finset.sum_nonneg
      intro W _
      split_ifs <;> first | exact hw W | rfl
  have hsample := uniform_two_root_weighted_sum G hne embeddedWitnessRoots w hw
  have hm : 0 ≤ prefixM n := by rw [← hGood.2.1]; positivity
  have hmpos : 0 < prefixM n := by rw [← hGood.2.1]; exact_mod_cast hne.card_pos
  have hsum := witness_total_weight_bound (d := d) (r := 2) G (by norm_num : 4 ≤ 4) hm
    (show 0 ≤ C by linarith) hx
  apply (hcover.trans hsample).trans
  change (2/(G.card : ℝ)^2)*(∑ W, w W) ≤ _
  apply (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 2/(G.card : ℝ)^2)).trans_eq
  rw [hGood.2.1]
  dsimp only [x]
  field_simp [ne_of_gt hmpos]
  ring

end SharpTerminalLeave

end

end OAI
end

theorem solution : type_of% @OAI.SharpTerminalLeave.averaged_disjoint_grid_collision_oai := @OAI.SharpTerminalLeave.averaged_disjoint_grid_collision_oai
