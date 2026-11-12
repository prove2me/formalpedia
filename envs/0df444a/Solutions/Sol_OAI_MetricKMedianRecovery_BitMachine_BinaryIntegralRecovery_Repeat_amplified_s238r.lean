-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.amplified_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:49:46.104558+00:00
-- url     : https://prove2.me/submissions/d1130260-85ad-4400-8399-69de980bc563

import Mathlib
import Definitions.Def_Q238L012
import Definitions.Def_Q238L030
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBranchProgram_result_guarantee_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_FiniteSampling_average_le_threshold_add_failure_s238r

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Average
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
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

lemma average_le [Nonempty Ω] {X : Ω → ℝ} {c : ℝ} (h : ∀ ω, X ω ≤ c) :
    average X ≤ c := Finset.expect_le Finset.univ_nonempty (fun ω _ => h ω)

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

end Average

section Probability
variable {Ω : Type*} [Fintype Ω]

lemma probability_le_one [Nonempty Ω] (P : Ω → Prop) : probability P ≤ 1 := by
  classical
  apply average_le
  intro ω
  split_ifs <;> norm_num

lemma probability_mono {P Q : Ω → Prop} (h : ∀ ω, P ω → Q ω) :
    probability P ≤ probability Q := by
  classical
  apply average_mono
  intro ω
  split_ifs with hp hq hq <;> try norm_num
  exact absurd (h ω hp) hq

lemma probability_compl [Nonempty Ω] (P : Ω → Prop) :
    probability (fun ω => ¬P ω) = 1 - probability P := by
  classical
  unfold probability
  rw [average_congr (Y := fun ω => 1 - if P ω then 1 else 0) (by
    intro ω
    by_cases hp : P ω <;> simp [hp]), average_sub, average_const]

lemma probability_congr {P Q : Ω → Prop} (h : ∀ ω, P ω ↔ Q ω) :
    probability P = probability Q := by
  classical
  apply average_congr
  intro ω
  simp only [h ω]

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Basic
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic
namespace RationalMin
open WordList

lemma fold_lower (qs : List ℚ) (a u : ℚ) (ha : u≤a) (hq : ∀ q∈qs,u≤q) : u≤qs.foldl min a := by
  induction qs generalizing a with
  | nil=>exact ha
  | cons q qs ih=>
    rw [List.foldl_cons]
    exact ih (min a q) (le_min ha (hq q (by simp))) (by intro r hr; exact hq r (by simp [hr]))
lemma fold_le_init (qs : List ℚ) (a : ℚ) : qs.foldl min a≤a := by
  induction qs generalizing a with
  | nil=>exact le_rfl
  | cons q qs ih=>exact (ih (min a q)).trans (min_le_left a q)
lemma fold_le_mem (qs : List ℚ) (a q : ℚ) (hq : q∈qs) : qs.foldl min a≤q := by
  induction qs generalizing a with
  | nil=>simp only [List.not_mem_nil] at hq
  | cons r rs ih=>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hq with rfl|hq
    · exact (fold_le_init rs (min a q)).trans (min_le_right a q)
    · exact ih (min a r) hq
lemma minimum_lower (qs : List ℚ) (u : ℚ) (hne : qs≠[]) (hu : ∀q∈qs,u≤q) : u ≤ minimum qs := by
  cases qs with
  | nil=>exact (hne rfl).elim
  | cons q qs=>
    apply fold_lower
    · exact hu q (by simp)
    · exact hu
lemma minimum_le_mem (qs : List ℚ) (q : ℚ) (hq : q∈qs) : minimum qs≤q := fold_le_mem qs _ q hq
end RationalMin
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Virtual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion

variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

omit [DecidableEq V] in
lemma distanceTo_nonneg (S : Finset V) (hS : S.Nonempty) (x : V) :
    0 ≤ distanceTo S hS x := Finset.le_inf' hS _ (fun _ _ => dist_nonneg)

omit [DecidableEq V] in
lemma distanceTo_le {S : Finset V} (hS : S.Nonempty) (x : V) {s : V} (hs : s ∈ S) :
    distanceTo S hS x ≤ dist x s := Finset.inf'_le _ hs

end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricArrays
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.SortedIndex
variable {α : Type*} [LinearOrder α]
lemma map_enum {β : Type*} (S : Finset α) (f : α→β) :
    (S.sort (·≤·)).map f=List.ofFn (fun i=>f (enum S i)) := by rw [←enum_list,List.map_ofFn]; rfl
end MetricKMedianRecovery.SortedIndex

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BestFallback
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.FiniteSampling
variable {Ω Y : Type*} [Fintype Ω] [Nonempty Ω]

lemma probability_all_fin (P : Ω → Prop) (n : ℕ) :
    probability (fun s : Fin n → Ω => ∀ i, P (s i)) = (probability P)^n := by
  classical
  induction n with
  | zero => simp [probability,average_const]
  | succ n ih =>
    unfold probability
    rw [average_fin_succ]
    have he (x : Ω) :
        probability (fun s : Fin n → Ω =>
          ∀ i, P ((Fin.cons x s : Fin (n+1) → Ω) i)) =
        (if P x then (1:ℝ) else 0) * probability (fun s : Fin n → Ω => ∀ i, P (s i)) := by
      unfold probability
      rw [← average_const_mul]
      apply average_congr
      intro s
      simp only [Fin.forall_fin_succ,Fin.cons_zero,Fin.cons_succ]
      split_ifs <;> simp_all
    change average (fun x => probability (fun s : Fin n → Ω =>
      ∀ i, P ((Fin.cons x s : Fin (n+1) → Ω) i))) = _
    rw [average_congr he,average_mul_const,ih,pow_succ']
    rfl

omit [Fintype Ω] [Nonempty Ω] in
lemma bestWithFallback_mem [DecidableEq Y] (cost : Y → ℝ) (fallback : Y)
    (trial : Ω → Y) (n : ℕ) (s : Fin n → Ω) :
    bestWithFallback cost fallback trial n s = fallback ∨
      ∃ i, bestWithFallback cost fallback trial n s = trial (s i) := by
  classical
  have hh := (Classical.choose_spec (Finset.exists_min_image
    (insert fallback (Finset.univ.image (fun i => trial (s i)))) cost
    (Finset.insert_nonempty _ _))).1
  rcases Finset.mem_insert.mp hh with h | h
  · exact Or.inl h
  · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp h
    exact Or.inr ⟨i,hi.symm⟩

omit [Fintype Ω] [Nonempty Ω] in
lemma bestWithFallback_le [DecidableEq Y] (cost : Y → ℝ) (fallback : Y)
    (trial : Ω → Y) (n : ℕ) (s : Fin n → Ω) :
    cost (bestWithFallback cost fallback trial n s) ≤ cost fallback ∧
    ∀ i, cost (bestWithFallback cost fallback trial n s) ≤ cost (trial (s i)) := by
  classical
  have hh := (Classical.choose_spec (Finset.exists_min_image
    (insert fallback (Finset.univ.image (fun i => trial (s i)))) cost
    (Finset.insert_nonempty _ _))).2
  exact ⟨hh _ (Finset.mem_insert_self _ _),fun i => hh _ (Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩))⟩

lemma bestWithFallback_failure [DecidableEq Y] (cost : Y → ℝ) (fallback : Y)
    (trial : Ω → Y) (n : ℕ) (B : ℝ) {p : ℝ}
    (hp : p ≤ probability (fun s => cost (trial s) ≤ B)) :
    probability (fun s : Fin n → Ω => B < cost (bestWithFallback cost fallback trial n s)) ≤
      (1-p)^n := by
  have hle : probability (fun s : Fin n → Ω => B < cost (bestWithFallback cost fallback trial n s)) ≤
      probability (fun s : Fin n → Ω => ∀ i, B < cost (trial (s i))) :=
    probability_mono (fun s hs i =>
      lt_of_lt_of_le hs ((bestWithFallback_le cost fallback trial n s).2 i))
  refine hle.trans ?_
  rw [probability_all_fin (fun s : Ω => B < cost (trial s)) n]
  have he : probability (fun s => B < cost (trial s)) =
      1 - probability (fun s => cost (trial s) ≤ B) := by
    rw [← probability_compl]
    exact probability_congr (fun _ => not_le.symm)
  rw [he]
  exact pow_le_pow_left₀ (sub_nonneg.mpr (probability_le_one _)) (by linarith :
    1 - probability (fun s => cost (trial s) ≤ B) ≤ 1-p) n

lemma exponential_failure_bound {p : ℝ} (hp1 : p ≤ 1) (n : ℕ) :
    (1-p)^n ≤ Real.exp (-p*(n:ℝ)) := by
  have hh : 1-p ≤ Real.exp (-p) := by linarith [Real.add_one_le_exp (-p)]
  have hp := pow_le_pow_left₀ (sub_nonneg.mpr hp1) hh n
  rw [← Real.exp_nat_mul] at hp
  simpa only [mul_comm (n:ℝ) (-p)] using hp

lemma repetition_count_suffices {p zeta : ℝ} (hp : 0 < p) (hzeta : 0 < zeta)
    (n : ℕ) (hn : Real.log (1/zeta)/p ≤ (n:ℝ)) :
    Real.exp (-p*(n:ℝ)) ≤ zeta := by
  have hn' : Real.log (1/zeta) ≤ (n:ℝ)*p := (div_le_iff₀ hp).mp hn
  have hl : Real.log (1/zeta) = - Real.log zeta := by simp
  rw [hl] at hn'
  calc
    Real.exp (-p*(n:ℝ)) ≤ Real.exp (Real.log zeta) := Real.exp_le_exp.mpr (by nlinarith)
    _ = zeta := Real.exp_log hzeta

theorem amplified_output [DecidableEq Y] (cost : Y → ℝ) (fallback : Y)
    (trial : Ω → Y) {B M p zeta : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hfall : cost fallback ≤ M) (hp : 0 < p)
    (hsuccess : p ≤ probability (fun s => cost (trial s) ≤ B))
    (hzeta : 0 < zeta) (n : ℕ) (hn : Real.log (1/zeta)/p ≤ (n:ℝ)) :
    (∀ s, cost (bestWithFallback cost fallback trial n s) ≤ M) ∧
    probability (fun s : Fin n → Ω => cost (bestWithFallback cost fallback trial n s) ≤ B)
      ≥ 1-zeta ∧
    average (fun s : Fin n → Ω => cost (bestWithFallback cost fallback trial n s)) ≤ B+M*zeta := by
  have hpoint (s : Fin n → Ω) := ((bestWithFallback_le cost fallback trial n s).1).trans hfall
  have hp1 : p ≤ 1 := hsuccess.trans (probability_le_one _)
  have hfail := (bestWithFallback_failure cost fallback trial n B hsuccess).trans
    ((exponential_failure_bound hp1 n).trans (repetition_count_suffices hp hzeta n hn))
  refine ⟨hpoint,?_,?_⟩
  · have he : probability (fun s : Fin n → Ω => B < cost (bestWithFallback cost fallback trial n s)) =
        1 - probability (fun s : Fin n → Ω => cost (bestWithFallback cost fallback trial n s) ≤ B) := by
      rw [← probability_compl]
      exact probability_congr (fun _ => not_le.symm)
    rw [he] at hfail
    linarith
  · exact (average_le_threshold_add_failure_s238r _ hB hpoint).trans
      (by nlinarith [mul_le_mul_of_nonneg_right hfail hM])

end MetricKMedianRecovery.FiniteSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CompletionFairCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.SortedIndex
variable {α β : Type*} [LinearOrder α] [AddCommMonoid β]
lemma sum_enum (S : Finset α) (f : α→β) : (∑ i:Fin S.card,f (enum S i))=∑ x∈S,f x := by
  rw [←List.sum_ofFn]
  change (List.ofFn (f ∘ enum S)).sum = _
  rw [←List.map_ofFn,enum_list,←List.sum_toFinset f (S.sort_nodup (·≤·)),Finset.sort_toFinset]
end MetricKMedianRecovery.SortedIndex

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchObjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryObservableBranch
open WordOperations WordList BinaryBranchContext BinaryBranchProgram
open BinaryOpeningPayment (field field_encode)
variable {n m : ℕ}
variable [PseudoMetricSpace (Fin n)]
lemma output_feasible (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty) (Δ : ℚ) (hΔ : 0≤Δ)
    (hbound : ∀ x,∀ f∈F,δ x f≤Δ) (s : RationalSampling.State n) (colors : Fin n→Fin 3)
    (label : Fin n→Fin m) (q c : ℕ) (r0 y0 : Fin n) (bits) :
    output δ D F S Δ s colors label q c r0 y0 bits⊆F ∧
      (output δ D F S Δ s colors label q c r0 y0 bits).card=S.card ∧
      (output δ D F S Δ s colors label q c r0 y0 bits).Nonempty := by
  classical
  unfold output
  split_ifs with hr
  · split
    · exact ⟨hSF,rfl,hS⟩
    · rename_i v xs hb
      let P:=BlueDP.makePlan _ _ _ _ _ r0 y0 v xs hb
      have hradius (i : Fin s.leaves.length) : 0≤ s.radius i := by
        change (0:ℝ)≤(s.leaves[i.val].2:ℝ)
        exact_mod_cast hr.2.2.1 _ (List.getElem_mem i.isLt)
      exact (result_guarantee_s238r δ hδ D F S hSF hS Δ hΔ hbound s hr.1 colors hr.2.1 hradius P.sel P.dst c q
        P.selected_injective (fun j=>(P.selection j).1) (fun j=>(P.selection j).2.2) P.destination_count hr.2.2.2.2 hr.2.2.2.1).1 bits
  · exact ⟨hSF,rfl,hS⟩
end MetricKMedianRecovery.BitMachine.BinaryObservableBranch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricCost2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricCost
open WordOperations WordList
variable {n : ℕ}
variable [PseudoMetricSpace (Fin n)]
lemma connection_cast (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (S : Finset (Fin n)) (hS : S.Nonempty) (x : Fin n) :
    (connection δ S x:ℝ)=Completion.distanceTo S hS x := by
  have he : List.ofFn (fun j:Fin S.card=>δ x (SortedIndex.enum S j))=(S.sort (·≤·)).map (δ x) :=
    (SortedIndex.map_enum S (δ x)).symm
  have hne : (S.sort (·≤·)).map (δ x)≠[] := by
    intro hem
    have hl:=congrArg List.length hem
    simp only [List.length_map,Finset.length_sort,List.length_nil] at hl
    exact hS.card_pos.ne' hl
  rw [connection,he]
  apply le_antisymm
  · apply Finset.le_inf'
    intro y hy
    rw [←hδ x y]
    exact_mod_cast RationalMin.minimum_le_mem ((S.sort (·≤·)).map (δ x)) (δ x y)
      (List.mem_map.mpr ⟨y,(Finset.mem_sort (·≤·)).mpr hy,rfl⟩)
  · obtain ⟨y,hy,hmin⟩:=Finset.exists_min_image S (δ x) hS
    have hh : δ x y≤RationalMin.minimum ((S.sort (·≤·)).map (δ x)) := by
      apply RationalMin.minimum_lower _ _ hne
      intro q hq
      obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hq
      exact hmin z ((Finset.mem_sort (·≤·)).mp hz)
    exact (Completion.distanceTo_le hS x hy).trans (hδ x y ▸ Rat.cast_le.mpr hh)
lemma cost_cast (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D S : Finset (Fin n)) (hS : S.Nonempty) :
    (cost δ D S:ℝ)=Completion.realCost D S := by
  simp only [cost,Rat.cast_sum,connection_cast δ hδ S hS,Completion.realCost,dite_eq_left hS]
  exact SortedIndex.sum_enum D (Completion.distanceTo S hS)
end MetricKMedianRecovery.BitMachine.BinaryMetricCost

namespace MetricKMedianRecovery.BitMachine.BinaryMetricBest
open WordOperations WordList
open BinaryOpeningPayment (field field_encode)
variable {n : ℕ}
lemma best_mem (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (xs : List (Finset (Fin n))) :
    best δ D S xs=S ∨ best δ D S xs∈xs := OrderedMaximum.mem _ _ _
lemma cost_le_self (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (xs : List (Finset (Fin n))) :
    BinaryMetricCost.cost δ D (best δ D S xs)≤BinaryMetricCost.cost δ D S := by
  exact neg_le_neg_iff.mp (OrderedMaximum.own_le (fun U=> -BinaryMetricCost.cost δ D U) S xs)
lemma cost_le_mem (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (xs : List (Finset (Fin n)))
    (U : Finset (Fin n)) (hU : U∈xs) :
    BinaryMetricCost.cost δ D (best δ D S xs)≤BinaryMetricCost.cost δ D U := by
  exact neg_le_neg_iff.mp (OrderedMaximum.score_le (fun U=> -BinaryMetricCost.cost δ D U) S xs U hU)
lemma best_property (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (xs : List (Finset (Fin n)))
    (P : Finset (Fin n)→Prop) (hS : P S) (hxs : ∀ U∈xs,P U) : P (best δ D S xs) := by
  rcases best_mem δ D S xs with h|h
  · rwa [h]
  · exact hxs _ h
variable [PseudoMetricSpace (Fin n)]
lemma realCost_le_mem (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D S : Finset (Fin n)) (hS : S.Nonempty) (xs : List (Finset (Fin n)))
    (hxs : ∀ U∈xs,U.Nonempty) (U : Finset (Fin n)) (hU : U∈xs) :
    Completion.realCost D (best δ D S xs)≤Completion.realCost D U := by
  rw [←BinaryMetricCost.cost_cast δ hδ D U (hxs U hU),
    ←BinaryMetricCost.cost_cast δ hδ D (best δ D S xs) (best_property δ D S xs Finset.Nonempty hS hxs)]
  exact_mod_cast cost_le_mem δ D S xs U hU
end MetricKMedianRecovery.BitMachine.BinaryMetricBest

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RecoveryCandidates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open WordOperations WordList BinaryBranchTape Completion FiniteSampling
variable {n m H : ℕ}
variable (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ)
  (s : RationalSampling.State n) (hn : n≤H) (hm : m≤H) (hH : 1≤H)
  (hp : s.leaves.length≤H) (r0 y0 : Fin n) (seed : Fin (tapeSize H)→Bool)
lemma candidates_property (P : Finset (Fin n)→Prop)
    (hz : ∀ q,P (zero δ D F S Δ s hn hH hp seed q))
    (hb : ∀ q c b,P (positive δ D F S Δ s hn hm hp r0 y0 seed q c b)) :
    ∀ U∈candidates δ D F S Δ s hn hm hH hp r0 y0 seed,P U := by
  intro U hU
  rcases List.mem_append.mp hU with hz'|hb'
  · obtain ⟨q,rfl⟩:=List.mem_ofFn.mp hz'
    exact hz q
  · obtain ⟨q,_,hq⟩:=List.mem_flatMap.mp hb'
    obtain ⟨c,_,hc⟩:=List.mem_flatMap.mp hq
    obtain ⟨b,rfl⟩:=List.mem_ofFn.mp hc
    exact hb q c b
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_DesignatedBranchSuccess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryZeroBranch
open Completion Categorical FiniteSampling BinaryBranchContext Sampling BinaryBranchProgram
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
lemma output_feasible (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty) (Δ : ℚ) (hΔ : 0≤Δ)
    (hbound : ∀ x,∀ f∈F,δ x f≤Δ) (s : RationalSampling.State n) (colors : Fin n→Fin 3)
    (q : ℕ) (bits) :
    output δ D F S Δ s colors q bits⊆F ∧
      (output δ D F S Δ s colors q bits).card=S.card ∧
      (output δ D F S Δ s colors q bits).Nonempty := by
  classical
  unfold output
  split_ifs with hr
  · have hradius (i : Fin s.leaves.length) : 0≤ s.radius i := by
      change (0:ℝ)≤(s.leaves[i.val].2:ℝ)
      exact_mod_cast hr.2.2.1 _ (List.getElem_mem i.isLt)
    exact (result_guarantee_s238r δ hδ D F S hSF hS Δ hΔ hbound s hr.1 colors hr.2.1 hradius
      (Fin.elim0 : Fin 0→Fin n) Fin.elim0 0 q (fun i=>Fin.elim0 i) (fun i=>Fin.elim0 i)
      (fun i=>Fin.elim0 i) (by simp) hr.2.2.2.2 hr.2.2.2.1).1 bits
  · exact ⟨hSF,rfl,hS⟩
end MetricKMedianRecovery.BitMachine.BinaryZeroBranch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RecoveryFeasible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRecovery
open Completion FiniteSampling
variable {n m H : ℕ} [PseudoMetricSpace (Fin n)]
variable (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
  (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty) (Δ : ℚ) (hΔ : 0≤Δ)
  (hbound : ∀ x,∀ f∈F,δ x f≤Δ) (s : RationalSampling.State n)
  (hn : n≤H) (hm : m≤H) (hH : 1≤H) (hp : s.leaves.length≤H)
  (r0 y0 : Fin n) (seed : Fin (tapeSize H)→Bool)
include hδ hSF hS hΔ hbound
lemma candidates_feasible : ∀ U∈candidates δ D F S Δ s hn hm hH hp r0 y0 seed,
    U⊆F ∧ U.card=S.card ∧ U.Nonempty := by
  apply candidates_property
  · intro q
    exact BinaryZeroBranch.output_feasible δ hδ D F S hSF hS Δ hΔ hbound s _ q.val _
  · intro q c b
    exact BinaryObservableBranch.output_feasible δ hδ D F S hSF hS Δ hΔ hbound s _ _ q.val c.val r0 y0 _
lemma result_feasible : result δ D F S Δ s hn hm hH hp r0 y0 seed⊆F ∧
    (result δ D F S Δ s hn hm hH hp r0 y0 seed).card=S.card ∧
    (result δ D F S Δ s hn hm hH hp r0 y0 seed).Nonempty := by
  exact BinaryMetricBest.best_property δ D S _ _ ⟨hSF,rfl,hS⟩
    (candidates_feasible δ hδ D F S hSF hS Δ hΔ hbound s hn hm hH hp r0 y0 seed)
end MetricKMedianRecovery.BitMachine.BinaryRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryFeasible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery
open Completion Sampling.Comparison
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
variable (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
  (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty) (Δ : ℕ)
  (hbound : ∀ x,∀ f∈F,δ x f≤Δ) (P : ℚ) (m : ℕ) (hm : m≤n) (r0 y0 : Fin n)
  (sample : Fin (2*m)→Fin (integralPrecision D (Δ:ℝ) m)→Bool)
  (complete : Fin (BinaryRecovery.tapeSize (n+1))→Bool)
include hδ hSF hS hbound
lemma optionOutput_feasible (w : Option (RationalSampling.State n)) :
    optionOutput δ D F S Δ m hm r0 y0 complete w⊆F ∧
    (optionOutput δ D F S Δ m hm r0 y0 complete w).card=S.card ∧
    (optionOutput δ D F S Δ m hm r0 y0 complete w).Nonempty := by
  cases w with
  | none=>exact ⟨hSF,rfl,hS⟩
  | some s=>
    unfold optionOutput
    simp only [Option.elim_some]
    split_ifs with hp
    · exact BinaryRecovery.result_feasible δ hδ D F S hSF hS Δ (by positivity) hbound s _ _ _ hp r0 y0 complete
    · exact ⟨hSF,rfl,hS⟩
lemma candidates_feasible : ∀ U∈candidates δ D F S Δ P m hm r0 y0 sample complete,
    U⊆F ∧ U.card=S.card ∧ U.Nonempty := by
  intro U hU
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hU
  exact optionOutput_feasible δ hδ D F S hSF hS Δ hbound m hm r0 y0 complete _
lemma result_feasible : result δ D F S Δ P m hm r0 y0 sample complete⊆F ∧
    (result δ D F S Δ P m hm r0 y0 sample complete).card=S.card ∧
    (result δ D F S Δ P m hm r0 y0 sample complete).Nonempty :=
  BinaryMetricBest.best_property δ D S _ _ ⟨hSF,rfl,hS⟩
    (candidates_feasible δ hδ D F S hSF hS Δ hbound P m hm r0 y0 sample complete)
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryDemand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair
open Completion Sampling Sampling.Comparison FiniteSampling
variable {n : ℕ}
variable [PseudoMetricSpace (Fin n)]
lemma output_feasible (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty) (Δ : ℕ) (hbound : ∀ x,∀ f∈F,δ x f≤Δ)
    (P : ℚ) (m : ℕ) (hm : m≤n) (r0 y0 : Fin n) (seed : Fin (count D Δ m)→Bool) :
    output δ D F S Δ P m hm r0 y0 seed⊆F ∧ (output δ D F S Δ P m hm r0 y0 seed).card=S.card ∧
      (output δ D F S Δ P m hm r0 y0 seed).Nonempty :=
  BinaryIntegralRecovery.result_feasible δ hδ D F S hSF hS Δ hbound P m hm r0 y0 _ _
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_MetricBestProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricBest
open Completion FiniteSampling
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
lemma realCost_le_self (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D S : Finset (Fin n)) (hS : S.Nonempty) (xs : List (Finset (Fin n)))
    (hxs : ∀ U∈xs,U.Nonempty) : realCost D (best δ D S xs) ≤ realCost D S := by
  rw [←BinaryMetricCost.cost_cast δ hδ D S hS,
    ←BinaryMetricCost.cost_cast δ hδ D (best δ D S xs) (best_property δ D S xs Finset.Nonempty hS hxs)]
  exact_mod_cast cost_le_self δ D S xs
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]
omit [Fintype Ω] [Nonempty Ω] in
lemma cost_le_reference (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D S : Finset (Fin n)) (hS : S.Nonempty) (trial : Ω→Finset (Fin n))
    (htrial : ∀ s,(trial s).Nonempty) (t : ℕ) (seed : Fin t→Ω) :
    realCost D (best δ D S (List.ofFn (fun i=>trial (seed i))))≤
      realCost D (bestWithFallback (realCost D) S trial t seed) := by
  have hxs : ∀ U∈List.ofFn (fun i=>trial (seed i)),U.Nonempty := by
    intro U hU
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hU
    exact htrial _
  rcases bestWithFallback_mem (realCost D) S trial t seed with h|⟨i,h⟩
  · rw [h]
    exact realCost_le_self δ hδ D S hS _ hxs
  · rw [h]
    exact realCost_le_mem δ hδ D S hS _ hxs _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
lemma amplified (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D S : Finset (Fin n)) (hS : S.Nonempty) (trial : Ω→Finset (Fin n))
    (htrial : ∀ s,(trial s).Nonempty) {B M p ζ : ℝ} (hB : 0≤B) (hM : 0≤M)
    (hfall : realCost D S≤M) (hp : 0<p)
    (hsuccess : p≤probability (fun s=>realCost D (trial s)≤B)) (hζ : 0<ζ)
    (t : ℕ) (ht : Real.log (1/ζ)/p≤(t:ℝ)) :
    (∀ seed:Fin t→Ω,realCost D (best δ D S (List.ofFn (fun i:Fin t=>trial (seed i))))≤M) ∧
    1-ζ≤probability (fun seed:Fin t→Ω=>realCost D (best δ D S (List.ofFn (fun i=>trial (seed i))))≤B) ∧
    average (fun seed:Fin t→Ω=>realCost D (best δ D S (List.ofFn (fun i=>trial (seed i)))))≤B+M*ζ := by
  obtain ⟨hh,hprob,hexp⟩:=amplified_output (realCost D) S trial hB hM hfall hp hsuccess hζ t ht
  have hdom:=cost_le_reference δ hδ D S hS trial htrial t
  exact ⟨fun seed=>(hdom seed).trans (hh seed),hprob.trans (probability_mono (fun seed h=>(hdom seed).trans h)),
    (average_mono hdom).trans hexp⟩
end MetricKMedianRecovery.BitMachine.BinaryMetricBest

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoveryAmplified
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat
open Completion Sampling Sampling.Comparison FiniteSampling
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
lemma amplified_s238r_oai (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty)
    (Δ : ℕ) (hbound : ∀ x,∀ f∈F,δ x f≤Δ) (P : ℚ) (m : ℕ) (hm : m≤n) (r0 y0 : Fin n)
    {B p ζ : ℝ} (hB : 0≤B) (hp : 0<p)
    (hsuccess : p≤probability (fun seed:Fin (Fair.count D Δ m)→Bool=>realCost D
      (Fair.output δ D F S Δ P m hm r0 y0 seed)≤B)) (hζ : 0<ζ)
    (t : ℕ) (ht : Real.log (1/ζ)/p≤(t:ℝ)) :
    (∀ seed:Fin t→Fin (Fair.count D Δ m)→Bool,realCost D (output δ D F S Δ P m hm r0 y0 t seed) ≤ realCost D S) ∧
    1-ζ≤probability (fun seed:Fin t→Fin (Fair.count D Δ m)→Bool=>realCost D (output δ D F S Δ P m hm r0 y0 t seed)≤B) ∧
    average (fun seed:Fin t→Fin (Fair.count D Δ m)→Bool=>realCost D (output δ D F S Δ P m hm r0 y0 t seed))≤B+realCost D S*ζ := by
  exact BinaryMetricBest.amplified δ hδ D S hS (Fair.output δ D F S Δ P m hm r0 y0)
    (fun seed=>(Fair.output_feasible δ hδ D F S hSF hS Δ hbound P m hm r0 y0 seed).2.2)
    hB (by rw [realCost,dite_eq_left hS]; exact Finset.sum_nonneg (fun _ _=>distanceTo_nonneg _ _ _)) le_rfl hp hsuccess hζ t ht
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.amplified_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.amplified_s238r_oai
