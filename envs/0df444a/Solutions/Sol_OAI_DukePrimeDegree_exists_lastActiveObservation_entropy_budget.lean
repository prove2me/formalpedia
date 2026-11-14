-- Prove2me | solution 1 for OAI.DukePrimeDegree.exists_lastActiveObservation_entropy_budget
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:26:45.575885+00:00
-- url     : https://prove2.me/submissions/2a124718-8f1a-42cd-a269-93ce3326b453

import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Finset.Max
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Definitions.Def_OAIQ244Duke012

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_SmallReturnRefinement
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A quantitative entropy budget for fine return cells -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma tsum_option_eq {α : Type*} (f : Option α → ℝ) (hs : Summable f) :
    (∑' z, f z)=f none+∑' z : α, f (some z) := by
  let e : Option α ≃ α ⊕ PUnit.{1} := Equiv.optionEquivSumPUnit α
  have hh : Summable (fun z => f (e.symm z)) := hs.comp_injective e.symm.injective
  calc
    _ = ∑' z, f (e.symm z) := (e.symm.tsum_eq f).symm
    _ = _ := by
      rw [hh.comp_injective Sum.inl_injective |>.tsum_sum
        (hh.comp_injective Sum.inr_injective)]
      simp only [e,Equiv.optionEquivSumPUnit_symm_inl,
        Equiv.optionEquivSumPUnit_symm_inr,tsum_fintype,Finset.sum_const,
        Finset.card_univ,Fintype.card_punit,one_nsmul,add_comm]

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_LastActiveObservation
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.xMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Countable observations at the last active scale

Summably small sections overlap only finitely often almost everywhere.
Recording the largest active scale therefore preserves arbitrarily fine
visits while keeping the observation alphabet countable.
-/

noncomputable section
open Set MeasureTheory
namespace DukePrimeDegree

lemma measurableSet_lastActiveSection {Y : Type*} [MeasurableSpace Y]
    {S : ℕ → Set Y} (hS : ∀ n, MeasurableSet (S n)) (n : ℕ) :
    MeasurableSet (lastActiveSection S n) := by
  have he : lastActiveSection S n = S n ∩ ⋂ m : ℕ, ⋂ (_ : n < m), (S m)ᶜ := by
    ext x
    simp only [lastActiveSection,mem_ofPred_eq,mem_inter_iff,mem_iInter,mem_compl_iff]
  rw [he]
  exact (hS n).inter (MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ => (hS m).compl)

lemma lastActiveSection_unique {Y : Type*} {S : ℕ → Set Y} {n m : ℕ} {x : Y}
    (hn : x ∈ lastActiveSection S n) (hm : x ∈ lastActiveSection S m) : n=m := by
  rcases lt_trichotomy n m with h | h | h
  · exact (hn.2 m h hm.1).elim
  · exact h
  · exact (hm.2 n h hn.1).elim

lemma lastActiveObservationAtom_unique {Y : Type*} (S : ℕ → Set Y)
    {K : ℕ → ℕ} (B : ∀ n, Y → Fin (K n))
    {a b : Option (Σ n : ℕ, Fin (K n))} {x : Y}
    (ha : x ∈ lastActiveObservationAtom S B a)
    (hb : x ∈ lastActiveObservationAtom S B b) : a=b := by
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some b => exact (ha (mem_iUnion.mpr ⟨b.1,hb.1⟩)).elim
  | some a =>
      cases b with
      | none => exact (hb (mem_iUnion.mpr ⟨a.1,ha.1⟩)).elim
      | some b =>
        rcases a with ⟨n,i⟩
        rcases b with ⟨m,j⟩
        have he := lastActiveSection_unique ha.1 hb.1
        dsimp at he
        subst m
        have hij : i=j := ha.2.symm.trans hb.2
        subst j
        rfl

lemma lastActiveObservation_fiber {Y : Type*} (S : ℕ → Set Y)
    {K : ℕ → ℕ} (B : ∀ n, Y → Fin (K n)) (z : Option (Σ n : ℕ, Fin (K n))) :
    {x | lastActiveObservation S B x=z}=lastActiveObservationAtom S B z := by
  ext x
  constructor
  · intro hx
    have hm : x ∈ lastActiveObservationAtom S B (lastActiveObservation S B x) :=
      (lastActiveObservation_covers S B x).choose_spec
    rwa [hx] at hm
  · intro hx
    exact lastActiveObservationAtom_unique S B (lastActiveObservation_covers S B x).choose_spec hx

lemma measurable_lastActiveObservation {Y : Type*} [MeasurableSpace Y]
    {S : ℕ → Set Y} (hS : ∀ n, MeasurableSet (S n))
    {K : ℕ → ℕ} (B : ∀ n, Y → Fin (K n)) (hB : ∀ n, Measurable (B n)) :
    @Measurable Y (Option (Σ n : ℕ, Fin (K n))) _ ⊤ (lastActiveObservation S B) := by
  let : MeasurableSpace (Option (Σ n : ℕ, Fin (K n))) := ⊤
  apply measurable_to_countable'
  intro z
  change MeasurableSet {x | lastActiveObservation S B x=z}
  rw [lastActiveObservation_fiber]
  cases z with
  | none => exact (MeasurableSet.iUnion (measurableSet_lastActiveSection hS)).compl
  | some z =>
      exact (measurableSet_lastActiveSection hS z.1).inter
        (hB z.1 (measurableSet_singleton z.2))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_SparseObservationEntropy
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Entropy budgets for observations on sparse sections -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace DukePrimeDegree

private lemma summable_option_of_summable_some {α : Type*}
    (f : Option α → ℝ) (hf : Summable (fun a => f (some a))) : Summable f := by
  let e : Option α ≃ α ⊕ PUnit.{1} := Equiv.optionEquivSumPUnit α
  have H : Summable (fun z : α ⊕ PUnit.{1} => f (e.symm z)) := by
    apply Summable.sum
    · simpa only [Function.comp_def,e,Equiv.optionEquivSumPUnit_symm_inl] using hf
    · exact (hasSum_fintype _).summable
  simpa only [Function.comp_def,Equiv.symm_apply_apply] using H.comp_injective e.injective

/-- A row-wise budget controls both the rare-label mass and its entropy. -/
theorem sparse_distribution_information_le (K : ℕ → ℕ)
    (p : Option (Σ n : ℕ, Fin (K n)) → ℝ)
    (hp : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1)
    (hs : Summable p) (hsum : ∑' z, p z=1)
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (hws : Summable w)
    (hsmall : ∀ n (i : Fin (K n)), p (some ⟨n,i⟩) ≤ w n/(K n+1:ℝ))
    (hinfo : ∀ n (i : Fin (K n)),
      Real.negMulLog (p (some ⟨n,i⟩)) ≤ w n/(K n+1:ℝ)) :
    Summable (fun z => Real.negMulLog (p z)) ∧
      (∑' z, Real.negMulLog (p z)) ≤ 2*∑' n, w n := by
  let f (z : Σ n : ℕ, Fin (K n)) := Real.negMulLog (p (some z))
  have hf0 (z) : 0 ≤ f z := Real.negMulLog_nonneg (hp _) (hp1 _)
  have hrow (n) : (∑' i : Fin (K n), f ⟨n,i⟩) ≤ w n := by
    rw [tsum_fintype]
    calc
      _ ≤ ∑ _i : Fin (K n), w n/(K n+1:ℝ) :=
        Finset.sum_le_sum fun i _ => hinfo n i
      _ ≤ w n := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        have hden : (0:ℝ)<K n+1 := by positivity
        have he := div_mul_cancel₀ (w n) hden.ne'
        nlinarith [hw n]
  have hrows : Summable (fun n => ∑' i : Fin (K n), f ⟨n,i⟩) :=
    Summable.of_nonneg_of_le (fun n => tsum_nonneg fun _ => hf0 _) hrow hws
  have hf : Summable f := (summable_sigma_of_nonneg hf0).mpr
    ⟨fun _ => (hasSum_fintype _).summable,hrows⟩
  have hfle : (∑' z, f z) ≤ ∑' n, w n := by
    rw [hf.tsum_sigma]
    exact hrows.tsum_le_tsum hrow hws
  have hmassrows (n) : (∑' i : Fin (K n), p (some ⟨n,i⟩)) ≤ w n := by
    rw [tsum_fintype]
    calc
      _ ≤ ∑ _i : Fin (K n), w n/(K n+1:ℝ) :=
        Finset.sum_le_sum fun i _ => hsmall n i
      _ ≤ w n := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        have hden : (0:ℝ)<K n+1 := by positivity
        have he := div_mul_cancel₀ (w n) hden.ne'
        nlinarith [hw n]
  have hps : Summable (fun z : Σ n : ℕ, Fin (K n) => p (some z)) :=
    hs.comp_injective (Option.some_injective _)
  have hmass : (∑' z : Σ n : ℕ, Fin (K n), p (some z)) ≤ ∑' n, w n := by
    rw [hps.tsum_sigma]
    exact hps.sigma.tsum_le_tsum hmassrows hws
  have hbase : Real.negMulLog (p none) ≤ ∑' n, w n := by
    have H := Real.negMulLog_le_one_sub_self (hp none)
    rw [tsum_option_eq p hs] at hsum
    linarith
  have hfull := summable_option_of_summable_some
    (fun z => Real.negMulLog (p z)) hf
  refine ⟨hfull,?_⟩
  rw [tsum_option_eq _ hfull]
  change Real.negMulLog (p none)+(∑' z, f z) ≤ _
  linarith

lemma exists_small_mass_information_budget {b : ℝ} (hb : 0 < b) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ b ∧
      ∀ p : ℝ, 0 ≤ p → p ≤ δ → Real.negMulLog p ≤ b := by
  have ht : Filter.Tendsto Real.negMulLog (nhds 0) (nhds 0) := by
    have H := Real.continuous_negMulLog.continuousAt (x := 0)
    change Filter.Tendsto Real.negMulLog (nhds 0) (nhds (Real.negMulLog 0)) at H
    simpa only [Real.negMulLog_zero] using H
  obtain ⟨r,hr,H⟩ := Metric.tendsto_nhds_nhds.mp ht b hb
  refine ⟨min b (r/2),lt_min hb (by positivity),min_le_left _ _,?_⟩
  intro p hp hpδ
  have hpr : dist p 0 < r := by
    rw [Real.dist_eq,sub_zero,abs_of_nonneg hp]
    have := hpδ.trans (min_le_right b (r/2))
    linarith
  have he := H hpr
  rw [Real.dist_eq,sub_zero] at he
  exact (le_abs_self _).trans he.le

/-- The finite label cardinalities may grow arbitrarily fast: their
section masses can be chosen afterwards to absorb their Shannon cost. -/
theorem exists_sparse_distribution_budget (K : ℕ → ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℕ → ℝ, (∀ n, 0 < δ n) ∧ Summable δ ∧
      (∑' n, δ n) ≤ ε/4 ∧
      ∀ p : Option (Σ n : ℕ, Fin (K n)) → ℝ,
        (∀ z, 0 ≤ p z) → (∀ z, p z ≤ 1) → Summable p → (∑' z, p z)=1 →
        (∀ n (i : Fin (K n)), p (some ⟨n,i⟩) ≤ δ n) →
        Summable (fun z => Real.negMulLog (p z)) ∧
          (∑' z, Real.negMulLog (p z)) < ε := by
  let w : ℕ → ℝ := fun n => (ε/4)*(1/2:ℝ)^(n+1)
  have hw (n) : 0 < w n := by dsimp only [w] <;> positivity
  have hws : Summable w := by
    simpa only [w,pow_succ',←mul_assoc] using
      (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)).mul_left ((ε/4)*(1/2))
  have hwSum : (∑' n, w n)=ε/4 := by
    simp only [w,pow_succ',←mul_assoc,tsum_mul_left,
      tsum_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)]
    ring
  choose δ hδ hδb hδI using fun n => exists_small_mass_information_budget
    (b := w n/(K n+1:ℝ)) (div_pos (hw n) (by positivity))
  have hδw (n) : δ n ≤ w n := (hδb n).trans (by
    apply div_le_self (hw n).le
    linarith [Nat.cast_nonneg (α := ℝ) (K n)])
  have hδs := Summable.of_nonneg_of_le (fun n => (hδ n).le) hδw hws
  refine ⟨δ,hδ,hδs,(hδs.tsum_le_tsum hδw hws).trans_eq hwSum,?_⟩
  intro p hp hp1 hs hsum hsmall
  obtain ⟨hI,hIle⟩ := sparse_distribution_information_le K p hp hp1 hs hsum w
    (fun n => (hw n).le) hws
    (fun n i => (hsmall n i).trans (hδb n))
    (fun n i => hδI n _ (hp _) (hsmall n i))
  refine ⟨hI,?_⟩
  rw [hwSum] at hIle
  linarith

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Entropy_LastActiveEntropy
attribute [-instance] _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.xMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Small Shannon entropy for the last-active-scale observation -/

noncomputable section
open Set MeasureTheory Function
open scoped ENNReal
namespace DukePrimeDegree

lemma countable_observation_distribution
    {Y α : Type*} [MeasurableSpace Y] [Countable α]
    (μ : Measure Y) [IsProbabilityMeasure μ] (P : Y → α)
    (hP : ∀ a, MeasurableSet {x | P x=a}) :
    Summable (fun a => μ.real {x | P x=a}) ∧
      (∑' a, μ.real {x | P x=a})=1 := by
  have hdis : Pairwise (Disjoint on (fun a => {x | P x=a})) := by
    intro a b hab
    exact disjoint_left.mpr fun x hx hy => hab (hx.symm.trans hy)
  have hcover : (⋃ a, {x | P x=a})=univ := by ext x; simp
  have hsum : (∑' a, μ {x | P x=a})=1 := by
    rw [←measure_iUnion hdis hP,hcover,measure_univ]
  refine ⟨ENNReal.summable_toReal (by rw [hsum]; exact ENNReal.one_ne_top),?_⟩
  change (∑' a, (μ {x | P x=a}).toReal)=1
  rw [←ENNReal.tsum_toReal_eq (fun _ => measure_ne_top μ _),hsum,ENNReal.toReal_one]

/-- All grid sizes are fixed before the section masses are chosen. -/
theorem exists_lastActiveObservation_entropy_budget_oai
    {Y : Type*} [MeasurableSpace Y] (K : ℕ → ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℕ → ℝ, (∀ n, 0 < δ n) ∧ Summable δ ∧ (∑' n, δ n) ≤ ε/4 ∧
      ∀ (μ : Measure Y) [IsProbabilityMeasure μ] (S : ℕ → Set Y),
        (∀ n, MeasurableSet (S n)) → (∀ n, μ.real (S n) ≤ δ n) →
        ∀ B : ∀ n, Y → Fin (K n), (∀ n, Measurable (B n)) →
          Summable (fun z => Real.negMulLog (μ.real {x | lastActiveObservation S B x=z})) ∧
          (∑' z, Real.negMulLog (μ.real {x | lastActiveObservation S B x=z})) < ε := by
  obtain ⟨δ,hδ,hδs,hδsum,H⟩ := exists_sparse_distribution_budget K hε
  refine ⟨δ,hδ,hδs,hδsum,?_⟩
  intro μ _ S hS hsmall B hB
  let I := Option (Σ n : ℕ, Fin (K n))
  let : MeasurableSpace I := ⊤
  let P := lastActiveObservation S B
  have hP : Measurable P := measurable_lastActiveObservation hS B hB
  have hdist := countable_observation_distribution μ P (fun z => hP (measurableSet_singleton z))
  apply H (fun z => μ.real {x | P x=z}) (fun _ => measureReal_nonneg)
    (fun _ => measureReal_le_one) hdist.1 hdist.2
  intro n i
  apply (measureReal_mono (s₁ := {x | P x=some ⟨n,i⟩}) (s₂ := S n) ?_
    (measure_ne_top μ _)).trans (hsmall n)
  intro x hx
  have hx' : x ∈ lastActiveObservationAtom S B (some ⟨n,i⟩) := by
    rw [←lastActiveObservation_fiber]
    exact hx
  exact hx'.1.1

end DukePrimeDegree

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.DukePrimeDegree.exists_lastActiveObservation_entropy_budget_oai.{u_1} := @OAI.DukePrimeDegree.exists_lastActiveObservation_entropy_budget_oai.{u_1}
