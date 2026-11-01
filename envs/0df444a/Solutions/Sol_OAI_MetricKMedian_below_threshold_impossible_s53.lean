-- Prove2me | solution 1 for OAI.MetricKMedian.below_threshold_impossible_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:41:04.015611+00:00
-- url     : https://prove2.me/submissions/6a59f884-1295-4292-a3e0-8ef8af15078e

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K064
import Definitions.Def_OAIQ053K070
import Theorems.Thm_OAI_MetricKMedian_Coverage_projection_gap_np_reductions_s53
import Theorems.Thm_OAI_MetricKMedian_Coverage_reduction_from_projections_s53

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Coverage
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.Instance.instDecidableZeroTest _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.Coverage.Input.client_val _root_.OAI.MetricKMedian.Coverage.Input.facility_val _root_.OAI.MetricKMedian.Coverage.Input.raw_k _root_.OAI.MetricKMedian.Coverage.Input.raw_m _root_.OAI.MetricKMedian.Coverage.Input.raw_n _root_.OAI.MetricKMedian.Coverage.ProjectionInput.incident_equiv _root_.OAI.MetricKMedian.Instance.restrict_cost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Finset

namespace Input

theorem client_injective (C : Input) : Function.Injective C.client := by
  intro i j h
  exact Sum.inl.inj (finSumFinEquiv.injective h)

theorem chosenFacilities_subset (C : Input) (S : Finset (Fin C.n)) :
    C.chosenFacilities S ⊆ C.toMedian.facilities :=
  image_subset_image (subset_univ S)

theorem nearest_chosen_ge_one (C : Input) (j : Fin C.m)
    (S : Finset (Fin C.n)) (hS : S.Nonempty) :
    1 ≤ nearest C.toMedian (C.client j) (C.chosenFacilities S) := by
  obtain ⟨x, hx, he⟩ := C.toMedian.nearest_attained (C.client j)
    (C.chosenFacilities S) ((C.chosenFacilities_nonempty S).mpr hS)
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
  rw [he, C.distance_client_facility]
  split <;> norm_num

theorem nearest_chosen (C : Input) (j : Fin C.m)
    (S : Finset (Fin C.n)) (hS : S.Nonempty) :
    nearest C.toMedian (C.client j) (C.chosenFacilities S) =
      if j ∈ C.covered S then 1 else 3 := by
  split_ifs with hj
  · obtain ⟨i, hi, hji⟩ := (C.mem_covered S j).mp hj
    apply le_antisymm _ (C.nearest_chosen_ge_one j S hS)
    have h := C.toMedian.nearest_le (C.client j) (mem_image_of_mem C.facility hi)
    simpa only [chosenFacilities, C.distance_client_facility, hji, Bool.true_eq, ↓reduceIte,
      Rat.cast_one] using h
  · obtain ⟨x, hx, he⟩ := C.toMedian.nearest_attained (C.client j)
      (C.chosenFacilities S) ((C.chosenFacilities_nonempty S).mpr hS)
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    have hji : C.incident j i ≠ true := fun h => hj ((C.mem_covered S j).mpr ⟨i, hi, h⟩)
    rw [he, C.distance_client_facility]
    simp [hji]

theorem cost_chosen (C : Input) (S : Finset (Fin C.n)) (hS : S.Nonempty) :
    cost C.toMedian (C.chosenFacilities S) =
      3 * (C.m : ℝ) - 2 * ((C.covered S).card : ℝ) := by
  unfold cost
  change (∑ j ∈ univ.image C.client,
    nearest C.toMedian j (C.chosenFacilities S)) = _
  rw [sum_image]
  · simp_rw [C.nearest_chosen _ S hS]
    calc
      ∑ j : Fin C.m, (if j ∈ C.covered S then (1 : ℝ) else 3) =
          ∑ j : Fin C.m, (3 - 2 * (if j ∈ C.covered S then (1 : ℝ) else 0)) := by
        apply sum_congr rfl
        intro j _
        split_ifs <;> norm_num
      _ = _ := by
        rw [sum_sub_distrib, ← mul_sum]
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
          sum_boole, filter_mem_eq_inter, univ_inter]
        ring
  · intro i _ j _ hij
    exact C.client_injective hij

theorem chosen_selected (C : Input) {T : Finset (Fin (C.m + C.n))}
    (hT : T ⊆ C.toMedian.facilities) : C.chosenFacilities (C.selected T) = T := by
  ext x
  simp only [chosenFacilities, selected, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hx
    obtain ⟨i, _, hi⟩ := mem_image.mp (hT hx)
    exact ⟨i, hi ▸ hx, hi⟩

theorem cost_selected (C : Input) {T : Finset (Fin (C.m + C.n))}
    (hT : T ⊆ C.toMedian.facilities) (hne : T.Nonempty) :
    cost C.toMedian T = 3 * (C.m : ℝ) - 2 * ((C.covered (C.selected T)).card : ℝ) := by
  have he := C.chosen_selected hT
  have hs : (C.selected T).Nonempty := (C.chosenFacilities_nonempty _).mp (he.symm ▸ hne)
  simpa only [he] using C.cost_chosen (C.selected T) hs

theorem covered_card_le (C : Input) (S : Finset (Fin C.n)) :
    (C.covered S).card ≤ C.m := by
  simpa only [card_univ, Fintype.card_fin] using card_le_card (subset_univ (C.covered S))

theorem cost_ge_universe (C : Input) {T : Finset (Fin (C.m + C.n))}
    (hT : T ⊆ C.toMedian.facilities) (hne : T.Nonempty) :
    (C.m : ℝ) ≤ cost C.toMedian T := by
  rw [C.cost_selected hT hne]
  have h : ((C.covered (C.selected T)).card : ℝ) ≤ C.m := by
    exact_mod_cast C.covered_card_le (C.selected T)
  linarith

theorem perfect_nonempty (C : Input) {S : Finset (Fin C.n)}
    (h : C.covered S = univ) : S.Nonempty := by
  let j : Fin C.m := ⟨0, C.m_pos⟩
  have hj : j ∈ C.covered S := by rw [h]; exact mem_univ j
  obtain ⟨i, hi, _⟩ := (C.mem_covered S j).mp hj
  exact ⟨i, hi⟩

theorem optimum_of_perfect (C : Input) (h : C.Perfect) :
    optimum C.toMedian = C.m := by
  apply le_antisymm
  · obtain ⟨S, hk, hcover⟩ := h
    have hne := C.perfect_nonempty hcover
    have hb := C.toMedian.optimum_le (C.chosenFacilities_subset S)
      ((C.chosenFacilities_nonempty _).mpr hne) (by
        change (C.chosenFacilities S).card ≤ C.k
        simpa only [chosenFacilities_card] using hk)
    rw [C.cost_chosen S hne, hcover] at hb
    simp only [card_univ, Fintype.card_fin] at hb
    linarith
  · obtain ⟨T, hT, hne, _, he⟩ := C.toMedian.optimum_attained
    rw [← he]
    exact C.cost_ge_universe hT hne

theorem cost_of_sound (C : Input) (δ : ℝ) (h : C.Sound δ)
    {T : Finset (Fin (C.m + C.n))} (hT : T ⊆ C.toMedian.facilities)
    (hne : T.Nonempty) (hk : T.card ≤ C.k) :
    (1 + 2 / Real.exp 1 - 2 * δ) * C.m ≤ cost C.toMedian T := by
  have he := C.chosen_selected hT
  have hs : (C.selected T).card ≤ C.k := by
    rw [← C.chosenFacilities_card, he]
    exact hk
  have hc := h (C.selected T) hs
  rw [C.cost_selected hT hne]
  simp only [div_eq_mul_inv, one_mul] at hc ⊢
  nlinarith

end Input

end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Analysis
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
attribute [-simp] _root_.OAI.MetricKMedian.Coverage.Input.client_val _root_.OAI.MetricKMedian.Coverage.Input.facility_val _root_.OAI.MetricKMedian.Coverage.Input.raw_k _root_.OAI.MetricKMedian.Coverage.Input.raw_m _root_.OAI.MetricKMedian.Coverage.Input.raw_n _root_.OAI.MetricKMedian.Coverage.ProjectionInput.incident_equiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage.Input
open Finset

theorem selectedMask_eq_selected (C : Input) (T : Finset (Fin (C.m + C.n))) :
    C.selectedMask (List.ofFn (fun x : Fin (C.m + C.n) => decide (x ∈ T))) =
      C.selected T := by
  ext i
  simp [selectedMask, selected]

theorem comparisonCost_eq_cost (C : Input) {T : Finset (Fin (C.m + C.n))}
    (hT : T ⊆ C.toMedian.facilities) (hne : T.Nonempty)
    {output : List Bool} (hmask : output = List.ofFn (fun x => decide (x ∈ T))) :
    (C.comparisonCost output : ℝ) = cost C.toMedian T := by
  rw [C.cost_selected hT hne, hmask]
  simp [comparisonCost, C.selectedMask_eq_selected]

theorem accepts_of_perfect (C : Input) {α : ℝ} {q : ℚ} {output : List Bool}
    (hαq : α < (q : ℝ)) (h : C.Perfect)
    (hcorrect : FactorCorrect α C.toMedian output) : C.accepts q output = true := by
  obtain ⟨T, hT, hne, hk, hmask, hcost⟩ := hcorrect
  have hpos : (0 : ℝ) < C.m := by exact_mod_cast C.m_pos
  rw [C.optimum_of_perfect h] at hcost
  have hcmp : (C.comparisonCost output : ℝ) < (q : ℝ) * C.m := by
    rw [C.comparisonCost_eq_cost hT hne hmask]
    exact hcost.trans_lt (mul_lt_mul_of_pos_right hαq hpos)
  simp only [accepts, decide_eq_true_eq]
  exact_mod_cast hcmp

theorem rejects_of_sound (C : Input) {α δ : ℝ} {q : ℚ} {output : List Bool}
    (hq : (q : ℝ) ≤ 1 + 2 / Real.exp 1 - 2 * δ) (h : C.Sound δ)
    (hcorrect : FactorCorrect α C.toMedian output) : C.accepts q output = false := by
  obtain ⟨T, hT, hne, hk, hmask, _⟩ := hcorrect
  have hcost := C.cost_of_sound δ h hT hne hk
  have hcmp : (q : ℝ) * C.m ≤ (C.comparisonCost output : ℝ) := by
    rw [C.comparisonCost_eq_cost hT hne hmask]
    exact (mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg _)).trans hcost
  simp only [accepts, decide_eq_false_iff_not]
  intro hlt
  have hlt' : (C.comparisonCost output : ℝ) < (q : ℝ) * C.m := by exact_mod_cast hlt
  exact (not_lt_of_ge hcmp) hlt'

end MetricKMedian.Coverage.Input

namespace MetricKMedian

theorem exists_coverage_margin {α : ℝ} (hα : α < 1 + 2 / Real.exp 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q : ℚ,
      α < (q : ℝ) ∧ (q : ℝ) < 1 + 2 / Real.exp 1 - 2 * δ := by
  let δ := (1 + 2 / Real.exp 1 - α) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hg : α < 1 + 2 / Real.exp 1 - 2 * δ := by dsimp [δ]; linarith
  obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn hg
  exact ⟨δ, hδ, q, hq₁, hq₂⟩

end MetricKMedian

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Composition
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Complexity.FiniteComposition
open Turing Function Finset Polynomial
open Binary (Trace)

attribute [instance] Machine.decK Machine.finK Machine.finΓ Machine.finLabel Machine.finState

namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
variable {f : α → β} {g : β → γ}

 theorem finite_work (P : PolyProgram ea eb f) (k : P.stock.tm.K) : Finite (P.stock.tm.Γ k) :=
  @Finite.of_fintype (P.machine.Γ k) (P.machine.finΓ k)

end PolyProgram

end MetricKMedian.Complexity.FiniteComposition

namespace MetricKMedian.Complexity

theorem FinitePolyTime.comp {α β γ : Type}
    {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
    {f : α → β} {g : β → γ}
    (hf : FinitePolyTime ea eb f) (hg : FinitePolyTime eb ec g) :
    FinitePolyTime ea ec (g ∘ f) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  let r := (FiniteComposition.PolyProgram.ofStock p hp).comp
    (FiniteComposition.PolyProgram.ofStock q hq)
  exact ⟨r.stock, r.finite_work⟩

end MetricKMedian.Complexity

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Classes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Complexity
open Binary.Automatic Binary.Automatic.Poly

 theorem firstProjection_finite : FinitePolyTime encodePair id Prod.fst :=
  ⟨firstProjectionProgram.stock, firstProjectionProgram.finite_work⟩

theorem P_subset_NP : P ⊆ NP := by
  intro L hL
  obtain ⟨d, hd, hc⟩ := hL
  refine ⟨d ∘ Prod.fst, 0, firstProjection_finite.comp hd, ?_⟩
  intro x
  constructor
  · intro hx
    exact ⟨[], by simp, (hc x).mpr hx⟩
  · rintro ⟨w, _, hw⟩
    exact (hc x).mp hw

theorem exists_NP_not_P (h : PNeNP) : ∃ L : Language, L ∈ NP ∧ L ∉ P := by
  by_contra hn
  apply h
  apply Set.Subset.antisymm P_subset_NP
  intro L hL
  by_contra hp
  exact hn ⟨L, hL, hp⟩

end MetricKMedian.Complexity

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Constants
attribute [-instance] _root_.OAI.MetricKMedian.PCP.CloudCopies.incidentNonempty _root_.OAI.MetricKMedian.PCP.CloudCopies.nodeNonempty _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleNonempty _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Filter

theorem partition_parameters_exist {δ : ℝ} (hδ : 0 < δ) :
    Nonempty (PartitionParameters δ) := by
  have hlim : Tendsto (fun n : ℕ => (1 - 1 / (n : ℝ)) ^ n) atTop
      (nhds (1 / Real.exp 1)) := by
    simpa only [neg_div, one_div, sub_eq_add_neg, Real.exp_neg] using
      Real.tendsto_one_add_div_pow_exp (-1)
  have hev : ∀ᶠ n : ℕ in atTop,
      1 / Real.exp 1 - δ / 3 < (1 - 1 / (n : ℝ)) ^ n :=
    hlim.eventually_const_lt (by linarith)
  obtain ⟨D,hD,hd⟩ := ((eventually_ge_atTop 2).and hev).exists
  have hDr : 0 < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
  obtain ⟨t,ht⟩ := exists_nat_gt ((D : ℝ) / (δ / 3))
  have ht0 : 0 < (t : ℝ) := lt_trans (div_pos hDr (by linarith)) ht
  have htp : 1 ≤ t := by exact_mod_cast (show (1 : ℝ) ≤ t by
    have : 0 < t := by exact_mod_cast ht0
    exact_mod_cast this)
  have hratio : (D : ℝ) / t < δ / 3 := by
    apply (div_lt_iff₀ ht0).mpr
    have := (div_lt_iff₀ (by linarith : 0 < δ / 3)).mp ht
    nlinarith
  have hden : 0 < (t : ℝ)^2 * (D : ℝ)^2 := mul_pos (sq_pos_of_pos ht0) (sq_pos_of_pos hDr)
  obtain ⟨ε,hε,he⟩ := exists_rat_btwn (div_pos (show 0 < δ / 3 by linarith) hden)
  have hsmall : (t : ℝ)^2 * (D : ℝ)^2 * (ε : ℝ) < δ / 3 := by
    have := (lt_div_iff₀ hden).mp he
    nlinarith
  refine ⟨⟨D,t,ε,hD,htp,?_,?_⟩⟩
  · exact_mod_cast hε
  · linarith

end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Encoding
attribute [-instance] _root_.OAI.MetricKMedian.Instance.instDecidableZeroTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Binary Binary.Automatic Binary.Automatic.Poly

namespace Raw

end Raw

namespace Input

theorem reduction_finite_poly : Complexity.FinitePolyTime encode encodeInstance toMedian :=
  ⟨reductionProgram.stock, reductionProgram.finite_work⟩

end Input
end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Threads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Complexity

theorem FinitePolyTime.withInput {α β : Type}
    {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
    (h : FinitePolyTime ea eb f) :
    FinitePolyTime ea (Binary.encodePair eb ea) (fun a => (f a,a)) := by
  obtain ⟨p,hp⟩ := h
  let q := (FiniteComposition.PolyProgram.ofStock p hp).withInput
  exact ⟨q.stock,q.finite_work⟩

end MetricKMedian.Complexity

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Reduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Complexity

theorem approximation_gives_separator {α : ℝ}
    (hα : α ∈ approximationFactors) (hsmall : α < 1+2/Real.exp 1) :
    ∃ δ : ℝ, 0 < δ ∧ HasSeparator δ := by
  obtain ⟨δ,hδ,q,hq₁,hq₂⟩ := exists_coverage_margin hsmall
  obtain ⟨algorithm,halg,hcorrect⟩ := hα
  let result : Input → List Bool := algorithm ∘ Input.toMedian
  have hr : FinitePolyTime Input.encode id result :=
    Input.reduction_finite_poly.comp halg
  have hv : FinitePolyTime (Binary.encodePair id Input.encode) encodeBit
      (fun x : List Bool × Input => x.2.accepts q x.1) :=
    ⟨(Input.verdictProgram q).stock,(Input.verdictProgram q).finite_work⟩
  refine ⟨δ,hδ,(fun C => C.accepts q (result C)), ?_, ?_, ?_⟩
  · exact hr.withInput.comp hv
  · intro C hC
    exact C.accepts_of_perfect hq₁ hC (hcorrect C.toMedian)
  · intro C hC
    exact C.rejects_of_sound hq₂.le hC (hcorrect C.toMedian)

theorem separator_decides_reduction {δ : ℝ} (hsep : HasSeparator δ)
    {L : Language} {r : Word → Input}
    (hr : FinitePolyTime id Input.encode r)
    (hyes : ∀ x, x ∈ L → (r x).Perfect)
    (hno : ∀ x, x ∉ L → (r x).Sound δ) : L ∈ P := by
  obtain ⟨d,hd,hy,hn⟩ := hsep
  refine ⟨d ∘ r,hr.comp hd,?_⟩
  intro x
  constructor
  · intro hx
    by_contra h
    have hh := hn (r x) (hno x h)
    exact Bool.noConfusion (hx.symm.trans hh)
  · intro hx
    exact hy (r x) (hyes x hx)

theorem remaining_gap_obstruction (hPNP : PNeNP) {α : ℝ}
    (hα : α ∈ approximationFactors) (hsmall : α < 1+2/Real.exp 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ L : Language, L ∈ NP ∧
      ¬ ∃ r : Word → Input, FinitePolyTime id Input.encode r ∧
        (∀ x, x ∈ L → (r x).Perfect) ∧
        (∀ x, x ∉ L → (r x).Sound δ) := by
  obtain ⟨δ,hδ,hsep⟩ := approximation_gives_separator hα hsmall
  obtain ⟨L,hL,hnot⟩ := exists_NP_not_P hPNP
  refine ⟨δ,hδ,L,hL,?_⟩
  rintro ⟨r,hr,hy,hn⟩
  exact hnot (separator_decides_reduction hsep hr hy hn)

end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_ProjectionReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Complexity

theorem remaining_projection_obstruction (hPNP : PNeNP) {α : ℝ}
    (hα : α ∈ approximationFactors) (hsmall : α < 1+2/Real.exp 1) :
    ∃ ε : ℚ, 0 < ε ∧ ∃ L : Language, L ∈ NP ∧ ¬ ProjectionReduction ε L := by
  obtain ⟨δ,hδ,L,hL,hno⟩ := remaining_gap_obstruction hPNP hα hsmall
  obtain ⟨P⟩ := partition_parameters_exist hδ
  exact ⟨P.ε,P.ε_pos,L,hL,fun h => hno (reduction_from_projections_s53 P h)⟩

end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Threshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPThreshold
namespace MetricKMedian

theorem below_threshold_impossible_s53_oai (h : Complexity.PNeNP) :
    ∀ α ∈ approximationFactors, 1+2/Real.exp 1≤α := by
  intro α hα
  by_contra hn
  obtain ⟨ε,hε,L,hL,hno⟩ := Coverage.remaining_projection_obstruction h hα (lt_of_not_ge hn)
  exact hno (Coverage.projection_gap_np_reductions_s53 ε hε L hL)

end MetricKMedian

end Inline_PCPThreshold

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.below_threshold_impossible_s53_oai := @OAI.MetricKMedian.below_threshold_impossible_s53_oai
