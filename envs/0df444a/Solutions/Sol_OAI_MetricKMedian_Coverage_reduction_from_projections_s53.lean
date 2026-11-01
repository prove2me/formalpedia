-- Prove2me | solution 1 for OAI.MetricKMedian.Coverage.reduction_from_projections_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:40:18.927281+00:00
-- url     : https://prove2.me/submissions/3041107f-5a80-49c5-bba0-c337fd1c1285

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K070
import Theorems.Thm_OAI_MetricKMedian_Coverage_ProjectionSystem_coverage_agreement_bound_s53

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Composition
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Projection
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.Coverage.ProjectionInput.incident_equiv _root_.OAI.MetricKMedian.Coverage.ProjectionInput.raw_edge _root_.OAI.MetricKMedian.Coverage.ProjectionSystem.mem_agreement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Finset

namespace ProjectionSystem
variable {U V I A B : Type} [Fintype U] [Fintype V] [Fintype I]
  [Fintype A] [Fintype B] [DecidableEq U] [DecidableEq V] [DecidableEq I]
  [DecidableEq A] [DecidableEq B]
variable (G : ProjectionSystem U V I A B)

omit [DecidableEq V] in
theorem perfect_cover (left : U → A) (right : V → B)
    (h : ∀ v i, G.project v i (left (G.neighbor v i)) = right v) :
    ∃ S : Finset (U × A), S.card ≤ Fintype.card U ∧ G.covered S = univ := by
  let S : Finset (U × A) := univ.image (fun u => (u,left u))
  refine ⟨S, (card_image_le.trans (by simp)), ?_⟩
  apply eq_univ_of_forall
  rintro ⟨v,w⟩
  simp only [covered, mem_filter, mem_univ, true_and]
  refine ⟨w (right v),left (G.neighbor v (w (right v))),?_,?_⟩
  · exact mem_image_of_mem _ (mem_univ _)
  · rw [h]

omit [Fintype A] [Fintype B] [DecidableEq V] [DecidableEq I]
  [DecidableEq A] [DecidableEq B] in
theorem regular_sum {d : ℕ} (hreg : G.LeftRegular d) (f : U → ℕ) :
    (∑ v, ∑ i, f (G.neighbor v i)) = d * ∑ u, f u := by
  rw [← Fintype.sum_prod_type (fun p : V × I => f (G.neighbor p.1 p.2))]
  have he (p : V × I) : f (G.neighbor p.1 p.2) =
      ∑ u, if G.neighbor p.1 p.2 = u then f u else 0 := by simp
  simp_rw [he]
  rw [sum_comm, mul_sum]
  apply sum_congr rfl
  intro u _
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul, hreg u, Nat.cast_id]

end ProjectionSystem
end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_SamplingCounts
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Finset

theorem coordinate_sum {J I : Type} [Fintype J] [Fintype I] [DecidableEq J]
    (j : J) (f : I → ℕ) :
    (∑ s : J → I, f (s j)) = Fintype.card I ^ (Fintype.card J-1) * ∑ i, f i := by
  classical
  have hJ : Fintype.card {k : J // k ≠ j} = Fintype.card J-1 := by
    rw [Fintype.card_subtype_compl]
    simp
  calc
    _ = ∑ p : I × ({k : J // k ≠ j} → I), f p.1 :=
      Fintype.sum_equiv (Equiv.funSplitAt j I) _ _ (fun _ => rfl)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,Fintype.card_fun,hJ]
      rw [mul_sum]

theorem equal_pair_count {J I B : Type} [Fintype J] [Fintype I] [DecidableEq J]
    [DecidableEq B] (j k : J) (hjk : j ≠ k) (color : I → B) (M : ℕ)
    (hM : ∀ b, (univ.filter (fun i => color i = b)).card ≤ M) :
    (univ.filter (fun s : J → I => color (s j) = color (s k))).card ≤
      Fintype.card I ^ (Fintype.card J-1) * M := by
  classical
  have hJ : Fintype.card {k : J // k ≠ j} = Fintype.card J-1 := by
    rw [Fintype.card_subtype_compl]
    simp
  rw [card_filter]
  have he : (∑ s : J → I, if color (s j) = color (s k) then 1 else 0) =
      ∑ p : I × ({x : J // x ≠ j} → I),
        if color p.1 = color (p.2 ⟨k,hjk.symm⟩) then 1 else 0 :=
    Fintype.sum_equiv (Equiv.funSplitAt j I) _ _ (fun _ => rfl)
  rw [he,Fintype.sum_prod_type,sum_comm]
  calc
    _ ≤ ∑ _ : ({x : J // x ≠ j} → I), M := by
      apply sum_le_sum
      intro r _
      simpa only [sum_boole,Nat.cast_id] using hM (color (r ⟨k,hjk.symm⟩))
    _ = _ := by simp [hJ]

theorem sampled_agreement_count {J I B : Type} [Fintype J] [Fintype I]
    [DecidableEq J] [DecidableEq B] (color : I → B) (M : ℕ)
    (hM : ∀ b, (univ.filter (fun i => color i = b)).card ≤ M) :
    (univ.filter (fun s : J → I => ∃ j k, j ≠ k ∧ color (s j) = color (s k))).card ≤
      (Fintype.card J)^2 * Fintype.card I ^ (Fintype.card J-1) * M := by
  classical
  let E (j k : J) : Finset (J → I) :=
    univ.filter (fun s => j ≠ k ∧ color (s j) = color (s k))
  have he : (univ.filter (fun s : J → I => ∃ j k, j ≠ k ∧ color (s j) = color (s k))) =
      univ.biUnion (fun j => univ.biUnion (E j)) := by
    ext s
    simp [E]
  have hp (j k : J) : (E j k).card ≤ Fintype.card I ^ (Fintype.card J-1) * M := by
    by_cases hjk : j = k
    · subst k; simp [E]
    · have he : E j k = univ.filter (fun s : J → I => color (s j) = color (s k)) := by
        ext s; simp [E,hjk]
      rw [he]
      exact equal_pair_count j k hjk color M hM
  rw [he]
  calc
    _ ≤ ∑ j, (univ.biUnion (E j)).card := card_biUnion_le
    _ ≤ ∑ j, ∑ k, (E j k).card := sum_le_sum (fun _ _ => card_biUnion_le)
    _ ≤ ∑ _ : J, ∑ _ : J, Fintype.card I ^ (Fintype.card J-1) * M :=
      sum_le_sum (fun j _ => sum_le_sum (fun k _ => hp j k))
    _ = _ := by simp [pow_two]; ring

end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Sampling
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.Coverage.ProjectionInput.incident_equiv _root_.OAI.MetricKMedian.Coverage.ProjectionInput.raw_edge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage.ProjectionSystem
open Finset

variable {U V I A B : Type} [Fintype U] [Fintype V] [Fintype I]
  [Fintype A] [Fintype B] [DecidableEq U] [DecidableEq V] [DecidableEq I]
  [DecidableEq A] [DecidableEq B]
variable (G : ProjectionSystem U V I A B)

variable (J : Type) [Fintype J] [DecidableEq J]

omit [Fintype U] [Fintype V] [Fintype I] [Fintype A] [Fintype B]
  [DecidableEq U] [DecidableEq V] [DecidableEq I] [DecidableEq A] [DecidableEq B]
  [Fintype J] [DecidableEq J] in
theorem sample_consistent (hdup : G.DuplicateConsistent) :
    (G.sample J).DuplicateConsistent := by
  intro p j k h a
  exact hdup p.1 (p.2 j) (p.2 k) h a

omit [Fintype U] [Fintype A] [Fintype B] [DecidableEq U] [DecidableEq V]
  [DecidableEq I] [DecidableEq A] [DecidableEq B] in
theorem sample_sum (f : U → ℕ) :
    (∑ p, ∑ j, f ((G.sample J).neighbor p j)) =
      Fintype.card J * Fintype.card I ^ (Fintype.card J-1) *
        ∑ v, ∑ i, f (G.neighbor v i) := by
  change (∑ p : V × (J → I), ∑ j, f (G.neighbor p.1 (p.2 j))) = _
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ v, ∑ j : J, ∑ s : J → I, f (G.neighbor v (s j)) := by
      apply sum_congr rfl
      intro v _
      rw [sum_comm]
    _ = ∑ v, ∑ _ : J, Fintype.card I ^ (Fintype.card J-1) * ∑ i, f (G.neighbor v i) := by
      apply sum_congr rfl
      intro v _
      apply sum_congr rfl
      intro j _
      exact coordinate_sum j (fun i => f (G.neighbor v i))
    _ = _ := by
      simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,← mul_assoc]
      rw [mul_sum]

omit [Fintype A] [Fintype B] [DecidableEq V] [DecidableEq I]
  [DecidableEq A] [DecidableEq B] in
theorem sample_regular {d : ℕ} (hreg : G.LeftRegular d) :
    (G.sample J).LeftRegular (Fintype.card J * Fintype.card I ^ (Fintype.card J-1) * d) := by
  intro u
  rw [card_filter,Fintype.sum_prod_type]
  rw [G.sample_sum J (fun x => if x = u then 1 else 0)]
  rw [G.regular_sum hreg (fun x => if x = u then 1 else 0)]
  simp

omit [Fintype U] [Fintype A] [Fintype B] [DecidableEq U] [DecidableEq V]
  [DecidableEq I] [DecidableEq A] in
theorem satisfied_card (left : U → A) (right : V → B) :
    (G.satisfied left right).card =
      ∑ v, (univ.filter (fun i => G.project v i (left (G.neighbor v i)) = right v)).card := by
  simp only [satisfied,card_filter,Fintype.sum_prod_type]

omit [Fintype U] [Fintype A] [Fintype B] [DecidableEq U] [DecidableEq V]
  [DecidableEq I] [DecidableEq A] in
theorem sample_agreement_card (left : U → A) :
    ((G.sample J).agreement left).card =
      ∑ v, (univ.filter (fun s : J → I => ∃ j k, j ≠ k ∧
        G.project v (s j) (left (G.neighbor v (s j))) =
        G.project v (s k) (left (G.neighbor v (s k))))).card := by
  change (univ.filter (fun p : V × (J → I) => ∃ j k, j ≠ k ∧
    G.project p.1 (p.2 j) (left (G.neighbor p.1 (p.2 j))) =
    G.project p.1 (p.2 k) (left (G.neighbor p.1 (p.2 k))))).card = _
  rw [card_filter,Fintype.sum_prod_type]
  simp only [card_filter]

omit [Fintype U] [Fintype A] [DecidableEq U] [DecidableEq V]
  [DecidableEq I] [DecidableEq A] in
theorem sample_agreement_bound [Nonempty B] (hJ : 0 < Fintype.card J) (ε : ℝ)
    (hsound : ∀ left right, ((G.satisfied left right).card:ℝ) ≤
      ε * Fintype.card V * Fintype.card I) (left : U → A) :
    (((G.sample J).agreement left).card:ℝ) ≤
      ((Fintype.card J:ℝ)^2 * ε) * Fintype.card (V × (J → I)) := by
  classical
  let color (v : V) (i : I) := G.project v i (left (G.neighbor v i))
  let count (v : V) (b : B) := (univ.filter (fun i => color v i = b)).card
  have hmax (v : V) : ∃ b : B, ∀ b', count v b' ≤ count v b := by
    obtain ⟨b,_,hb⟩ := exists_max_image univ (count v) univ_nonempty
    exact ⟨b,fun b' => hb b' (mem_univ b')⟩
  choose right hr using hmax
  have hs : (∑ v, (count v (right v):ℝ)) ≤ ε * Fintype.card V * Fintype.card I := by
    simpa only [G.satisfied_card left right,Nat.cast_sum] using hsound left right
  have hp (v : V) :
      ((univ.filter (fun s : J → I => ∃ j k, j ≠ k ∧ color v (s j) = color v (s k))).card:ℝ) ≤
        (Fintype.card J:ℝ)^2 * (Fintype.card I:ℝ)^(Fintype.card J-1) * count v (right v) := by
    exact_mod_cast sampled_agreement_count (J := J) (color v) (count v (right v)) (hr v)
  have hpow : (Fintype.card I:ℝ)^Fintype.card J =
      (Fintype.card I:ℝ)^(Fintype.card J-1) * Fintype.card I := by
    rw [← pow_succ,Nat.sub_add_cancel (by omega : 1 ≤ Fintype.card J)]
  rw [G.sample_agreement_card J left,Nat.cast_sum]
  calc
    _ ≤ ∑ v, (Fintype.card J:ℝ)^2 * (Fintype.card I:ℝ)^(Fintype.card J-1) * count v (right v) :=
      sum_le_sum (fun v _ => hp v)
    _ = (Fintype.card J:ℝ)^2 * (Fintype.card I:ℝ)^(Fintype.card J-1) *
        ∑ v, (count v (right v):ℝ) := by rw [mul_sum]
    _ ≤ (Fintype.card J:ℝ)^2 * (Fintype.card I:ℝ)^(Fintype.card J-1) *
        (ε * Fintype.card V * Fintype.card I) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by
      rw [Fintype.card_prod,Fintype.card_fun,Nat.cast_mul,Nat.cast_pow,hpow]
      ring

omit [DecidableEq V] [DecidableEq I] in
theorem sample_perfect (left : U → A) (right : V → B)
    (h : ∀ v i, G.project v i (left (G.neighbor v i)) = right v) :
    ∃ S : Finset (U × A), S.card ≤ Fintype.card U ∧ (G.sample J).covered S = univ := by
  exact (G.sample J).perfect_cover left (fun p => right p.1) (fun p j => h p.1 (p.2 j))

theorem sampled_coverage_bound [Nonempty B] {d : ℕ} (hreg : G.LeftRegular d)
    (hdup : G.DuplicateConsistent) (hJ : 1 < Fintype.card J)
    (S : Finset (U × A)) (hS : S.card ≤ Fintype.card U)
    {t : ℕ} (ht : 1 ≤ t) (default : A) (ε : ℝ)
    (hsound : ∀ left right, ((G.satisfied left right).card:ℝ) ≤
      ε * Fintype.card V * Fintype.card I) :
    (((G.sample J).covered S).card:ℝ) ≤
      (1-(1-1/(Fintype.card J:ℝ))^Fintype.card J+
        (Fintype.card J:ℝ)/t+(t:ℝ)^2*(Fintype.card J:ℝ)^2*ε) *
        ((Fintype.card (V × (J → I)):ℝ)*(Fintype.card J:ℝ)^Fintype.card B) := by
  have hc := (G.sample J).coverage_agreement_bound_s53 (G.sample_regular J hreg) hJ
    (G.sample_consistent J hdup) S hS ht default ((Fintype.card J:ℝ)^2*ε)
    (G.sample_agreement_bound J (by omega) ε hsound)
  convert hc using 1 <;> first | rfl | ring

end MetricKMedian.Coverage.ProjectionSystem

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_ProjectionInput
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Finset

namespace ProjectionSystem
variable {U V I A B : Type} [Fintype U] [Fintype V] [Fintype I]
  [Fintype A] [Fintype B] [DecidableEq U] [DecidableEq V] [DecidableEq I]
  [DecidableEq A] [DecidableEq B]
omit [Fintype U] [DecidableEq V] in
theorem covered_iff (H : ProjectionSystem U V I A B) (S : Finset (U × A))
    (v : V) (w : B → I) :
    (v,w) ∈ H.covered S ↔ ∃ i c, (H.neighbor v i,c) ∈ S ∧ w (H.project v i c) = i := by
  simp only [covered,mem_filter,mem_univ,true_and]
end ProjectionSystem

namespace ProjectionInput
variable {r a b : ℕ} (G : ProjectionInput r a b)

theorem covered_equiv (D : ℕ) (hD : 0 < D) (S : Finset (Fin G.u × Fin a)) :
    (G.toCoverage D hD).covered (S.image G.facilityEquiv) =
      ((G.system.sample (Fin D)).covered S).image (G.clientEquiv D) := by
  classical
  ext x
  obtain ⟨p,rfl⟩ := (G.clientEquiv D).surjective x
  constructor
  · intro hx
    obtain ⟨y,hy,hin⟩ := ((G.toCoverage D hD).mem_covered _ _).mp hx
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hy
    obtain ⟨j,hj,hw⟩ := (G.incident_equiv D hD p q).mp hin
    apply mem_image.mpr
    refine ⟨p,?_,rfl⟩
    apply ((G.system.sample (Fin D)).covered_iff S p.1 p.2).mpr
    refine ⟨j,q.2,?_,hw⟩
    change (G.system.neighbor p.1.1 (p.1.2 j),q.2) ∈ S
    simpa only [hj] using hq
  · intro hx
    obtain ⟨p',hp',he⟩ := mem_image.mp hx
    have hp : p' = p := (G.clientEquiv D).injective he
    subst p'
    obtain ⟨j,c,hc,hw⟩ := (show ∃ j c,
      (G.system.neighbor p.1.1 (p.1.2 j),c) ∈ S ∧
      p.2 (G.system.project p.1.1 (p.1.2 j) c) = j by
      exact ((G.system.sample (Fin D)).covered_iff S p.1 p.2).mp hp')
    apply ((G.toCoverage D hD).mem_covered _ _).mpr
    refine ⟨G.facilityEquiv (G.system.neighbor p.1.1 (p.1.2 j),c),
      mem_image.mpr ⟨_,hc,rfl⟩,?_⟩
    exact (G.incident_equiv D hD p _).mpr ⟨j,rfl,hw⟩

theorem coverage_perfect (D : ℕ) (hD : 0 < D) (h : G.Perfect) :
    (G.toCoverage D hD).Perfect := by
  classical
  obtain ⟨left,right,hh⟩ := h
  obtain ⟨S,hs,hcover⟩ := G.system.sample_perfect (Fin D) left right hh
  refine ⟨S.image G.facilityEquiv,?_,?_⟩
  · simpa only [card_image_of_injective _ G.facilityEquiv.injective,
      toCoverage,Fintype.card_fin] using hs
  · rw [G.covered_equiv D hD,hcover]
    exact image_univ_of_surjective (G.clientEquiv D).surjective

theorem coverage_sound {δ : ℝ} (P : PartitionParameters δ) (h : G.Sound P.ε) :
    (G.toCoverage P.D (by have := P.D_ge; omega)).Sound δ := by
  classical
  let : Nonempty (Fin b) := ⟨⟨0,G.b_pos⟩⟩
  intro T hT
  let S := T.image G.facilityEquiv.symm
  have hS : S.card ≤ Fintype.card (Fin G.u) := by
    simpa only [S,card_image_of_injective _ G.facilityEquiv.symm.injective,
      Fintype.card_fin,toCoverage] using hT
  have he : S.image G.facilityEquiv = T := by
    simp only [S,image_image,Function.comp_def,Equiv.apply_symm_apply,image_id']
  have hc := G.system.sampled_coverage_bound (Fin P.D) G.regular G.consistent
    (by simp only [Fintype.card_fin]; have := P.D_ge; omega) S hS P.t_pos ⟨0,G.a_pos⟩
    (P.ε : ℝ) (by simpa only [Sound,Fintype.card_fin] using h)
  have hcard : ((G.toCoverage P.D _).covered T).card =
      ((G.system.sample (Fin P.D)).covered S).card := by
    rw [← he,G.covered_equiv]
    exact card_image_of_injective _ (G.clientEquiv P.D).injective
  rw [hcard]
  have hmargin := le_of_lt P.margin
  have hw : (0 : ℝ) ≤ (G.v : ℝ) * (r : ℝ)^P.D * (P.D : ℝ)^b := by positivity
  have hmul := mul_le_mul_of_nonneg_right hmargin hw
  simp only [Fintype.card_fin,Fintype.card_prod,Fintype.card_fun,Nat.cast_mul,
    Nat.cast_pow] at hc
  change _ ≤ (1 - 1 / Real.exp 1 + δ) * ((G.v * width r b P.D : ℕ) : ℝ)
  simp only [width,Nat.cast_mul,Nat.cast_pow]
  nlinarith [hc,hmul]

end ProjectionInput
end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_ProjectionEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Binary Binary.Automatic Binary.Automatic.Poly

namespace ProjectionInput
variable {r a b : ℕ} (G : ProjectionInput r a b)

theorem coverage_finite_poly (D : ℕ) (hD : 0 < D) :
    Complexity.FinitePolyTime (encode (r:=r) (a:=a) (b:=b)) Input.encode
      (fun G => G.toCoverage D hD) :=
  ⟨coverageProgram D hD |>.stock,coverageProgram D hD |>.finite_work⟩

end ProjectionInput
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

theorem reduction_from_projections_s53_oai {δ : ℝ} (P : PartitionParameters δ)
    {L : Language} (h : ProjectionReduction P.ε L) :
    ∃ reduce : Word → Input, FinitePolyTime id Input.encode reduce ∧
      (∀ x, x ∈ L → (reduce x).Perfect) ∧
      (∀ x, x ∉ L → (reduce x).Sound δ) := by
  obtain ⟨r,a,b,f,hf,hy,hn⟩ := h
  have hD : 0 < P.D := by have := P.D_ge; omega
  let g : ProjectionInput r a b → Input := fun G => G.toCoverage P.D hD
  refine ⟨g ∘ f,hf.comp (ProjectionInput.coverage_finite_poly P.D hD),?_,?_⟩
  · intro x hx
    exact (f x).coverage_perfect P.D hD (hy x hx)
  · intro x hx
    exact (f x).coverage_sound P (hn x hx)

end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Coverage.reduction_from_projections_s53_oai := @OAI.MetricKMedian.Coverage.reduction_from_projections_s53_oai
