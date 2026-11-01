-- Prove2me | solution 1 for OAI.MetricKMedian.RationalPhysicalKernel.graph_data_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:38:29.493384+00:00
-- url     : https://prove2.me/submissions/acb9ff8d-21b1-4682-8113-4b3722034b0b

import Mathlib
import Definitions.Def_OAIQ053K060
import Definitions.Def_OAIQ053K061

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CopyRound
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset FixedBatch
variable {F : Type*} [DecidableEq F] [Fintype F] (Δ : ℕ)

omit [Fintype F] in
 theorem own_card_le (A : Finset (Copy (F := F) Δ)) (i : A) : (own Δ A i).card ≤ Δ := by
  have hc : (own Δ A i).image Subtype.val ⊆ slots Δ i.val.1 := by
    rintro h hh
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hh
    exact (mem_slots _ _ _).mpr ((mem_own _ _ _ _).mp ht)
  have hh := card_le_card hc
  rw [card_image_of_injective _ Subtype.val_injective,card_slots] at hh
  exact hh

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseCardinalRounding
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.RationalSignedTerminal.point_state _root_.OAI.MetricKMedian.SparseTargetSubset.point_initial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseCardinalRounding
open Finset RationalWeightedStep
variable {n : ℕ}

theorem selected_card (q : Vector ℚ n)
    (hq : ∀ i, point q i=0 ∨ point q i=1) (K : ℕ)
    (hs : (∑ i, point q i)=(K:ℚ)) : (selected q).card=K := by
  have he : ((selected q).card:ℚ)=(K:ℚ) := by
    calc
      _ = ∑ i, if i ∈ selected q then (1:ℚ) else 0 := by simp
      _ = ∑ i, point q i := sum_congr rfl (fun i _ => selected_indicator q hq i)
      _ = _ := hs
  exact_mod_cast he

end MetricKMedian.SparseCardinalRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseGraphLaw
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.RationalLaw.real_expect _root_.OAI.MetricKMedian.SparseEnumeratedGraph.mem_lift _root_.OAI.MetricKMedian.SparseGraph.cast_edge _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseGraph
open Finset
variable {n m : ℕ}

theorem columns_moment (q : Fin n → Fin m → ℚ) (Δ : ℕ)
    (hq : ∀ h i, 0 ≤ q h i ∧ q h i ≤ 1) (hs : ∀ i, (∑ h, q h i)=(Δ:ℚ))
    (h : Fin n) (i : Fin m) : (columns q i).moment (fun S => if h∈S then 1 else 0)=q h i := by
  rw [columns,SparseIntegerLaw.map_moment]
  calc
    _ = (SparseCardinalRounding.round (Vector.ofFn (fun h => q h i))).moment
        (fun p => RationalWeightedStep.point p h) := by
      apply SparseIntegerLaw.moment_congr
      intro a
      have hh := SparseCardinalRounding.round_invariants (Vector.ofFn (fun h => q h i))
        (fun h => by simpa only [RationalWeightedStep.point,Vector.getElem_ofFn] using hq h i)
        Δ (by simpa only [RationalWeightedStep.point,Vector.getElem_ofFn] using hs i) a
      exact SparseCardinalRounding.selected_indicator _ hh.1 h
    _ = _ := by rw [SparseCardinalRounding.round_mean]; simp only [RationalWeightedStep.point,Vector.getElem_ofFn]

theorem columns_card (q : Fin n → Fin m → ℚ) (Δ : ℕ)
    (hq : ∀ h i, 0 ≤ q h i ∧ q h i ≤ 1) (hs : ∀ i, (∑ h, q h i)=(Δ:ℚ))
    (i : Fin m) (a : Fin (columns q i).length) : ((columns q i).states[a.val]).card=Δ := by
  change Fin (SparseCardinalRounding.round (Vector.ofFn (fun h => q h i))).length at a
  have he := SparseIntegerLaw.map_states (SparseCardinalRounding.round
    (Vector.ofFn (fun h => q h i))) SparseCardinalRounding.selected a
  change (columns q i).states[a.val]=_ at he
  rw [he]
  have hh := SparseCardinalRounding.round_invariants (Vector.ofFn (fun h => q h i))
    (fun h => by simpa only [RationalWeightedStep.point,Vector.getElem_ofFn] using hq h i)
    Δ (by simpa only [RationalWeightedStep.point,Vector.getElem_ofFn] using hs i) a
  exact SparseCardinalRounding.selected_card _ hh.1 Δ hh.2

theorem law_spec (q : Fin n → Fin m → ℚ) (Δ : ℕ)
    (hq : ∀ h i, 0 ≤ q h i ∧ q h i ≤ 1) (hs : ∀ i, (∑ h, q h i)=(Δ:ℚ)) :
    (law q).length ≤ n*m+(n*m)*(n*m)+1 ∧
    (∀ a : Fin (law q).length, ∀ i, ((law q).states[a.val] i).card=Δ) ∧
    (∀ h i, (law q).moment (fun G => edge G h i)=q h i) ∧
    (∀ h l i j, i≠j → (law q).moment (fun G => edge G h i*edge G l j)=q h i*q l j) := by
  refine ⟨run_length (columns q) m,?_,?_,?_⟩
  · intro a i
    exact run_columns (columns q) (fun _ S => S.card=Δ) (columns_card q Δ hq hs) m
      (le_refl m) a i i.isLt
  · intro h i
    have hh := run_single (columns q) q (columns_moment q Δ hq hs) m (le_refl m) h i
    simpa only [law,target,i.isLt,ite_eq_left] using hh
  · intro h l i j hij
    have hh := run_pair (columns q) q (columns_moment q Δ hq hs) m (le_refl m) h l i j hij
    simpa only [law,target,i.isLt,j.isLt,ite_eq_left] using hh

theorem run_positive (ν : Fin m → SparseIntegerLaw (Finset (Fin n))) (t : ℕ) :
    ∀ a : Fin (run ν t).length, 0 < (run ν t).law.rational.weight a := by
  induction t with
  | zero => intro a; change 0 < ((1:ℤ):ℚ)/1; norm_num
  | succ t ih =>
    let inv : SparseIntegerLaw (Graph n m) → Prop := fun μ =>
      ∀ a : Fin μ.length, 0 < μ.law.rational.weight a
    change inv (run ν (t+1))
    by_cases ht : t < m
    · rw [run,dite_eq_left ht]
      intro a
      exact ((run ν t).prod (ν ⟨t,ht⟩) (fun G S => next G S ⟨t,ht⟩)).compressAuto_positive features a
    · rw [run,dite_eq_right ht]
      exact ih

theorem law_fixed (q : Fin n → Fin m → ℚ) (Δ : ℕ)
    (hq : ∀ h i, 0 ≤ q h i ∧ q h i ≤ 1) (hs : ∀ i, (∑ h, q h i)=(Δ:ℚ))
    (a : Fin (law q).length) (h : Fin n) (i : Fin m) :
    (q h i=1 → h∈(law q).states[a.val] i) ∧
    (q h i=0 → h∉(law q).states[a.val] i) := by
  have hh := (law_spec q Δ hq hs).2.2.1 h i
  have hp := run_positive (columns q) m a
  constructor
  · intro he
    exact (law q).one_indicator (fun G => h∈G i) (hh.trans he) a hp
  · intro he
    exact (law q).zero_indicator (fun G => h∈G i) (hh.trans he) a hp

end MetricKMedian.SparseGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseEnumeratedGraph
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseEnumeratedGraph
open Finset
variable {I : Type} [DecidableEq I] {n : ℕ}

omit [DecidableEq I] in
theorem length (enum : Fin n ≃ I) (q : I → I → ℚ) (Δ : ℕ)
    (hq : ∀ h i, 0 ≤ q h i ∧ q h i ≤ 1)
    (hs : ∀ i, (∑ h : Fin n, q (enum h) i)=(Δ:ℚ)) :
    (law enum q).length ≤ n*n+(n*n)*(n*n)+1 :=
  (SparseGraph.law_spec (fun h i => q (enum h) (enum i)) Δ
    (fun h i => hq (enum h) (enum i)) (fun i => hs (enum i))).1

omit [DecidableEq I] in
theorem columns_card (enum : Fin n ≃ I) (q : I → I → ℚ) (Δ : ℕ)
    (hq : ∀ h i, 0 ≤ q h i ∧ q h i ≤ 1)
    (hs : ∀ i, (∑ h : Fin n, q (enum h) i)=(Δ:ℚ))
    (a : Fin (law enum q).length) (i : I) :
    ((law enum q).states[a.val] i).card=Δ := by
  have he := SparseIntegerLaw.map_states (SparseGraph.law (fun h i => q (enum h) (enum i))) (lift enum) a
  change (law enum q).states[a.val]=_ at he
  rw [he]
  rw [lift,card_map]
  exact (SparseGraph.law_spec (fun h i => q (enum h) (enum i)) Δ
    (fun h i => hq (enum h) (enum i)) (fun i => hs (enum i))).2.1 a _

theorem single (enum : Fin n ≃ I) (q : I → I → ℚ) (Δ : ℕ)
    (hq : ∀ h i, 0 ≤ q h i ∧ q h i ≤ 1)
    (hs : ∀ i, (∑ h : Fin n, q (enum h) i)=(Δ:ℚ)) (h i : I) :
    (law enum q).moment (fun G => if h∈G i then 1 else 0)=q h i := by
  rw [law,SparseIntegerLaw.map_moment]
  simp only [mem_lift]
  have hh := (SparseGraph.law_spec (fun h i => q (enum h) (enum i)) Δ
    (fun h i => hq (enum h) (enum i)) (fun i => hs (enum i))).2.2.1 (enum.symm h) (enum.symm i)
  simpa only [SparseGraph.edge,Equiv.apply_symm_apply] using hh

theorem pair (enum : Fin n ≃ I) (q : I → I → ℚ) (Δ : ℕ)
    (hq : ∀ h i, 0 ≤ q h i ∧ q h i ≤ 1)
    (hs : ∀ i, (∑ h : Fin n, q (enum h) i)=(Δ:ℚ)) (h l i j : I) (hij : i≠j) :
    (law enum q).moment (fun G => (if h∈G i then 1 else 0)*(if l∈G j then 1 else 0))=q h i*q l j := by
  rw [law,SparseIntegerLaw.map_moment]
  simp only [mem_lift]
  have hh := (SparseGraph.law_spec (fun h i => q (enum h) (enum i)) Δ
    (fun h i => hq (enum h) (enum i)) (fun i => hs (enum i))).2.2.2 (enum.symm h) (enum.symm l)
      (enum.symm i) (enum.symm j) (fun he => hij (enum.symm.injective he))
  simpa only [SparseGraph.edge,Equiv.apply_symm_apply] using hh

end MetricKMedian.SparseEnumeratedGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseRealLaw
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian

namespace SparseIntegerLaw
variable {α : Type}

theorem real_property [Fintype α] [DecidableEq α] (μ : SparseIntegerLaw α) (P : α → Prop)
    (hP : ∀ i : Fin μ.length, P μ.states[i.val]) : ∀ a, 0 < μ.real.weight a → P a := by
  exact μ.realIndex.property_map (fun i => μ.states[i.val]) P (fun i _ => hP i)

end SparseIntegerLaw
end MetricKMedian

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseEnumeratedGraphReal
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.SparseGraph.cast_edge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseEnumeratedGraph
open Finset
variable {I : Type} [DecidableEq I] [Fintype I] {n : ℕ}

omit [Fintype I] [DecidableEq I] in
theorem fixed (enum : Fin n ≃ I) (q : I → I → ℚ) (Δ : ℕ)
    (hq : ∀ h i, 0 ≤ q h i ∧ q h i ≤ 1)
    (hs : ∀ i, (∑ h : Fin n, q (enum h) i)=(Δ:ℚ))
    (a : Fin (law enum q).length) (h i : I) :
    (q h i=1 → h∈(law enum q).states[a.val] i) ∧
    (q h i=0 → h∉(law enum q).states[a.val] i) := by
  have he := SparseIntegerLaw.map_states (SparseGraph.law (fun h i => q (enum h) (enum i))) (lift enum) a
  change (law enum q).states[a.val]=_ at he
  rw [he]
  simp only [mem_lift]
  have hh := SparseGraph.law_fixed (fun h i => q (enum h) (enum i)) Δ
    (fun h i => hq (enum h) (enum i)) (fun i => hs (enum i)) a (enum.symm h) (enum.symm i)
  simpa only [Equiv.apply_symm_apply] using hh

theorem real_spec (enum : Fin n ≃ I) (q : I → I → ℚ) (Δ : ℕ)
    (hq : ∀ h i, 0 ≤ q h i ∧ q h i ≤ 1)
    (hs : ∀ i, (∑ h : Fin n, q (enum h) i)=(Δ:ℚ)) :
    (∀ G, 0 < (law enum q).real.weight G → ∀ i, (G i).card=Δ) ∧
    (∀ h i, (law enum q).real.expect (fun G => GraphLaw.edge G h i)=(q h i:ℝ)) ∧
    (∀ h l i j, i≠j → (law enum q).real.expect (fun G => GraphLaw.edge G h i*GraphLaw.edge G l j)=
      (q h i:ℝ)*(q l j:ℝ)) ∧
    (∀ G, 0 < (law enum q).real.weight G → ∀ h i, q h i=1 → h∈G i) ∧
    (∀ G, 0 < (law enum q).real.weight G → ∀ h i, q h i=0 → h∉G i) := by
  refine ⟨(law enum q).real_property _ (columns_card enum q Δ hq hs),?_,?_,?_,?_⟩
  · intro h i
    have he : (fun G : I → Finset I => GraphLaw.edge G h i)=
        (fun G => ((if h∈G i then 1 else 0:ℚ):ℝ)) := by
      funext G
      by_cases hh : h∈G i <;> simp [GraphLaw.edge,hh]
    rw [he,SparseIntegerLaw.real_expect,single enum q Δ hq hs]
  · intro h l i j hij
    have he : (fun G : I → Finset I => GraphLaw.edge G h i*GraphLaw.edge G l j)=
        (fun G => (((if h∈G i then 1 else 0)*(if l∈G j then 1 else 0):ℚ):ℝ)) := by
      funext G
      by_cases hh : h∈G i <;> by_cases hl : l∈G j <;> simp [GraphLaw.edge,hh,hl]
    rw [he,SparseIntegerLaw.real_expect,pair enum q Δ hq hs h l i j hij,Rat.cast_mul]
  · exact (law enum q).real_property _ (fun a h i => (fixed enum q Δ hq hs a h i).1)
  · exact (law enum q).real_property _ (fun a h i => (fixed enum q Δ hq hs a h i).2)

end MetricKMedian.SparseEnumeratedGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalPhysicalGraph
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset
variable {I : Type} [LinearOrder I] [Fintype I] {n : ℕ} {X : Type*} [PseudoMetricSpace X]

theorem physical_sparse_graph (enum : Fin n ≃ I) (Δ : ℕ) (g P : ℚ)
    (d : I → I → ℚ) (location : I → X) (own : I → Finset I)
    (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2)
    (hd : ∀ i h, 0 ≤ d i h) (hdist : ∀ i h, dist (location i) (location h)=(d i h:ℝ))
    (htotal : 1 ≤ ∑ _i : I, (g:ℝ))
    (hown : ∀ i h, h∈own i → d i h=0) (howncard : ∀ i, (own i).card ≤ Δ) :
    let D := physicalGraphData Δ g P d location own hg hunit hP hP1 hd hdist htotal hown howncard
    let q := fun h i => sourceMarginals g P (d i) (own i) Δ h
    let μ := SparseEnumeratedGraph.law enum q
    μ.length ≤ n*n+(n*n)*(n*n)+1 ∧
      (∀ G, 0 < μ.real.weight G → D.Good G) ∧
      (∀ h i, μ.real.expect (fun G => GraphLaw.edge G h i)=D.marginal h i) ∧
      (∀ h l i j, i≠j → μ.real.expect (fun G => GraphLaw.edge G h i*GraphLaw.edge G l j)=
        D.marginal h i*D.marginal l j) := by
  dsimp only
  let q := fun h i => sourceMarginals g P (d i) (own i) Δ h
  have hall := fun i => rational_data g P (d i) (own i) Δ hg hunit hP hP1 (hd i) htotal (hown i) (howncard i)
  have hq : ∀ h i, 0 ≤ q h i ∧ q h i ≤ 1 := fun h i => ⟨(hall i).2.1 h,(hall i).2.2.1 h⟩
  have hs : ∀ i, (∑ h : Fin n, q (enum h) i)=(Δ:ℚ) := by
    intro i
    rw [enum.sum_comp (fun h => q h i)]
    exact (hall i).2.2.2.2.1
  have hh := SparseEnumeratedGraph.real_spec enum q Δ hq hs
  refine ⟨SparseEnumeratedGraph.length enum q Δ hq hs,?_,hh.2.1,hh.2.2.1⟩
  intro G hG
  refine ⟨hh.1 G hG,?_,?_⟩
  · intro i h he
    exact hh.2.2.2.1 G hG h i ((hall i).2.2.2.2.2.1 h he)
  · intro h i hedge
    change (0:ℝ) < (q h i:ℝ)
    have hn : q h i≠0 := fun he => hh.2.2.2.2 G hG h i he hedge
    exact_mod_cast lt_of_le_of_ne (hq h i).1 (Ne.symm hn)

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalPhysicalInvariant
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential
variable {F : Type} [LinearOrder F] [Fintype F] {Δ : ℕ}

omit [Fintype F] in
                                                                        
theorem own_card (A : Finset (CopyState.Copy (F := F) Δ)) (i : A) :
    (own A i).card ≤ Δ := by
  exact CopyState.own_card_le Δ A i

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalPhysicalGraphInstance
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {Δ : ℕ}

attribute [local instance] OAI.MetricKMedian.RationalPhysicalKernel.instLinearOrderCopy_1
omit [Fintype F] in

theorem graph_data_s53_oai (d : F → F → ℚ) (location : F → X)
    (hd : ∀ i j, dist (location i) (location j)=(d i j:ℝ))
    (g P : ℚ) (A : Finset (CopyState.Copy (F := F) Δ))
    (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2) (hA : 1 ≤ mass (g:ℝ) A) :
    ∃ D : Taper.GraphData Δ (g:ℝ) (P:ℝ) (fun i : A => location i.val.1) (CopyState.own Δ A),
      (∀ G, 0 < (graphLaw d g P A).real.weight G → D.Good G) ∧
      (∀ h i, (graphLaw d g P A).real.expect (fun G => GraphLaw.edge G h i)=D.marginal h i) ∧
      (∀ h l i j, i≠j → (graphLaw d g P A).real.expect
        (fun G => GraphLaw.edge G h i*GraphLaw.edge G l j)=D.marginal h i*D.marginal l j) := by
  let dA : A → A → ℚ := fun i j => d i.val.1 j.val.1
  have hd0 : ∀ i j, 0 ≤ dA i j := by
    intro i j
    have hh : 0 ≤ (dA i j:ℝ) := by rw [← hd]; exact dist_nonneg
    exact_mod_cast hh
  have hown : ∀ i j, j∈own A i → dA i j=0 := by
    intro i j hj
    have he : j.val.1=i.val.1 := (mem_filter.mp hj).2
    have hh : (dA i j:ℝ)=0 := by rw [← hd,he,dist_self]
    exact_mod_cast hh
  have htotal : 1 ≤ ∑ _i : A, (g:ℝ) := by
    simpa only [sum_const,card_univ,Fintype.card_coe,nsmul_eq_mul,mass,mul_comm] using hA
  let D := Taper.physicalGraphData Δ g P dA (fun i : A => location i.val.1) (own A)
    hg hunit hP hP1 hd0 (fun i j => hd _ _) htotal hown (own_card A)
  have hh := Taper.physical_sparse_graph (enumeration A) Δ g P dA
    (fun i : A => location i.val.1) (own A) hg hunit hP hP1 hd0
      (fun i j => hd _ _) htotal hown (own_card A)
  exact ⟨D,hh.2⟩

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.RationalPhysicalKernel.graph_data_s53_oai := @OAI.MetricKMedian.RationalPhysicalKernel.graph_data_s53_oai
