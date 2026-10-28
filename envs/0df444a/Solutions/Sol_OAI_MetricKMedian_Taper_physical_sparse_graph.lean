-- Prove2me | solution 1 for OAI.MetricKMedian.Taper.physical_sparse_graph
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T08:55:06.386061+00:00
-- url     : https://prove2.me/submissions/64cdf278-bc65-4ec5-88e5-a3bf31f29ad2

import Mathlib
import Definitions.Def_OAIQ035K045
import Definitions.Def_OAIQ035K064
import Definitions.Def_OAIQ035K070

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseCardinalRounding
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
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseGraphLaw
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
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseEnumeratedGraph
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
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseRealLaw
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
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseEnumeratedGraphReal
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
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalPhysicalGraph
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

theorem physical_sparse_graph_oai (enum : Fin n ≃ I) (Δ : ℕ) (g P : ℚ)
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

theorem solution.{u_1} : type_of% @OAI.MetricKMedian.Taper.physical_sparse_graph_oai.{u_1} := @OAI.MetricKMedian.Taper.physical_sparse_graph_oai.{u_1}
