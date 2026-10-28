-- Prove2me | solution 1 for OAI.MetricKMedian.RationalPhysicalKernel.graph_data_all
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T08:54:43.812095+00:00
-- url     : https://prove2.me/submissions/35ea3558-3227-486b-a464-2dac9592c4ff

import Mathlib
import Definitions.Def_OAIQ035K045
import Definitions.Def_OAIQ035K064
import Definitions.Def_OAIQ035K070

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CopyRound
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

end MetricKMedian.SparseEnumeratedGraph
end
end

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

end MetricKMedian.SparseEnumeratedGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalPhysicalInvariant
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
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalHistoryValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential
variable {F J X : Type} [LinearOrder F] [Fintype F] [Fintype J] [DecidableEq J]
  [PseudoMetricSpace X] {Δ : ℕ}

attribute [local instance] OAI.MetricKMedian.RationalPhysicalKernel.rationalHistoryValidCopyOrder
omit [Fintype F] [Fintype J] [DecidableEq J] in

theorem graph_data_all_oai (d : F → F → ℚ) (location : F → X)
    (hd : ∀ i j, dist (location i) (location j)=(d i j:ℝ))
    (g P : ℚ) (A : Finset (CopyState.Copy (F := F) Δ))
    (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2) (hA : 1 ≤ mass (g:ℝ) A) :
    ∃ D : Taper.GraphData Δ (g:ℝ) (P:ℝ) (fun i : A => location i.val.1) (CopyState.own Δ A),
      ∀ a : Fin (graphLaw d g P A).length, D.Good (graphLaw d g P A).states[a.val] := by
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
  let q := fun h i : A => Taper.sourceMarginals g P (dA i) (own A i) Δ h
  have hall := fun i => Taper.rational_data g P (dA i) (own A i) Δ hg hunit hP hP1
    (hd0 i) htotal (hown i) (own_card A i)
  have hq : ∀ h i, 0 ≤ q h i ∧ q h i ≤ 1 := fun h i => ⟨(hall i).2.1 h,(hall i).2.2.1 h⟩
  have hs : ∀ i, (∑ h : Fin A.card, q (enumeration A h) i)=(Δ:ℚ) := by
    intro i
    rw [(enumeration A).sum_comp (fun h => q h i)]
    exact (hall i).2.2.2.2.1
  refine ⟨D,fun a => ⟨?_,?_,?_⟩⟩
  · exact SparseEnumeratedGraph.columns_card (enumeration A) q Δ hq hs a
  · intro i h he
    exact (SparseEnumeratedGraph.fixed (enumeration A) q Δ hq hs a h i).1
      ((hall i).2.2.2.2.2.1 h he)
  · intro h i hedge
    change (0:ℝ)<(q h i:ℝ)
    have hn : q h i≠0 := fun he =>
      (SparseEnumeratedGraph.fixed (enumeration A) q Δ hq hs a h i).2 he hedge
    exact_mod_cast lt_of_le_of_ne (hq h i).1 (Ne.symm hn)

end MetricKMedian.RationalPhysicalKernel
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.RationalPhysicalKernel.graph_data_all_oai := @OAI.MetricKMedian.RationalPhysicalKernel.graph_data_all_oai
