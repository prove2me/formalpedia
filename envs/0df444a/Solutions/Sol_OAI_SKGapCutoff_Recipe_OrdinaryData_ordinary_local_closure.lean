-- Prove2me | solution 1 for OAI.SKGapCutoff.Recipe.OrdinaryData.ordinary_local_closure
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:56:43.995248+00:00
-- url     : https://prove2.me/submissions/4b783d8c-db1a-49e1-8b84-8668405c5506

import Mathlib
import Definitions.Def_OAIQ072A002

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_Spin
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped BigOperators

namespace SKGapCutoff

theorem halfDiff_mul {n : ℕ} (i : Fin n) (f g : Spin n → ℝ) (x : Spin n) :
    halfDiff i (fun y => f y * g y) x =
      f x * halfDiff i g x + g x * halfDiff i f x -
        2 * spin x i * halfDiff i f x * halfDiff i g x := by
  have hx : replace x i (x i) = x := replace_self x i
  cases h : x i <;> simp only [h] at hx
  · simp only [halfDiff, spin, h, Bool.false_eq_true, ↓reduceIte]
    rw [hx]
    ring
  · simp only [halfDiff, spin, h, ↓reduceIte]
    rw [hx]
    ring

theorem halfDiff_sub {n : ℕ} (i : Fin n) (f g : Spin n → ℝ) (x : Spin n) :
    halfDiff i (fun y => f y - g y) x = halfDiff i f x - halfDiff i g x := by
  simp only [halfDiff]
  ring

theorem halfDiff_sum {n : ℕ} {α : Type*} [Fintype α] (i : Fin n)
    (f : α → Spin n → ℝ) (x : Spin n) :
    halfDiff i (fun y => ∑ a, f a y) x = ∑ a, halfDiff i (f a) x := by
  simp only [halfDiff, sub_div, Finset.sum_sub_distrib, Finset.sum_div]

end SKGapCutoff
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_SquaredGaussianFourth
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
namespace SKGapCutoff.RandomMatrix

lemma matrix_opNorm_sq_le_frobenius {n : ℕ} (A : Interaction n) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖^2 ≤ ∑ i, ∑ j, A i j^2 := by
  let S := ∑ i, ∑ j, A i j^2
  have hS : 0 ≤ S := by unfold S; positivity
  have hN : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖ ≤ Real.sqrt S := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro x
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ Real.sqrt S * ‖x‖)).mp
    rw [mul_pow, Real.sq_sqrt hS]
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    change ∑ i, (∑ j, A i j*x j)^2 ≤ S * ∑ j, x j^2
    calc
      _ ≤ ∑ i, (∑ j, A i j^2)*(∑ j, x j^2) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A i) x)
      _ = _ := by rw [← Finset.sum_mul]
  exact (pow_le_pow_left₀ (norm_nonneg _) hN 2).trans_eq (Real.sq_sqrt hS)

end SKGapCutoff.RandomMatrix

open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_SeparateCut
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap.Noncrossing
universe u v
namespace Diagram
variable {D : Type*}

section Value
variable {ι : Type*} [Fintype ι]

lemma mean_const_mul (c : ℝ) (a : ι→ℝ) :
    mean (fun i => c*a i) = c*mean a := by
  simp only [mean,← Finset.mul_sum,mul_div_assoc]

end Value

end Diagram
end SKGap.Noncrossing

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_InverseDiagram
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing

namespace InverseDiagram

lemma nodup_arch_list (U V : List InverseDiagram) (hU : U.Nodup) (hV : V.Nodup) :
    (U.flatMap fun u => V.map (fun v => InverseDiagram.arch u v)).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro u _
    exact (List.nodup_map_iff (fun v w h => (InverseDiagram.arch.inj h).2)).mpr hV
  · apply List.Pairwise.imp (fun {u v} huv => ?_) hU
    apply List.disjoint_left.mpr
    intro t htU htV
    obtain ⟨u', -, hu'⟩ := List.mem_map.mp htU
    obtain ⟨v', -, hv'⟩ := List.mem_map.mp htV
    exact huv (InverseDiagram.arch.inj (hu'.trans hv'.symm)).1

theorem enumerate_nodup (n : ℕ) : (enumerate n).Nodup := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [enumerate]
    | succ n =>
      rw [enumerate, List.nodup_append]
      refine ⟨?_, ?_, ?_⟩
      · exact (List.nodup_map_iff (fun u v h => InverseDiagram.counterterm.inj h)).mpr
          (ih n (by omega))
      · apply List.nodup_flatMap.mpr
        constructor
        · intro k _
          exact nodup_arch_list _ _ (ih k.val k.isLt) (ih (n-k.val) (by omega))
        · apply List.Pairwise.imp (fun {k l} hkl => ?_) (List.nodup_finRange (n+1))
          apply List.disjoint_left.mpr
          intro t htK htL
          simp only [List.mem_flatMap, List.mem_map] at htK htL
          obtain ⟨u, hu, v, -, he⟩ := htK
          obtain ⟨u', hu', v', -, he'⟩ := htL
          have huu : u = u' := (InverseDiagram.arch.inj (he.trans he'.symm)).1
          have hk := (mem_enumerate u k.val).mp hu
          have hl := (mem_enumerate u' l.val).mp hu'
          apply hkl
          apply Fin.ext
          exact hk.symm.trans ((congrArg degree huu).trans hl)
      · intro t ht1 s ht2 he
        subst s
        obtain ⟨u, -, hu⟩ := List.mem_map.mp ht1
        simp only [List.mem_flatMap, List.mem_map] at ht2
        obtain ⟨k, -, a, -, b, -, ht⟩ := ht2
        cases hu.trans ht.symm

variable {ι : Type*} [Fintype ι]

lemma average_add (x y : ι → ℝ) : average (x+y) = average x + average y := by
  simp [average, Finset.sum_add_distrib, add_div]

lemma average_list_sum {α : Type*} (l : List α) (f : α → ι → ℝ) :
    average (fun i => (l.map (fun u => f u i)).sum) =
      (l.map (fun u => average (f u))).sum := by
  induction l with
  | nil => simp [average]
  | cons u l ih =>
    simp only [List.map_cons, List.sum_cons]
    change average (f u + fun i => (l.map (fun v => f v i)).sum) = _
    rw [average_add, ih]

lemma sum_flatMap {α : Type*} {R : Type*} [AddMonoid R]
    (l : List α) (f : α → List R) : (l.flatMap f).sum = (l.map (fun x => (f x).sum)).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.flatMap_cons, List.sum_append, List.map_cons, List.sum_cons, ih]

lemma sum_arch (j : ℝ) (a : ι → ℝ) (U V : List InverseDiagram) (i : ι) :
    ((U.flatMap fun u => V.map (fun v => .arch u v)).map (fun d => value j a d i)).sum =
      j * a i * average (fun k => a k * (U.map (fun u => value j a u k)).sum) *
        (V.map (fun v => value j a v i)).sum := by
  simp only [List.map_flatMap, List.map_map, Function.comp_def, sum_flatMap, value,
    List.sum_map_mul_left]
  rw [List.sum_map_mul_right, List.sum_map_mul_left]
  congr 2
  rw [← average_list_sum]
  congr 1
  funext k
  exact List.sum_map_mul_left U (fun u => value j a u k) (a k)

lemma coefficient_succ (j : ℝ) (a : ι → ℝ) (n : ℕ) (i : ι) :
    coefficient j a (n+1) i = -(j * average a) * a i * coefficient j a n i +
      ∑ k : Fin (n+1), j * a i * average (fun u => a u * coefficient j a k.val u) *
        coefficient j a (n-k.val) i := by
  rw [coefficient, enumerate]
  simp only [List.map_append, List.sum_append, List.map_map, Function.comp_def,
    value, List.sum_map_mul_left, List.map_flatMap, sum_flatMap]
  rw [Fin.sum_univ_def]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro k _
  simpa only [List.map_flatMap, List.map_map, Function.comp_def, sum_flatMap,
    value, List.sum_map_mul_left, coefficient] using
      sum_arch j a (enumerate k.val) (enumerate (n-k.val)) i

theorem coefficient_positive (j : ℝ) (a : ι → ℝ) (n : ℕ) (hn : 0 < n) (i : ι) :
    coefficient j a n i = 0 := by
  induction n using Nat.strong_induction_on generalizing i with
  | h n ih =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    rw [coefficient_succ]
    have hs : (∑ k : Fin (n+1), j * a i * average (fun u => a u * coefficient j a k.val u) *
        coefficient j a (n-k.val) i) = j * a i * average a * coefficient j a n i := by
      rw [Finset.sum_eq_single (0 : Fin (n+1))]
      · simp
      · intro k _ hk
        have hk0 : 0 < k.val := by have hne : k.val ≠ 0 := fun he => hk (Fin.ext he); omega
        have hz (u : ι) : coefficient j a k.val u = 0 := ih k.val k.isLt hk0 u
        simp [hz, average]
      · simp
    rw [hs]
    ring

end InverseDiagram
end SKGap.Noncrossing

end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Append
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section

noncomputable section
namespace SKGap.Noncrossing
namespace Diagram
variable {D : Type*}

lemma value_append {ι : Type*} [Fintype ι] (j : ℝ) (d e : Diagram (ι→ℝ)) (i : ι) :
    (d.append e).value j i = d.value j i * e.value j i := by
  induction d with
  | nil => simp [append,value]
  | diag a d ih => simp [append,value,ih,mul_assoc]
  | arch a b ia ib => simp [append,value,ib,mul_assoc]

end Diagram
end SKGap.Noncrossing

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_BlockDegree
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.Noncrossing.Diagram.noiseSplitFinite _root_.OAI.SKGap.Noncrossing.Diagram.noiseSplitFintype _root_.OAI.SKGap.Noncrossing.Diagram.pairedNilUnique _root_.OAI.SKGap.Noncrossing.Primary.Tensor.Loop.blocksOneUnique _root_.OAI.SKGap.Noncrossing.WordSeries.blocksZeroUnique _root_.OAI.SKGap.Noncrossing.WordSeries.noiseSplitNilIsEmpty _root_.OAI.SKGap.Noncrossing.noiseSplitDiagIsEmpty _root_.OAI.SKGap.Noncrossing.noiseSplitNoiseUnique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
namespace InverseDiagram

lemma literal_odd_empty (n : ℕ) : IsEmpty (LiteralPaired (2*n+1)) := by
  constructor
  intro z
  obtain ⟨e,he,hed⟩ := toDiagram_surjective z.2.val z.1.val z.2.property
  have hh := e.blocks_degree
  rw [he] at hh
  change blockDegree z.1.val=2*e.degree at hh
  rw [z.1.property] at hh
  omega

variable {ι : Type*} [Fintype ι]

lemma toDiagram_value (j : ℝ) (a : ι→ℝ) (d : InverseDiagram) (i : ι) :
    (d.toDiagram.map (blockLabel j a)).value j i = d.value j a i := by
  induction d generalizing i with
  | empty => rfl
  | counterterm d ih => simp [toDiagram,Diagram.map,Diagram.value,blockLabel,value,ih]
  | arch u v iu iv =>
    simp only [toDiagram,Diagram.map,Diagram.map_append,Diagram.value,blockLabel,
      value,iv]
    have hm : Diagram.mean (fun k => (u.toDiagram.map (blockLabel j a)).value j k*a k) =
        average (fun k => a k*value j a u k) := by
      simp only [Diagram.mean,average]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [iu]
      ring
    have hv : Diagram.value j ((u.toDiagram.map (blockLabel j a)).append (.diag a .nil)) =
        (fun k => (u.toDiagram.map (blockLabel j a)).value j k * a k) := by
      funext k
      simp only [Diagram.value_append,Diagram.value,mul_one]
    rw [hv,hm]
    ring

lemma literalCoefficient_even (j : ℝ) (a : ι→ℝ) (n : ℕ) (i : ι) :
    literalCoefficient j a (2*n) i=coefficient j a n i := by
  have hh := Fintype.sum_equiv (literalEquiv n)
    (fun d => value j a d.val i)
    (fun z => (z.2.val.map (blockLabel j a)).value j i)
    (fun d => (toDiagram_value j a d.val i).symm)
  change _=literalCoefficient j a (2*n) i at hh
  rw [← hh]
  let : Fintype {d : InverseDiagram // d.degree=n} := atDegreeFintype n
  change (∑ d : {d : InverseDiagram // d.degree=n}, value j a d.val i) = _
  have hx := Finset.sum_subtype (p := fun d : InverseDiagram => d.degree=n)
    (F := atDegreeFintype n)
    (enumerate n).toFinset (by
      intro d; simpa only [List.mem_toFinset] using mem_enumerate d n)
    (fun d => value j a d i)
  exact hx.symm.trans (List.sum_toFinset _ (enumerate_nodup n))

lemma literalCoefficient_odd (j : ℝ) (a : ι→ℝ) (n : ℕ) (i : ι) :
    literalCoefficient j a (2*n+1) i=0 := by
  let := literal_odd_empty n
  exact Finset.sum_eq_zero (by intro z; exact isEmptyElim z)

theorem literalCoefficient_eq (j : ℝ) (a : ι→ℝ) (n : ℕ) (i : ι) :
    literalCoefficient j a n i = if n=0 then 1 else 0 := by
  obtain ⟨m,hm⟩|⟨m,hm⟩ := Nat.even_or_odd n
  · have he : n=2*m := by omega
    rw [he,literalCoefficient_even]
    by_cases h : m=0
    · subst m; simp
    · rw [coefficient_positive j a m (by omega)]
      simp [h]
  · have he : n=2*m+1 := by omega
    rw [he,literalCoefficient_odd]
    simp

end InverseDiagram
end SKGap.Noncrossing

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ScalarVariance
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
namespace SKGapCutoff

lemma halfDiff_as_flip {n : ℕ} (f : Observables n) (x : Spin n) (i : Fin n) :
    halfDiff i f x = spin x i * (f x - f (flip x i)) / 2 := by
  have hx := replace_self x i
  cases hi : x i <;> simp only [hi] at hx
  · simp only [spin, hi, Bool.false_eq_true, ↓reduceIte, flip, Bool.not_false, halfDiff]
    rw [hx]; ring
  · simp only [spin, hi, ↓reduceIte, flip, Bool.not_true, halfDiff]
    rw [hx]; ring

lemma abs_spin_eq_one {n : ℕ} (x : Spin n) (i : Fin n) : |spin x i| = 1 := by
  cases hi : x i <;> simp [spin, hi]

end SKGapCutoff

open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Taylor
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set
namespace SKGap.SourceTaylor
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma segment_taylor (F : E→ℝ) (F' : E→E→L[ℝ]ℝ) (x y : E) {L : ℝ}
    (hL : 0≤L)
    (hF : ∀t∈Icc (0:ℝ) 1,HasFDerivAt F (F' (x+t • (y-x))) (x+t • (y-x)))
    (hLip : ∀t∈Icc (0:ℝ) 1,‖F' (x+t • (y-x))-F' x‖≤L*‖t • (y-x)‖) :
    |F y-F x-F' x (y-x)|≤L*‖y-x‖^2 := by
  let g : ℝ→ℝ:=fun t=>F (x+t • (y-x))-F x-t*(F' x (y-x))
  let g' : ℝ→ℝ:=fun t=>(F' (x+t • (y-x))-F' x) (y-x)
  have hg (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : HasDerivAt g (g' t) t := by
    have H:=(((hF t ht).comp_hasDerivAt t
      (((hasDerivAt_id t).smul_const (y-x)).const_add x)).sub_const (F x)).sub
      ((hasDerivAt_id t).mul_const (F' x (y-x)))
    convert! H using 1
    all_goals try with_reducible_and_instances rfl
    simp only [g',sub_apply,one_smul,one_mul]
  have hb (t : ℝ) (ht : t∈Ico (0:ℝ) 1) : ‖g' t‖≤L*‖y-x‖^2 := by
    calc
      _ ≤ ‖F' (x+t • (y-x))-F' x‖*‖y-x‖ := (F' (x+t • (y-x))-F' x).le_opNorm _
      _ ≤ (L*‖t • (y-x)‖)*‖y-x‖ := mul_le_mul_of_nonneg_right (hLip t ⟨ht.1,ht.2.le⟩) (norm_nonneg _)
      _ ≤ (L*‖y-x‖)*‖y-x‖ := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
        gcongr
        exact mul_le_of_le_one_left (norm_nonneg _) ht.2.le
      _ = _ := by ring
  have H:=norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht=>(hg t ht).hasDerivWithinAt) hb
  simpa only [g,one_smul,zero_smul,add_sub_cancel,add_zero,one_mul,zero_mul,sub_self,sub_zero,
    Real.norm_eq_abs] using H

lemma segment_lipschitz (F : E→ℝ) (F' : E→E→L[ℝ]ℝ) (x y : E) {C : ℝ}
    (hC : 0≤C)
    (hF : ∀t∈Icc (0:ℝ) 1,HasFDerivAt F (F' (x+t • (y-x))) (x+t • (y-x)))
    (hBound : ∀t∈Icc (0:ℝ) 1,‖F' (x+t • (y-x))‖≤C) :
    |F y-F x|≤C*‖y-x‖ := by
  let g : ℝ→ℝ:=fun t=>F (x+t • (y-x))
  let g' : ℝ→ℝ:=fun t=>F' (x+t • (y-x)) (y-x)
  have hg (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : HasDerivAt g (g' t) t := by
    convert! (hF t ht).comp_hasDerivAt t (((hasDerivAt_id t).smul_const (y-x)).const_add x) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [g',one_smul]
  have hb (t : ℝ) (ht : t∈Ico (0:ℝ) 1) : ‖g' t‖≤C*‖y-x‖ :=
    ((F' (x+t • (y-x))).le_opNorm _).trans
      (mul_le_mul (hBound t ⟨ht.1,ht.2.le⟩) le_rfl (norm_nonneg _) hC)
  have H:=norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht=>(hg t ht).hasDerivWithinAt) hb
  simpa only [g,one_smul,zero_smul,add_sub_cancel,add_zero,Real.norm_eq_abs] using H

end SKGap.SourceTaylor

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_CoefficientFlip
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set
namespace SKGapCutoff.Recipe
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma flipHalfDiff_norm (i : Fin n) (P : Spin n→E) (x : Spin n) :
    ‖flipHalfDiff i P x‖=‖P (flip x i)-P x‖/2 := by
  simp only [flipHalfDiff,norm_smul,Real.norm_eq_abs,abs_div,abs_spin_eq_one,abs_of_pos (by norm_num : (0:ℝ)<2)]
  rw [norm_sub_rev]
  ring

lemma coefficient_linearization (i : Fin n) (P : Spin n→E) (x : Spin n)
    (F : E→ℝ) (T : E→L[ℝ]ℝ) :
    halfDiff i (fun y=>F (P y)) x-T (flipHalfDiff i P x)=
      (-spin x i/2)*(F (P (flip x i))-F (P x)-T (P (flip x i)-P x)) := by
  rw [halfDiff_as_flip]
  simp only [flipHalfDiff,map_smul,map_sub,smul_eq_mul]
  ring

lemma coefficient_taylor (i : Fin n) (P : Spin n→E) (x : Spin n)
    (F : E→ℝ) (F' : E→E→L[ℝ]ℝ) {L : ℝ} (hL : 0≤L)
    (hF : ∀t∈Icc (0:ℝ) 1,HasFDerivAt F
      (F' (P x+t • (P (flip x i)-P x))) (P x+t • (P (flip x i)-P x)))
    (hLip : ∀t∈Icc (0:ℝ) 1,
      ‖F' (P x+t • (P (flip x i)-P x))-F' (P x)‖≤L*‖t • (P (flip x i)-P x)‖) :
    |halfDiff i (fun y=>F (P y)) x-F' (P x) (flipHalfDiff i P x)|≤
      2*L*‖flipHalfDiff i P x‖^2 := by
  have H:=SKGap.SourceTaylor.segment_taylor F F' (P x) (P (flip x i)) hL hF hLip
  rw [coefficient_linearization,abs_mul,abs_div,abs_neg,abs_spin_eq_one,
    abs_of_pos (by norm_num : (0:ℝ)<2),flipHalfDiff_norm]
  calc
    _ ≤ (1/2:ℝ)*(L*‖P (flip x i)-P x‖^2) := mul_le_mul_of_nonneg_left H (by norm_num)
    _ = _ := by ring

lemma coefficient_lipschitz (i : Fin n) (P : Spin n→E) (x : Spin n)
    (F : E→ℝ) (F' : E→E→L[ℝ]ℝ) {C : ℝ} (hC : 0≤C)
    (hF : ∀t∈Icc (0:ℝ) 1,HasFDerivAt F
      (F' (P x+t • (P (flip x i)-P x))) (P x+t • (P (flip x i)-P x)))
    (hBound : ∀t∈Icc (0:ℝ) 1,‖F' (P x+t • (P (flip x i)-P x))‖≤C) :
    |halfDiff i (fun y=>F (P y)) x|≤C*‖flipHalfDiff i P x‖ := by
  have H:=SKGap.SourceTaylor.segment_lipschitz F F' (P x) (P (flip x i)) hC hF hBound
  rw [halfDiff_as_flip,abs_div,abs_mul,abs_spin_eq_one,one_mul,
    abs_of_pos (by norm_num : (0:ℝ)<2),flipHalfDiff_norm,abs_sub_comm]
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right H (show (0:ℝ)≤2 by norm_num)

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_OpNorm
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma colVec_eq (M : Matrix ι ι ℝ) (k : ι) :
    colVec M k = M.toEuclideanLin.toContinuousLinearMap (EuclideanSpace.single k (1:ℝ)) := by
  ext i
  simp [colVec,Matrix.toLpLin_apply]

lemma colVec_norm_le (M : Matrix ι ι ℝ) (k : ι) : ‖colVec M k‖ ≤ opNorm M := by
  rw [colVec_eq]
  simpa only [PiLp.norm_single,norm_one,mul_one,opNorm] using!
    M.toEuclideanLin.toContinuousLinearMap.le_opNorm (EuclideanSpace.single k (1:ℝ))

lemma matrix_entry_le_opNorm (M : Matrix ι ι ℝ) (i k : ι) : |M i k| ≤ opNorm M := by
  have h : |M i k| ≤ ‖colVec M k‖ := by
    simpa only [colVec,Real.norm_eq_abs] using (PiLp.norm_apply_le (colVec M k) i)
  exact h.trans (colVec_norm_le M k)

end SKGap

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_FrobeniusSq
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
namespace SKGap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma frobenius_col_sq (M : Matrix ι ι ℝ) : ‖M‖^2 = ∑ k, ‖colVec M k‖^2 := by
  rw [frobenius_sq,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [EuclideanSpace.norm_sq_eq]
  simp [colVec,Real.norm_eq_abs,sq_abs]

lemma colVec_mul (M N : Matrix ι ι ℝ) (k : ι) :
    colVec (M*N) k = M.toEuclideanLin.toContinuousLinearMap (colVec N k) := by
  ext i
  rfl

lemma frobenius_mul_le_opNorm (M N : Matrix ι ι ℝ) : ‖M*N‖ ≤ opNorm M * ‖N‖ := by
  have hp : 0 ≤ opNorm M := norm_nonneg _
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hp (norm_nonneg N))
  simp only [← sq]
  rw [frobenius_col_sq,mul_pow,frobenius_col_sq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  rw [colVec_mul]
  have hh := M.toEuclideanLin.toContinuousLinearMap.le_opNorm (colVec N k)
  change ‖M.toEuclideanLin.toContinuousLinearMap (colVec N k)‖ ≤ opNorm M * ‖colVec N k‖ at hh
  nlinarith only [hh, norm_nonneg (M.toEuclideanLin.toContinuousLinearMap (colVec N k)),
    mul_nonneg hp (norm_nonneg (colVec N k))]

lemma opNorm_transpose (M : Matrix ι ι ℝ) : opNorm Mᵀ = opNorm M := by
  change ‖Mᵀ.toEuclideanLin.toContinuousLinearMap‖ = ‖M.toEuclideanLin.toContinuousLinearMap‖
  have he : Mᵀ.toEuclideanLin.toContinuousLinearMap =
      ContinuousLinearMap.adjoint M.toEuclideanLin.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℝ
    intro y
    rw [ContinuousLinearMap.adjoint_inner_right]
    change (∑ i, (∑ k, M k i*x k)*y i) = ∑ i, x i * (∑ k, M i k*y k)
    simp only [Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he,ContinuousLinearMap.adjoint.norm_map]

end SKGap

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MatrixSeminorm
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance instFactLeENNRealOfNat_solutions : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩

omit [DecidableEq ι] in
lemma diagonalSeminorm_sq (M : Matrix ι ι ℝ) : diagonalSeminorm M^2=∑ i,(M i i)^2 := by
  simp only [diagonalSeminorm,EuclideanSpace.norm_sq_eq,diagonalVector,Real.norm_eq_abs,sq_abs]

lemma offDiagonalSeminorm_fourth (M : Matrix ι ι ℝ) :
    offDiagonalSeminorm M^4=∑ p : ι×ι,if p.1=p.2 then 0 else (M p.1 p.2)^4 := by
  rw [offDiagonalSeminorm,PiLp.norm_eq_of_nat (p:=4) 4 (by norm_num)]
  rw [←Real.rpow_natCast,←Real.rpow_mul (Finset.sum_nonneg (fun _ _=>pow_nonneg (norm_nonneg _) _))]
  norm_num only [Nat.cast_ofNat,one_div,mul_inv_cancel₀ (by norm_num : (4:ℝ)≠0),Real.rpow_one]
  apply Finset.sum_congr rfl
  intro p _
  simp only [offDiagonalVector,WithLp.ofLp_toLp]
  split_ifs
  · simp
  · rw [Real.norm_eq_abs]
    calc
      |M p.1 p.2|^4=(|M p.1 p.2|^2)^2 := by ring
      _ = ((M p.1 p.2)^2)^2 := by rw [sq_abs]
      _ = (M p.1 p.2)^4 := by ring

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_DiscreteMatrixCalculus
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Primary
open SKGap Matrix
variable {n : ℕ}
local instance instFactLeENNRealOfNat_solutions : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩

lemma opNorm_eq (M : Interaction n) :
    SKGap.opNorm M = ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M‖ := rfl

lemma opNorm_le_frobenius (M : Interaction n) : SKGap.opNorm M ≤ ‖M‖ := by
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg M)
  simp only [← sq]
  rw [SKGap.frobenius_sq,opNorm_eq]
  exact RandomMatrix.matrix_opNorm_sq_le_frobenius M

lemma fourth_sum (M : Interaction n) :
    (∑ i,∑ k,(M i k)^4) = (∑ i,(M i i)^4)+SKGap.offDiagonalSeminorm M^4 := by
  rw [SKGap.offDiagonalSeminorm_fourth,Fintype.sum_prod_type,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hs : (M i i)^4 = ∑ k : Fin n, if i=k then (M i k)^4 else 0 := by simp
  rw [hs,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : i=k <;> simp [h]

lemma fourth_sum_le {M : Interaction n} {C : ℝ} (hC : 0≤C) (hM : ShapeBound M C) :
    (∑ i,∑ k,(M i k)^4) ≤ 2*C^4 := by
  rw [fourth_sum]
  have hd : (∑ i,(M i i)^4) ≤ SKGap.diagonalSeminorm M^4 := by
    rw [show (4:ℕ)=2*2 by rfl,pow_mul,SKGap.diagonalSeminorm_sq]
    simpa only [pow_mul] using
      (Finset.sum_sq_le_sq_sum_of_nonneg (s:=Finset.univ) (f:=fun i => (M i i)^2)
        (fun i _ => sq_nonneg _))
  have hdC := (pow_le_pow_iff_left₀ (norm_nonneg (SKGap.diagonalVector M)) hC
    (by decide : 4 ≠ 0)).2 hM.2.1
  have hoC := pow_le_pow_left₀ (norm_nonneg (SKGap.offDiagonalVector M)) hM.2.2 4
  dsimp only [SKGap.diagonalSeminorm,SKGap.offDiagonalSeminorm] at hd ⊢
  nlinarith

lemma siteMean_derivative (F : VectorFields n) (x : Spin n) :
    derivativeVector (siteMean F) x = (n:ℝ)⁻¹ •
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) ((derivativeMatrix F x)ᵀ))
        (WithLp.toLp 2 (fun _ => 1)) := by
  ext k
  change halfDiff k (siteMean F) x = (n:ℝ)⁻¹*(∑ i,halfDiff k (fun y => F y i) x*1)
  simp only [mul_one,halfDiff,siteMean]
  rw [← Finset.sum_div,Finset.sum_sub_distrib]
  ring

lemma euclidean_ones_norm_sq :
    ‖(WithLp.toLp 2 (fun _ : Fin n => (1:ℝ)) : EuclideanSpace ℝ (Fin n))‖^2 = n := by
  simp [EuclideanSpace.real_norm_sq_eq]

lemma siteMean_derivative_square (F : VectorFields n) (x : Spin n) (hn : 0<n) :
    (n:ℝ)*‖derivativeVector (siteMean F) x‖^2 ≤ SKGap.opNorm (derivativeMatrix F x)^2 := by
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have h := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) ((derivativeMatrix F x)ᵀ)).le_opNorm
    (WithLp.toLp 2 (fun _ : Fin n => (1:ℝ)))
  change ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) ((derivativeMatrix F x)ᵀ))
    (WithLp.toLp 2 (fun _ : Fin n => (1:ℝ)))‖ ≤
    SKGap.opNorm ((derivativeMatrix F x)ᵀ) * ‖(WithLp.toLp 2 (fun _ : Fin n => (1:ℝ)) : EuclideanSpace ℝ (Fin n))‖ at h
  rw [SKGap.opNorm_transpose] at h
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow,euclidean_ones_norm_sq] at hs
  rw [siteMean_derivative,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hnR,mul_pow]
  field_simp
  nlinarith

lemma siteMean_derivative_square_bound {F : VectorFields n} {x : Spin n} {B : ℝ}
    (hn : 0<n) (hB : SKGap.opNorm (derivativeMatrix F x)≤B) :
    (n:ℝ)*‖derivativeVector (siteMean F) x‖^2 ≤ B^2 :=
  (siteMean_derivative_square F x hn).trans
    (pow_le_pow_left₀ (norm_nonneg _) hB 2)

lemma derivative_norm_of_mean_square {f : Spin n→ℝ} {x : Spin n} {B : ℝ}
    (hn : 0<n) (hB : 0≤B) (h : (n:ℝ)*‖derivativeVector f x‖^2≤B^2) :
    ‖derivativeVector f x‖≤B := by
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  nlinarith [sq_nonneg ‖derivativeVector f x‖,norm_nonneg (derivativeVector f x)]

lemma outer_frobenius_bound {v : Fin n→ℝ} {f : Spin n→ℝ} {x : Spin n} {B : ℝ}
    (hv : ∀ i,|v i|≤1) (hB : 0≤B)
    (h : (n:ℝ)*‖derivativeVector f x‖^2≤B^2) :
    ‖Matrix.of (fun i k => v i*halfDiff k f x)‖≤B := by
  apply nonneg_le_nonneg_of_sq_le_sq hB
  simp only [← sq]
  rw [SKGap.frobenius_sq]
  calc
    _ ≤ ∑ _i : Fin n,∑ k,(halfDiff k f x)^2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro k _
      have hi := pow_le_pow_left₀ (abs_nonneg (v i)) (hv i) 2
      simp only [sq_abs,one_pow] at hi
      change (v i*halfDiff k f x)^2 ≤ _
      rw [mul_pow]
      nlinarith [sq_nonneg (halfDiff k f x)]
    _ = (n:ℝ)*‖derivativeVector f x‖^2 := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        EuclideanSpace.real_norm_sq_eq,derivativeVector]
    _ ≤ B^2 := h

lemma spin_diagonal_frobenius (f : Spin n→ℝ) (x : Spin n) :
    ‖Matrix.diagonal (fun k => spin x k*halfDiff k f x)‖ = ‖derivativeVector f x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [SKGap.frobenius_sq,EuclideanSpace.real_norm_sq_eq]
  simp [Matrix.diagonal_apply,derivativeVector,mul_pow,spin_sq]

lemma derivativeMatrix_product (f : Spin n→ℝ) (F : VectorFields n) (x : Spin n) :
    derivativeMatrix (fun y i => f y*F y i) x = f x • derivativeMatrix F x +
      Matrix.of (fun i k => F x i*halfDiff k f x) -
      (2:ℝ) • (derivativeMatrix F x*Matrix.diagonal (fun k => spin x k*halfDiff k f x)) := by
  ext i k
  simp only [derivativeMatrix,Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,
    smul_eq_mul,Matrix.mul_diagonal,halfDiff_mul,Matrix.of_apply]
  ring

lemma product_derivative_error {f : Spin n→ℝ} {F : VectorFields n} {x : Spin n} {B C : ℝ}
    (hn : 0<n) (hB : 0≤B) (hC : SKGap.opNorm (derivativeMatrix F x)≤C)
    (hF : ∀ i,|F x i|≤1) (hf : (n:ℝ)*‖derivativeVector f x‖^2≤B^2) :
    ‖derivativeMatrix (fun y i => f y*F y i) x-f x • derivativeMatrix F x‖ ≤ B+2*C*B := by
  have hdb := derivative_norm_of_mean_square hn hB hf
  have hC0 : 0≤C := (norm_nonneg _).trans hC
  rw [derivativeMatrix_product]
  have he (A R T : Interaction n) : A+R-T-A=R-T := by abel
  rw [he]
  calc
    _ ≤ ‖Matrix.of (fun i k => F x i*halfDiff k f x)‖+
        ‖(2:ℝ) • (derivativeMatrix F x*Matrix.diagonal (fun k => spin x k*halfDiff k f x))‖ := norm_sub_le _ _
    _ ≤ B+2*C*B := by
      apply add_le_add (outer_frobenius_bound hF hB hf)
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)]
      calc
        _ ≤ 2*(SKGap.opNorm (derivativeMatrix F x)*‖Matrix.diagonal (fun k => spin x k*halfDiff k f x)‖) :=
          mul_le_mul_of_nonneg_left (SKGap.frobenius_mul_le_opNorm _ _) (by norm_num)
        _ ≤ 2*(C*B) := by
          rw [spin_diagonal_frobenius]
          exact mul_le_mul_of_nonneg_left (mul_le_mul hC hdb (norm_nonneg _) hC0) (by norm_num)
        _ = _ := by ring

lemma derivativeMatrix_linear (J : Interaction n) (F : VectorFields n) (h : Fin n→ℝ)
    (x : Spin n) :
    derivativeMatrix (fun y i => h i+∑ k,J i k*F y k) x = J*derivativeMatrix F x := by
  ext i l
  simp only [derivativeMatrix,Matrix.mul_apply,halfDiff]
  simp_rw [← mul_div_assoc,mul_sub]
  rw [← Finset.sum_div,Finset.sum_sub_distrib]
  ring

lemma derivativeMatrix_sub (F G : VectorFields n) (x : Spin n) :
    derivativeMatrix (fun y i => F y i-G y i) x=derivativeMatrix F x-derivativeMatrix G x := by
  ext i k
  exact halfDiff_sub k (fun y => F y i) (fun y => G y i) x

lemma derivativeMatrix_smul (c : ℝ) (F : VectorFields n) (x : Spin n) :
    derivativeMatrix (fun y i => c*F y i) x=c • derivativeMatrix F x := by
  ext i k
  simp only [derivativeMatrix,halfDiff,Matrix.smul_apply,smul_eq_mul]
  ring

end SKGapCutoff.Primary
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LocalCoefficient
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary
variable {n : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma linear_apply_coordinates {α : Type*} [Fintype α] [DecidableEq α]
    (T : (α→ℝ)→L[ℝ]ℝ) (v : α→ℝ) : T v=∑l,v l*T (Pi.single l 1) := by
  have he : v=∑l,v l • Pi.single l (1:ℝ) := by
    funext i
    simp [Finset.sum_apply,Pi.single_apply]
  conv_lhs => rw [he]
  simp only [map_sum,map_smul,smul_eq_mul]

lemma flipHalfDiff_coordinate {α : Type*} [Fintype α] (P : Spin n→α→ℝ)
    (k : Fin n) (x : Spin n) (l : α) :
    flipHalfDiff k P x l=halfDiff k (fun y=>P y l) x := by
  rw [halfDiff_as_flip]
  dsimp only [flipHalfDiff,Pi.smul_apply,Pi.sub_apply,smul_eq_mul]
  ring

lemma coefficient_chain (H : ι→VectorFields n) (θ : κ→Spin n→ℝ) (x : Spin n) (i k : Fin n)
    (T : Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ) :
    T (flipHalfDiff k (fun y=>localArgs H θ y i) x)=
      (∑l,partialAt T (.inl l)*derivativeMatrix (H l) x i k)+
      ∑α,partialAt T (.inr α)*halfDiff k (θ α) x := by
  rw [linear_apply_coordinates,Fintype.sum_sum_type]
  simp only [flipHalfDiff_coordinate,partialAt,localArgs,Sum.elim_inl,Sum.elim_inr,derivativeMatrix,mul_comm]

omit [DecidableEq ι] [DecidableEq κ] in
lemma local_argument_bound (H : ι→VectorFields n) (θ : κ→Spin n→ℝ) (x : Spin n) (i k : Fin n) :
    ‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖ ≤
      (∑l,|derivativeMatrix (H l) x i k|)+(∑α,|halfDiff k (θ α) x|) := by
  apply (pi_norm_le_iff_of_nonneg (add_nonneg
    (Finset.sum_nonneg fun l _=>abs_nonneg _) (Finset.sum_nonneg fun α _=>abs_nonneg _))).mpr
  intro l
  rw [Real.norm_eq_abs,flipHalfDiff_coordinate]
  cases l with
  | inl l =>
    dsimp only [localArgs,Sum.elim_inl]
    exact (Finset.single_le_sum (fun l _=>abs_nonneg (derivativeMatrix (H l) x i k)) (Finset.mem_univ l)).trans
      (le_add_of_nonneg_right (Finset.sum_nonneg fun α _=>abs_nonneg _))
  | inr α =>
    dsimp only [localArgs,Sum.elim_inr]
    exact (Finset.single_le_sum (fun α _=>abs_nonneg (halfDiff k (θ α) x)) (Finset.mem_univ α)).trans
      (le_add_of_nonneg_left (Finset.sum_nonneg fun l _=>abs_nonneg _))

lemma source_derivative_exact (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
    (s : VectorFields n) (x : Spin n) (i k : Fin n) :
    derivativeMatrix (fun x i=>coefficient H θ F x i*s x i) x i k=
      coefficient H θ F x i*derivativeMatrix s x i k+
      (∑l,s x i*localPartial H θ F' (.inl l) x i*derivativeMatrix (H l) x i k)+
      (∑α,s x i*localPartial H θ F' (.inr α) x i*halfDiff k (θ α) x)+
      s x i*taylorError H θ F F' x i k-
      2*spin x k*derivativeMatrix (coefficient H θ F) x i k*derivativeMatrix s x i k := by
  dsimp only [taylorError,localPartial]
  rw [coefficient_chain]
  simp only [←Finset.mul_sum,mul_assoc]
  rw [derivativeMatrix,halfDiff_mul]
  dsimp only [derivativeMatrix]
  ring

omit [DecidableEq ι] [DecidableEq κ] in
lemma taylor_error_bound (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
    (x : Spin n) (i k : Fin n) {L Q T : ℝ} (hL : 0≤L) (hQ : 0≤Q) (hT : 0≤T)
    (hargs : ‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖≤Q+T)
    (hF : ∀t∈Set.Icc (0:ℝ) 1,HasFDerivAt (F i)
      (F' i (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i)))
      (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i)))
    (hLip : ∀t∈Set.Icc (0:ℝ) 1,
      ‖F' i (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i))-
        F' i (localArgs H θ x i)‖≤L*‖t • (localArgs H θ (flip x k) i-localArgs H θ x i)‖) :
    |taylorError H θ F F' x i k|≤4*L*(Q^2+Q*T+T^2) := by
  have h:=coefficient_taylor k (fun y=>localArgs H θ y i) x (F i) (F' i) hL hF hLip
  have hs:=(pow_le_pow_iff_left₀ (norm_nonneg _) (add_nonneg hQ hT)
    (by decide : 2 ≠ 0)).2 hargs
  have hh:=mul_le_mul_of_nonneg_left hs (mul_nonneg (by norm_num : (0:ℝ)≤2) hL)
  change |taylorError H θ F F' x i k|≤_ at h
  refine h.trans (hh.trans ?_)
  nlinarith [sq_nonneg Q,sq_nonneg T,mul_nonneg hL (sq_nonneg Q),mul_nonneg hL (sq_nonneg T)]

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Error
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.SourceError
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance instFactLeENNRealOfNat_solutions_reb0def_1 : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩
lemma real_op_norm_nonneg (P : Matrix ι ι ℝ) : 0≤opNorm P := norm_nonneg _

lemma cauchy_bound {α : Type*} [Fintype α] (f g : α→ℝ) {A B : ℝ}
    (hA : 0≤A) (hB : 0≤B) (hf : (∑i,(f i)^2)≤A^2) (hg : (∑i,(g i)^2)≤B^2) :
    |∑i,f i*g i|≤A*B := by
  have H:=Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  have hh:=mul_le_mul hf hg (Finset.sum_nonneg (fun i _=>sq_nonneg _)) (sq_nonneg _)
  nlinarith [sq_abs (∑i,f i*g i),mul_nonneg hA hB,abs_nonneg (∑i,f i*g i)]

omit [DecidableEq ι] in
lemma double_cauchy (f g : ι→ι→ℝ) {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hf : (∑i,∑k,(f i k)^2)≤A^2) (hg : (∑i,∑k,(g i k)^2)≤B^2) :
    |∑i,∑k,f i k*g i k|≤A*B := by
  have H:=cauchy_bound (fun a : ι×ι=>f a.1 a.2) (fun a=>g a.1 a.2) hA hB
    (by simpa only [Fintype.sum_prod_type] using hf) (by simpa only [Fintype.sum_prod_type] using hg)
  simpa only [Fintype.sum_prod_type] using H

omit [DecidableEq ι] in
lemma trace_le_traceAbsolute (P E : Matrix ι ι ℝ) : |trace (P*E)|≤traceAbsolute P E := by
  rw [trace_mul_comm]
  simp only [trace,diag,Matrix.mul_apply]
  apply (Finset.abs_sum_le_sum_abs ..).trans
  apply Finset.sum_le_sum; intro i _
  exact (Finset.abs_sum_le_sum_abs ..).trans_eq (by simp only [abs_mul,mul_comm])

lemma matrix_column_square_le (P : Matrix ι ι ℝ) (i : ι) :
    (∑k,(P k i)^2)≤(opNorm P)^2 := by
  have H:=pow_le_pow_left₀ (norm_nonneg (colVec P i)) (colVec_norm_le P i) 2
  simpa only [colVec,EuclideanSpace.real_norm_sq_eq] using H

lemma matrix_row_square_le (P : Matrix ι ι ℝ) (i : ι) :
    (∑k,(P i k)^2)≤(opNorm P)^2 := by
  simpa only [Matrix.transpose_apply,opNorm_transpose] using matrix_column_square_le Pᵀ i

lemma small_column_square (P : Matrix ι ι ℝ) (s : ι→ℝ) :
    (∑i,∑k,(|P k i| * |s i|)^2)≤(opNorm P)^2*(∑i,(s i)^2) := by
  simp only [mul_pow,sq_abs]
  calc
    _ ≤ ∑i,(opNorm P)^2*(s i)^2 := by
      apply Finset.sum_le_sum; intro i _
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (matrix_column_square_le P i) (sq_nonneg _)
    _ = _ := by rw [←Finset.mul_sum]

lemma small_row_square (P : Matrix ι ι ℝ) (t : ι→ℝ) :
    (∑i,∑k,(|P k i| * |t k|)^2)≤(opNorm P)^2*(∑k,(t k)^2) := by
  rw [Finset.sum_comm]
  simpa only [Matrix.transpose_apply,opNorm_transpose] using small_column_square Pᵀ t

lemma quadratic_trace_bound (P Q : Matrix ι ι ℝ) (s : ι→ℝ) {S B : ℝ}
    (hS : 0≤S) (hB : 0≤B) (hs : (∑i,(s i)^2)≤S^2)
    (hQ : (∑i,∑k,(Q i k)^4)≤B^4) :
    (∑i,∑k,|P k i| * |s i| *(Q i k)^2)≤opNorm P*S*B^2 := by
  have H:=double_cauchy (fun i k=>|P k i| * |s i|) (fun i k=>(Q i k)^2)
    (mul_nonneg (real_op_norm_nonneg P) hS) (pow_nonneg hB 2)
    ((small_column_square P s).trans (by
      simpa only [mul_pow] using mul_le_mul_of_nonneg_left hs (sq_nonneg (opNorm P))))
    (by simpa only [←pow_mul] using hQ)
  exact (le_abs_self _).trans H

lemma mixed_trace_bound (P Q : Matrix ι ι ℝ) (s t : ι→ℝ) {S T B : ℝ}
    (hS : 0≤S) (hT : 0≤T) (hB : 0≤B)
    (hs : (∑i,(s i)^2)≤S^2) (ht : (∑k,(t k)^2)≤T^2)
    (hQ : ∀i,(∑k,(Q i k)^2)≤B^2) :
    (∑i,∑k,|P k i| * |s i| * |Q i k| * |t k|)≤opNorm P*T*(S*B) := by
  have hf : (∑i,∑k,(|P k i| * |t k|)^2)≤(opNorm P*T)^2 :=
    (small_row_square P t).trans (by simpa only [mul_pow] using (mul_le_mul_of_nonneg_left ht (sq_nonneg (opNorm P))))
  have hg : (∑i,∑k,(|s i| * |Q i k|)^2)≤(S*B)^2 := by
    simp only [mul_pow,sq_abs,←Finset.mul_sum]
    calc
      _ ≤ ∑i,(s i)^2*B^2 := Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_left (hQ i) (sq_nonneg _))
      _ = (∑i,(s i)^2)*B^2 := (Finset.sum_mul ..).symm
      _ ≤ S^2*B^2 := mul_le_mul_of_nonneg_right hs (sq_nonneg _)
  have H:=double_cauchy (fun i k=>|P k i| * |t k|) (fun i k=>|s i| * |Q i k|)
    (mul_nonneg (real_op_norm_nonneg P) hT) (mul_nonneg hS hB) hf hg
  apply (le_abs_self _).trans
  have he : (∑i,∑k,|P k i| * |s i| * |Q i k| * |t k|) =
      ∑i,∑k,|P k i| * |t k| * (|s i| * |Q i k|) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _; ring
  rw [he]
  exact H

lemma parameter_square_trace_bound (P : Matrix ι ι ℝ) (s t : ι→ℝ) {S T : ℝ}
    (hS : 0≤S) (hT : 0≤T) (hs : (∑i,(s i)^2)≤S^2) (ht : (∑k,(t k)^2)≤T^2) :
    (∑i,∑k,|P k i| * |s i| *(t k)^2)≤opNorm P*T*(S*T) := by
  have hf : (∑i,∑k,(|P k i| * |t k|)^2)≤(opNorm P*T)^2 :=
    (small_row_square P t).trans (by simpa only [mul_pow] using (mul_le_mul_of_nonneg_left ht (sq_nonneg (opNorm P))))
  have hg : (∑i,∑k,(|s i| * |t k|)^2)≤(S*T)^2 := by
    simp only [mul_pow,sq_abs,←Finset.mul_sum,←Finset.sum_mul]
    exact mul_le_mul hs ht (Finset.sum_nonneg (fun k _=>sq_nonneg _)) (sq_nonneg _)
  have H:=double_cauchy (fun i k=>|P k i| * |t k|) (fun i k=>|s i| * |t k|)
    (mul_nonneg (real_op_norm_nonneg P) hT) (mul_nonneg hS hT) hf hg
  apply (le_abs_self _).trans
  have he : (∑i,∑k,|P k i| * |s i| * (t k)^2) =
      ∑i,∑k,|P k i| * |t k| * (|s i| * |t k|) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _
    rw [← sq_abs (t k)]; ring
  rw [he]
  exact H

theorem source_taylor_trace_bound (P E Q : Matrix ι ι ℝ) (s t : ι→ℝ) {C S T B R : ℝ}
    (hC : 0≤C) (hS : 0≤S) (hT : 0≤T) (hB : 0≤B) (hR : 0≤R)
    (hs : (∑i,(s i)^2)≤S^2) (ht : (∑k,(t k)^2)≤T^2)
    (hQ4 : (∑i,∑k,(Q i k)^4)≤B^4) (hQr : ∀i,(∑k,(Q i k)^2)≤R^2)
    (hE : ∀i k,|E i k|≤C*|s i| *((Q i k)^2+|Q i k| * |t k|+(t k)^2)) :
    |trace (P*E)|≤C*opNorm P*S*(B^2+R*T+T^2) := by
  apply (trace_le_traceAbsolute P E).trans
  calc
    _ ≤ ∑i,∑k,|P k i| *(C*|s i| *((Q i k)^2+|Q i k| * |t k|+(t k)^2)) := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro k _
      exact mul_le_mul_of_nonneg_left (hE i k) (abs_nonneg _)
    _ = C*((∑i,∑k,|P k i| * |s i| *(Q i k)^2)+
      (∑i,∑k,|P k i| * |s i| * |Q i k| * |t k|)+
      (∑i,∑k,|P k i| * |s i| *(t k)^2)) := by
      simp only [Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro k _; ring
    _ ≤ C*(opNorm P*S*B^2+opNorm P*T*(S*R)+opNorm P*T*(S*T)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add
        (quadratic_trace_bound P Q s hS hB hs hQ4)
        (mixed_trace_bound P Q s t hS hT hR hs ht hQr))
        (parameter_square_trace_bound P s t hS hT hs ht)) hC
    _ = _ := by ring

omit [DecidableEq ι] in
lemma fourth_holder (P D Q : Matrix ι ι ℝ) {B S R : ℝ}
    (hB : 0≤B) (hS : 0≤S) (hR : 0≤R)
    (hP : (∑i,∑k,(P i k)^4)≤B^4) (hD : (∑i,∑k,(D i k)^2)≤S^2)
    (hQ : (∑i,∑k,(Q i k)^4)≤R^4) :
    (∑i,∑k,|P i k| * |D i k| * |Q i k|)≤S*(B*R) := by
  have H₁:=double_cauchy (fun i k=>(P i k)^2) (fun i k=>(Q i k)^2)
    (sq_nonneg B) (sq_nonneg R) (by simpa only [←pow_mul] using hP)
    (by simpa only [←pow_mul] using hQ)
  have H₂ : (∑i,∑k,(|P i k| * |Q i k|)^2)≤(B*R)^2 := by
    simp only [mul_pow,sq_abs]
    exact (le_abs_self _).trans H₁
  have H₃:=double_cauchy (fun i k=>|D i k|) (fun i k=>|P i k| * |Q i k|)
    hS (mul_nonneg hB hR) (by simpa only [sq_abs] using hD) H₂
  apply (le_abs_self _).trans
  have he : (∑i,∑k,|P i k| * |D i k| * |Q i k|) =
      ∑i,∑k,|D i k| * (|P i k| * |Q i k|) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _; ring
  rw [he]; exact H₃

lemma sum_split_diagonal (f : ι→ι→ℝ) :
    (∑i,∑k,f i k)=(∑i,f i i)+(∑i,∑k,if i=k then 0 else f i k) := by
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  have he : f i i=∑k,if i=k then f i k else 0 := by simp
  rw [he,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k _
  split_ifs <;> simp

lemma diagonal_product_trace_bound (P D Q : Matrix ι ι ℝ) {S R : ℝ}
    (hS : 0≤S) (hR : 0≤R) (hD : (∑i,(D i i)^2)≤S^2)
    (hQ : (∑i,(Q i i)^2)≤R^2) :
    (∑i,|P i i| * |D i i| * |Q i i|)≤opNorm P*(S*R) := by
  calc
    _ ≤ ∑i,opNorm P*(|D i i| * |Q i i|) := by
      apply Finset.sum_le_sum; intro i _
      nlinarith [mul_le_mul_of_nonneg_right (matrix_entry_le_opNorm P i i)
        (mul_nonneg (abs_nonneg (D i i)) (abs_nonneg (Q i i)))]
    _ = opNorm P*(∑i,|D i i| * |Q i i|) := by rw [Finset.mul_sum]
    _ ≤ opNorm P*(S*R) := by
      apply mul_le_mul_of_nonneg_left _ (real_op_norm_nonneg P)
      exact (le_abs_self _).trans (cauchy_bound (fun i=>|D i i|) (fun i=>|Q i i|)
        hS hR (by simpa only [sq_abs] using hD) (by simpa only [sq_abs] using hQ))

lemma parameter_product_trace_bound (P D : Matrix ι ι ℝ) (t : ι→ℝ) {S T : ℝ}
    (hS : 0≤S) (hT : 0≤T) (hD : (∑i,∑k,(D i k)^2)≤S^2)
    (ht : (∑k,(t k)^2)≤T^2) :
    (∑i,∑k,|P k i| * |D i k| * |t k|)≤S*(opNorm P*T) := by
  have hf : (∑i,∑k,(|P k i| * |t k|)^2)≤(opNorm P*T)^2 :=
    (small_row_square P t).trans (by simpa only [mul_pow] using
      (mul_le_mul_of_nonneg_left ht (sq_nonneg (opNorm P))))
  have H:=double_cauchy (fun i k=>|D i k|) (fun i k=>|P k i| * |t k|)
    hS (mul_nonneg (real_op_norm_nonneg P) hT) (by simpa only [sq_abs] using hD) hf
  apply (le_abs_self _).trans
  have he : (∑i,∑k,|P k i| * |D i k| * |t k|) =
      ∑i,∑k,|D i k| * (|P k i| * |t k|) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _; ring
  rw [he]; exact H

theorem source_product_trace_bound (P E D Q : Matrix ι ι ℝ) (t : ι→ℝ) {C S T B R L : ℝ}
    (hC : 0≤C) (hS : 0≤S) (hT : 0≤T) (hB : 0≤B) (hR : 0≤R) (hL : 0≤L)
    (hD : (∑i,∑k,(D i k)^2)≤S^2) (ht : (∑k,(t k)^2)≤T^2)
    (hP : (∑i,∑k,if i=k then 0 else (P k i)^4)≤B^4)
    (hQ : (∑i,∑k,(Q i k)^4)≤R^4) (hQd : (∑i,(Q i i)^2)≤L^2)
    (hE : ∀i k,|E i k|≤C*|D i k| *(|Q i k|+|t k|)) :
    |trace (P*E)|≤C*S*(B*R+opNorm P*(L+T)) := by
  have hDd : (∑i,(D i i)^2)≤S^2 := by
    apply le_trans _ hD
    exact Finset.sum_le_sum (fun i _=>Finset.single_le_sum (fun k _=>sq_nonneg (D i k))
      (Finset.mem_univ i))
  let O : Matrix ι ι ℝ := fun i k=>if i=k then 0 else P k i
  have hO : (∑i,∑k,(O i k)^4)≤B^4 := by
    simpa only [O,ite_pow,zero_pow (by decide : 4≠0)] using hP
  have hOff := fourth_holder O D Q hB hS hR hO hD hQ
  have heOff : (∑i,∑k,if i=k then 0 else |P k i| * |D i k| * |Q i k|) =
      ∑i,∑k,|O i k| * |D i k| * |Q i k| := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _
    dsimp only [O]; split_ifs <;> simp
  have hProd : (∑i,∑k,|P k i| * |D i k| * |Q i k|)≤opNorm P*(S*L)+S*(B*R) := by
    rw [sum_split_diagonal,heOff]
    exact add_le_add (diagonal_product_trace_bound P D Q hS hL hDd hQd) hOff
  apply (trace_le_traceAbsolute P E).trans
  calc
    _ ≤ ∑i,∑k,|P k i| *(C*|D i k| *(|Q i k|+|t k|)) := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro k _
      exact mul_le_mul_of_nonneg_left (hE i k) (abs_nonneg _)
    _ = C*((∑i,∑k,|P k i| * |D i k| * |Q i k|)+
        (∑i,∑k,|P k i| * |D i k| * |t k|)) := by
      simp only [Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro k _; ring
    _ ≤ C*(opNorm P*(S*L)+S*(B*R)+S*(opNorm P*T)) :=
      mul_le_mul_of_nonneg_left (add_le_add hProd
        (parameter_product_trace_bound P D t hS hT hD ht)) hC
    _ = _ := by ring

lemma rank_one_trace_bound (P : Matrix ι ι ℝ) (u v : EuclideanSpace ℝ ι) :
    |trace (P*Matrix.of (fun i k=>u i*v k))|≤opNorm P*‖u‖*‖v‖ := by
  have H:=abs_real_inner_le_norm v (P.toEuclideanLin.toContinuousLinearMap u)
  have he : trace (P*Matrix.of (fun i k=>u i*v k))=
      inner ℝ v (P.toEuclideanLin.toContinuousLinearMap u) := by
    change (∑i,∑k,P i k*(u k*v i))=∑i,(∑k,P i k*u k)*v i
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _; ring
  rw [he]
  apply H.trans
  have h:=mul_le_mul_of_nonneg_left
    (P.toEuclideanLin.toContinuousLinearMap.le_opNorm u) (norm_nonneg v)
  change ‖v‖*‖P.toEuclideanLin.toContinuousLinearMap u‖≤opNorm P*‖u‖*‖v‖
  change ‖v‖*‖P.toEuclideanLin.toContinuousLinearMap u‖≤‖v‖*(opNorm P*‖u‖) at h
  nlinarith only [h]

end SKGap.SourceError

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Operation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ}

lemma vectorNorm_sq (u : Fin n→ℝ) : vectorNorm u^2=∑i,(u i)^2 := by
  exact EuclideanSpace.real_norm_sq_eq _

lemma vectorNorm_nonneg (u : Fin n→ℝ) : 0 ≤ vectorNorm u := norm_nonneg _

lemma vectorNorm_mul (a s : Fin n→ℝ) {A : ℝ} (hA : 0 ≤ A) (ha : ∀i,|a i| ≤ A) :
    vectorNorm (fun i=>a i*s i) ≤ A*vectorNorm s := by
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hA (vectorNorm_nonneg _))
  simp only [←sq,vectorNorm_sq,mul_pow]
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _=>mul_le_mul_of_nonneg_right
    (by nlinarith [sq_abs (a i),ha i,abs_nonneg (a i)]) (sq_nonneg _)

lemma row_scaled_frobenius (D : Interaction n) (s : Fin n→ℝ) {R : ℝ}
    (hR : 0 ≤ R) (hD : ∀i,∑k,(D i k)^2 ≤ R^2) :
    ‖Matrix.of (fun i k=>s i*D i k)‖ ≤ R*vectorNorm s := by
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hR (vectorNorm_nonneg _))
  simp only [←sq]
  rw [SKGap.frobenius_sq,mul_pow,vectorNorm_sq]
  simp only [Matrix.of_apply,mul_pow,←Finset.mul_sum]
  calc
    _  ≤  ∑i,(s i)^2*R^2 := Finset.sum_le_sum fun i _=>mul_le_mul_of_nonneg_left (hD i) (sq_nonneg _)
    _ = _ := by rw [←Finset.sum_mul]; ring

lemma row_entry_bound (D : Interaction n) {R : ℝ} (hR : 0 ≤ R)
    (hD : ∀i,∑k,(D i k)^2 ≤ R^2) (i k : Fin n) : |D i k| ≤ R := by
  have H: (D i k)^2 ≤ R^2 :=
    (Finset.single_le_sum (fun l _=>sq_nonneg (D i l)) (Finset.mem_univ k)).trans (hD i)
  nlinarith [sq_abs (D i k),abs_nonneg (D i k)]

lemma multiplier_frobenius (a : Fin n→ℝ) (D : Interaction n) {A : ℝ}
    (hA : 0 ≤ A) (ha : ∀i,|a i| ≤ A) : ‖Matrix.of (fun i k=>a i*D i k)‖ ≤ A*‖D‖ := by
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hA (norm_nonneg _))
  simp only [←sq]
  rw [SKGap.frobenius_sq,mul_pow,SKGap.frobenius_sq]
  simp only [Matrix.of_apply,mul_pow,Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _
  apply Finset.sum_le_sum; intro k _
  exact mul_le_mul_of_nonneg_right (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (a i)) (ha i) 2) (sq_nonneg _)

lemma product_remainder_frobenius (A D : Interaction n) (x : Spin n) {R : ℝ}
    (hR : 0 ≤ R) (hA : ∀i,∑k,(A i k)^2 ≤ R^2) :
    ‖Matrix.of (fun i k=>2*spin x k*A i k*D i k)‖ ≤ 2*R*‖D‖ := by
  apply nonneg_le_nonneg_of_sq_le_sq (by positivity)
  simp only [←sq]
  rw [SKGap.frobenius_sq,mul_pow,mul_pow,SKGap.frobenius_sq]
  simp only [Matrix.of_apply,mul_pow,spin_sq,mul_one,Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _
  apply Finset.sum_le_sum; intro k _
  have H:=row_entry_bound A hR hA i k
  have HH : (A i k)^2 ≤ R^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (A i k)) H 2
  nlinarith [mul_nonneg (sq_nonneg (D i k)) (sub_nonneg.mpr HH)]

lemma source_derivative_product (a s : VectorFields n) (x : Spin n) :
    derivativeMatrix (fun x i=>a x i*s x i) x=
      (fun i k=>a x i*derivativeMatrix s x i k)+
      (fun i k=>s x i*derivativeMatrix a x i k)-
      (fun i k=>2*spin x k*derivativeMatrix a x i k*derivativeMatrix s x i k) := by
  ext i k
  exact halfDiff_mul k (fun x=>a x i) (fun x=>s x i) x

lemma source_frobenius (a s : VectorFields n) (x : Spin n) {A R : ℝ}
    (hA : 0 ≤ A) (hR : 0 ≤ R) (ha : ∀i,|a x i| ≤ A)
    (hda : ∀i,∑k,(derivativeMatrix a x i k)^2 ≤ R^2) :
    ‖derivativeMatrix (fun x i=>a x i*s x i) x‖ ≤
      A*‖derivativeMatrix s x‖+R*vectorNorm (s x)+2*R*‖derivativeMatrix s x‖ := by
  rw [source_derivative_product]
  exact (norm_sub_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (multiplier_frobenius _ _ hA ha)
      (row_scaled_frobenius _ _ hR hda))) (product_remainder_frobenius _ _ x hR hda))

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ}

lemma vectorNorm_add (u v : Fin n→ℝ) :
    vectorNorm (u+v) ≤ vectorNorm u+vectorNorm v := by
  exact norm_add_le (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 v)

lemma vectorNorm_smul (c : ℝ) (u : Fin n→ℝ) :
    vectorNorm (c • u)=|c| *vectorNorm u := by
  exact norm_smul c (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))

lemma vectorNorm_sum {ι : Type*} [Fintype ι] (u : ι→Fin n→ℝ) :
    vectorNorm (∑l,u l) ≤ ∑l,vectorNorm (u l) := by
  change ‖(WithLp.toLp 2 (∑l,u l) : EuclideanSpace ℝ (Fin n))‖≤_
  have he : (WithLp.toLp 2 (∑l,u l) : EuclideanSpace ℝ (Fin n))=∑l,WithLp.toLp 2 (u l) := by
    ext i; simp [Finset.sum_apply]
  rw [he]
  exact norm_sum_le _ _

lemma vectorNorm_mono {u v : Fin n→ℝ} (h : ∀i,|u i|≤|v i|) : vectorNorm u ≤ vectorNorm v := by
  apply nonneg_le_nonneg_of_sq_le_sq (vectorNorm_nonneg _)
  simp only [←sq,vectorNorm_sq]
  exact Finset.sum_le_sum fun i _=>by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (u i)) (h i) 2

lemma vectorNorm_abs (u : Fin n→ℝ) : vectorNorm (fun i=>|u i|)=vectorNorm u := by
  apply (sq_eq_sq₀ (vectorNorm_nonneg _) (vectorNorm_nonneg _)).mp
  simp [vectorNorm_sq]

lemma vectorNorm_matrix_mul (J : Interaction n) (u : Fin n→ℝ) :
    vectorNorm (J.mulVec u) ≤ SKGap.opNorm J*vectorNorm u := by
  exact (Matrix.toEuclideanCLM (𝕜:=ℝ) J).le_opNorm (WithLp.toLp 2 u)

lemma siteMean_square (U : VectorFields n) (x : Spin n) (hn : 0<n) :
    (n:ℝ)*(siteMean U x)^2 ≤ (vectorNorm (U x))^2 := by
  have H:=sq_sum_le_card_mul_sum_sq (s:=Finset.univ) (f:=U x)
  simp only [Finset.card_univ,Fintype.card_fin] at H
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
  dsimp only [siteMean]
  rw [div_pow,vectorNorm_sq]
  apply (mul_le_mul_iff_left₀ hnR).mp
  field_simp
  nlinarith

lemma primary_mean_size (U m : VectorFields n) (x : Spin n) (hn : 0<n)
    (hm : ∀i,|m x i|≤1) :
    vectorNorm (fun i=>siteMean U x*m x i) ≤ vectorNorm (U x) := by
  apply nonneg_le_nonneg_of_sq_le_sq (vectorNorm_nonneg _)
  simp only [←sq,vectorNorm_sq,mul_pow]
  calc
    _ ≤ ∑_i:Fin n,(siteMean U x)^2 := by
      apply Finset.sum_le_sum; intro i _
      have H : (m x i)^2≤1 := by
        simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg (m x i)) (hm i) 2
      nlinarith [sq_nonneg (siteMean U x)]
    _ = (n:ℝ)*(siteMean U x)^2 := by simp
    _ ≤ _ := by simpa only [vectorNorm_sq] using siteMean_square U x hn

lemma scaled_frobenius_by_rows (D : Interaction n) (a : ℝ) {C P : ℝ}
    (hC : 0≤C) (hP : 0≤P) (ha : (n:ℝ)*a^2≤C^2)
    (hD : ∀i,∑k,(D i k)^2≤P^2) : ‖a • D‖≤C*P := by
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hC hP)
  simp only [←sq]
  rw [SKGap.frobenius_sq,mul_pow]
  simp only [Matrix.smul_apply,smul_eq_mul,mul_pow]
  calc
    _ ≤ ∑_i:Fin n,a^2*P^2 := Finset.sum_le_sum fun i _=>by
      rw [←Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hD i) (sq_nonneg _)
    _ = ((n:ℝ)*a^2)*P^2 := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right ha (sq_nonneg _)

lemma primary_mean_frobenius (U m : VectorFields n) (x : Spin n) (hn : 0<n) {C P : ℝ}
    (hC : 0≤C) (hP : 0≤P) (hu : vectorNorm (U x)≤C) (hdu : ‖derivativeMatrix U x‖≤C)
    (hm : ∀i,|m x i|≤1) (hdm : SKGap.opNorm (derivativeMatrix m x)≤P) :
    ‖derivativeMatrix (fun y i=>siteMean U y*m y i) x‖≤C*(1+3*P) := by
  have hav : (n:ℝ)*(siteMean U x)^2≤C^2 := (siteMean_square U x hn).trans
    (pow_le_pow_left₀ (vectorNorm_nonneg _) hu 2)
  have hdav : (n:ℝ)*‖derivativeVector (siteMean U) x‖^2≤C^2 :=
    siteMean_derivative_square_bound hn ((opNorm_le_frobenius _).trans hdu)
  have hs := scaled_frobenius_by_rows (derivativeMatrix m x) (siteMean U x) hC hP hav (fun i=>
    (SKGap.SourceError.matrix_row_square_le _ i).trans (pow_le_pow_left₀ (norm_nonneg _) hdm 2))
  have he := product_derivative_error hn hC hdm hm hdav
  calc
    _ ≤ ‖derivativeMatrix (fun y i=>siteMean U y*m y i) x-siteMean U x • derivativeMatrix m x‖+
      ‖siteMean U x • derivativeMatrix m x‖ := norm_le_norm_sub_add _ _
    _ ≤ (C+2*P*C)+C*P := add_le_add he hs
    _ = _ := by ring

lemma coefficient_mean_value (a : VectorFields n) (x : Spin n) {A : ℝ}
    (hA : 0≤A) (ha : ∀i,|a x i|≤A) : |siteMean a x|≤A := by
  by_cases hn : n=0
  · subst n; simp [siteMean,hA]
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [siteMean,abs_div,abs_of_pos hnR]
  apply (div_le_iff₀ hnR).mpr
  calc
    _ ≤ ∑i,|a x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑_i:Fin n,A := Finset.sum_le_sum fun i _=>ha i
    _ = _ := by simp [mul_comm]

lemma coefficient_mean_difference (a : VectorFields n) (x : Spin n) {R : ℝ}
    (hR : 0≤R) (hda : ∀i,∑k,(derivativeMatrix a x i k)^2≤R^2) :
    ‖derivativeVector (siteMean a) x‖≤R := by
  have he : derivativeVector (siteMean a) x = (n:ℝ)⁻¹ •
      ∑i,WithLp.toLp 2 (fun k=>derivativeMatrix a x i k) := by
    ext k
    simp only [derivativeVector,WithLp.ofLp_toLp,PiLp.smul_apply,smul_eq_mul,WithLp.ofLp_sum,Finset.sum_apply,WithLp.ofLp_toLp]
    simp only [halfDiff,siteMean,derivativeMatrix]
    rw [←Finset.sum_div,Finset.sum_sub_distrib]
    ring
  rw [he,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (Nat.cast_nonneg n)]
  by_cases hn : n=0
  · subst n; simp [hR]
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  calc
    _ ≤ (n:ℝ)⁻¹*(∑_i:Fin n,R) := mul_le_mul_of_nonneg_left
      ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _=>by
        apply nonneg_le_nonneg_of_sq_le_sq hR
        simpa only [←sq,EuclideanSpace.real_norm_sq_eq,WithLp.ofLp_toLp] using hda i)) (inv_nonneg.mpr hnR.le)
    _ = R := by simp [hnR.ne']

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_CoefficientRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma row_vectorNorm_le_opNorm (D : Interaction n) (i : Fin n) :
    vectorNorm (D i) ≤ SKGap.opNorm D := by
  have h0 : 0≤SKGap.opNorm D := norm_nonneg _
  apply nonneg_le_nonneg_of_sq_le_sq h0
  simp only [←sq,vectorNorm_sq]
  exact SKGap.SourceError.matrix_row_square_le D i

lemma local_argument_row_bound (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (x : Spin n) (i : Fin n) :
    vectorNorm (fun k=>‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖) ≤
      (∑l,SKGap.opNorm (derivativeMatrix (H l) x))+(∑α,‖derivativeVector (θ α) x‖) := by
  have hQ (l : ι) : vectorNorm (fun k=>|derivativeMatrix (H l) x i k|)≤SKGap.opNorm (derivativeMatrix (H l) x) := by
    rw [vectorNorm_abs]; exact row_vectorNorm_le_opNorm _ _
  have hT (α : κ) : vectorNorm (fun k=>|halfDiff k (θ α) x|)=‖derivativeVector (θ α) x‖ := by
    rw [vectorNorm_abs]; rfl
  calc
    _ ≤ vectorNorm (fun k=>(∑l,|derivativeMatrix (H l) x i k|)+(∑α,|halfDiff k (θ α) x|)) :=
      vectorNorm_mono fun k=>by
        have hp : 0≤(∑l,|derivativeMatrix (H l) x i k|)+(∑α,|halfDiff k (θ α) x|) :=
          add_nonneg (Finset.sum_nonneg fun _ _=>abs_nonneg _) (Finset.sum_nonneg fun _ _=>abs_nonneg _)
        simpa only [abs_of_nonneg (norm_nonneg _),abs_of_nonneg hp] using local_argument_bound H θ x i k
    _ ≤ vectorNorm (fun k=>∑l,|derivativeMatrix (H l) x i k|)+
        vectorNorm (fun k=>∑α,|halfDiff k (θ α) x|) := vectorNorm_add _ _
    _ ≤ (∑l,vectorNorm (fun k=>|derivativeMatrix (H l) x i k|))+
        ∑α,vectorNorm (fun k=>|halfDiff k (θ α) x|) := by
      apply add_le_add
      · convert! vectorNorm_sum (fun l k=>|derivativeMatrix (H l) x i k|) using 1
        all_goals try with_reducible_and_instances rfl
        congr 1; ext k; simp
      · convert! vectorNorm_sum (fun α k=>|halfDiff k (θ α) x|) using 1
        all_goals try with_reducible_and_instances rfl
        congr 1; ext k; simp
    _ ≤ _ := add_le_add (Finset.sum_le_sum fun l _=>hQ l) (by simp only [hT]; rfl)

lemma coefficient_row_bound (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
    (x : Spin n) (i : Fin n) {L : ℝ} (hL : 0≤L)
    (hF : ∀k t, t∈Set.Icc (0:ℝ) 1→HasFDerivAt (F i)
      (F' i (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i)))
      (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i)))
    (hBound : ∀k t, t∈Set.Icc (0:ℝ) 1→
      ‖F' i (localArgs H θ x i+t • (localArgs H θ (flip x k) i-localArgs H θ x i))‖≤L) :
    vectorNorm (derivativeMatrix (coefficient H θ F) x i) ≤
      L*((∑l,SKGap.opNorm (derivativeMatrix (H l) x))+(∑α,‖derivativeVector (θ α) x‖)) := by
  calc
    _ ≤ vectorNorm (fun k=>L*‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖) :=
      vectorNorm_mono fun k=>by
        rw [abs_of_nonneg (mul_nonneg hL (norm_nonneg _))]
        exact coefficient_lipschitz k (fun y=>localArgs H θ y i) x (F i) (F' i) hL (hF k) (hBound k)
    _ = L*vectorNorm (fun k=>‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖) := by
      convert! vectorNorm_smul L (fun k=>‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖) using 1
      all_goals try with_reducible_and_instances rfl
      rw [abs_of_nonneg hL]
    _ ≤ _ := mul_le_mul_of_nonneg_left (local_argument_row_bound H θ x i) hL

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ}

lemma derivativeMatrix_add (U V : VectorFields n) (x : Spin n) :
    derivativeMatrix (fun x i=>U x i+V x i) x=derivativeMatrix U x+derivativeMatrix V x := by
  ext i k; simp only [derivativeMatrix,halfDiff,Matrix.add_apply]; ring

lemma derivativeMatrix_sum {ι : Type*} [Fintype ι] (U : ι→VectorFields n) (x : Spin n) :
    derivativeMatrix (fun x i=>∑l,U l x i) x=∑l,derivativeMatrix (U l) x := by
  ext i k; simp only [Matrix.sum_apply,derivativeMatrix,halfDiff_sum]

lemma SmallBound.mono {U : VectorFields n} {x : Spin n} {C D : ℝ}
    (h : SmallBound U x C) (hCD : C≤D) : SmallBound U x D :=
  ⟨h.nonneg.trans hCD,h.size.trans hCD,h.derivative.trans hCD⟩

lemma SmallBound.seed (s : Fin n→ℝ) (x : Spin n) :
    SmallBound (fun _=>s) x (vectorNorm s) := by
  refine ⟨vectorNorm_nonneg _,le_rfl,?_⟩
  have he : derivativeMatrix (fun _=>s) x=0 := by ext i k; simp [derivativeMatrix,halfDiff]
  rw [he,norm_zero]; exact vectorNorm_nonneg _

lemma SmallBound.add {U V : VectorFields n} {x : Spin n} {C D : ℝ}
    (hU : SmallBound U x C) (hV : SmallBound V x D) :
    SmallBound (fun x i=>U x i+V x i) x (C+D) := by
  refine ⟨add_nonneg hU.nonneg hV.nonneg,(vectorNorm_add _ _).trans (add_le_add hU.size hV.size),?_⟩
  rw [derivativeMatrix_add]
  exact (norm_add_le _ _).trans (add_le_add hU.derivative hV.derivative)

lemma SmallBound.smul {U : VectorFields n} {x : Spin n} {C : ℝ}
    (hU : SmallBound U x C) (c : ℝ) : SmallBound (fun x i=>c*U x i) x (|c| *C) := by
  refine ⟨mul_nonneg (abs_nonneg _) hU.nonneg,?_,?_⟩
  · calc
      _ = |c| *vectorNorm (U x) := vectorNorm_smul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hU.size (abs_nonneg _)
  · rw [derivativeMatrix_smul,norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hU.derivative (abs_nonneg _)

lemma SmallBound.sub {U V : VectorFields n} {x : Spin n} {C D : ℝ}
    (hU : SmallBound U x C) (hV : SmallBound V x D) :
    SmallBound (fun x i=>U x i-V x i) x (C+D) := by
  simpa only [abs_neg,abs_one,one_mul,neg_one_mul,sub_eq_add_neg] using hU.add (hV.smul (-1))

lemma SmallBound.sum {ι : Type*} [Fintype ι] {U : ι→VectorFields n} {x : Spin n} {C : ι→ℝ}
    (hU : ∀l,SmallBound (U l) x (C l)) :
    SmallBound (fun x i=>∑l,U l x i) x (∑l,C l) := by
  refine ⟨Finset.sum_nonneg fun l _=>(hU l).nonneg,?_,?_⟩
  · have h:= (vectorNorm_sum (fun l=>U l x)).trans (Finset.sum_le_sum fun l _=>(hU l).size)
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    congr 1; ext i; simp
  · rw [derivativeMatrix_sum]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _=>(hU l).derivative)

lemma SmallBound.coefficient {U : VectorFields n} {x : Spin n} {C : ℝ}
    (hU : SmallBound U x C) (a : VectorFields n) {A R : ℝ}
    (hA : 0≤A) (hR : 0≤R) (ha : ∀i,|a x i|≤A)
    (hda : ∀i,∑k,(derivativeMatrix a x i k)^2≤R^2) :
    SmallBound (fun x i=>a x i*U x i) x (C*(A+3*R)) := by
  refine ⟨mul_nonneg hU.nonneg (by positivity),?_,?_⟩
  · exact ((vectorNorm_mul _ _ hA ha).trans (mul_le_mul_of_nonneg_left hU.size hA)).trans
      (by nlinarith [mul_nonneg hU.nonneg hR])
  · calc
      _ ≤ A*‖derivativeMatrix U x‖+R*vectorNorm (U x)+2*R*‖derivativeMatrix U x‖ :=
        source_frobenius a U x hA hR ha hda
      _ ≤ A*C+R*C+2*R*C := add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left hU.derivative hA) (mul_le_mul_of_nonneg_left hU.size hR))
        (mul_le_mul_of_nonneg_left hU.derivative (by positivity))
      _ = _ := by ring

lemma SmallBound.linear {U : VectorFields n} {x : Spin n} {C : ℝ}
    (hU : SmallBound U x C) (J : Interaction n) :
    SmallBound (fun x=>J.mulVec (U x)) x (SKGap.opNorm J*C) := by
  refine ⟨mul_nonneg (norm_nonneg _) hU.nonneg,
    (vectorNorm_matrix_mul _ _).trans (mul_le_mul_of_nonneg_left hU.size (norm_nonneg _)),?_⟩
  have he : derivativeMatrix (fun x=>J.mulVec (U x)) x=J*derivativeMatrix U x := by
    convert! derivativeMatrix_linear J U (fun _=>0) x using 1
    all_goals try with_reducible_and_instances rfl
    simp only [zero_add]; rfl
  rw [he]
  exact (SKGap.frobenius_mul_le_opNorm _ _).trans (mul_le_mul_of_nonneg_left hU.derivative (norm_nonneg _))

lemma SmallBound.primaryCorrection {U : VectorFields n} {x : Spin n} {C P : ℝ}
    (hU : SmallBound U x C) (m : VectorFields n) (hn : 0<n) (hP : 0≤P)
    (hm : ∀i,|m x i|≤1) (hdm : SKGap.opNorm (derivativeMatrix m x)≤P) :
    SmallBound (fun y i=>siteMean U y*m y i) x (C*(1+3*P)) := by
  refine ⟨mul_nonneg hU.nonneg (by positivity),?_,
    primary_mean_frobenius U m x hn hU.nonneg hP hU.size hU.derivative hm hdm⟩
  exact ((primary_mean_size U m x hn hm).trans hU.size).trans (by nlinarith [mul_nonneg hU.nonneg hP])

lemma SmallBound.auxiliaryCorrection {U : VectorFields n} {x : Spin n} {C : ℝ}
    (hU : SmallBound U x C) (a : VectorFields n) {A R : ℝ}
    (hA : 0≤A) (hR : 0≤R) (ha : ∀i,|a x i|≤A)
    (hda : ∀i,∑k,(derivativeMatrix a x i k)^2≤R^2) :
    SmallBound (fun y i=>siteMean a y*U y i) x (C*(A+3*R)) := by
  apply hU.coefficient (fun x _=>siteMean a x) hA hR (fun _=>coefficient_mean_value a x hA ha)
  intro i
  have H:=pow_le_pow_left₀ (norm_nonneg _) (coefficient_mean_difference a x hR hda) 2
  simpa only [derivativeMatrix,derivativeVector,EuclideanSpace.real_norm_sq_eq,WithLp.ofLp_toLp] using H

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_WordPartnerContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open scoped BigOperators
variable {ι : Type*}

lemma wordPartners_inverse_sides (a : ι→ℝ) (F : List (WordLetter ι)) (c : WordCut ι)
    (hc : c∈wordPartners a F) (hi : c.inversePartner=true) :
    1≤ inverseCount c.left ∧ 1≤ inverseCount c.right := by
  induction F generalizing c with
  | nil => simp [wordPartners] at hc
  | cons l F ih =>
    rw [wordPartners_cons,List.mem_append] at hc
    rcases hc with hc|hc
    · cases l with
      | diag d => simp at hc
      | noise => simp only [List.mem_singleton] at hc;subst c;contradiction
      | inverse =>
        simp only [List.mem_singleton] at hc
        subst c
        simp [inverseCount]
    · obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
      have hh := ih d hd hi
      cases l <;> simp [WordCut.prepend,inverseCount] at * <;> tauto

lemma wordRecursionAt_one_inverse (a : ι→ℝ) (P Q : List (WordLetter ι))
    (hI : inverseCount (P++(.noise::Q))≤1)
    (t : WordRecursionTerm ι) (ht : t∈wordRecursionAt a P Q) :
    inverseCount t.outer≤1 ∧ inverseCount t.inner≤1 := by
  dsimp only [wordRecursionAt] at ht
  rw [List.mem_append] at ht
  simp only [inverseCount_append,inverseCount_noise] at hI
  rcases ht with ht|ht
  · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ht
    have hh := (wordPartners_counts a P c hc).2
    cases hi : c.inversePartner
    · simp [WordCut.asLeft,hi] at *;omega
    · have hs := wordPartners_inverse_sides a P c hc hi
      simp [WordCut.asLeft,hi] at *;omega
  · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ht
    have hh := (wordPartners_counts a Q c hc).2
    cases hi : c.inversePartner
    · simp [WordCut.asRight,hi] at *;omega
    · have hs := wordPartners_inverse_sides a Q c hc hi
      simp [WordCut.asRight,hi] at *;omega

lemma firstNoiseSplit_none (F : List (WordLetter ι)) : firstNoiseSplit F=none ↔ ordinaryCount F=0 := by
  induction F with
  | nil => simp [firstNoiseSplit,ordinaryCount]
  | cons l F ih => cases l <;> simp [firstNoiseSplit,ordinaryCount] at * <;> exact ih

lemma wordRecursionTerms_one_inverse (a : ι→ℝ) (F : List (WordLetter ι))
    (hI : inverseCount F≤1) (t : WordRecursionTerm ι) (ht : t∈wordRecursionTerms a F) :
    inverseCount t.outer≤1 ∧ inverseCount t.inner≤1 := by
  unfold wordRecursionTerms at ht
  cases hs : firstNoiseSplit F with
  | none => simp [hs] at ht
  | some pq =>
    rcases pq with ⟨P,Q⟩
    have he := firstNoiseSplit_some F P Q hs
    simp only [hs] at ht
    exact wordRecursionAt_one_inverse a P Q (by simpa only [he] using hI) t ht

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_NoiseSplit
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.Noncrossing.Diagram.pairedNilUnique _root_.OAI.SKGap.Noncrossing.WordSeries.noiseSplitNilIsEmpty _root_.OAI.SKGap.Noncrossing.noiseSplitDiagIsEmpty _root_.OAI.SKGap.Noncrossing.noiseSplitNoiseUnique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
namespace Diagram
variable {D : Type*}

section Evaluate
variable {ι : Type*} [Fintype ι]

lemma evaluate_insert (j : ℝ) (v : D→ι→ℝ) (d e : Diagram D) (p : ℕ) (i : ι) :
    evaluate j v (d.insert p e) i = j*mean (evaluate j v e)*evaluate j v d i := by
  induction d generalizing p i with
  | nil => simp only [insert]; split_ifs <;> rfl
  | diag a d ih =>
    by_cases hp : p=0
    · simp [hp]
    · simp only [insert,hp,↓reduceIte,evaluate_diag,ih]; ring
  | arch a b ia ib =>
    by_cases hp : p=0
    · simp [hp]
    · simp only [insert,hp,↓reduceIte]
      split_ifs
      · have hh : evaluate j v (a.insert (p-1) e) =
            fun k => j*mean (evaluate j v e)*evaluate j v a k := funext (ia (p-1))
        simp only [evaluate_arch,hh,mean_const_mul]; ring
      · simp only [evaluate_arch,ib]; ring

lemma mean_expect (j : ℝ) (v : D→ι→ℝ) (F : List (Letter D)) :
    mean (expect j v F) = ∑ d : Paired F, mean (evaluate j v d.val) := by
  simp only [mean,expect]
  rw [Finset.sum_comm,Finset.sum_div]

lemma expect_cut (j : ℝ) (v : D→ι→ℝ) (F : List (Letter D)) (k : ℕ)
    (hk : F[k]?=some .noise) (i : ι) :
    expect j v F i = ∑ s : PairShape F k,
      j * mean (expect j v s.between) * expect j v (s.before++s.after) i := by
  let e := (cutEquiv F k hk).trans (separateEquiv F k)
  have he : expect j v F i = ∑ z : Separated F k,
      j*mean (evaluate j v z.2.1.val)*evaluate j v z.2.2.val i := by
    apply Fintype.sum_equiv e
    intro d
    have hd : d.val.word[k]?=some .noise := by rw [d.property]; exact hk
    have hc := cut_spec d.val k _ (cut_markedCut d.val k hd)
    change evaluate j v d.val i =
      j*mean (evaluate j v (d.val.markedCut k hd).inside)*
        evaluate j v (d.val.markedCut k hd).outside i
    exact (congrArg (fun a => evaluate j v a i) hc.2.2).symm.trans
      (evaluate_insert j v _ _ _ i)
  rw [he]
  change (∑ z : Σ s : PairShape F k, Paired s.between × Paired (s.before++s.after),
    j*mean (evaluate j v z.2.1.val)*evaluate j v z.2.2.val i) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro s _
  rw [Fintype.sum_prod_type]
  change (∑ a : Paired s.between, ∑ b : Paired (s.before++s.after),
    j*mean (evaluate j v a.val)*evaluate j v b.val i) = _
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul,← Finset.mul_sum,← mean_expect]
  rfl

theorem expect_at (j : ℝ) (v : D→ι→ℝ) (P Q : List (Letter D)) (i : ι) :
    expect j v (P++(.noise::Q)) i =
      (∑ s : NoiseSplit P, j*mean (expect j v s.after)*expect j v (s.before++Q) i) +
      (∑ s : NoiseSplit Q, j*mean (expect j v s.before)*expect j v (P++s.after) i) := by
  rw [expect_cut j v _ P.length (by simp)]
  have hh := Fintype.sum_equiv (shapeAtEquiv P Q)
    (fun s : NoiseSplit P ⊕ NoiseSplit Q => match s with
      | .inl s => j*mean (expect j v s.after)*expect j v (s.before++Q) i
      | .inr s => j*mean (expect j v s.before)*expect j v (P++s.after) i)
    (fun s => j*mean (expect j v s.between)*expect j v (s.before++s.after) i)
    (by intro s; cases s <;> rfl)
  rw [← hh,Fintype.sum_sum_type]

end Evaluate
end Diagram
end SKGap.Noncrossing

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Map
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.Noncrossing.Diagram.pairedNilUnique _root_.OAI.SKGap.Noncrossing.Primary.Tensor.Loop.blocksOneUnique _root_.OAI.SKGap.Noncrossing.WordSeries.blocksZeroUnique _root_.OAI.SKGap.Noncrossing.WordSeries.noiseSplitNilIsEmpty _root_.OAI.SKGap.Noncrossing.noiseSplitDiagIsEmpty _root_.OAI.SKGap.Noncrossing.noiseSplitNoiseUnique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
namespace Diagram
variable {D E : Type*}

lemma NoiseSplit.sum_append {M : Type*} [AddCommMonoid M]
    (P Q : List (Letter D)) (f : List (Letter D)→List (Letter D)→M) :
    (∑ s : NoiseSplit (P++Q), f s.before s.after) =
      (∑ s : NoiseSplit P, f s.before (s.after++Q))+
      (∑ s : NoiseSplit Q, f (P++s.before) s.after) := by
  have he := Fintype.sum_equiv (NoiseSplit.appendEquiv P Q)
    (fun s => match s with
      | .inl s => f s.before (s.after++Q)
      | .inr s => f (P++s.before) s.after)
    (fun s => f s.before s.after) (by intro s; cases s <;> rfl)
  rw [← he,Fintype.sum_sum_type]

end Diagram
end SKGap.Noncrossing

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
namespace InverseDiagram
open Diagram

theorem sum_marked_blocks {M : Type*} [AddCommMonoid M] (n : ℕ)
    (f : List (Letter Bool)→List (Letter Bool)→M) :
    (∑ bs : Blocks (n+1), ∑ s : NoiseSplit (expandBlocks bs.val), f s.before s.after) =
      ∑ k : Fin (n+1), ∑ p : Blocks k.val, ∑ q : Blocks (n-k.val),
        f (expandBlocks p.val++[.diag true]) (expandBlocks q.val) := by
  have he := Fintype.sum_equiv (markedBlockEquiv n)
    (fun z => f (expandBlocks z.2.1.val++[.diag true]) (expandBlocks z.2.2.val))
    (fun z => f z.2.before z.2.after) (by intro z; rfl)
  change (∑ z : Σ k : Fin (n+1), Blocks k.val × Blocks (n-k.val),
    f (expandBlocks z.2.1.val++[.diag true]) (expandBlocks z.2.2.val)) =
    (∑ z : Σ bs : Blocks (n+1), NoiseSplit (expandBlocks bs.val),
      f z.2.before z.2.after) at he
  rw [Fintype.sum_sigma,Fintype.sum_sigma] at he
  simp_rw [Fintype.sum_prod_type] at he
  exact he.symm

end InverseDiagram
end SKGap.Noncrossing

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_Map
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.Noncrossing.Diagram.pairedNilUnique _root_.OAI.SKGap.Noncrossing.WordSeries.noiseSplitNilIsEmpty _root_.OAI.SKGap.Noncrossing.noiseSplitDiagIsEmpty _root_.OAI.SKGap.Noncrossing.noiseSplitNoiseUnique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
namespace Diagram
variable {D E : Type*}

lemma map_map {G : Type*} (f : D→E) (g : E→G) (d : Diagram D) :
    (d.map f).map g=d.map (g∘f) := by induction d <;> simp_all [map]

variable {ι : Type*} [Fintype ι]
lemma evaluate_map (j : ℝ) (v : E→ι→ℝ) (f : D→E) (d : Diagram D) :
    evaluate j v (d.map f)=evaluate j (v∘f) d := by simp [evaluate,map_map]

lemma expect_map (j : ℝ) (v : E→ι→ℝ) (f : D→E) (F : List (Letter D)) (i : ι) :
    expect j v (F.map (Letter.map f)) i=expect j (v∘f) F i := by
  symm
  apply Fintype.sum_equiv (Paired.mapEquiv f F)
  intro d
  exact congrFun (evaluate_map j v f d.val).symm i

end Diagram
end SKGap.Noncrossing

end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_Ordinary
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.Noncrossing.Diagram.pairedNilUnique _root_.OAI.SKGap.Noncrossing.Primary.Tensor.Loop.blocksOneUnique _root_.OAI.SKGap.Noncrossing.WordSeries.noiseSplitNilIsEmpty _root_.OAI.SKGap.Noncrossing.noiseSplitDiagIsEmpty _root_.OAI.SKGap.Noncrossing.noiseSplitNoiseUnique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
open Diagram InverseDiagram
namespace WordSeries
variable {ι : Type*} [Fintype ι]

lemma inverseCoefficient_empty (j : ℝ) (a : ι→ℝ) (n : ℕ) (i : ι) :
    inverseCoefficient j a [] [] n i=if n=0 then 1 else 0 := by
  have he : inverseCoefficient j a [] [] n i=literalCoefficient j a n i := by
    simp only [inverseCoefficient,List.nil_append,List.append_nil,ordinary,chain,expect_map,
      Function.id_comp]
    symm
    change (∑ z : Σ bs : Blocks n, Paired (expandBlocks bs.val), _) = _
    rw [Fintype.sum_sigma]
    rfl
  rw [he,literalCoefficient_eq]

lemma mean_inverseCoefficient (j : ℝ) (a : ι→ℝ)
    (P Q : List (Letter (ι→ℝ))) (n : ℕ) :
    mean (inverseCoefficient j a P Q n) =
      ∑ bs : Blocks n, mean (ordinary j (P++chain j a bs.val++Q)) := by
  simp only [mean,inverseCoefficient]
  rw [Finset.sum_comm,Finset.sum_div]

lemma sum_marked_chain {M : Type*} [AddCommMonoid M] (j : ℝ) (a : ι→ℝ) (n : ℕ)
    (f : List (Letter (ι→ℝ))→List (Letter (ι→ℝ))→M) :
    (∑ bs : Blocks (n+1), ∑ s : NoiseSplit (chain j a bs.val), f s.before s.after) =
      ∑ k : Fin (n+1), ∑ p : Blocks k.val, ∑ q : Blocks (n-k.val),
        f (chain j a p.val++[.diag a]) (chain j a q.val) := by
  calc
    _ = ∑ bs : Blocks (n+1), ∑ s : NoiseSplit (expandBlocks bs.val),
        f (s.before.map (Letter.map (blockLabel j a)))
          (s.after.map (Letter.map (blockLabel j a))) := by
      apply Finset.sum_congr rfl
      intro bs _
      symm
      apply Fintype.sum_equiv (NoiseSplit.mapEquiv (blockLabel j a) (expandBlocks bs.val))
      intro s; rfl
    _ = _ := by
      simpa only [List.map_append,List.map_cons,List.map_nil,Letter.map,blockLabel,chain] using
        sum_marked_blocks n (fun P Q => f (P.map (Letter.map (blockLabel j a)))
          (Q.map (Letter.map (blockLabel j a))))

lemma inverse_partner_right (j : ℝ) (a : ι→ℝ) (P R T : List (Letter (ι→ℝ)))
    (n : ℕ) (i : ι) :
    (∑ bs : Blocks (n+1), ∑ s : NoiseSplit (chain j a bs.val),
      j*mean (ordinary j (R++s.before))*ordinary j (P++s.after++T) i) =
      ∑ k : Fin (n+1), j*mean (inverseCoefficient j a R [.diag a] k.val)*
        inverseCoefficient j a P T (n-k.val) i := by
  rw [sum_marked_chain j a n (fun P' Q' =>
    j*mean (ordinary j (R++P'))*ordinary j (P++Q'++T) i)]
  apply Finset.sum_congr rfl
  intro k _
  simp only [List.append_assoc]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul,← Finset.mul_sum,mean_inverseCoefficient]
  simp only [inverseCoefficient,List.append_assoc]

end WordSeries
end SKGap.Noncrossing

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
namespace WordSeries
open Diagram InverseDiagram
variable {ι : Type*} [Fintype ι]

lemma ordinary_cut_right (j : ℝ) (P R K T : List (Letter (ι→ℝ))) (i : ι) :
    ordinary j ((P++(.noise::R))++K++T) i =
      (∑ s : NoiseSplit P, j*mean (ordinary j s.after)*ordinary j (s.before++R++K++T) i) +
      (∑ s : NoiseSplit R, j*mean (ordinary j s.before)*ordinary j (P++s.after++K++T) i) +
      (∑ s : NoiseSplit K, j*mean (ordinary j (R++s.before))*ordinary j (P++s.after++T) i) +
      (∑ s : NoiseSplit T, j*mean (ordinary j (R++K++s.before))*ordinary j (P++s.after) i) := by
  have hh := expect_at j (id : (ι→ℝ)→ι→ℝ) P (R++(K++T)) i
  rw [NoiseSplit.sum_append R (K++T) (fun U V =>
    j*mean (expect j id U)*expect j id (P++V) i)] at hh
  rw [NoiseSplit.sum_append K T (fun U V =>
    j*mean (expect j id (R++U))*expect j id (P++V) i)] at hh
  simpa only [ordinary,List.append_assoc,List.cons_append,add_assoc] using hh

theorem inverseCoefficient_right (j : ℝ) (a : ι→ℝ)
    (P R T : List (Letter (ι→ℝ))) (n : ℕ) (i : ι) :
    inverseCoefficient j a (P++(.noise::R)) T (n+1) i =
      (∑ s : NoiseSplit P, j*mean (ordinary j s.after)*
        inverseCoefficient j a (s.before++R) T (n+1) i) +
      (∑ s : NoiseSplit R, j*mean (ordinary j s.before)*
        inverseCoefficient j a (P++s.after) T (n+1) i) +
      (∑ k : Fin (n+1), j*mean (inverseCoefficient j a R [.diag a] k.val)*
        inverseCoefficient j a P T (n-k.val) i) +
      (∑ s : NoiseSplit T, j*mean (inverseCoefficient j a R s.before (n+1))*
        ordinary j (P++s.after) i) := by
  have hh : inverseCoefficient j a (P++(.noise::R)) T (n+1) i =
      (∑ bs : Blocks (n+1), ∑ s : NoiseSplit P, j*mean (ordinary j s.after)*
        ordinary j (s.before++R++chain j a bs.val++T) i) +
      (∑ bs : Blocks (n+1), ∑ s : NoiseSplit R, j*mean (ordinary j s.before)*
        ordinary j (P++s.after++chain j a bs.val++T) i) +
      (∑ bs : Blocks (n+1), ∑ s : NoiseSplit (chain j a bs.val),
        j*mean (ordinary j (R++s.before))*ordinary j (P++s.after++T) i) +
      (∑ bs : Blocks (n+1), ∑ s : NoiseSplit T, j*mean (ordinary j (R++chain j a bs.val++s.before))*
        ordinary j (P++s.after) i) := by
    unfold inverseCoefficient
    simp_rw [ordinary_cut_right,Finset.sum_add_distrib]
  rw [hh,inverse_partner_right]
  congr 2
  · congr 1
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      rw [← Finset.mul_sum]
      rfl
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      rw [← Finset.mul_sum]
      rfl
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    rw [← Finset.sum_mul,← Finset.mul_sum,← mean_inverseCoefficient]

end WordSeries
end SKGap.Noncrossing

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_OrdinaryCutLeft
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.Noncrossing.Diagram.pairedNilUnique _root_.OAI.SKGap.Noncrossing.Primary.Tensor.Loop.blocksOneUnique _root_.OAI.SKGap.Noncrossing.WordSeries.noiseSplitNilIsEmpty _root_.OAI.SKGap.Noncrossing.noiseSplitDiagIsEmpty _root_.OAI.SKGap.Noncrossing.noiseSplitNoiseUnique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
namespace WordSeries
open Diagram InverseDiagram
variable {ι : Type*} [Fintype ι]

lemma ordinary_cut_left (j : ℝ) (P K R T : List (Letter (ι→ℝ))) (i : ι) :
    ordinary j (P++K++R++(.noise::T)) i =
      (∑ s : NoiseSplit P, j*mean (ordinary j (s.after++K++R))*ordinary j (s.before++T) i) +
      (∑ s : NoiseSplit K, j*mean (ordinary j (s.after++R))*ordinary j (P++s.before++T) i) +
      (∑ s : NoiseSplit R, j*mean (ordinary j s.after)*ordinary j (P++K++s.before++T) i) +
      (∑ s : NoiseSplit T, j*mean (ordinary j s.before)*ordinary j (P++K++R++s.after) i) := by
  have hh := expect_at j (id : (ι→ℝ)→ι→ℝ) (P++(K++R)) T i
  rw [NoiseSplit.sum_append P (K++R) (fun U V =>
    j*mean (expect j id V)*expect j id (U++T) i)] at hh
  rw [NoiseSplit.sum_append K R (fun U V =>
    j*mean (expect j id V)*expect j id ((P++U)++T) i)] at hh
  simpa only [ordinary,List.append_assoc,add_assoc] using hh

lemma inverse_partner_left (j : ℝ) (a : ι→ℝ) (P R T : List (Letter (ι→ℝ)))
    (n : ℕ) (i : ι) :
    (∑ bs : Blocks (n+1), ∑ s : NoiseSplit (chain j a bs.val),
      j*mean (ordinary j (s.after++R))*ordinary j (P++s.before++T) i) =
      ∑ k : Fin (n+1), j*mean (inverseCoefficient j a [] R (n-k.val))*
        inverseCoefficient j a P (.diag a::T) k.val i := by
  rw [sum_marked_chain j a n (fun U V =>
    j*mean (ordinary j (V++R))*ordinary j (P++U++T) i)]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  simp only [List.append_assoc,List.cons_append,List.nil_append]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul,← Finset.mul_sum,mean_inverseCoefficient]
  simp only [inverseCoefficient,List.append_assoc,List.nil_append]

theorem inverseCoefficient_left (j : ℝ) (a : ι→ℝ)
    (P R T : List (Letter (ι→ℝ))) (n : ℕ) (i : ι) :
    inverseCoefficient j a P (R++(.noise::T)) (n+1) i =
      (∑ s : NoiseSplit P, j*mean (inverseCoefficient j a s.after R (n+1))*
        ordinary j (s.before++T) i) +
      (∑ k : Fin (n+1), j*mean (inverseCoefficient j a [] R (n-k.val))*
        inverseCoefficient j a P (.diag a::T) k.val i) +
      (∑ s : NoiseSplit R, j*mean (ordinary j s.after)*
        inverseCoefficient j a P (s.before++T) (n+1) i) +
      (∑ s : NoiseSplit T, j*mean (ordinary j s.before)*
        inverseCoefficient j a P (R++s.after) (n+1) i) := by
  have hh : inverseCoefficient j a P (R++(.noise::T)) (n+1) i =
      (∑ bs : Blocks (n+1), ∑ s : NoiseSplit P, j*mean (ordinary j (s.after++chain j a bs.val++R))*
        ordinary j (s.before++T) i) +
      (∑ bs : Blocks (n+1), ∑ s : NoiseSplit (chain j a bs.val),
        j*mean (ordinary j (s.after++R))*ordinary j (P++s.before++T) i) +
      (∑ bs : Blocks (n+1), ∑ s : NoiseSplit R, j*mean (ordinary j s.after)*
        ordinary j (P++chain j a bs.val++s.before++T) i) +
      (∑ bs : Blocks (n+1), ∑ s : NoiseSplit T, j*mean (ordinary j s.before)*
        ordinary j (P++chain j a bs.val++R++s.after) i) := by
    unfold inverseCoefficient
    have hcut (bs : Blocks (n+1)) := ordinary_cut_left j P (chain j a bs.val) R T i
    have he := Finset.sum_congr rfl (fun bs (_ : bs∈(Finset.univ : Finset (Blocks (n+1)))) => hcut bs)
    simpa only [List.append_assoc,Finset.sum_add_distrib] using he
  rw [hh,inverse_partner_left]
  congr 2
  · congr 2
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    rw [← Finset.sum_mul,← Finset.mul_sum,← mean_inverseCoefficient]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    rw [← Finset.mul_sum]
    simp only [inverseCoefficient,List.append_assoc]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    rw [← Finset.mul_sum]
    simp only [inverseCoefficient,List.append_assoc]

end WordSeries
end SKGap.Noncrossing

end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_InverseSeries
attribute [-instance] _root_.OAI.SKGap.Noncrossing.Diagram.pairedNilUnique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.WordSeries
open Diagram InverseDiagram PowerSeries
variable {ι : Type*} [Fintype ι]

lemma coeff_mul_fin (p q : ℝ⟦X⟧) (n : ℕ) :
    coeff n (p*q)=∑ k : Fin (n+1), coeff k.val p*coeff (n-k.val) q := by
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k l => coeff k p*coeff l q) n]
  exact (Fin.sum_univ_eq_sum_range (fun k => coeff k p*coeff (n-k) q) (n+1)).symm

lemma inverseSeries_right (j : ℝ) (a : ι→ℝ) (P R T : List (Letter (ι→ℝ))) (i : ι) :
    inverseSeries j a (P++(.noise::R)) T i =
      (∑ s : NoiseSplit P, C (j*mean (ordinary j s.after))*inverseSeries j a (s.before++R) T i) +
      (∑ s : NoiseSplit R, C (j*mean (ordinary j s.before))*inverseSeries j a (P++s.after) T i) +
      X*(C j*meanSeries (inverseSeries j a R [.diag a])*inverseSeries j a P T i) +
      (∑ s : NoiseSplit T, C j*meanSeries (inverseSeries j a R s.before)*C (ordinary j (P++s.after) i)) := by
  ext n
  cases n with
  | zero =>
    simp only [map_add,map_sum,coeff_inverseSeries,coeff_C_mul,coeff_mul_C,coeff_meanSeries,
      inverseCoefficient_zero,coeff_zero_X_mul,add_zero]
    simpa only [ordinary,List.append_assoc,List.nil_append,List.append_nil,Finset.univ_eq_empty,
      Finset.sum_empty,add_zero] using
      ordinary_cut_right j P R ([] : List (Letter (ι→ℝ))) T i
  | succ n =>
    simp only [map_add,map_sum,coeff_inverseSeries,coeff_C_mul,coeff_mul_C,coeff_meanSeries,
      coeff_succ_X_mul,coeff_mul_fin]
    exact inverseCoefficient_right j a P R T n i

lemma inverseSeries_left (j : ℝ) (a : ι→ℝ) (P R T : List (Letter (ι→ℝ))) (i : ι) :
    inverseSeries j a P (R++(.noise::T)) i =
      (∑ s : NoiseSplit P, C j*meanSeries (inverseSeries j a s.after R)*C (ordinary j (s.before++T) i)) +
      X*(C j*meanSeries (inverseSeries j a [] R)*inverseSeries j a P (.diag a::T) i) +
      (∑ s : NoiseSplit R, C (j*mean (ordinary j s.after))*inverseSeries j a P (s.before++T) i) +
      (∑ s : NoiseSplit T, C (j*mean (ordinary j s.before))*inverseSeries j a P (R++s.after) i) := by
  ext n
  cases n with
  | zero =>
    simp only [map_add,map_sum,coeff_inverseSeries,coeff_C_mul,coeff_mul_C,coeff_meanSeries,
      inverseCoefficient_zero,coeff_zero_X_mul,add_zero]
    simpa only [ordinary,List.append_assoc,List.nil_append,List.append_nil,Finset.univ_eq_empty,
      Finset.sum_empty,add_zero] using
      ordinary_cut_left j P ([] : List (Letter (ι→ℝ))) R T i
  | succ n =>
    simp only [map_add,map_sum,coeff_inverseSeries,coeff_C_mul,coeff_mul_C,coeff_meanSeries,
      coeff_succ_X_mul,coeff_mul_fin]
    rw [inverseCoefficient_left]
    congr 2
    congr 1
    apply Fintype.sum_equiv (Fin.revPerm (n := n+1))
    intro k
    simp only [Fin.revPerm_apply,Fin.val_rev]
    rw [show n+1-(k.val+1)=n-k.val by omega, Nat.sub_sub_self (Nat.le_of_lt_succ k.isLt)]

end SKGap.Noncrossing.WordSeries

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
open Diagram InverseDiagram WordSeries PowerSeries
variable {ι : Type*}

lemma exists_lift_of_no_inverse (F : List (WordLetter ι)) (h : inverseCount F=0) :
    ∃ P : List (Letter (ι→ℝ)), liftWord P=F := by
  induction F with
  | nil => exact ⟨[],rfl⟩
  | cons l F ih =>
    cases l with
    | inverse => simp [inverseCount] at h
    | diag d =>
      obtain ⟨P,rfl⟩ := ih (by simpa [inverseCount] using h)
      exact ⟨.diag d::P,rfl⟩
    | noise =>
      obtain ⟨P,rfl⟩ := ih (by simpa [inverseCount] using h)
      exact ⟨.noise::P,rfl⟩

lemma one_inverse_cases (F : List (WordLetter ι)) (h : inverseCount F≤1) :
    (∃ P, F=liftWord P) ∨ (∃ P Q, F=liftWord P++(.inverse::liftWord Q)) := by
  induction F with
  | nil => exact Or.inl ⟨[],rfl⟩
  | cons l F ih =>
    cases l with
    | inverse =>
      have hz : inverseCount F=0 := by rw [inverseCount_inverse] at h; omega
      obtain ⟨P,rfl⟩ := exists_lift_of_no_inverse F hz
      exact Or.inr ⟨[],P,rfl⟩
    | diag d =>
      have ht : inverseCount F≤1 := by simpa [inverseCount] using h
      rcases ih ht with ⟨P,rfl⟩ | ⟨P,Q,rfl⟩
      · exact Or.inl ⟨.diag d::P,rfl⟩
      · exact Or.inr ⟨.diag d::P,Q,rfl⟩
    | noise =>
      have ht : inverseCount F≤1 := by simpa [inverseCount] using h
      rcases ih ht with ⟨P,rfl⟩ | ⟨P,Q,rfl⟩
      · exact Or.inl ⟨.noise::P,rfl⟩
      · exact Or.inr ⟨.noise::P,Q,rfl⟩

lemma sum_noiseSplit_cons_diag {D M : Type*} [AddCommMonoid M] (d : D) (F : List (Letter D))
    (f : List (Letter D)→List (Letter D)→M) :
    (∑ s : NoiseSplit (.diag d::F), f s.before s.after)=
      ∑ s : NoiseSplit F, f (.diag d::s.before) s.after := by
  have hh := NoiseSplit.sum_append [Letter.diag d] F f
  simpa using hh
lemma sum_noiseSplit_cons_noise {D M : Type*} [AddCommMonoid M] (F : List (Letter D))
    (f : List (Letter D)→List (Letter D)→M) :
    (∑ s : NoiseSplit (.noise::F), f s.before s.after)=
      f [] F+∑ s : NoiseSplit F, f (.noise::s.before) s.after := by
  have hh := NoiseSplit.sum_append [Letter.noise] F f
  have he : (default : NoiseSplit [Letter.noise (D := D)])=⟨[],[],rfl⟩ := Subsingleton.elim _ _
  simpa only [Fintype.sum_unique,he,List.nil_append,List.singleton_append] using hh

lemma sum_wordPartners_lift {M : Type*} [AddCommMonoid M] (a : ι→ℝ)
    (F : List (Letter (ι→ℝ))) (f : WordCut ι→M) :
    ((wordPartners a (liftWord F)).map f).sum=
      ∑ s : NoiseSplit F, f ⟨liftWord s.before,liftWord s.after,false⟩ := by
  induction F generalizing f with
  | nil => simp [wordPartners]
  | cons l F ih =>
    cases l with
    | diag d =>
      simp only [liftWord_cons,Letter.toWord,wordPartners,List.nil_append,List.map_map]
      rw [ih,sum_noiseSplit_cons_diag d F (fun U V=>f ⟨liftWord U,liftWord V,false⟩)]
      rfl
    | noise =>
      simp only [liftWord_cons,Letter.toWord,wordPartners,List.singleton_append,List.map_cons,
        List.sum_cons,List.map_map]
      rw [ih,sum_noiseSplit_cons_noise F (fun U V=>f ⟨liftWord U,liftWord V,false⟩)]
      rfl

lemma sum_wordPartners_append {M : Type*} [AddCommMonoid M] (a : ι→ℝ)
    (P Q : List (WordLetter ι)) (f : WordCut ι→M) :
    ((wordPartners a (P++Q)).map f).sum=
      ((wordPartners a P).map (fun c=>f ⟨c.left,c.right++Q,c.inversePartner⟩)).sum+
      ((wordPartners a Q).map (fun c=>f ⟨P++c.left,c.right,c.inversePartner⟩)).sum := by
  induction P generalizing f with
  | nil => simp [wordPartners]
  | cons l P ih =>
    cases l <;>
      simp only [List.cons_append,wordPartners,List.nil_append,
        List.map_cons,List.sum_cons,List.map_map,Function.comp_def,WordCut.prepend] <;>
      rw [ih] <;> simp only [add_assoc]

lemma sum_wordPartners_oneInverse {M : Type*} [AddCommMonoid M] (a : ι→ℝ)
    (P Q : List (Letter (ι→ℝ))) (f : WordCut ι→M) :
    ((wordPartners a (liftWord P++(.inverse::liftWord Q))).map f).sum=
      (∑ s : NoiseSplit P, f ⟨liftWord s.before,liftWord s.after++(.inverse::liftWord Q),false⟩)+
      f ⟨liftWord P++[.inverse,.diag a],[.inverse]++liftWord Q,true⟩+
      (∑ s : NoiseSplit Q, f ⟨liftWord P++(.inverse::liftWord s.before),liftWord s.after,false⟩) := by
  rw [sum_wordPartners_append,sum_wordPartners_lift]
  simp only [wordPartners,List.singleton_append,List.map_cons,List.sum_cons,List.map_map,
    Function.comp_def,WordCut.prepend]
  rw [sum_wordPartners_lift]
  simp [add_assoc]

end SKGap.Noncrossing

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_ConsDiag
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.Noncrossing.Primary.Tensor.Loop.blocksOneUnique _root_.OAI.SKGap.Noncrossing.WordSeries.noiseSplitNilIsEmpty _root_.OAI.SKGap.Noncrossing.noiseSplitDiagIsEmpty _root_.OAI.SKGap.Noncrossing.noiseSplitNoiseUnique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
namespace Diagram
variable {D : Type*}

variable {ι : Type*} [Fintype ι]
@[simp] lemma expect_append_diag (j : ℝ) (v : D→ι→ℝ) (a : D) (F : List (Letter D)) (i : ι) :
    expect j v (F++[.diag a]) i=expect j v F i*v a i := by
  unfold expect
  rw [Finset.sum_mul]
  symm
  apply Fintype.sum_equiv (Paired.appendDiagEquiv a F)
  intro d
  simp [Paired.appendDiagEquiv,Paired.appendDiag,evaluate,map_append,map,value_append,value]
end Diagram
namespace WordSeries
open Diagram InverseDiagram
variable {ι : Type*} [Fintype ι]
@[simp] lemma ordinary_append_diag (j : ℝ) (d : ι→ℝ) (F : List (Letter (ι→ℝ))) (i : ι) :
    ordinary j (F++[.diag d]) i=ordinary j F i*d i := expect_append_diag j id d F i

lemma ordinary_diag_prefix (j : ℝ) (D : List (ι→ℝ)) (F : List (Letter (ι→ℝ))) (i : ι) :
    ordinary j (D.map Letter.diag++F) i=(D.map (fun d=>d i)).prod*ordinary j F i := by
  induction D with
  | nil => simp
  | cons d D ih => simp [ih,mul_assoc]
lemma ordinary_diag_suffix (j : ℝ) (D : List (ι→ℝ)) (F : List (Letter (ι→ℝ))) (i : ι) :
    ordinary j (F++D.map Letter.diag) i=ordinary j F i*(D.map (fun d=>d i)).prod := by
  induction D using List.reverseRecOn with
  | nil => simp
  | append_singleton D d ih =>
    simp only [List.map_append,List.map_singleton,List.prod_append,List.prod_singleton]
    rw [← List.append_assoc,ordinary_append_diag,ih,mul_assoc]
lemma inverseCoefficient_diagonal (j : ℝ) (a : ι→ℝ) (P Q : List (ι→ℝ)) (n : ℕ) (i : ι) :
    inverseCoefficient j a (P.map Letter.diag) (Q.map Letter.diag) n i=
      if n=0 then (P.map (fun d=>d i)).prod*(Q.map (fun d=>d i)).prod else 0 := by
  have he : inverseCoefficient j a (P.map Letter.diag) (Q.map Letter.diag) n i=
      (P.map (fun d=>d i)).prod*inverseCoefficient j a [] [] n i*(Q.map (fun d=>d i)).prod := by
    simp only [inverseCoefficient,List.nil_append,List.append_nil,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro bs _
    rw [List.append_assoc,ordinary_diag_prefix,ordinary_diag_suffix]
    ring
  rw [he,inverseCoefficient_empty]
  split_ifs <;> ring
end WordSeries
end SKGap.Noncrossing

end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LiteralSeriesLiftAppend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
open Diagram InverseDiagram WordSeries PowerSeries
variable {ι : Type*} [Fintype ι]

lemma literalSeries_at_noInverse (j : ℝ) (a : ι→ℝ)
    (P Q : List (Letter (ι→ℝ))) (i : ι) :
    literalSeries j a (liftWord P++(.noise::liftWord Q)) i=
      ((wordRecursionAt a (liftWord P) (liftWord Q)).map (fun t=>
        (if t.inversePartner then X else 1)*C j*meanSeries (literalSeries j a t.inner)*
          literalSeries j a t.outer i)).sum := by
  rw [show liftWord P++(.noise::liftWord Q)=liftWord (P++(.noise::Q)) by
    simp [liftWord,Letter.toWord]]
  simp only [wordRecursionAt,List.map_append,List.sum_append,List.map_map,
    WordCut.asLeft,WordCut.asRight,Function.comp_def]
  rw [sum_wordPartners_lift,sum_wordPartners_lift]
  simp only [Bool.false_eq_true,↓reduceIte,one_mul,literalSeries_lift,literalSeries_lift_append,
    literalSeries_lift_fun,meanSeries_C]
  have hh := congrArg C (expect_at j (id : (ι→ℝ)→ι→ℝ) P Q i)
  simpa only [map_add,map_sum,map_mul,ordinary,mul_assoc] using hh

lemma literalSeries_at_rightInverse (j : ℝ) (a : ι→ℝ)
    (P R T : List (Letter (ι→ℝ))) (i : ι) :
    literalSeries j a (liftWord P++(.noise::(liftWord R++(.inverse::liftWord T)))) i=
      ((wordRecursionAt a (liftWord P) (liftWord R++(.inverse::liftWord T))).map (fun t=>
        (if t.inversePartner then X else 1)*C j*meanSeries (literalSeries j a t.inner)*
          literalSeries j a t.outer i)).sum := by
  rw [show liftWord P++(.noise::(liftWord R++(.inverse::liftWord T)))=
      liftWord (P++(.noise::R))++(.inverse::liftWord T) by
    simp [liftWord,Letter.toWord,List.append_assoc]]
  simp only [wordRecursionAt,List.map_append,List.sum_append,List.map_map,
    WordCut.asLeft,WordCut.asRight,Function.comp_def]
  rw [sum_wordPartners_lift,sum_wordPartners_oneInverse]
  simp only [Bool.false_eq_true,↓reduceIte,one_mul,literalSeries_lift_append,
    literalSeries_oneInverse,literalSeries_two_prefix,literalSeries_oneInverse_fun,
    literalSeries_inverse_diag_fun,literalSeries_inverse_single_append,literalSeries_lift_fun,meanSeries_C]
  simpa only [map_mul,mul_assoc,add_assoc] using inverseSeries_right j a P R T i

lemma literalSeries_at_leftInverse (j : ℝ) (a : ι→ℝ)
    (P R T : List (Letter (ι→ℝ))) (i : ι) :
    literalSeries j a ((liftWord P++(.inverse::liftWord R))++(.noise::liftWord T)) i=
      ((wordRecursionAt a (liftWord P++(.inverse::liftWord R)) (liftWord T)).map (fun t=>
        (if t.inversePartner then X else 1)*C j*meanSeries (literalSeries j a t.inner)*
          literalSeries j a t.outer i)).sum := by
  rw [show (liftWord P++(.inverse::liftWord R))++(.noise::liftWord T)=
      liftWord P++(.inverse::liftWord (R++(.noise::T))) by
    simp [liftWord,Letter.toWord,List.append_assoc]]
  simp only [wordRecursionAt,List.map_append,List.sum_append,List.map_map,
    WordCut.asLeft,WordCut.asRight,Function.comp_def]
  rw [sum_wordPartners_oneInverse,sum_wordPartners_lift]
  simp only [Bool.false_eq_true,↓reduceIte,one_mul,literalSeries_lift_append,
    literalSeries_oneInverse,literalSeries_two_suffix,literalSeries_oneInverse_fun,
    literalSeries_inverse_diag_suffix,List.singleton_append,literalSeries_cons_inverse_fun,
    literalSeries_lift_fun,meanSeries_C]
  have hh := inverseSeries_left j a P R T i
  simp only [map_mul,mul_assoc,add_assoc] at hh ⊢
  exact hh

lemma literalSeries_at (j : ℝ) (a : ι→ℝ) (P Q : List (WordLetter ι))
    (hI : inverseCount (P++(.noise::Q))≤1) (i : ι) :
    literalSeries j a (P++(.noise::Q)) i=
      ((wordRecursionAt a P Q).map (fun t=>
        (if t.inversePartner then X else 1)*C j*meanSeries (literalSeries j a t.inner)*
          literalSeries j a t.outer i)).sum := by
  have hP : inverseCount P≤1 := by simp only [inverseCount_append,inverseCount_noise] at hI; omega
  have hQ : inverseCount Q≤1 := by simp only [inverseCount_append,inverseCount_noise] at hI; omega
  rcases one_inverse_cases P hP with ⟨P,rfl⟩ | ⟨P,R,rfl⟩
  · rcases one_inverse_cases Q hQ with ⟨Q,rfl⟩ | ⟨R,T,rfl⟩
    · exact literalSeries_at_noInverse j a P Q i
    · exact literalSeries_at_rightInverse j a P R T i
  · have hQ0 : inverseCount Q=0 := by
      simp only [inverseCount_append,inverseCount_inverse,inverseCount_noise,inverseCount_lift] at hI
      omega
    obtain ⟨T,rfl⟩ := exists_lift_of_no_inverse Q hQ0
    exact literalSeries_at_leftInverse j a P R T i

end SKGap.Noncrossing

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
open Diagram InverseDiagram WordSeries PowerSeries
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma exists_diagonals_of_count_zero (F : List (Letter (ι→ℝ)))
    (h : ordinaryCount (liftWord F)=0) : ∃ D : List (ι→ℝ), D.map Letter.diag=F := by
  induction F with
  | nil => exact ⟨[],rfl⟩
  | cons l F ih =>
    cases l with
    | noise => simp [liftWord,Letter.toWord,ordinaryCount] at h
    | diag d =>
      have ht : ordinaryCount (liftWord F)=0 := by simpa [liftWord,Letter.toWord,ordinaryCount] using h
      obtain ⟨D,rfl⟩ := ih ht
      exact ⟨d::D,rfl⟩

lemma literalSeries_base (j : ℝ) (a : ι→ℝ) (F : List (WordLetter ι))
    (hI : inverseCount F≤1) (ho : ordinaryCount F=0) (i : ι) :
    literalSeries j a F i=C (wordDiagonal F i) := by
  rcases one_inverse_cases F hI with ⟨P,rfl⟩ | ⟨P,Q,rfl⟩
  · obtain ⟨D,rfl⟩ := exists_diagonals_of_count_zero P ho
    rw [literalSeries_lift,wordDiagonal_diags]
    congr 1
    simpa using ordinary_diag_prefix j D [] i
  · have hc : ordinaryCount (liftWord P)+ordinaryCount (liftWord Q)=0 := by
      simpa [ordinaryCount,List.countP_append] using ho
    obtain ⟨D,rfl⟩ := exists_diagonals_of_count_zero P (by omega)
    obtain ⟨E,rfl⟩ := exists_diagonals_of_count_zero Q (by omega)
    rw [literalSeries_oneInverse,wordDiagonal_append,wordDiagonal_inverse,wordDiagonal_diags,wordDiagonal_diags]
    ext n
    rw [coeff_inverseSeries,inverseCoefficient_diagonal,coeff_C]

end SKGap.Noncrossing

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_WordPredictionStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix Set
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
lemma wordPrediction_base (j : ℝ) (a : ι→ℝ) (z : ℝ) (F : List (WordLetter ι)) (i : ι)
    (hO : ordinaryCount F=0) : wordPrediction j a z F i=wordDiagonal F i := by
  rw [wordPrediction,ite_eq_left hO]

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_WordDiagUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Polynomial
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma wordRecursionAt_degree_budget (a : ι→ℝ) (P Q : List (WordLetter ι))
    (t : WordRecursionTerm ι) (ht : t∈wordRecursionAt a P Q) :
    (if t.inversePartner then 1 else 0)+ordinaryCount t.inner+ordinaryCount t.outer ≤
      ordinaryCount (P++(.noise::Q)) := by
  dsimp only [wordRecursionAt] at ht
  rw [List.mem_append] at ht
  rcases ht with ht|ht
  · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ht
    have hh := (wordPartners_counts a P c hc).1
    cases hi : c.inversePartner <;> simp [WordCut.asLeft,hi] at * <;> omega
  · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ht
    have hh := (wordPartners_counts a Q c hc).1
    cases hi : c.inversePartner <;> simp [WordCut.asRight,hi] at * <;> omega

omit [Fintype ι] in
lemma wordRecursionTerms_degree_budget (a : ι→ℝ) (F : List (WordLetter ι))
    (t : WordRecursionTerm ι) (ht : t∈wordRecursionTerms a F) :
    (if t.inversePartner then 1 else 0)+ordinaryCount t.inner+ordinaryCount t.outer ≤ ordinaryCount F := by
  unfold wordRecursionTerms at ht
  cases hs : firstNoiseSplit F with
  | none => simp [hs] at ht
  | some pq =>
    rcases pq with ⟨P,Q⟩
    have he := firstNoiseSplit_some F P Q hs
    simp only [hs] at ht
    simpa only [he] using wordRecursionAt_degree_budget a P Q t ht

lemma polynomial_list_degree_le (l : List ℝ[X]) (n : ℕ) (h : ∀ p∈l,p.natDegree≤n) : l.sum.natDegree≤n := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [List.sum_cons]
    exact (natDegree_add_le p l.sum).trans (max_le (h p (List.mem_cons_self)) (ih (fun q hq=>h q (List.mem_cons_of_mem _ hq))))
lemma polynomial_eval_list_sum (l : List ℝ[X]) (z : ℝ) :
    eval z l.sum=(l.map (eval z)).sum := by
  induction l with
  | nil => simp
  | cons p l ih => simp only [List.sum_cons,eval_add,List.map_cons,ih]

theorem wordPredictionPolynomial_spec (j : ℝ) (a : ι→ℝ) (F : List (WordLetter ι)) :
    ∀ i,(wordPredictionPolynomial j a F i).natDegree≤ordinaryCount F ∧
      ∀ z,eval z (wordPredictionPolynomial j a F i)=wordPrediction j a z F i := by
  generalize hk : ordinaryCount F=k
  induction k using Nat.strong_induction_on generalizing F with
  | h k ih =>
    have hsub (t : WordRecursionTerm ι) (ht : t∈wordRecursionTerms a F) :
        (∀ i,(wordPredictionPolynomial j a t.inner i).natDegree≤ordinaryCount t.inner ∧
          ∀ z,eval z (wordPredictionPolynomial j a t.inner i)=wordPrediction j a z t.inner i) ∧
        (∀ i,(wordPredictionPolynomial j a t.outer i).natDegree≤ordinaryCount t.outer ∧
          ∀ z,eval z (wordPredictionPolynomial j a t.outer i)=wordPrediction j a z t.outer i) := by
      have hh := wordRecursionTerms_decreases a F t ht
      exact ⟨ih _ (by omega) _ rfl,ih _ (by omega) _ rfl⟩
    intro i
    by_cases ho : ordinaryCount F=0
    · rw [wordPredictionPolynomial]
      simp only [ho,ite_true,natDegree_C,zero_le,eval_C,true_and]
      intro z
      exact (wordPrediction_base j a z F i ho).symm
    constructor
    · rw [wordPredictionPolynomial,ite_eq_right ho]
      apply polynomial_list_degree_le
      intro p hp
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hp
      have hs := hsub t.val t.property
      have hinner : (C ((Fintype.card ι:ℝ)⁻¹)*(∑ u,wordPredictionPolynomial j a t.val.inner u)).natDegree≤ordinaryCount t.val.inner :=
        (natDegree_C_mul_le _ _).trans (natDegree_sum_le_of_forall_le _ _ (fun u _=>(hs.1 u).1))
      have hw : (if t.val.inversePartner then (X:ℝ[X]) else 1).natDegree≤(if t.val.inversePartner then 1 else 0) := by
        cases t.val.inversePartner <;> simp
      have hj : ((if t.val.inversePartner then (X:ℝ[X]) else 1)*C j).natDegree≤(if t.val.inversePartner then 1 else 0) :=
        (natDegree_mul_C_le _ _).trans hw
      have hb := wordRecursionTerms_degree_budget a F t.val t.property
      rw [hk] at hb
      exact natDegree_mul_le.trans ((add_le_add (natDegree_mul_le.trans (add_le_add hj hinner)) (hs.2 i).1).trans hb)
    · intro z
      rw [wordPredictionPolynomial,ite_eq_right ho,wordPrediction,ite_eq_right ho,polynomial_eval_list_sum,List.map_map]
      congr 1
      apply List.map_congr_left
      intro t ht
      have hs := hsub t.val t.property
      simp only [Function.comp_def,eval_mul,eval_C,eval_finsetSum]
      simp_rw [(hs.1 _).2 z,(hs.2 _).2 z]
      cases t.val.inversePartner <;> simp only [Bool.false_eq_true,ite_false,ite_true,eval_one,eval_X] <;> ring
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_PolynomialCoeListSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
open Diagram InverseDiagram WordSeries PowerSeries
variable {ι : Type*} [Fintype ι]

lemma polynomial_coe_list_sum (L : List (Polynomial ℝ)) :
    (L.sum : ℝ⟦X⟧)=(L.map (fun p : Polynomial ℝ=> (p : ℝ⟦X⟧))).sum :=
  map_list_sum Polynomial.coeToPowerSeries.ringHom L
lemma polynomial_coe_finset_sum {α : Type*} (S : Finset α) (f : α→Polynomial ℝ) :
    ((∑ k∈S,f k : Polynomial ℝ) : ℝ⟦X⟧)=∑ k∈S,(f k : ℝ⟦X⟧) :=
  map_sum Polynomial.coeToPowerSeries.ringHom f S

theorem literalSeries_eq_wordPredictionPolynomial (j : ℝ) (a : ι→ℝ)
    (F : List (WordLetter ι)) (hI : inverseCount F≤1) (i : ι) :
    literalSeries j a F i=(wordPredictionPolynomial j a F i : ℝ⟦X⟧) := by
  generalize hk : ordinaryCount F=k
  induction k using Nat.strong_induction_on generalizing F i with
  | h k ih =>
    by_cases ho : ordinaryCount F=0
    · rw [literalSeries_base j a F hI ho,wordPredictionPolynomial,ite_eq_left ho,Polynomial.coe_C]
    · have hsub (t : WordRecursionTerm ι) (ht : t∈wordRecursionTerms a F) :
          (∀ u,literalSeries j a t.inner u=(wordPredictionPolynomial j a t.inner u : ℝ⟦X⟧)) ∧
          (∀ u,literalSeries j a t.outer u=(wordPredictionPolynomial j a t.outer u : ℝ⟦X⟧)) := by
        have hd := wordRecursionTerms_decreases a F t ht
        have hI' := wordRecursionTerms_one_inverse a F hI t ht
        exact ⟨fun u=>ih _ (by omega) _ hI'.2 u rfl,fun u=>ih _ (by omega) _ hI'.1 u rfl⟩
      have hrec : literalSeries j a F i=
          ((wordRecursionTerms a F).map (fun t=>
            (if t.inversePartner then X else 1)*C j*meanSeries (literalSeries j a t.inner)*
              literalSeries j a t.outer i)).sum := by
        cases hs : firstNoiseSplit F with
        | none => exact False.elim (ho ((firstNoiseSplit_none F).mp hs))
        | some pq =>
          rcases pq with ⟨P,Q⟩
          have he := firstNoiseSplit_some F P Q hs
          rw [wordRecursionTerms,hs]
          simpa only [he] using literalSeries_at j a P Q (by simpa only [he] using hI) i
      rw [hrec,wordPredictionPolynomial,ite_eq_right ho,polynomial_coe_list_sum,List.map_map]
      rw [← List.attach_map_val (l := wordRecursionTerms a F)]
      congr 1
      apply List.map_congr_left
      intro t ht
      have hs := hsub t.val t.property
      simp only [Function.comp_def,Polynomial.coe_mul,Polynomial.coe_C]
      have hm : meanSeries (literalSeries j a t.val.inner)=
          ((Polynomial.C ((Fintype.card ι:ℝ)⁻¹)*(∑ k,wordPredictionPolynomial j a t.val.inner k) : Polynomial ℝ) : ℝ⟦X⟧) := by
        simp only [meanSeries,Polynomial.coe_mul,Polynomial.coe_C,polynomial_coe_finset_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro u _
        exact hs.1 u
      rw [hs.2 i]
      rw [hm]
      cases t.val.inversePartner <;> simp only [Bool.false_eq_true,↓reduceIte,Polynomial.coe_one,Polynomial.coe_X,
        Polynomial.coe_mul,Polynomial.coe_C]

end SKGap.Noncrossing

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_CyclicPrediction
attribute [-instance] _root_.OAI.SKGap.Noncrossing.Primary.Tensor.Loop.blocksOneUnique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
open Diagram InverseDiagram WordSeries
variable {ι : Type*} [Fintype ι]

lemma mean_finset_sum {α : Type*} (s : Finset α) (f : α→ι→ℝ) :
    Diagram.mean (fun i =>∑ a∈s,f a i)=∑ a∈s,Diagram.mean (f a) := by
  simp only [Diagram.mean]
  rw [Finset.sum_comm,Finset.sum_div]

lemma ordinary_mean_noise_rotate (j : ℝ) (F : List (Letter (ι→ℝ))) :
    Diagram.mean (ordinary j (.noise::F))=Diagram.mean (ordinary j (F++[.noise])) := by
  have h1 := funext (expect_at j (id : (ι→ℝ)→ι→ℝ) [] F)
  have h2 := funext (expect_at j (id : (ι→ℝ)→ι→ℝ) F [])
  simp only [ordinary]
  simp only [List.nil_append,List.append_nil,Fintype.sum_empty,zero_add,add_zero] at h1 h2
  rw [h1,h2,mean_finset_sum,mean_finset_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [mean_const_mul,mean_const_mul]
  ring

lemma ordinary_mean_cons_rotate (j : ℝ) (a : Letter (ι→ℝ)) (F : List (Letter (ι→ℝ))) :
    Diagram.mean (ordinary j (a::F))=Diagram.mean (ordinary j (F++[a])) := by
  cases a with
  | noise => exact ordinary_mean_noise_rotate j F
  | diag d => congr 1; funext i; simp [mul_comm]

theorem ordinary_mean_cyclic (j : ℝ) (P Q : List (Letter (ι→ℝ))) :
    Diagram.mean (ordinary j (P++Q))=Diagram.mean (ordinary j (Q++P)) := by
  induction P generalizing Q with
  | nil => simp
  | cons a P ih =>
    rw [List.cons_append,ordinary_mean_cons_rotate,List.append_assoc,ih]
    simp [List.append_assoc]

lemma meanSeries_cyclic (j : ℝ) (a : ι→ℝ) (P Q : List (WordLetter ι)) :
    meanSeries (literalSeries j a (P++Q))=meanSeries (literalSeries j a (Q++P)) := by
  have hi : inverseCount (P++Q)=inverseCount (Q++P) := by simp [inverseCount_append,add_comm]
  ext m
  simp only [coeff_meanSeries]
  by_cases h : inverseCount (P++Q)=0
  · have h' : inverseCount (Q++P)=0 := hi ▸ h
    simp only [literalSeries,h,h',ite_true,PowerSeries.coeff_C]
    by_cases hm : m=0
    · simp only [hm,ite_true]
      simpa only [expandWord,List.flatMap_append] using
        ordinary_mean_cyclic j (expandWord j a [] P) (expandWord j a [] Q)
    · simp [hm,Diagram.mean]
  · have h' : inverseCount (Q++P)≠0 := hi ▸ h
    simp only [literalSeries,h,h',ite_false,PowerSeries.coeff_mk]
    rw [mean_finset_sum,mean_finset_sum]
    apply Finset.sum_congr rfl
    intro bs _
    simpa only [expandWord,List.flatMap_append] using
      ordinary_mean_cyclic j (expandWord j a bs.val P) (expandWord j a bs.val Q)

theorem wordPrediction_mean_cyclic (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (P Q : List (WordLetter ι)) (hI : inverseCount (P++Q)≤1) :
    (∑ i,wordPrediction j a z (P++Q) i)=(∑ i,wordPrediction j a z (Q++P) i) := by
  classical
  by_cases hn : Fintype.card ι=0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hn
    simp
  have hc := meanSeries_cyclic j a P Q
  have hI' : inverseCount (Q++P)≤1 := by simpa only [inverseCount_append,add_comm] using hI
  unfold meanSeries at hc
  simp_rw [literalSeries_eq_wordPredictionPolynomial j a (P++Q) hI,
    literalSeries_eq_wordPredictionPolynomial j a (Q++P) hI'] at hc
  have hmult : (PowerSeries.C ((Fintype.card ι:ℝ)⁻¹))≠0 := by
    exact (map_ne_zero PowerSeries.C).mpr (inv_ne_zero (Nat.cast_ne_zero.mpr hn))
  have hs := mul_left_cancel₀ hmult hc
  have hp : (∑ i,wordPredictionPolynomial j a (P++Q) i)=
      ∑ i,wordPredictionPolynomial j a (Q++P) i := by
    apply Polynomial.coe_injective ℝ
    simpa only [polynomial_coe_finset_sum] using hs
  have he := congrArg (Polynomial.eval z) hp
  simpa only [Polynomial.eval_finsetSum,fun F i => (wordPredictionPolynomial_spec j a F i).2 z] using he
end SKGap.Noncrossing

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PrimaryPrediction
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.Noncrossing.Diagram.noiseSplitFinite _root_.OAI.SKGap.Noncrossing.Diagram.noiseSplitFintype _root_.OAI.SKGap.Noncrossing.Diagram.pairedNilUnique _root_.OAI.SKGap.Noncrossing.WordSeries.noiseSplitNilIsEmpty _root_.OAI.SKGap.Noncrossing.noiseSplitDiagIsEmpty _root_.OAI.SKGap.Noncrossing.noiseSplitNoiseUnique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary
open Diagram

namespace Partial
variable {D : Type*}
lemma word_contract (p q : Partial D) (h : p.contract=some q) : q.word = .noise :: p.word := by
  cases p with
  | done d => simp [contract] at h
  | more d p => cases p <;> simp only [contract,Option.some.injEq] at h <;> subst q <;>
      simp [word,Diagram.word,List.append_assoc]
lemma diag_injective (a : D) : Function.Injective (diag a : Partial D → Partial D) := by
  intro p q h; cases p <;> cases q <;> simp_all [diag]
lemma create_injective : Function.Injective (create : Partial D → Partial D) := by
  intro p q h; exact Partial.more.inj h |>.2
lemma contract_injective {p q r : Partial D} (hp : p.contract=some r) (hq : q.contract=some r) : p=q := by
  cases p with
  | done d => simp [contract] at hp
  | more d p =>
    cases q with
    | done e => simp [contract] at hq
    | more e q =>
      cases p <;> cases q <;> simp only [contract,Option.some.injEq] at hp hq <;>
        subst r <;> simp_all
lemma create_ne_contract (p q r : Partial D) (h : q.contract=some r) : p.create≠r := by
  cases q with
  | done d => simp [contract] at h
  | more d q => cases q <;> simp only [contract,Option.some.injEq] at h <;> subst r <;> simp [create]

lemma diag_preimage (a : D) (F : List (Letter D)) (p : Partial D)
    (h : p.word = .diag a :: F) : ∃ q : Partial D, q.word=F ∧ p=q.diag a := by
  cases p with
  | done d => cases d <;> simp only [word,Diagram.word] at h
              case diag b d => simp only [List.cons.injEq,Letter.diag.injEq] at h
                               obtain ⟨rfl,h⟩ := h; exact ⟨.done d,h,rfl⟩
              all_goals simp at h
  | more d p =>
    cases d with
    | nil => simp [word,Diagram.word] at h
    | arch d e => simp [word,Diagram.word] at h
    | diag b d =>
      simp only [word,Diagram.word,List.cons_append,List.cons.injEq,Letter.diag.injEq] at h
      obtain ⟨rfl,h⟩ := h; exact ⟨.more d p,h,rfl⟩
lemma noise_preimage (F : List (Letter D)) (p : Partial D)
    (h : p.word = .noise :: F) :
    ∃ q : Partial D, q.word=F ∧ (p=q.create ∨ q.contract=some p) := by
  cases p with
  | done d =>
    cases d with
    | nil => simp [word,Diagram.word] at h
    | diag a d => simp [word,Diagram.word] at h
    | arch d e =>
      simp only [word,Diagram.word,List.cons.injEq,true_and] at h
      exact ⟨.more d (.done e),h,Or.inr rfl⟩
  | more d p =>
    cases d with
    | nil =>
      simp only [word,Diagram.word,List.nil_append,List.cons.injEq,true_and] at h
      exact ⟨p,h,Or.inl rfl⟩
    | diag a d => simp [word,Diagram.word] at h
    | arch d e =>
      simp only [word,Diagram.word,List.cons_append,List.cons.injEq,true_and,List.append_assoc] at h
      exact ⟨.more d (.more e p),h,Or.inr rfl⟩

@[simp] lemma mem_enumerate (F : List (Letter D)) (p : Partial D) :
    p∈enumerate F ↔ p.word=F := by
  induction F generalizing p with
  | nil =>
    cases p with
    | done d => cases d <;> simp [enumerate,word,Diagram.word]
    | more d p => simp [enumerate,word]
  | cons a F ih =>
    cases a with
    | diag a =>
      simp only [enumerate,List.mem_map,ih]
      constructor
      · rintro ⟨q,hq,rfl⟩; simp [hq]
      · intro hp; obtain ⟨q,hq,hp⟩ := diag_preimage a F p hp; exact ⟨q,hq,hp.symm⟩
    | noise =>
      simp only [enumerate,List.mem_flatMap,noise,List.mem_cons,Option.mem_toList,ih]
      constructor
      · rintro ⟨q,hq,hp|hp⟩
        · subst p; simp [hq]
        · rw [word_contract q p hp,hq]
      · intro hp; obtain ⟨q,hq,hp⟩ := noise_preimage F p hp; exact ⟨q,hq,hp⟩

lemma noise_nodup (p : Partial D) : p.noise.Nodup := by
  cases p with
  | done d => simp [noise,contract]
  | more d p => cases p <;> simp [noise,contract,create]
lemma noise_disjoint {p q : Partial D} (h : p≠q) : List.Disjoint p.noise q.noise := by
  apply List.disjoint_left.mpr
  intro r hr hq
  simp only [noise,List.mem_cons,Option.mem_toList] at hr hq
  rcases hr with hr|hr <;> rcases hq with hq|hq
  · exact h (create_injective (hr.symm.trans hq))
  · exact create_ne_contract p q r hq hr.symm
  · exact create_ne_contract q p r hr hq.symm
  · exact h (contract_injective hr hq)
lemma enumerate_nodup (F : List (Letter D)) : (enumerate F).Nodup := by
  induction F with
  | nil => simp [enumerate]
  | cons a F ih =>
    cases a with
    | diag a => exact ih.map (diag_injective a)
    | noise =>
      rw [enumerate,List.nodup_flatMap]
      exact ⟨fun p _ => noise_nodup p, List.Pairwise.imp (fun h => noise_disjoint h) ih⟩
end Partial

section Fock
variable {ι : Type*} [Fintype ι]

lemma value_factor (j : ℝ) (d : Diagram (D (ι:=ι))) (i : ι) :
    d.value j i=coefficient j d * outer d i := by
  induction d with
  | nil => simp [Diagram.value,coefficient,outer]
  | diag a d ih => simp [Diagram.value,coefficient,outer,ih]; ring
  | arch a b ia ib => simp [Diagram.value,coefficient,outer,ib]; ring
lemma mean_value (j : ℝ) (d : Diagram (D (ι:=ι))) :
    Diagram.mean (d.value j)=coefficient j d * Diagram.mean (outer d) := by
  simp only [funext (value_factor j d),Diagram.mean_const_mul]

lemma Partial.state_diag (j : ℝ) (a : D (ι:=ι)) (p : Partial (D (ι:=ι))) :
    (p.diag a).state j = diagonal a (p.state j) := by
  cases p <;> simp [state,stack,Partial.diag,Partial.coefficient,Primary.coefficient,Primary.outer]
lemma Partial.state_create (j : ℝ) (p : Partial (D (ι:=ι))) :
    p.create.state j = creation (p.state j) := by
  simp [state,stack,create,Partial.coefficient,Primary.coefficient,Primary.outer]
lemma Partial.state_contract (j : ℝ) (p : Partial (D (ι:=ι))) :
    ((p.contract.toList).map (Partial.state j)).sum = j • annihilation (p.state j) := by
  cases p with
  | done d => simp [state,stack,Partial.contract]
  | more d p =>
    cases p <;> simp [state,stack,Partial.contract,Partial.coefficient,
      Primary.coefficient,Primary.outer,mean_value,smul_smul,mul_assoc,mul_left_comm,mul_comm]
lemma Partial.state_noise (j : ℝ) (p : Partial (D (ι:=ι))) :
    ((p.noise).map (Partial.state j)).sum = Primary.noise j (p.state j) := by
  simp only [Partial.noise,List.map_cons,List.sum_cons,state_create,state_contract]
  rfl

lemma word_vacuum (j : ℝ) (F : List (Letter (D (ι:=ι)))) :
    word j F vacuum = ((Partial.enumerate F).map (Partial.state j)).sum := by
  induction F with
  | nil => simp [word,vacuum,Partial.enumerate,Partial.state,Partial.stack,
      Partial.coefficient,Primary.coefficient,Primary.outer]
  | cons a F ih =>
    cases a with
    | diag a =>
      simp only [word,letter,LinearMap.comp_apply,ih,Partial.enumerate,List.map_map]
      simp only [map_list_sum,Function.comp_def,Partial.state_diag,List.map_map]
    | noise =>
      simp only [word,letter,LinearMap.comp_apply,ih,Partial.enumerate,List.map_flatMap]
      rw [SKGap.Noncrossing.InverseDiagram.sum_flatMap]
      simp only [Partial.state_noise,map_list_sum,List.map_map,Function.comp_def]

lemma Partial.project_state_done (j : ℝ) (d : Diagram (D (ι:=ι))) (i : ι) :
    project ((.done d : Partial _).state j) i = d.value j i := by
  simp [Partial.state,Partial.stack,Partial.coefficient,value_factor]
lemma Partial.project_state_more (j : ℝ) (d : Diagram (D (ι:=ι)))
    (p : Partial (D (ι:=ι))) : project ((Partial.more d p).state j) = 0 := by
  simp [Partial.state,Partial.stack]

lemma prediction_as_finset (j : ℝ) (F : List (Letter (D (ι:=ι)))) (i : ι) :
    Diagram.prediction j F i = ∑ d∈Diagram.enumerate F, d.value j i := by
  classical
  let e : Diagram.Paired F ≃ {d // d∈Diagram.enumerate F} :=
    { toFun := fun d => ⟨d.val,(Diagram.mem_enumerate F d.val).mpr d.property⟩
      invFun := fun d => ⟨d.val,(Diagram.mem_enumerate F d.val).mp d.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  change (∑ d : Diagram.Paired F, d.val.value j i) = _
  calc
    _ = ∑ d : {d // d∈Diagram.enumerate F}, d.val.value j i :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = _ := Finset.sum_coe_sort (Diagram.enumerate F) (fun d => d.value j i)

theorem project_word (j : ℝ) (F : List (Letter (D (ι:=ι)))) (i : ι) :
    project (word j F vacuum) i = Diagram.prediction j F i := by
  classical
  rw [word_vacuum,map_list_sum,List.map_map]
  change (((Partial.enumerate F).map (fun p => project (p.state j))).sum) i = _
  have heval : (((Partial.enumerate F).map (fun p => project (p.state j))).sum) i =
      ((Partial.enumerate F).map (fun p => project (p.state j) i)).sum := by
    induction Partial.enumerate F with
    | nil => rfl
    | cons p L ih => simp [ih]
  rw [heval,← List.sum_toFinset _ (Partial.enumerate_nodup F),prediction_as_finset]
  have hsub : (Diagram.enumerate F).image Partial.done ⊆ (Partial.enumerate F).toFinset := by
    intro p hp
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hp
    simpa [Partial.word] using hd
  rw [← Finset.sum_subset hsub (fun p hp hn => ?_)]
  · rw [Finset.sum_image (fun d _ e _ h => Partial.done.inj h)]
    exact Finset.sum_congr rfl (fun d _ => Partial.project_state_done j d i)
  · cases p with
    | done d =>
      exfalso; apply hn
      exact Finset.mem_image.mpr ⟨d,by simpa [Partial.word] using hp,rfl⟩
    | more d p => simp [Partial.project_state_more]

lemma word_append (j : ℝ) (F G : List (Letter (D (ι:=ι)))) :
    word j (F++G) = (word j F).comp (word j G) := by
  induction F with
  | nil => simp [word]
  | cons a F ih => simp [word,ih,LinearMap.comp_assoc]
lemma polynomialOperator_append (j : ℝ) (P Q : WordPolynomial (ι:=ι)) :
    polynomialOperator j (P++Q) = polynomialOperator j P + polynomialOperator j Q := by
  simp [polynomialOperator]
lemma polynomialOperator_prefix (j : ℝ) (F : List (Letter (D (ι:=ι))))
    (P : WordPolynomial (ι:=ι)) :
    polynomialOperator j (prependWords F P) = (word j F).comp (polynomialOperator j P) := by
  induction P with
  | nil => simp [prependWords,polynomialOperator]
  | cons p P ih =>
    simp only [prependWords,List.map_cons,polynomialOperator,List.sum_cons] at *
    rw [word_append,ih,LinearMap.comp_add,LinearMap.comp_smul]
lemma polynomialOperator_scale (j c : ℝ) (P : WordPolynomial (ι:=ι)) :
    polynomialOperator j (scale c P)=c • polynomialOperator j P := by
  induction P with
  | nil => simp [scale,polynomialOperator]
  | cons p P ih =>
    simp only [scale,List.map_cons,polynomialOperator,List.sum_cons] at *
    rw [ih,smul_add,mul_smul]

lemma polynomialPrediction_eq_project (j : ℝ) (P : WordPolynomial (ι:=ι)) (i : ι) :
    polynomialPrediction j P i = project (polynomialOperator j P vacuum) i := by
  induction P with
  | nil => simp [polynomialPrediction,polynomialOperator]
  | cons p P ih =>
    simp only [polynomialPrediction,polynomialOperator,List.map_cons,List.sum_cons,
      LinearMap.add_apply,LinearMap.smul_apply,map_add,map_smul,Pi.add_apply,Pi.smul_apply,
      smul_eq_mul] at *
    rw [project_word,ih]

end Fock
end SKGap.Noncrossing.Primary
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_PrimaryMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary
open WordSeries
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma wordPrediction_lift (j : ℝ) (a : ι→ℝ) (z : ℝ)
    (F : List (Letter (ι→ℝ))) (i : ι) :
    wordPrediction j a z (liftWord F) i=Diagram.prediction j F i := by
  have h := literalSeries_eq_wordPredictionPolynomial j a (liftWord F) (by simp) i
  rw [literalSeries_lift] at h
  have hp : wordPredictionPolynomial j a (liftWord F) i=Polynomial.C (ordinary j F i) := by
    apply Polynomial.ext
    intro k
    have hc := congrArg (PowerSeries.coeff k) h
    simpa only [← Polynomial.coe_C,Polynomial.coeff_coe] using hc.symm
  rw [← (wordPredictionPolynomial_spec j a (liftWord F) i).2 z,hp]
  rw [Polynomial.eval_C]
  have hm (d : Diagram (ι→ℝ)) : d.map id=d := by
    induction d <;> simp [Diagram.map, *]
  simp only [ordinary,Diagram.expect,Diagram.evaluate,Diagram.prediction,hm]

lemma exactWord_lift (j : ℝ) (a : ι→ℝ) (J : Matrix ι ι ℝ) (F : List (Letter (ι→ℝ))) :
    exactWord j a (liftWord F) J=matrixWord J F := by
  induction F with
  | nil => rfl
  | cons l F ih =>
    cases l <;> simp [liftWord,Letter.toWord,exactWord,matrixFactorProduct,
      WordLetter.exactEval,matrixWord,matrixLetter] at * <;> exact congrArg _ ih

lemma matrixWord_append (J : Matrix ι ι ℝ) (F G : List (Letter (ι→ℝ))) :
    matrixWord J (F++G)=matrixWord J F*matrixWord J G := by simp [matrixWord]
lemma matrixPolynomial_append (J : Matrix ι ι ℝ) (P Q : WordPolynomial (ι:=ι)) :
    matrixPolynomial J (P++Q)=matrixPolynomial J P+matrixPolynomial J Q := by
  simp [matrixPolynomial]
lemma matrixPolynomial_prefix (J : Matrix ι ι ℝ) (F : List (Letter (ι→ℝ)))
    (P : WordPolynomial (ι:=ι)) :
    matrixPolynomial J (prependWords F P)=matrixWord J F*matrixPolynomial J P := by
  induction P with
  | nil => simp [prependWords,matrixPolynomial]
  | cons p P ih =>
    simp only [prependWords,List.map_cons,matrixPolynomial,List.sum_cons] at *
    rw [matrixWord_append,ih,mul_add,mul_smul_comm]
lemma matrixPolynomial_scale (J : Matrix ι ι ℝ) (c : ℝ) (P : WordPolynomial (ι:=ι)) :
    matrixPolynomial J (scale c P)=c • matrixPolynomial J P := by
  induction P with
  | nil => simp [scale,matrixPolynomial]
  | cons p P ih =>
    simp only [scale,List.map_cons,matrixPolynomial,List.sum_cons] at *
    rw [ih,smul_add,mul_smul]

end SKGap.Noncrossing.Primary
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_GraphPrediction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary
open Diagram
variable {ι : Type*} [Fintype ι]

lemma annihilation_diagonal_creation (a : D (ι:=ι)) (v : Space (ι:=ι)) :
    annihilation (diagonal a (creation v))=Diagram.mean a • v := by
  have he : annihilation.comp ((diagonal a).comp creation)=
      Diagram.mean a • (LinearMap.id : Space (ι:=ι)→ₗ[ℝ] Space (ι:=ι)) := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext
    intro r
    simp [creation,diagonal,annihilation,ket,mul_comm]
  exact LinearMap.congr_fun he v

omit [Fintype ι] in
lemma project_diagonal_creation (a : D (ι:=ι)) (v : Space (ι:=ι)) :
    project (diagonal a (creation v))=0 := by
  have he : project.comp ((diagonal a).comp creation)=
      (0 : Space (ι:=ι)→ₗ[ℝ] D (ι:=ι)) := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext
    intro r
    simp [creation,diagonal,project,ket]
  exact LinearMap.congr_fun he v

omit [Fintype ι] in
lemma project_creation (v : Space (ι:=ι)) : project (creation v)=0 := by
  have he : project.comp creation=(0 : Space (ι:=ι)→ₗ[ℝ] D (ι:=ι)) := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext
    intro r
    simp [creation,project,ket]
  exact LinearMap.congr_fun he v

end SKGap.Noncrossing.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_FockTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.Tensor
open Diagram
variable {ι : Type*} [Fintype ι]
omit [Fintype ι] in
lemma realize_ket (s : Stack (ι:=ι)) (i : ι) (I : List ι) :
    realize (ket s) i I=s.1 i*tensorValue s.2 I := by simp [realize,ket]

omit [Fintype ι] in
lemma realize_diagonal (a : ι→ℝ) (v : Primary.Space (ι:=ι)) :
    realize (Primary.diagonal a v)=diagonal a (realize v) := by
  have h : realize.comp (Primary.diagonal a)=(diagonal a).comp realize := by
    apply Finsupp.lhom_ext'
    intro s
    ext i I
    change realize (Primary.diagonal a (ket s)) i I = diagonal a (realize (ket s)) i I
    rw [Primary.diagonal_ket,realize_ket]
    change (a i*s.1 i)*tensorValue s.2 I=a i*realize (ket s) i I
    rw [realize_ket]; ring
  exact LinearMap.congr_fun h v
omit [Fintype ι] in
lemma realize_creation (v : Primary.Space (ι:=ι)) :
    realize (Primary.creation v)=creation (realize v) := by
  have h : (realize (ι:=ι)).comp Primary.creation=creation.comp realize := by
    apply Finsupp.lhom_ext'
    intro s
    ext i I
    change realize (Primary.creation (ket s)) i I = creation (realize (ket s)) i I
    rw [Primary.creation_ket,realize_ket]
    cases I <;> simp [creation,tensorValue,realize_ket]
  exact LinearMap.congr_fun h v
lemma realize_annihilation (v : Primary.Space (ι:=ι)) :
    realize (Primary.annihilation v)=annihilation (realize v) := by
  have h : (realize (ι:=ι)).comp Primary.annihilation=annihilation.comp realize := by
    apply Finsupp.lhom_ext'
    rintro ⟨a,L⟩
    ext i I
    change realize (Primary.annihilation (ket (a,L))) i I = annihilation (realize (ket (a,L))) i I
    cases L <;> simp [annihilation,realize_ket,tensorValue,Diagram.mean,←Finset.sum_mul,div_mul_eq_mul_div]
  exact LinearMap.congr_fun h v
lemma realize_noise (j : ℝ) (v : Primary.Space (ι:=ι)) :
    realize (Primary.noise j v)=noise j (realize v) := by
  simp [Primary.noise,noise,realize_annihilation,realize_creation]
omit [Fintype ι] in
lemma project_realize (v : Primary.Space (ι:=ι)) : project (realize v)=Primary.project v := by
  have h : (project (ι:=ι)).comp realize=Primary.project := by
    apply Finsupp.lhom_ext'
    rintro ⟨a,L⟩
    ext i
    change project (realize (ket (a,L))) i = Primary.project (ket (a,L)) i
    cases L <;> simp [project,realize_ket,tensorValue]
  exact LinearMap.congr_fun h v
lemma realize_word (j : ℝ) (F : List (Letter (ι→ℝ))) (v : Primary.Space (ι:=ι)) :
    realize (Primary.word j F v)=word j F (realize v) := by
  induction F generalizing v with
  | nil => rfl
  | cons a F ih =>
    cases a <;> simp [Primary.word,Primary.letter,word,letter,realize_noise,realize_diagonal,ih]
omit [Fintype ι] in
lemma diagram_map_id (d : Diagram (ι→ℝ)) : d.map id=d := by
  induction d <;> simp_all [Diagram.map]
lemma project_word (j : ℝ) (F : List (Letter (ι→ℝ))) (i : ι) :
    project (word j F vacuum) i=WordSeries.ordinary j F i := by
  rw [vacuum,←realize_word,project_realize,Primary.project_word]
  simp [WordSeries.ordinary,Diagram.expect,Diagram.evaluate,Diagram.prediction,diagram_map_id]
lemma word_append (j : ℝ) (F G : List (Letter (ι→ℝ))) :
    word j (F++G)=(word j F).comp (word j G) := by
  induction F with
  | nil => simp [word]
  | cons a F ih => simp [word,ih,LinearMap.comp_assoc]
omit [Fintype ι] in
lemma diagonal_scale (c : ℝ) (a : ι→ℝ) : diagonal (fun i=>c*a i)=c • diagonal a := by
  ext v i I
  change (c*a i)*v i I=c*(a i*v i I)
  ring
end SKGap.Noncrossing.Primary.Tensor

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_LoopPrediction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.Tensor.Loop
open Diagram InverseDiagram WordSeries
variable {ι : Type*} [Fintype ι]

lemma blockPrepend_bijective (n : ℕ) : Function.Bijective (blockPrepend n) := by
  constructor
  · intro x y h
    have hv := congrArg (fun q : Blocks (n+2) => q.val) h
    cases x <;> cases y <;> simp only [blockPrepend] at hv
    · exact congrArg Sum.inl (Subtype.ext (List.cons.inj hv).2)
    · exact False.elim (Bool.noConfusion (List.cons.inj hv).1)
    · exact False.elim (Bool.noConfusion (List.cons.inj hv).1)
    · exact congrArg Sum.inr (Subtype.ext (List.cons.inj hv).2)
  · rintro ⟨bs,hbs⟩
    cases bs with
    | nil => simp only [blockDegree_nil] at hbs; omega
    | cons b bs =>
      cases b with
      | true => exact ⟨.inl ⟨bs,by rw [blockDegree_true] at hbs; omega⟩,rfl⟩
      | false => exact ⟨.inr ⟨bs,by rw [blockDegree_false] at hbs; omega⟩,rfl⟩

lemma kernel_zero (j : ℝ) (a : ι→ℝ) : kernel j a 0=LinearMap.id := by
  simp [kernel,blocks_zero,word]
lemma kernel_one (j : ℝ) (a : ι→ℝ) : kernel j a 1=(diagonal a).comp (noise j) := by
  simp [kernel,blocks_one,word,letter]
end SKGap.Noncrossing.Primary.Tensor.Loop

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_OrdinaryGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary
open Diagram
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace SourceTree
variable {D : Type*}

section
omit [DecidableEq ι]

lemma source_leaf (j c : ℝ) : sourceOperator (ι:=ι) j (.leaf c)=c • LinearMap.id := by
  simp [sourceOperator,words,polynomialOperator,word]
lemma field_leaf (j c : ℝ) : fieldOperator (ι:=ι) j (.leaf c)=c • noise j := by
  simp [fieldOperator,words,polynomialOperator,word,letter]
lemma source_branch (j : ℝ) (p : ι→ℝ) (a b : SourceTree (ι→ℝ)) :
    sourceOperator j (.branch p a b)=(diagonal p).comp (fieldOperator j a)+sourceOperator j b := by
  simp [sourceOperator,fieldOperator,words,polynomialOperator_append,
    polynomialOperator_prefix,word,letter]
lemma field_branch (j : ℝ) (p : ι→ℝ) (a b : SourceTree (ι→ℝ)) :
    fieldOperator j (.branch p a b)=
      (noise j).comp ((diagonal p).comp (fieldOperator j a))-
        (j*Diagram.mean p) • sourceOperator j a+fieldOperator j b := by
  simp only [sourceOperator,fieldOperator,words,polynomialOperator_append,
    polynomialOperator_prefix,polynomialOperator_scale,word,letter,LinearMap.comp_id,
    LinearMap.comp_assoc]
  ext v s
  simp [LinearMap.sub_apply,LinearMap.smul_apply,sub_eq_add_neg]

theorem field_vacuum (j : ℝ) (t : SourceTree (ι→ℝ)) :
    fieldOperator j t vacuum=creation (sourceOperator j t vacuum) := by
  induction t with
  | leaf c => simp [field_leaf,source_leaf,noise,vacuum]
  | branch p a b ia ib =>
    rw [field_branch,source_branch]
    simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.comp_apply,
      LinearMap.smul_apply,ia,ib,map_add,noise]
    simp only [annihilation_diagonal_creation,smul_smul]
    abel

theorem field_prediction_zero (j : ℝ) (t : SourceTree (ι→ℝ)) (i : ι) :
    polynomialPrediction j (t.words j).2 i=0 := by
  rw [polynomialPrediction_eq_project]
  change project (fieldOperator j t vacuum) i=0
  rw [field_vacuum,project_creation]; rfl

theorem source_prediction (j : ℝ) (t : SourceTree (ι→ℝ)) (i : ι) :
    polynomialPrediction j (t.words j).1 i=t.leafMass := by
  rw [polynomialPrediction_eq_project]
  change project (sourceOperator j t vacuum) i=t.leafMass
  induction t with
  | leaf c => simp [source_leaf,leafMass,vacuum,project,ket]
  | branch p a b ia ib =>
    rw [source_branch]
    simp only [LinearMap.add_apply,LinearMap.comp_apply,map_add,field_vacuum,
      project_diagonal_creation,zero_add,leafMass]
    exact ib

end

lemma sourceMatrix_leaf (j c : ℝ) (J : Matrix ι ι ℝ) :
    sourceMatrix j J (.leaf c)=c • 1 := by simp [sourceMatrix,words,matrixPolynomial,matrixWord]
lemma fieldMatrix_leaf (j c : ℝ) (J : Matrix ι ι ℝ) :
    fieldMatrix j J (.leaf c)=c • J := by
  simp [fieldMatrix,words,matrixPolynomial,matrixWord,matrixLetter]
lemma sourceMatrix_branch (j : ℝ) (J : Matrix ι ι ℝ) (p : ι→ℝ) (a b : SourceTree (ι→ℝ)) :
    sourceMatrix j J (.branch p a b)=Matrix.diagonal p*fieldMatrix j J a+sourceMatrix j J b := by
  simp [sourceMatrix,fieldMatrix,words,matrixPolynomial_append,matrixPolynomial_prefix,
    matrixWord,matrixLetter]
lemma fieldMatrix_branch (j : ℝ) (J : Matrix ι ι ℝ) (p : ι→ℝ) (a b : SourceTree (ι→ℝ)) :
    fieldMatrix j J (.branch p a b)=J*(Matrix.diagonal p*fieldMatrix j J a)-
      (j*Diagram.mean p) • sourceMatrix j J a+fieldMatrix j J b := by
  simp [sourceMatrix,fieldMatrix,words,matrixPolynomial_append,matrixPolynomial_prefix,
    matrixPolynomial_scale,matrixWord,matrixLetter,mul_assoc,sub_eq_add_neg,add_assoc]
end SourceTree
end SKGap.Noncrossing.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_FockSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.Tensor.Series
open Diagram InverseDiagram WordSeries Loop
variable {ι : Type*}

variable [Fintype ι]

lemma kernel_add_two_left (j : ℝ) (a : ι→ℝ) (n : ℕ) :
    kernel j a (n+2)=((diagonal a).comp (noise j)).comp (kernel j a (n+1))-
      (j*Diagram.mean a) • (diagonal a).comp (kernel j a n) := by
  have h := Fintype.sum_equiv (Equiv.ofBijective (blockPrepend n) (blockPrepend_bijective n))
    (fun s => match s with
      | .inl bs => word j (chain j a (true::bs.val))
      | .inr bs => word j (chain j a (false::bs.val)))
    (fun bs => word j (chain j a bs.val)) (by intro s; cases s <;> rfl)
  change _=kernel j a (n+2) at h
  rw [Fintype.sum_sum_type] at h
  rw [←h]
  simp only [chain_true,chain_false,word,letter,diagonal_scale,LinearMap.smul_comp]
  ext v i I
  simp [kernel,LinearMap.sum_apply,LinearMap.comp_apply,Finset.sum_neg_distrib,
    ←Finset.mul_sum,sub_eq_add_neg]

lemma inverse_ofVector (j : ℝ) (a : ι→ℝ) (v : Space (ι:=ι)) (n : ℕ) :
    inverse j a (ofVector v) n=kernel j a n v := by
  induction n using Nat.twoStepInduction with
  | zero => simp [inverse,inverseSeq,ofVector,kernel_zero]
  | one => simp [inverse,inverseSeq,ofVector,kernel_one]
  | more n ih0 ih1 =>
    change inverseSeq j a (ofVector v) (n+2)=_
    rw [inverseSeq]
    change ofVector v (n+2)+diagonal a (noise j (inverse j a (ofVector v) (n+1)))-
      (j*Diagram.mean a) • diagonal a (inverse j a (ofVector v) n)=_
    rw [ih0,ih1,kernel_add_two_left]
    simp [ofVector]

end SKGap.Noncrossing.Primary.Tensor.Series

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_OrdinaryRecipe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

namespace OrdinaryData
variable (D : OrdinaryData n ι κ σ)

lemma source_eq (a : ℕ) : D.source a=D.sourceOf a (fun b=>D.auxiliary b) := by
  rw [source,evaluate]; rfl
lemma auxiliary_eq (a : ℕ) : D.auxiliary a=D.fieldOf a (fun b=>D.source b) (fun b=>D.auxiliary b) := by
  rw [auxiliary,evaluate]; rfl

end OrdinaryData

lemma CoefficientBound.small_product {a U : VectorFields n} {x : Spin n} {A R C : ℝ}
    (ha : CoefficientBound a x A R) (hU : SmallBound U x C) :
    SmallBound (fun x i=>a x i*U x i) x (C*(A+3*R)) :=
  hU.coefficient a ha.size_nonneg ha.row_nonneg ha.value ha.difference

lemma CoefficientBound.mean_product {a U : VectorFields n} {x : Spin n} {A R C : ℝ}
    (ha : CoefficientBound a x A R) (hU : SmallBound U x C) :
    SmallBound (fun x i=>siteMean a x*U x i) x (C*(A+3*R)) :=
  hU.auxiliaryCorrection a ha.size_nonneg ha.row_nonneg ha.value ha.difference

namespace OrdinaryData
variable (D : OrdinaryData n ι κ σ)

lemma sourceOf_bound (a : ℕ) (Y : Fin a→VectorFields n) (x : Spin n) {A R : ℝ} (C : Fin a→ℝ)
    (hY : ∀b,SmallBound (Y b) x (C b))
    (hs : ∀s,CoefficientBound (D.seedCoefficient a s) x A R)
    (ha : ∀b,CoefficientBound (D.auxCoefficient a b) x A R) :
    SmallBound (D.sourceOf a Y) x (((∑s,vectorNorm (D.seed s))+(∑b,C b))*(A+3*R)) := by
  have H:=(SmallBound.sum fun s=>(hs s).small_product (SmallBound.seed (D.seed s) x)).add
    (SmallBound.sum fun b=>(ha b).small_product (hY b))
  convert! H using 1
  all_goals try with_reducible_and_instances rfl
  simp only [←Finset.sum_mul,add_mul]

lemma partialOf_bound (a : ℕ) (l : ι) (Y : Fin a→VectorFields n) (x : Spin n) {A R : ℝ} (C : Fin a→ℝ)
    (hY : ∀b,SmallBound (Y b) x (C b))
    (hs : ∀s,CoefficientBound (D.seedPartial a l s) x A R)
    (ha : ∀b,CoefficientBound (D.auxPartial a l b) x A R) :
    SmallBound (D.partialOf a l Y) x (((∑s,vectorNorm (D.seed s))+(∑b,C b))*(A+3*R)) := by
  have H:=(SmallBound.sum fun s=>(hs s).small_product (SmallBound.seed (D.seed s) x)).add
    (SmallBound.sum fun b=>(ha b).small_product (hY b))
  convert! H using 1
  all_goals try with_reducible_and_instances rfl
  simp only [←Finset.sum_mul,add_mul]

lemma fieldOf_bound (a : ℕ) (W Y : Fin a→VectorFields n) (x : Spin n) (hn : 0<n)
    {A R L P C : ℝ} (B : Fin a→ℝ) (hL : 0≤L) (hP : 0≤P) (hJ : SKGap.opNorm D.J≤L)
    (hw : SmallBound (D.sourceOf a Y) x C)
    (hp : ∀l,SmallBound (D.partialOf a l Y) x C)
    (hW : ∀b,SmallBound (W b) x (B b))
    (hm : ∀l i,|D.predecessor l x i|≤1)
    (hdm : ∀l,SKGap.opNorm (derivativeMatrix (D.predecessor l) x)≤P)
    (ha : ∀b,CoefficientBound (D.auxCoefficient a b) x A R) :
    SmallBound (D.fieldOf a W Y) x
      ((L*C+|D.j| *((Fintype.card ι:ℝ)*(C*(1+3*P))))+|D.j| *((∑b,B b)*(A+3*R))) := by
  have h0 := (hw.linear D.J).mono (mul_le_mul hJ le_rfl hw.nonneg hL)
  have h1 := (SmallBound.sum fun l=>(hp l).primaryCorrection (D.predecessor l) hn hP (hm l) (hdm l)).smul D.j
  have h2 := (SmallBound.sum fun b=>(ha b).mean_product (hW b)).smul D.j
  have H:= (h0.sub h1).sub h2
  convert! H using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←Finset.sum_mul]

end OrdinaryData
end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_RecipeBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix

lemma recipeBudget_nonneg {c S : ℝ} (hc : 0 ≤ c) (hS : 0≤S) (a : ℕ) : 0 ≤ recipeBudget c S a := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    rw [recipeBudget]
    exact mul_nonneg hc (add_nonneg hS (Finset.sum_nonneg fun b _=>ih b b.isLt))

lemma recipeCost_nonneg {A R L P j : ℝ} {d : ℕ} (hA : 0≤A) (hR : 0≤R) (hL : 0≤L) (hP : 0≤P) :
    0 ≤ recipeCost A R L P j d := by unfold recipeCost; positivity

lemma recipeCost_ge {A R L P j : ℝ} {d : ℕ} (hA : 0≤A) (hR : 0≤R) (hL : 0≤L) (hP : 0≤P) :
    A+3*R ≤ recipeCost A R L P j d := by
  have hT : 0≤A+3*R := by positivity
  have hd : 0≤|j| *((d:ℝ)*(1+3*P)+1) := by positivity
  unfold recipeCost
  nlinarith [mul_nonneg hT hL,mul_nonneg hT hd]

variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]
namespace OrdinaryData
variable (D : OrdinaryData n ι κ σ)

theorem evaluation_small (N : ℕ) (x : Spin n) (hn : 0<n) {A R L P S : ℝ}
    (hA : 0≤A) (hR : 0≤R) (hL : 0≤L) (hP : 0≤P) (hS : 0≤S)
    (hJ : SKGap.opNorm D.J≤L) (hseed : (∑s,vectorNorm (D.seed s))≤S)
    (hm : ∀l i,|D.predecessor l x i|≤1)
    (hdm : ∀l,SKGap.opNorm (derivativeMatrix (D.predecessor l) x)≤P)
    (hs : ∀a≤N,∀s,CoefficientBound (D.seedCoefficient a s) x A R)
    (ha : ∀a≤N,∀b,CoefficientBound (D.auxCoefficient a b) x A R)
    (hsp : ∀a≤N,∀l s,CoefficientBound (D.seedPartial a l s) x A R)
    (hap : ∀a≤N,∀l b,CoefficientBound (D.auxPartial a l b) x A R) :
    ∀a≤N,
      SmallBound (D.source a) x (recipeBudget (recipeCost A R L P D.j (Fintype.card ι)) S a) ∧
      SmallBound (D.auxiliary a) x (recipeBudget (recipeCost A R L P D.j (Fintype.card ι)) S a) ∧
      ∀l,SmallBound (D.sourcePartial a l) x (recipeBudget (recipeCost A R L P D.j (Fintype.card ι)) S a) := by
  let c:=recipeCost A R L P D.j (Fintype.card ι)
  have hc : 0 ≤ c := recipeCost_nonneg hA hR hL hP
  have hT : 0≤A+3*R := by positivity
  have hcg : A+3*R ≤ c := recipeCost_ge hA hR hL hP
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro haN
    let B : Fin a→ℝ := fun b=>recipeBudget c S b
    let I : ℝ := S+∑b,B b
    let Z : ℝ := I*(A+3*R)
    have hB : ∀b,0≤B b := fun b=>recipeBudget_nonneg hc hS b
    have hI : 0≤I := add_nonneg hS (Finset.sum_nonneg fun b _=>hB b)
    have hY : ∀b:Fin a,SmallBound (D.auxiliary b) x (B b) := fun b=>(ih b b.isLt (b.isLt.le.trans haN)).2.1
    have hW : ∀b:Fin a,SmallBound (D.source b) x (B b) := fun b=>(ih b b.isLt (b.isLt.le.trans haN)).1
    have hw : SmallBound (D.sourceOf a (fun b=>D.auxiliary b)) x Z :=
      (D.sourceOf_bound a _ x B hY (hs a haN) (ha a haN)).mono
        (mul_le_mul_of_nonneg_right (show (∑s,vectorNorm (D.seed s))+(∑b,B b) ≤ I from add_le_add hseed le_rfl) hT)
    have hp : ∀l,SmallBound (D.partialOf a l (fun b=>D.auxiliary b)) x Z := fun l=>
      (D.partialOf_bound a l _ x B hY (hsp a haN l) (hap a haN l)).mono
        (mul_le_mul_of_nonneg_right (show (∑s,vectorNorm (D.seed s))+(∑b,B b) ≤ I from add_le_add hseed le_rfl) hT)
    have hZ : Z ≤ recipeBudget c S a := by
      rw [recipeBudget]
      exact (mul_le_mul_of_nonneg_left hcg hI).trans_eq (by dsimp [I,B]; ring)
    have hf:=D.fieldOf_bound a (fun b=>D.source b) (fun b=>D.auxiliary b) x hn B hL hP hJ hw hp hW hm hdm (ha a haN)
    have hfC : (L*Z+|D.j| *((Fintype.card ι:ℝ)*(Z*(1+3*P))))+
          |D.j| *((∑b,B b)*(A+3*R)) ≤ recipeBudget c S a := by
      rw [recipeBudget]
      change _ ≤ c*I
      dsimp [c,recipeCost,Z,I]
      have h1 : 0≤(S+∑b,B b)*(A+3*R) := mul_nonneg hI hT
      have h2 : 0≤|D.j| *(S*(A+3*R)) := mul_nonneg (abs_nonneg _) (mul_nonneg hS hT)
      nlinarith only [h1,h2]
    refine ⟨?_,?_,?_⟩
    · rw [D.source_eq]; exact hw.mono hZ
    · rw [D.auxiliary_eq]; exact hf.mono hfC
    · intro l; exact (hp l).mono hZ

end OrdinaryData
end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_RecipeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.SourceTree
open Diagram
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma branches_leafMass (ts : List ((ι→ℝ)×SourceTree (ι→ℝ))) : (branches ts).leafMass=0 := by
  induction ts with
  | nil => rfl
  | cons t ts ih => exact ih

lemma branches_source (j : ℝ) (J : Matrix ι ι ℝ) (ts : List ((ι→ℝ)×SourceTree (ι→ℝ))) :
    sourceMatrix j J (branches ts)=(ts.map (fun t=>Matrix.diagonal t.1*fieldMatrix j J t.2)).sum := by
  induction ts with
  | nil => simp [branches,sourceMatrix_leaf]
  | cons t ts ih => simp [branches,sourceMatrix_branch,ih]

lemma branches_field (j : ℝ) (J : Matrix ι ι ℝ) (ts : List ((ι→ℝ)×SourceTree (ι→ℝ))) :
    fieldMatrix j J (branches ts)=J*sourceMatrix j J (branches ts)-
      (ts.map (fun t=>(j*Diagram.mean t.1) • sourceMatrix j J t.2)).sum := by
  induction ts with
  | nil => simp [branches,sourceMatrix_leaf,fieldMatrix_leaf]
  | cons t ts ih =>
    simp only [branches,sourceMatrix_branch,fieldMatrix_branch,List.map_cons,List.sum_cons,ih,mul_add]
    abel

end SKGap.Noncrossing.Primary.SourceTree
namespace SKGapCutoff.Recipe.OrdinaryData
open SKGap.Noncrossing.Primary SKGap.Noncrossing.Diagram Primary Matrix
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

lemma retainedTree_leafMass (D : OrdinaryData n ι κ σ) (T : ι→SourceTree (Fin n→ℝ))
    (x : Spin n) (a : ℕ) : (D.retainedTree T x a).leafMass=0 := by
  rw [retainedTree,SourceTree.branches_leafMass]

lemma retainedSource_eq (D : OrdinaryData n ι κ σ) (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) :
    D.retainedSource T x a=
      (∑l,Matrix.diagonal (D.sourcePartial a l x)*SourceTree.fieldMatrix D.j D.J (T l))+
      ∑b:Fin a,Matrix.diagonal (D.auxCoefficient a b x)*D.retainedField T x b := by
  rw [retainedSource,retainedTree,SourceTree.branches_source]
  simp [List.map_append,List.sum_append,List.map_map,Function.comp_def,retainedField]

lemma retainedField_eq (D : OrdinaryData n ι κ σ) (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) :
    D.retainedField T x a=D.J*D.retainedSource T x a-
      (∑l,(D.j*siteMean (D.sourcePartial a l) x) • SourceTree.sourceMatrix D.j D.J (T l))-
      ∑b:Fin a,(D.j*siteMean (D.auxCoefficient a b) x) • D.retainedSource T x b := by
  have h:=SourceTree.branches_field D.j D.J
    ((Finset.univ.toList.map (fun l=>(D.sourcePartial a l x,T l)))++
      (Finset.univ.toList.map (fun b:Fin a=>(D.auxCoefficient a b x,D.retainedTree T x b))))
  rw [show SourceTree.branches _=D.retainedTree T x a from (by rw [retainedTree])] at h
  simpa [List.map_append,List.sum_append,List.map_map,Function.comp_def,
    retainedField,retainedSource,siteMean,SKGap.Noncrossing.Diagram.mean,
    sub_add_eq_sub_sub] using h

theorem retained_prediction_zero (D : OrdinaryData n ι κ σ) (T : ι→SourceTree (Fin n→ℝ))
    (x : Spin n) (a : ℕ) (i : Fin n) :
    polynomialPrediction D.j ((D.retainedTree T x a).words D.j).1 i=0 ∧
    polynomialPrediction D.j ((D.retainedTree T x a).words D.j).2 i=0 := by
  constructor
  · rw [SourceTree.source_prediction,retainedTree_leafMass]
  · exact SourceTree.field_prediction_zero ..

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_CorrectionTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap.SourceError
variable {n : ℕ}

lemma trace_frobenius (P E : Interaction n) : |trace (P*E)|≤‖P‖*‖E‖ := by
  have H := double_cauchy (fun i k=>P k i) (fun i k=>E i k)
    (norm_nonneg P) (norm_nonneg E)
    (by rw [Finset.sum_comm]; exact le_of_eq (SKGap.frobenius_sq P).symm)
    (le_of_eq (SKGap.frobenius_sq E).symm)
  rw [Matrix.trace_mul_comm]
  simpa only [trace,diag,Matrix.mul_apply,mul_comm] using H

lemma trace_small_diagonal (P E : Interaction n) (u : Fin n→ℝ) :
    |trace (P*(Matrix.diagonal u*E))|≤SKGap.opNorm P*vectorNorm u*‖E‖ := by
  apply (trace_le_traceAbsolute P (Matrix.diagonal u*E)).trans
  have H := double_cauchy (fun i k=>|P k i| *|u i|) (fun i k=>|E i k|)
    (mul_nonneg (real_op_norm_nonneg P) (vectorNorm_nonneg u)) (norm_nonneg E)
    (by simpa only [mul_pow,vectorNorm_sq] using small_column_square P u)
    (by simpa only [sq_abs] using le_of_eq (SKGap.frobenius_sq E).symm)
  have HH := (le_abs_self (∑i,∑k,(|P k i| * |u i|)*|E i k|)).trans H
  simpa only [traceAbsolute,Matrix.diagonal_mul,abs_mul,mul_assoc] using HH

lemma trace_small_mean (P E : Interaction n) (U : VectorFields n) (x : Spin n) (hn : 0<n) :
    |trace (P*(siteMean U x • E))|≤SKGap.opNorm P*vectorNorm (U x)*‖E‖ := by
  have hscaled := scaled_frobenius_by_rows P (siteMean U x) (vectorNorm_nonneg _) (real_op_norm_nonneg P)
    (siteMean_square U x hn) (matrix_row_square_le P)
  rw [Matrix.mul_smul,←Matrix.smul_mul]
  exact (trace_frobenius _ E).trans ((mul_le_mul_of_nonneg_right hscaled (norm_nonneg E)).trans_eq (by ring))

lemma averageError_eq (a : Spin n→ℝ) (U : VectorFields n) (x : Spin n) :
    averageError a U x=Matrix.of (fun i k=>U x i*halfDiff k a x)-
      Matrix.of (fun i k=>2*spin x k*derivativeMatrix U x i k*halfDiff k a x) := by
  ext i k
  simp only [averageError,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.of_apply,derivativeMatrix]
  rw [halfDiff_mul]
  ring

lemma trace_column_scaled (P D : Interaction n) (t : Fin n→ℝ) (x : Spin n) :
    |trace (P*Matrix.of (fun i k=>2*spin x k*D i k*t k))|≤
      2*‖D‖*(SKGap.opNorm P*vectorNorm t) := by
  apply (trace_le_traceAbsolute P _).trans
  have H:=parameter_product_trace_bound P D t (norm_nonneg D) (vectorNorm_nonneg t)
    (le_of_eq (SKGap.frobenius_sq D).symm) (le_of_eq (vectorNorm_sq t).symm)
  have he : traceAbsolute P (Matrix.of (fun i k=>2*spin x k*D i k*t k))=
      2*(∑i,∑k,|P k i| *|D i k| *|t k|) := by
    simp only [traceAbsolute,Matrix.of_apply,abs_mul,abs_spin_eq_one,mul_one,
      abs_of_pos (by norm_num : (0:ℝ)<2),Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _; ring
  rw [he]
  exact (mul_le_mul_of_nonneg_left H (by norm_num)).trans_eq (by ring)

lemma averageError_trace (P : Interaction n) (a : Spin n→ℝ) (U : VectorFields n) (x : Spin n) :
    |trace (P*averageError a U x)|≤
      SKGap.opNorm P*(vectorNorm (U x)+2*‖derivativeMatrix U x‖)*‖derivativeVector a x‖ := by
  rw [averageError_eq,mul_sub,trace_sub]
  have h₁:=rank_one_trace_bound P (WithLp.toLp 2 (U x)) (derivativeVector a x)
  have h₂:=trace_column_scaled P (derivativeMatrix U x) (fun k=>halfDiff k a x) x
  apply ((abs_sub _ _).trans (add_le_add h₁ h₂)).trans_eq
  change SKGap.opNorm P*vectorNorm (U x)*‖derivativeVector a x‖+
    2*‖derivativeMatrix U x‖*(SKGap.opNorm P*‖derivativeVector a x‖)=_
  ring

lemma primary_averageError_trace (P : Interaction n) (U m : VectorFields n) (x : Spin n) (hn : 0<n)
    {C R : ℝ} (hC : 0≤C) (hR : 0≤R) (hU : ‖derivativeMatrix U x‖≤C)
    (hm : ∀i,|m x i|≤1) (hdm : SKGap.opNorm (derivativeMatrix m x)≤R) :
    |trace (P*averageError (siteMean U) m x)|≤SKGap.opNorm P*C*(1+2*R) := by
  have hd : (n:ℝ)*‖derivativeVector (siteMean U) x‖^2≤C^2 :=
    siteMean_derivative_square_bound hn ((opNorm_le_frobenius _).trans hU)
  have hm2 : vectorNorm (m x)^2≤(n:ℝ) := by
    rw [vectorNorm_sq]
    calc
      _ ≤ ∑_i:Fin n,(1:ℝ) := Finset.sum_le_sum fun i _=>by nlinarith [hm i,sq_abs (m x i),abs_nonneg (m x i)]
      _ = _ := by simp
  have hdm2 : ‖derivativeMatrix m x‖^2≤(n:ℝ)*R^2 := by
    rw [SKGap.frobenius_sq]
    calc
      _ ≤ ∑_i:Fin n,R^2 := Finset.sum_le_sum fun i _=>
        (matrix_row_square_le _ i).trans (pow_le_pow_left₀ (real_op_norm_nonneg _) hdm 2)
      _ = _ := by simp
  have h₁ : vectorNorm (m x)*‖derivativeVector (siteMean U) x‖≤C := by
    apply nonneg_le_nonneg_of_sq_le_sq hC
    simp only [←sq,mul_pow]
    exact (mul_le_mul_of_nonneg_right hm2 (sq_nonneg _)).trans hd
  have h₂ : ‖derivativeMatrix m x‖*‖derivativeVector (siteMean U) x‖≤C*R := by
    apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hC hR)
    simp only [←sq,mul_pow]
    have H := (mul_le_mul_of_nonneg_right hdm2 (sq_nonneg ‖derivativeVector (siteMean U) x‖)).trans
      (show (n:ℝ)*R^2*‖derivativeVector (siteMean U) x‖^2≤C^2*R^2 by
        nlinarith [mul_le_mul_of_nonneg_right hd (sq_nonneg R)])
    exact H
  apply (averageError_trace P (siteMean U) m x).trans
  have H := mul_le_mul_of_nonneg_left (add_le_add h₁ (mul_le_mul_of_nonneg_left h₂ (by norm_num : (0:ℝ)≤2)))
    (real_op_norm_nonneg P)
  nlinarith only [H]

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_Trace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap.SourceError
variable {n : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma SegmentRegular.partial_bound {H : ι→VectorFields n} {θ : κ→Spin n→ℝ}
    {F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ}
    {F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ}
    {x : Spin n} {C : ℝ} (h : SegmentRegular H θ F F' x C) (i : Fin n) (l : ι⊕κ) :
    |localPartial H θ F' l x i|≤C := by
  have hb : ‖F' i (localArgs H θ x i)‖≤C := by simpa using h.bound i i 0 (by constructor <;> norm_num)
  have hs : ‖(Pi.single l (1:ℝ) : Args (ι:=ι) (κ:=κ))‖≤1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
    intro a; simp only [Pi.single_apply]; split_ifs <;> norm_num
  have h₁ := (F' i (localArgs H θ x i)).le_opNorm (Pi.single l 1)
  exact h₁.trans ((mul_le_mul hb hs (norm_nonneg _) h.nonneg).trans_eq (mul_one C))

lemma sourceError_eq (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
    (s : VectorFields n) (x : Spin n) :
    sourceError H θ F F' s x=
      (∑α,Matrix.of (fun i k=>(s x i*localPartial H θ F' (.inr α) x i)*halfDiff k (θ α) x))+
      Matrix.of (fun i k=>s x i*taylorError H θ F F' x i k)-
      Matrix.of (fun i k=>2*spin x k*derivativeMatrix (coefficient H θ F) x i k*derivativeMatrix s x i k) := by
  ext i k
  simp only [sourceError,Matrix.sub_apply,Matrix.diagonal_mul,Matrix.sum_apply,Matrix.add_apply,Matrix.of_apply]
  rw [source_derivative_exact]
  ring

lemma sourceError_trace (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
    (s : VectorFields n) (x : Spin n) (P : Interaction n) {C S T B R L O : ℝ}
    (h : SegmentRegular H θ F F' x C) (hS : 0≤S) (hT : 0≤T) (hB : 0≤B)
    (hR : 0≤R) (hL : 0≤L) (hO : 0≤O)
    (hs : vectorNorm (s x)≤S) (hds : ‖derivativeMatrix s x‖≤S)
    (ht : vectorNorm (parameterIncrement θ x)≤T)
    (hQ4 : (∑i,∑k,(primaryIncrement H x i k)^4)≤B^4)
    (hQr : ∀i,(∑k,(primaryIncrement H x i k)^2)≤R^2)
    (hQd : (∑i,(primaryIncrement H x i i)^2)≤L^2)
    (hP : (∑i,∑k,if i=k then 0 else (P k i)^4)≤O^4) :
    |trace (P*sourceError H θ F F' s x)|≤
      SKGap.opNorm P*C*S*(∑α,‖derivativeVector (θ α) x‖)+
      4*C*SKGap.opNorm P*S*(B^2+R*T+T^2)+
      2*C*S*(O*B+SKGap.opNorm P*(L+T)) := by
  let Q := primaryIncrement H x
  let t := parameterIncrement θ x
  have hQ : ∀i k,0≤Q i k := fun i k=>Finset.sum_nonneg fun _ _=>abs_nonneg _
  have htt : ∀k,0≤t k := fun k=>Finset.sum_nonneg fun _ _=>abs_nonneg _
  have hs2 : (∑i,(s x i)^2)≤S^2 := by rw [←vectorNorm_sq]; exact pow_le_pow_left₀ (vectorNorm_nonneg _) hs 2
  have ht2 : (∑k,(t k)^2)≤T^2 := by rw [←vectorNorm_sq]; exact pow_le_pow_left₀ (vectorNorm_nonneg _) ht 2
  have hds2 : (∑i,∑k,(derivativeMatrix s x i k)^2)≤S^2 := by
    rw [←SKGap.frobenius_sq]; exact pow_le_pow_left₀ (norm_nonneg _) hds 2
  have htaylor := source_taylor_trace_bound P (Matrix.of (fun i k=>s x i*taylorError H θ F F' x i k)) Q (s x) t
    (mul_nonneg (by norm_num : (0:ℝ)≤4) h.nonneg) hS hT hB hR hs2 ht2 hQ4 hQr (by
      intro i k
      simp only [Matrix.of_apply,abs_mul,abs_of_nonneg (hQ i k),abs_of_nonneg (htt k)]
      have hh := taylor_error_bound H θ F F' x i k h.nonneg (hQ i k) (htt k)
        (local_argument_bound H θ x i k) (h.deriv i k) (h.lip i k)
      nlinarith [mul_le_mul_of_nonneg_left hh (abs_nonneg (s x i))])
  have hproduct := source_product_trace_bound P
    (Matrix.of (fun i k=>2*spin x k*derivativeMatrix (coefficient H θ F) x i k*derivativeMatrix s x i k))
    (derivativeMatrix s x) Q t (mul_nonneg (by norm_num : (0:ℝ)≤2) h.nonneg)
    hS hT hO hB hL hds2 ht2 hP hQ4 hQd (by
      intro i k
      simp only [Matrix.of_apply,abs_mul,abs_spin_eq_one,mul_one,abs_of_nonneg (hQ i k),abs_of_nonneg (htt k)]
      norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)]
      have hh := (coefficient_lipschitz k (fun y=>localArgs H θ y i) x (F i) (F' i)
        h.nonneg (h.deriv i k) (h.bound i k)).trans
          (mul_le_mul_of_nonneg_left (local_argument_bound H θ x i k) h.nonneg)
      change |derivativeMatrix (coefficient H θ F) x i k|≤C*(Q i k+t k) at hh
      nlinarith [mul_le_mul_of_nonneg_right hh (abs_nonneg (derivativeMatrix s x i k))])
  have hrank (α : κ) :
      |trace (P*Matrix.of (fun i k=>(s x i*localPartial H θ F' (.inr α) x i)*halfDiff k (θ α) x))|≤
        SKGap.opNorm P*C*S*‖derivativeVector (θ α) x‖ := by
    have hu : vectorNorm (fun i=>s x i*localPartial H θ F' (.inr α) x i)≤C*S := by
      have H₁ := (vectorNorm_mul (fun i=>localPartial H θ F' (.inr α) x i) (s x) h.nonneg
        (fun i=>h.partial_bound i (.inr α))).trans (mul_le_mul_of_nonneg_left hs h.nonneg)
      simpa only [mul_comm] using H₁
    have HH:=rank_one_trace_bound P
      (WithLp.toLp 2 (fun i=>s x i*localPartial H θ F' (.inr α) x i)) (derivativeVector (θ α) x)
    apply HH.trans
    change SKGap.opNorm P*vectorNorm _*‖derivativeVector (θ α) x‖≤_
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu (real_op_norm_nonneg P))
      (norm_nonneg (derivativeVector (θ α) x))]
  have hranks : |trace (P*(∑α,Matrix.of (fun i k=>(s x i*localPartial H θ F' (.inr α) x i)*halfDiff k (θ α) x)))|≤
      SKGap.opNorm P*C*S*(∑α,‖derivativeVector (θ α) x‖) := by
    rw [Matrix.mul_sum,trace_sum]
    exact (Finset.abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum fun α _=>hrank α).trans_eq (by rw [Finset.mul_sum]))
  rw [sourceError_eq,mul_sub,mul_add,trace_sub,trace_add]
  exact (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hranks htaylor)) hproduct)

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_RecipeError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap.Noncrossing.Primary
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

omit [Fintype κ] in
lemma sourceError_rearrange (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
    (s : VectorFields n) (x : Spin n) :
    derivativeMatrix (fun x i=>coefficient H θ F x i*s x i) x=
      Matrix.diagonal (coefficient H θ F x)*derivativeMatrix s x+
      (∑l,Matrix.diagonal (fun i=>s x i*localPartial H θ F' (.inl l) x i)*derivativeMatrix (H l) x)+
      sourceError H θ F F' s x := by unfold sourceError; abel

namespace OrdinaryData
variable (D : OrdinaryData n ι κ σ)

lemma sourceOf_derivative (a : ℕ) (Y : Fin a→VectorFields n) (x : Spin n) :
    derivativeMatrix (D.sourceOf a Y) x=
      (∑b,Matrix.diagonal (D.auxCoefficient a b x)*derivativeMatrix (Y b) x)+
      (∑l,Matrix.diagonal (D.partialOf a l Y x)*derivativeMatrix (D.H l) x)+D.sourceAtoms a Y x := by
  have he : D.sourceOf a Y=(fun x i=>(∑s,D.seedCoefficient a s x i*D.seed s i)+
      (∑b,D.auxCoefficient a b x i*Y b x i)) := rfl
  rw [he,derivativeMatrix_add,derivativeMatrix_sum,derivativeMatrix_sum]
  have hs (s : σ) := sourceError_rearrange D.H D.θ (D.seedFunction a s)
    (D.seedDerivative a s) (fun _=>D.seed s) x
  have hb (b : Fin a) := sourceError_rearrange D.H D.θ (D.auxFunction a b)
    (D.auxDerivative a b) (Y b) x
  change (∑s,derivativeMatrix (fun x i=>coefficient D.H D.θ (D.seedFunction a s) x i*D.seed s i) x)+
    (∑b,derivativeMatrix (fun x i=>coefficient D.H D.θ (D.auxFunction a b) x i*Y b x i) x)=_
  simp_rw [hs,hb]
  simp only [Finset.sum_add_distrib]
  have hz (s : σ) : derivativeMatrix (fun _ : Spin n=>D.seed s) x=0 := by
    ext i k; simp [derivativeMatrix,halfDiff]
  simp only [hz,mul_zero,Finset.sum_const_zero,zero_add]
  have hparts :
      (∑s,∑l,Matrix.diagonal (fun i=>D.seed s i*localPartial D.H D.θ (D.seedDerivative a s) (.inl l) x i)*derivativeMatrix (D.H l) x)+
      (∑b,∑l,Matrix.diagonal (fun i=>Y b x i*localPartial D.H D.θ (D.auxDerivative a b) (.inl l) x i)*derivativeMatrix (D.H l) x)=
      ∑l,Matrix.diagonal (D.partialOf a l Y x)*derivativeMatrix (D.H l) x := by
    rw [Finset.sum_comm (f:=fun s l=>Matrix.diagonal (fun i=>D.seed s i*localPartial D.H D.θ (D.seedDerivative a s) (.inl l) x i)*derivativeMatrix (D.H l) x),
      Finset.sum_comm (f:=fun b l=>Matrix.diagonal (fun i=>Y b x i*localPartial D.H D.θ (D.auxDerivative a b) (.inl l) x i)*derivativeMatrix (D.H l) x),
      ←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro l _
    ext i k
    simp only [Matrix.add_apply,Matrix.sum_apply,Matrix.diagonal_mul,partialOf,seedPartial,auxPartial,
      add_mul,Finset.sum_mul]
    congr 1 <;> (apply Finset.sum_congr rfl; intro b _; ring)
  dsimp only [sourceAtoms]
  rw [←hparts]
  simp only [auxCoefficient]
  abel

lemma source_error_recursion (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) :
    D.sourceDerivativeError T x a=
      (∑b:Fin a,Matrix.diagonal (D.auxCoefficient a b x)*D.fieldDerivativeError T x b)+
      (∑l,Matrix.diagonal (D.sourcePartial a l x)*
        (derivativeMatrix (D.H l) x-SourceTree.fieldMatrix D.j D.J (T l)))+
      D.sourceAtoms a (fun b=>D.auxiliary b) x := by
  rw [sourceDerivativeError,D.source_eq,D.sourceOf_derivative,D.retainedSource_eq]
  simp only [fieldDerivativeError,mul_sub,Finset.sum_sub_distrib,sourcePartial]
  abel

lemma fieldOf_derivative (a : ℕ) (W Y : Fin a→VectorFields n) (x : Spin n) :
    derivativeMatrix (D.fieldOf a W Y) x=
      D.J*derivativeMatrix (D.sourceOf a Y) x-
      (∑l,(D.j*siteMean (D.partialOf a l Y) x) • derivativeMatrix (D.predecessor l) x)-
      (∑b,(D.j*siteMean (D.auxCoefficient a b) x) • derivativeMatrix (W b) x)-
      D.j • ((∑l,averageError (siteMean (D.partialOf a l Y)) (D.predecessor l) x)+
        ∑b,averageError (siteMean (D.auxCoefficient a b)) (W b) x) := by
  have he : D.fieldOf a W Y=(fun x i=>(0+D.J.mulVec (D.sourceOf a Y x) i)-
      (D.j*(∑l,siteMean (D.partialOf a l Y) x*D.predecessor l x i))-
      (D.j*(∑b,siteMean (D.auxCoefficient a b) x*W b x i))) := by
    ext x i; simp [fieldOf]
  rw [he,derivativeMatrix_sub,derivativeMatrix_sub]
  simp only [Matrix.mulVec, dotProduct]
  rw [derivativeMatrix_linear,
    derivativeMatrix_smul,derivativeMatrix_smul,derivativeMatrix_sum,derivativeMatrix_sum]
  have he₁ (l : ι) : derivativeMatrix (fun y i=>siteMean (D.partialOf a l Y) y*D.predecessor l y i) x=
      siteMean (D.partialOf a l Y) x • derivativeMatrix (D.predecessor l) x+
        averageError (siteMean (D.partialOf a l Y)) (D.predecessor l) x := by unfold averageError; abel
  have he₂ (b : Fin a) : derivativeMatrix (fun y i=>siteMean (D.auxCoefficient a b) y*W b y i) x=
      siteMean (D.auxCoefficient a b) x • derivativeMatrix (W b) x+
        averageError (siteMean (D.auxCoefficient a b)) (W b) x := by unfold averageError; abel
  simp only [he₁,he₂,Finset.sum_add_distrib,smul_add,Finset.smul_sum,smul_smul]
  abel

lemma field_error_recursion (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) :
    D.fieldDerivativeError T x a=D.J*D.sourceDerivativeError T x a-
      (∑l,(D.j*siteMean (D.sourcePartial a l) x) •
        (derivativeMatrix (D.predecessor l) x-SourceTree.sourceMatrix D.j D.J (T l)))-
      (∑b:Fin a,(D.j*siteMean (D.auxCoefficient a b) x) • D.sourceDerivativeError T x b)-
      D.j • ((∑l,averageError (siteMean (D.sourcePartial a l)) (D.predecessor l) x)+
        ∑b:Fin a,averageError (siteMean (D.auxCoefficient a b)) (D.source b) x) := by
  rw [fieldDerivativeError,D.auxiliary_eq,D.fieldOf_derivative,D.retainedField_eq]
  rw [sourceDerivativeError,D.source_eq]
  simp only [sourceDerivativeError,smul_sub,Finset.sum_sub_distrib,mul_sub,sourcePartial]
  abel

end OrdinaryData
end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_RecipeIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma finite_sum_fourth (f : ι→ℝ) :
    (∑l,f l)^4≤(Fintype.card ι:ℝ)^3*∑l,(f l)^4 := by
  have h1:=sq_sum_le_card_mul_sum_sq (s:=Finset.univ) (f:=f)
  have h2:=sq_sum_le_card_mul_sum_sq (s:=Finset.univ) (f:=fun l=>(f l)^2)
  simp only [Finset.card_univ] at h1 h2
  have hsq:=pow_le_pow_left₀ (sq_nonneg (∑l,f l)) h1 2
  have hh:=mul_le_mul_of_nonneg_left h2 (sq_nonneg (Fintype.card ι:ℝ))
  simp only [←pow_mul] at hsq hh
  norm_num only [Nat.reduceMul] at hsq hh
  nlinarith only [hsq,hh]

lemma primaryIncrement_fourth (H : ι→VectorFields n) (x : Spin n) {P : ℝ}
    (hP : 0≤P) (hH : ∀l,ShapeBound (derivativeMatrix (H l) x) P) :
    (∑i,∑k,(primaryIncrement H x i k)^4)≤(2*(Fintype.card ι:ℝ)*P)^4 := by
  have h1 : (∑i,∑k,(primaryIncrement H x i k)^4)≤
      (Fintype.card ι:ℝ)^3*∑l,∑i,∑k,(derivativeMatrix (H l) x i k)^4 := by
    calc
      _ ≤ ∑i,∑k,(Fintype.card ι:ℝ)^3*∑l,(derivativeMatrix (H l) x i k)^4 := by
        apply Finset.sum_le_sum; intro i _; apply Finset.sum_le_sum; intro k _
        simpa only [primaryIncrement,show (4:ℕ)=2*2 from rfl,pow_mul,sq_abs] using finite_sum_fourth (fun l=>|derivativeMatrix (H l) x i k|)
      _ = _ := by
        simp_rw [←Finset.mul_sum]
        congr 1
        rw [show (∑i,∑k,∑l,(derivativeMatrix (H l) x i k)^4)=
            ∑i,∑l,∑k,(derivativeMatrix (H l) x i k)^4 from
          Finset.sum_congr rfl (fun i _=>Finset.sum_comm)]
        exact Finset.sum_comm
  have h2 : (∑l,∑i,∑k,(derivativeMatrix (H l) x i k)^4)≤(Fintype.card ι:ℝ)*(2*P^4) := by
    exact (Finset.sum_le_sum (fun l _=>fourth_sum_le hP (hH l))).trans_eq (by simp)
  have h3 := h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  have hnn : 0≤(Fintype.card ι:ℝ)^4*P^4 := by positivity
  nlinarith only [h3,hnn]

lemma primaryIncrement_row (H : ι→VectorFields n) (x : Spin n) {P : ℝ}
    (hP : 0≤P) (hH : ∀l,SKGap.opNorm (derivativeMatrix (H l) x)≤P) (i : Fin n) :
    (∑k,(primaryIncrement H x i k)^2)≤((Fintype.card ι:ℝ)*P)^2 := by
  have H₁ : vectorNorm (primaryIncrement H x i)≤(Fintype.card ι:ℝ)*P := by
    calc
      _ ≤ ∑l,vectorNorm (fun k=>|derivativeMatrix (H l) x i k|) := by
        convert! vectorNorm_sum (fun l k=>|derivativeMatrix (H l) x i k|) using 1
        all_goals try with_reducible_and_instances rfl
        congr 1; ext k; simp [primaryIncrement]
      _ ≤ ∑_l:ι,P := Finset.sum_le_sum fun l _=>by rw [vectorNorm_abs]; exact (row_vectorNorm_le_opNorm _ _).trans (hH l)
      _ = _ := by simp
  rw [←vectorNorm_sq]
  exact (pow_le_pow_iff_left₀ (vectorNorm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) hP) (by decide : 2 ≠ 0)).2 H₁

lemma primaryIncrement_diagonal (H : ι→VectorFields n) (x : Spin n) {P : ℝ}
    (hP : 0≤P) (hH : ∀l,SKGap.diagonalSeminorm (derivativeMatrix (H l) x)≤P) :
    (∑i,(primaryIncrement H x i i)^2)≤((Fintype.card ι:ℝ)*P)^2 := by
  have H₁ : vectorNorm (fun i=>primaryIncrement H x i i)≤(Fintype.card ι:ℝ)*P := by
    calc
      _ ≤ ∑l,vectorNorm (fun i=>|derivativeMatrix (H l) x i i|) := by
        convert! vectorNorm_sum (fun l i=>|derivativeMatrix (H l) x i i|) using 1
        all_goals try with_reducible_and_instances rfl
        congr 1; ext i; simp [primaryIncrement]
      _ ≤ ∑_l:ι,P := Finset.sum_le_sum fun l _=>by rw [vectorNorm_abs]; exact hH l
      _ = _ := by simp
  rw [←vectorNorm_sq]
  exact (pow_le_pow_iff_left₀ (vectorNorm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) hP) (by decide : 2 ≠ 0)).2 H₁

lemma parameterIncrement_bound (θ : κ→Spin n→ℝ) (x : Spin n) :
    vectorNorm (parameterIncrement θ x)≤∑α,‖derivativeVector (θ α) x‖ := by
  calc
    _ ≤ ∑α,vectorNorm (fun k=>|halfDiff k (θ α) x|) := by
      convert! vectorNorm_sum (fun α k=>|halfDiff k (θ α) x|) using 1
      all_goals try with_reducible_and_instances rfl
      congr 1; ext k; simp [parameterIncrement]
    _ = _ := by apply Finset.sum_congr rfl; intro α _; rw [vectorNorm_abs]; rfl

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {H : ι→VectorFields n} {θ : κ→Spin n→ℝ}
variable {F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ}
variable {F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ}
variable {x : Spin n} {C : ℝ}

lemma SegmentRegular.partial_difference (h : SegmentRegular H θ F F' x C)
    (l : ι⊕κ) (i k : Fin n) :
    |derivativeMatrix (localPartial H θ F' l) x i k|≤
      C*‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖ := by
  have hv : ‖(Pi.single l 1 : Args (ι:=ι) (κ:=κ))‖≤1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
    intro a; simp only [Pi.single_apply]; split_ifs <;> norm_num
  have hh:=h.lip i k 1 (by constructor <;> norm_num)
  simp only [one_smul,add_sub_cancel] at hh
  have H₁ := (F' i (localArgs H θ (flip x k) i)-F' i (localArgs H θ x i)).le_opNorm (Pi.single l 1)
  have H₂ : |localPartial H θ F' l (flip x k) i-localPartial H θ F' l x i|≤
      C*‖localArgs H θ (flip x k) i-localArgs H θ x i‖ := by
    apply H₁.trans
    exact (mul_le_mul_of_nonneg_left hv (norm_nonneg _)).trans (by simpa only [mul_one] using hh)
  rw [derivativeMatrix,halfDiff_as_flip,abs_div,abs_mul,abs_spin_eq_one,one_mul,
    abs_of_pos (by norm_num : (0:ℝ)<2),flipHalfDiff_norm,abs_sub_comm]
  exact (div_le_div_of_nonneg_right H₂ (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)

lemma SegmentRegular.partial_row (h : SegmentRegular H θ F F' x C) (l : ι⊕κ) (i : Fin n) :
    vectorNorm (derivativeMatrix (localPartial H θ F' l) x i)≤
      C*((∑q,SKGap.opNorm (derivativeMatrix (H q) x))+(∑α,‖derivativeVector (θ α) x‖)) := by
  calc
    _ ≤ vectorNorm (fun k=>C*‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖) :=
      vectorNorm_mono fun k=>by
        rw [abs_of_nonneg (mul_nonneg h.nonneg (norm_nonneg _))]
        exact h.partial_difference l i k
    _ = C*vectorNorm (fun k=>‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖) := by
      convert! vectorNorm_smul C (fun k=>‖flipHalfDiff k (fun y=>localArgs H θ y i) x‖) using 1
      all_goals try with_reducible_and_instances rfl
      rw [abs_of_nonneg h.nonneg]
    _ ≤ _ := mul_le_mul_of_nonneg_left (local_argument_row_bound H θ x i) h.nonneg

omit [DecidableEq ι] [DecidableEq κ] in
lemma SegmentRegular.coefficient_bound (h : SegmentRegular H θ F F' x C)
    {A G : ℝ} (hA : 0≤A) (hG : 0≤G) (hv : ∀i,|coefficient H θ F x i|≤A)
    (hg : (∑q,SKGap.opNorm (derivativeMatrix (H q) x))+(∑α,‖derivativeVector (θ α) x‖)≤G) :
    CoefficientBound (coefficient H θ F) x A (C*G) := by
  refine ⟨hA,mul_nonneg h.nonneg hG,hv,?_⟩
  intro i
  have H₁ := (coefficient_row_bound H θ F F' x i h.nonneg (h.deriv i) (h.bound i)).trans
    (mul_le_mul_of_nonneg_left hg h.nonneg)
  rw [←vectorNorm_sq]
  exact pow_le_pow_left₀ (vectorNorm_nonneg _) H₁ 2

lemma SegmentRegular.partial_bound_coefficient (h : SegmentRegular H θ F F' x C)
    (l : ι⊕κ) {A G : ℝ} (hA : 0≤A) (hG : 0≤G) (hCA : C≤A)
    (hg : (∑q,SKGap.opNorm (derivativeMatrix (H q) x))+(∑α,‖derivativeVector (θ α) x‖)≤G) :
    CoefficientBound (localPartial H θ F' l) x A (C*G) := by
  refine ⟨hA,mul_nonneg h.nonneg hG,fun i=>(h.partial_bound i l).trans hCA,?_⟩
  intro i
  have H₁ := (h.partial_row l i).trans (mul_le_mul_of_nonneg_left hg h.nonneg)
  rw [←vectorNorm_sq]
  exact pow_le_pow_left₀ (vectorNorm_nonneg _) H₁ 2

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_WordFockSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.Tensor.Series
open Diagram InverseDiagram WordSeries Loop
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma act_comp (A B : Space (ι:=ι)→ₗ[ℝ] Space (ι:=ι)) :
    act (A.comp B)=(act A).comp (act B) := rfl
omit [Fintype ι] in
lemma act_ofVector (A : Space (ι:=ι)→ₗ[ℝ] Space (ι:=ι)) (v : Space (ι:=ι)) :
    act A (ofVector v)=ofVector (A v) := by
  funext n
  simp only [act_apply,ofVector]
  split_ifs <;> simp
lemma wordOperator_append (j : ℝ) (a : ι→ℝ) (P Q : List (WordLetter ι)) :
    wordOperator j a (P++Q)=(wordOperator j a P).comp (wordOperator j a Q) := by
  induction P with
  | nil => simp [wordOperator]
  | cons l P ih => cases l <;> simp [wordOperator,ih,LinearMap.comp_assoc]
lemma wordOperator_lift (j : ℝ) (a : ι→ℝ) (P : List (Letter (ι→ℝ))) :
    wordOperator j a (liftWord P)=act (word j P) := by
  induction P with
  | nil => rfl
  | cons l P ih => cases l <;> simp only [liftWord_cons,Letter.toWord,wordOperator,word,letter,ih,act_comp]
lemma wordSeq_lift (j : ℝ) (a : ι→ℝ) (P : List (Letter (ι→ℝ))) :
    wordSeq j a (liftWord P)=ofVector (word j P vacuum) := by
  rw [wordSeq,wordOperator_lift,act_ofVector]
lemma wordSeq_oneInverse (j : ℝ) (a : ι→ℝ) (P Q : List (Letter (ι→ℝ))) (n : ℕ) :
    wordSeq j a (liftWord P++(.inverse::liftWord Q)) n=
      word j P (kernel j a n (word j Q vacuum)) := by
  simp only [wordSeq,wordOperator_append,wordOperator,wordOperator_lift,
    LinearMap.comp_apply,act_ofVector,act_apply,inverse_ofVector]
lemma project_kernel_sandwich (j : ℝ) (a : ι→ℝ) (P Q : List (Letter (ι→ℝ))) (n : ℕ) (i : ι) :
    project (word j P (kernel j a n (word j Q vacuum))) i=inverseCoefficient j a P Q n i := by
  simp only [kernel,LinearMap.sum_apply,map_sum,Finset.sum_apply,inverseCoefficient]
  apply Finset.sum_congr rfl
  intro bs _
  rw [←Tensor.project_word,word_append,word_append]
  rfl

theorem wordSeq_project_coeff (j : ℝ) (a : ι→ℝ) (F : List (WordLetter ι))
    (hF : inverseCount F≤1) (n : ℕ) (i : ι) :
    project (wordSeq j a F n) i=(wordPredictionPolynomial j a F i).coeff n := by
  have h:=congrArg (PowerSeries.coeff n)
    (literalSeries_eq_wordPredictionPolynomial j a F hF i)
  rw [Polynomial.coeff_coe] at h
  rw [←h]
  rcases one_inverse_cases F hF with ⟨P,rfl⟩ | ⟨P,Q,rfl⟩
  · rw [wordSeq_lift,literalSeries_lift]
    simp only [ofVector,PowerSeries.coeff_C]
    split_ifs <;> simp_all [Tensor.project_word]
  · rw [wordSeq_oneInverse,project_kernel_sandwich,literalSeries_oneInverse,coeff_inverseSeries]

end SKGap.Noncrossing.Primary.Tensor.Series

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.Tensor.Series
open Diagram InverseDiagram WordSeries Loop
variable {ι : Type*} [Fintype ι]

lemma wordSeq_cons (j : ℝ) (a : ι→ℝ) (l : WordLetter ι) (F : List (WordLetter ι)) :
    wordSeq j a (l::F)=letterOperator j a l (wordSeq j a F) := by cases l <;> rfl

end SKGap.Noncrossing.Primary.Tensor.Series

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_ClosedTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.Noncrossing
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma exactWord_append (j : ℝ) (a : ι→ℝ) (J : Matrix ι ι ℝ) (P Q : List (WordLetter ι)) :
    exactWord j a (P++Q) J=exactWord j a P J*exactWord j a Q J := by
  induction P with
  | nil => simp [exactWord,matrixFactorProduct]
  | cons l P ih =>
    change l.exactEval j a J*exactWord j a (P++Q) J=
      (l.exactEval j a J*exactWord j a P J)*exactWord j a Q J
    rw [ih,mul_assoc]
lemma exactWord_diag (j : ℝ) (a d : ι→ℝ) (J : Matrix ι ι ℝ) (F : List (WordLetter ι)) :
    exactWord j a (.diag d::F) J=Matrix.diagonal d*exactWord j a F J := rfl

omit [DecidableEq ι] in
lemma wordPrediction_diag (j : ℝ) (a d : ι→ℝ) (z : ℝ) (F : List (WordLetter ι))
    (hF : inverseCount F≤1) (i : ι) :
    wordPrediction j a z (.diag d::F) i=d i*wordPrediction j a z F i := by
  have hp : wordPredictionPolynomial j a (.diag d::F) i=
      Polynomial.C (d i)*wordPredictionPolynomial j a F i := by
    apply Polynomial.ext
    intro n
    rw [←Primary.Tensor.Series.wordSeq_project_coeff j a (.diag d::F) (show inverseCount (.diag d::F)≤1 from hF),
      Polynomial.coeff_C_mul,←Primary.Tensor.Series.wordSeq_project_coeff j a F hF,
      Primary.Tensor.Series.wordSeq_cons]
    rfl
  have h:=congrArg (Polynomial.eval z) hp
  simpa only [Polynomial.eval_mul,Polynomial.eval_C,
    fun F i=>(wordPredictionPolynomial_spec j a F i).2 z] using h

lemma trace_small_diagonal_error (s v : ι→ℝ) (Q : Matrix ι ι ℝ) :
    |trace (Matrix.diagonal s*Q)-∑ i,s i*v i|≤
      ‖(WithLp.toLp 2 s : EuclideanSpace ℝ ι)‖*diagonalSeminorm (Q-Matrix.diagonal v) := by
  have h:=abs_real_inner_le_norm (WithLp.toLp 2 s : EuclideanSpace ℝ ι)
    (diagonalVector (Q-Matrix.diagonal v))
  simpa only [trace,diag,Matrix.diagonal_mul,Matrix.sub_apply,Matrix.diagonal_apply_eq,
    diagonalVector,PiLp.inner_apply,Real.inner_apply,PiLp.toLp_apply,
    mul_sub,Finset.sum_sub_distrib,diagonalSeminorm] using h

theorem rotated_small_word_trace_error (j : ℝ) (a d s : ι→ℝ) (J : Matrix ι ι ℝ)
    (P Q : List (WordLetter ι)) (hF : inverseCount (P++(.diag s::Q))≤1) :
    |trace (Matrix.diagonal d*exactWord j a (P++(.diag s::Q)) J)-
      ∑ i,d i*wordPrediction j a 1 (P++(.diag s::Q)) i|≤
      ‖(WithLp.toLp 2 s : EuclideanSpace ℝ ι)‖*
        diagonalSeminorm (exactWord j a (Q++(.diag d::P)) J-
          Matrix.diagonal (wordPrediction j a 1 (Q++(.diag d::P)))) := by
  have hrot : inverseCount (Q++(.diag d::P))≤1 := by
    simp only [inverseCount_append] at hF ⊢
    change inverseCount Q+inverseCount P≤1
    change inverseCount P+inverseCount Q≤1 at hF
    omega
  have hc : (∑ i,d i*wordPrediction j a 1 (P++(.diag s::Q)) i)=
      ∑ i,s i*wordPrediction j a 1 (Q++(.diag d::P)) i := by
    have h0 : inverseCount ((.diag d::P)++(.diag s::Q))≤1 := hF
    have h:=wordPrediction_mean_cyclic j a 1 (.diag d::P) (.diag s::Q) h0
    simpa only [List.cons_append,wordPrediction_diag j a d 1 _ hF,
      wordPrediction_diag j a s 1 _ hrot] using h
  rw [hc,exactWord_append,exactWord_diag,←mul_assoc,
    trace_mul_comm (Matrix.diagonal d*exactWord j a P J),mul_assoc]
  rw [←exactWord_diag,←exactWord_append]
  exact trace_small_diagonal_error s _ _

end SKGap.Noncrossing

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.Noncrossing.Primary
open Diagram WordSeries Matrix
variable {n : ℕ}

namespace SmallMark

lemma prefix_vector (P : List (Letter (Fin n→ℝ))) (t : SmallMark n) : (t.prepend P).vector=t.vector := by cases t <;> rfl
lemma prefix_scalar (P : List (Letter (Fin n→ℝ))) (t : SmallMark n) : (t.prepend P).scalar=t.scalar := by cases t <;> rfl
lemma prefix_word (P : List (Letter (Fin n→ℝ))) (t : SmallMark n) : (t.prepend P).word=P++t.word := by
  cases t <;> simp [prepend,word,List.append_assoc]

lemma average_norm_product (hn : 0<n) (s d : Fin n→ℝ) (hd : ∀i,|d i|≤1) :
    |Diagram.mean s| * SKGapCutoff.Recipe.vectorNorm d ≤ SKGapCutoff.Recipe.vectorNorm s := by
  have H:=SKGapCutoff.Recipe.primary_mean_size (fun _=>s) (fun _=>d) (fun _=>false) hn
    (fun i=>hd i)
  change SKGapCutoff.Recipe.vectorNorm ((SKGapCutoff.Primary.siteMean (fun _=>s) (fun _=>false)) • d)≤_ at H
  rw [SKGapCutoff.Recipe.vectorNorm_smul] at H
  simpa only [SKGapCutoff.Primary.siteMean,Diagram.mean,Fintype.card_fin] using H

lemma rotated_trace_error (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (d s : Fin n→ℝ)
    (P Q : List (Letter (Fin n→ℝ))) :
    |trace (Matrix.diagonal d*matrixWord J (P++(.diag s::Q)))-
      ∑i,d i*Diagram.prediction j (P++(.diag s::Q)) i| ≤
      SKGapCutoff.Recipe.vectorNorm s * diagonalSeminorm
        (matrixWord J (Q++(.diag d::P))-Matrix.diagonal (Diagram.prediction j (Q++(.diag d::P)))) := by
  have h1 : liftWord P++(.diag s::liftWord Q)=liftWord (P++(.diag s::Q)) := by simp [liftWord,Letter.toWord]
  have h2 : liftWord Q++(.diag d::liftWord P)=liftWord (Q++(.diag d::P)) := by simp [liftWord,Letter.toWord]
  have H:=rotated_small_word_trace_error j (fun _:Fin n=>0) d s J (liftWord P) (liftWord Q)
    (by rw [h1,inverseCount_lift]; omega)
  rw [h1,h2,exactWord_lift,exactWord_lift] at H
  have he : wordPrediction j (fun _:Fin n=>0) 1 (liftWord (Q++(.diag d::P)))=
      Diagram.prediction j (Q++(.diag d::P)) := by funext i; exact wordPrediction_lift ..
  rw [he] at H
  simpa only [wordPrediction_lift,SKGapCutoff.Recipe.vectorNorm] using H

theorem trace_error (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (hn : 0<n)
    (d : Fin n→ℝ) (hd : ∀i,|d i|≤1) (t : SmallMark n) {B : ℝ} (hB : 0≤B)
    (hb : diagonalSeminorm (matrixWord J (t.diagnostic d)-
      Matrix.diagonal (Diagram.prediction j (t.diagnostic d)))≤B) :
    |t.scalar*(trace (Matrix.diagonal d*matrixWord J t.word)-
      ∑i,d i*Diagram.prediction j t.word i)| ≤ SKGapCutoff.Recipe.vectorNorm t.vector*B := by
  cases t with
  | diagonal P s Q =>
    simpa only [scalar,one_mul,word,diagnostic,vector] using
      (rotated_trace_error j J d s P Q).trans
        (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
  | average s P =>
    have H:=trace_small_diagonal_error d (Diagram.prediction j P) (matrixWord J P)
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left H (abs_nonneg _)).trans
      (by
        change |Diagram.mean s| * (SKGapCutoff.Recipe.vectorNorm d*_)≤SKGapCutoff.Recipe.vectorNorm s*B
        calc
          _ ≤ |Diagram.mean s| *(SKGapCutoff.Recipe.vectorNorm d*B) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (norm_nonneg _)) (abs_nonneg _)
          _ = (|Diagram.mean s| * SKGapCutoff.Recipe.vectorNorm d)*B := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (average_norm_product hn s d hd) hB)

end SmallMark

namespace MarkedPolynomial

lemma plain_prefix (F : List (Letter (Fin n→ℝ))) (P : MarkedPolynomial n) :
    (P.prepend F).plain=prependWords F P.plain := by
  simp [prepend,plain,prependWords,List.map_map,Function.comp_def,SmallMark.prefix_scalar,SmallMark.prefix_word]
lemma plain_scale (c : ℝ) (P : MarkedPolynomial n) : (P.scale c).plain=Primary.scale c P.plain := by
  simp [scale,plain,Primary.scale,List.map_map,Function.comp_def,mul_assoc]
lemma plain_append (P Q : MarkedPolynomial n) : (P++Q).plain=P.plain++Q.plain := by simp [plain]
lemma budget_prefix (F : List (Letter (Fin n→ℝ))) (P : MarkedPolynomial n) : (P.prepend F).budget=P.budget := by
  simp [prepend,budget,List.map_map,Function.comp_def,SmallMark.prefix_vector]
lemma budget_scale (c : ℝ) (P : MarkedPolynomial n) : (P.scale c).budget=|c| *P.budget := by
  induction P with
  | nil => simp [scale,budget]
  | cons t P ih => simp [scale,budget,abs_mul,mul_assoc,mul_add] at *; exact ih
lemma budget_append (P Q : MarkedPolynomial n) : (P++Q).budget=P.budget+Q.budget := by simp [budget]

theorem trace_error (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (hn : 0<n)
    (d : Fin n→ℝ) (hd : ∀i,|d i|≤1) (P : MarkedPolynomial n) {B : ℝ} (hB : 0≤B)
    (hb : ∀t∈P,diagonalSeminorm (matrixWord J (t.2.diagnostic d)-
      Matrix.diagonal (Diagram.prediction j (t.2.diagnostic d)))≤B) :
    |trace (Matrix.diagonal d*matrixPolynomial J P.plain)-
      ∑i,d i*polynomialPrediction j P.plain i|≤P.budget*B := by
  induction P with
  | nil => simp [plain,budget,matrixPolynomial,polynomialPrediction]
  | cons t P ih =>
    have ht:=SmallMark.trace_error j J hn d hd t.2 hB (hb t (by simp))
    have hh:=ih (fun s hs=>hb s (List.mem_cons_of_mem _ hs))
    simp only [plain,List.map_cons,matrixPolynomial,List.sum_cons,polynomialPrediction,budget] at *
    simp only [mul_add,mul_smul_comm,trace_add,trace_smul,smul_eq_mul,Finset.sum_add_distrib,add_mul]
    have he : (∑i,d i*(t.1*t.2.scalar*Diagram.prediction j t.2.word i))=
        t.1*t.2.scalar*(∑i,d i*Diagram.prediction j t.2.word i) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [he]
    have hc:=mul_le_mul_of_nonneg_left ht (abs_nonneg t.1)
    rw [←abs_mul] at hc
    calc
      _ = |t.1*(t.2.scalar*(trace (Matrix.diagonal d*matrixWord J t.2.word)-
            ∑i,d i*Diagram.prediction j t.2.word i))+
          (trace (Matrix.diagonal d*(List.map (fun p=>p.1 • matrixWord J p.2)
            (List.map (fun t=>(t.1*t.2.scalar,t.2.word)) P)).sum)-
            ∑i,d i*(List.map (fun p=>p.1*Diagram.prediction j p.2 i)
              (List.map (fun t=>(t.1*t.2.scalar,t.2.word)) P)).sum)| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add (by convert! hc using 1; ring) hh)

end MarkedPolynomial
end SKGap.Noncrossing.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_RecipeMarked
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.MarkedPolynomial
open Diagram
variable {n : ℕ}

lemma plain_diagonalWords (s : Fin n→ℝ) (P : WordPolynomial (ι:=Fin n)) :
    (diagonalWords s P).plain=prependWords [.diag s] P := by
  simp [diagonalWords,plain,prependWords,List.map_map,Function.comp_def,SmallMark.scalar,SmallMark.word]
lemma plain_averageWords (c : ℝ) (s : Fin n→ℝ) (P : WordPolynomial (ι:=Fin n)) :
    (averageWords c s P).plain=Primary.scale (c*Diagram.mean s) P := by
  simp only [averageWords,plain,Primary.scale,List.map_map,Function.comp_def,SmallMark.scalar,SmallMark.word]
  congr 1; funext t; congr 1; ring
lemma budget_diagonalWords (s : Fin n→ℝ) (P : WordPolynomial (ι:=Fin n)) :
    (diagonalWords s P).budget=SKGapCutoff.Recipe.vectorNorm s*mass P := by
  induction P with
  | nil => simp [diagonalWords,budget,mass]
  | cons t P ih =>
    simp only [diagonalWords,List.map_cons,budget,List.sum_cons,SmallMark.vector,mass] at *
    rw [ih]; ring
lemma budget_averageWords (c : ℝ) (s : Fin n→ℝ) (P : WordPolynomial (ι:=Fin n)) :
    (averageWords c s P).budget=|c| *SKGapCutoff.Recipe.vectorNorm s*mass P := by
  induction P with
  | nil => simp [averageWords,budget,mass]
  | cons t P ih =>
    simp only [averageWords,List.map_cons,budget,List.sum_cons,SmallMark.vector,mass,abs_mul] at *
    rw [ih]; ring

lemma zeroPair_plain (j : ℝ) : pairPlain (zeroPair (n:=n))=(SourceTree.leaf 0).words j := by
  simp [pairPlain,zeroPair,plain,SmallMark.scalar,SmallMark.word,SourceTree.words]

lemma smallBranch_plain (j : ℝ) (p : Fin n→ℝ) (T S : SourceTree (Fin n→ℝ)) (V : Pair n)
    (hV : pairPlain V=S.words j) : pairPlain (smallBranch j p T V)=(SourceTree.branch p T S).words j := by
  have hv₁ : V.1.plain=(S.words j).1 := congrArg Prod.fst hV
  have hv₂ : V.2.plain=(S.words j).2 := congrArg Prod.snd hV
  simp only [pairPlain,smallBranch,plain_append,plain_prefix,plain_diagonalWords,plain_averageWords,hv₁,hv₂,
    SourceTree.words]
  congr 1
  simp [prependWords,List.map_map,Function.comp_def,neg_mul]

lemma boundedBranch_plain (j : ℝ) (p : Fin n→ℝ) (T S : SourceTree (Fin n→ℝ)) (U V : Pair n)
    (hU : pairPlain U=T.words j) (hV : pairPlain V=S.words j) :
    pairPlain (boundedBranch j p U V)=(SourceTree.branch p T S).words j := by
  have hu₁ : U.1.plain=(T.words j).1 := congrArg Prod.fst hU
  have hu₂ : U.2.plain=(T.words j).2 := congrArg Prod.snd hU
  have hv₁ : V.1.plain=(S.words j).1 := congrArg Prod.fst hV
  have hv₂ : V.2.plain=(S.words j).2 := congrArg Prod.snd hV
  simp only [pairPlain,boundedBranch,plain_append,plain_prefix,plain_scale,hu₁,hu₂,hv₁,hv₂,SourceTree.words]

lemma fold_plain {α : Type*} (j : ℝ) (xs : List α) (p : α→Fin n→ℝ)
    (T : α→SourceTree (Fin n→ℝ)) (step : α→Pair n→Pair n)
    (hstep : ∀a V S,pairPlain V=S.words j→pairPlain (step a V)=(SourceTree.branch (p a) (T a) S).words j) :
    pairPlain (xs.foldr step zeroPair)=(SourceTree.branches (xs.map (fun a=>(p a,T a)))).words j := by
  induction xs with
  | nil => exact zeroPair_plain j
  | cons a xs ih => exact hstep a _ _ ih

end SKGap.Noncrossing.Primary.MarkedPolynomial
namespace SKGapCutoff.Recipe.OrdinaryData
open SKGap.Noncrossing.Primary SKGap.Noncrossing.Diagram MarkedPolynomial
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

theorem markedRecipe_plain (D : OrdinaryData n ι κ σ) (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) :
    pairPlain (D.markedRecipe T x a)=(D.retainedTree T x a).words D.j := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    rw [markedRecipe,retainedTree]
    have H:=fold_plain D.j (Finset.univ.toList.map (Sum.inl : ι→ι⊕Fin a)++Finset.univ.toList.map Sum.inr)
      (Sum.elim (fun l=>D.sourcePartial a l x) (fun b=>D.auxCoefficient a b x))
      (Sum.elim T (fun b=>D.retainedTree T x b))
      (fun e V=>match e with
        | .inl l=>smallBranch D.j (D.sourcePartial a l x) (T l) V
        | .inr b=>boundedBranch D.j (D.auxCoefficient a b x) (D.markedRecipe T x b) V)
      (by
        intro e V S hV
        cases e with
        | inl l=>exact smallBranch_plain D.j _ _ _ _ hV
        | inr b=>exact boundedBranch_plain D.j _ _ _ _ _ (ih b b.isLt) hV)
    simp only [List.map_append,List.map_map,Function.comp_def,Sum.elim_inl,Sum.elim_inr] at H
    try simp only [List.map_append,List.map_map,Function.comp_def,Sum.elim_inl,Sum.elim_inr]
    exact H

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_PrimitiveTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap.SourceError
variable {n : ℕ}
local instance instFactLeENNRealOfNat_solutions : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩

lemma testSize_nonneg (P : Interaction n) : 0≤testSize P := add_nonneg (norm_nonneg _) (norm_nonneg _)
lemma opNorm_le_testSize (P : Interaction n) : SKGap.opNorm P≤testSize P := le_add_of_nonneg_right (norm_nonneg _)

lemma TraceControl.mono {E : Interaction n} {C D : ℝ} (h : TraceControl E C) (hCD : C≤D) : TraceControl E D :=
  ⟨h.nonneg.trans hCD,fun P=>(h.bound P).trans (mul_le_mul_of_nonneg_right hCD (testSize_nonneg P))⟩
lemma TraceControl.add {E F : Interaction n} {C D : ℝ} (hE : TraceControl E C) (hF : TraceControl F D) :
    TraceControl (E+F) (C+D) := by
  refine ⟨add_nonneg hE.nonneg hF.nonneg,?_⟩
  intro P; rw [mul_add,trace_add,add_mul]
  exact (abs_add_le _ _).trans (add_le_add (hE.bound P) (hF.bound P))
lemma TraceControl.smul {E : Interaction n} {C : ℝ} (hE : TraceControl E C) (a : ℝ) :
    TraceControl (a • E) (|a| *C) := by
  refine ⟨mul_nonneg (abs_nonneg _) hE.nonneg,?_⟩
  intro P; rw [Matrix.mul_smul,trace_smul,smul_eq_mul,abs_mul]
  exact (mul_le_mul_of_nonneg_left (hE.bound P) (abs_nonneg a)).trans_eq (by ring)
lemma TraceControl.neg {E : Interaction n} {C : ℝ} (hE : TraceControl E C) : TraceControl (-E) C := by
  simpa using hE.smul (-1)
lemma TraceControl.sub {E F : Interaction n} {C D : ℝ} (hE : TraceControl E C) (hF : TraceControl F D) :
    TraceControl (E-F) (C+D) := by simpa only [sub_eq_add_neg] using hE.add hF.neg
lemma TraceControl.sum {α : Type*} [Fintype α] {E : α→Interaction n} {C : α→ℝ}
    (h : ∀a,TraceControl (E a) (C a)) : TraceControl (∑a,E a) (∑a,C a) := by
  refine ⟨Finset.sum_nonneg (fun a _=>(h a).nonneg),?_⟩
  intro P; rw [Matrix.mul_sum,trace_sum,Finset.sum_mul]
  exact (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun a _=>(h a).bound P)

lemma control_of_operator {E : Interaction n} {C : ℝ} (hC : 0≤C)
    (h : ∀P,|trace (P*E)|≤C*SKGap.opNorm P) : TraceControl E C :=
  ⟨hC,fun P=>(h P).trans (mul_le_mul_of_nonneg_left (opNorm_le_testSize P) hC)⟩

lemma small_diagonal_control (E : Interaction n) (u : Fin n→ℝ) :
    TraceControl (Matrix.diagonal u*E) (vectorNorm u*‖E‖) := by
  apply control_of_operator (mul_nonneg (vectorNorm_nonneg _) (norm_nonneg _))
  intro P; exact (trace_small_diagonal P E u).trans_eq (by ring)
lemma small_mean_control (E : Interaction n) (U : VectorFields n) (x : Spin n) (hn : 0<n) :
    TraceControl (siteMean U x • E) (vectorNorm (U x)*‖E‖) := by
  apply control_of_operator (mul_nonneg (vectorNorm_nonneg _) (norm_nonneg _))
  intro P; exact (trace_small_mean P E U x hn).trans_eq (by ring)
lemma averageError_control (a : Spin n→ℝ) (U : VectorFields n) (x : Spin n) :
    TraceControl (averageError a U x) ((vectorNorm (U x)+2*‖derivativeMatrix U x‖)*‖derivativeVector a x‖) := by
  apply control_of_operator (by positivity [vectorNorm_nonneg (U x)])
  intro P; exact (averageError_trace P a U x).trans_eq (by ring)
lemma primary_averageError_control (U m : VectorFields n) (x : Spin n) (hn : 0<n)
    {C R : ℝ} (hC : 0≤C) (hR : 0≤R) (hU : ‖derivativeMatrix U x‖≤C)
    (hm : ∀i,|m x i|≤1) (hdm : SKGap.opNorm (derivativeMatrix m x)≤R) :
    TraceControl (averageError (siteMean U) m x) (C*(1+2*R)) := by
  apply control_of_operator (by positivity)
  intro P; exact (primary_averageError_trace P U m x hn hC hR hU hm hdm).trans_eq (by ring)

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
lemma sourceError_control (H : ι→VectorFields n) (θ : κ→Spin n→ℝ)
    (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
    (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
    (s : VectorFields n) (x : Spin n) {C S T B R L : ℝ}
    (h : SegmentRegular H θ F F' x C) (hS : 0≤S) (hT : 0≤T) (hB : 0≤B) (hR : 0≤R) (hL : 0≤L)
    (hs : vectorNorm (s x)≤S) (hds : ‖derivativeMatrix s x‖≤S)
    (ht : vectorNorm (parameterIncrement θ x)≤T)
    (hQ4 : (∑i,∑k,(primaryIncrement H x i k)^4)≤B^4)
    (hQr : ∀i,(∑k,(primaryIncrement H x i k)^2)≤R^2)
    (hQd : (∑i,(primaryIncrement H x i i)^2)≤L^2) :
    TraceControl (sourceError H θ F F' s x)
      (C*S*((∑α,‖derivativeVector (θ α) x‖)+4*(B^2+R*T+T^2)+2*(B+L+T))) := by
  have hC := h.nonneg
  have hsum : 0≤∑α,‖derivativeVector (θ α) x‖ := Finset.sum_nonneg fun α _=>norm_nonneg _
  refine ⟨by positivity,?_⟩
  intro P
  have hO : 0≤SKGap.offDiagonalSeminorm P := norm_nonneg _
  have hP : (∑i,∑k,if i=k then 0 else (P k i)^4)≤SKGap.offDiagonalSeminorm P^4 := by
    rw [SKGap.offDiagonalSeminorm_fourth,Fintype.sum_prod_type,Finset.sum_comm]
    simp only [eq_comm]; rfl
  apply (sourceError_trace H θ F F' s x P h hS hT hB hR hL hO hs hds ht hQ4 hQr hQd hP).trans
  have h₁ : 0≤C*S*((∑α,‖derivativeVector (θ α) x‖)+4*(B^2+R*T+T^2)+2*(L+T)) := by positivity
  have h₂ : 0≤2*C*S*B := by positivity
  have H₁ := mul_nonneg (real_op_norm_nonneg P) h₂
  have H₂ := mul_nonneg hO h₁
  unfold testSize
  nlinarith only [H₁,H₂]

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Matrix SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Diagram
variable {n : ℕ}

lemma wordBounded_diag {A : ℝ} {w : OrdinaryWord n} (h : wordBounded A w)
    (p : Fin n→ℝ) (hp : ∀i,|p i|≤A) : wordBounded A (w++[.diag p]) := by
  intro l hl; rcases List.mem_append.mp hl with hl|hl
  · exact h l hl
  · have he : l=Letter.diag p := List.mem_singleton.mp hl; subst l; exact hp
lemma wordBounded_noise {A : ℝ} {w : OrdinaryWord n} (h : wordBounded A w) :
    wordBounded A (w++[.noise]) := by
  intro l hl; rcases List.mem_append.mp hl with hl|hl
  · exact h l hl
  · have he : l=Letter.noise := List.mem_singleton.mp hl; subst l; trivial

theorem finite_graph_trace (J : Interaction n) (E F Es Ef : ℕ→Interaction n)
    (p : (a : ℕ)→Fin a→Fin n→ℝ) (r : (a : ℕ)→Fin a→ℝ)
    (hE : ∀a,E a=(∑b:Fin a,Matrix.diagonal (p a b)*F b)+Es a)
    (hF : ∀a,F a=J*E a-(∑b:Fin a,r a b • E b)+Ef a)
    {A R M : ℝ} {Cs Cf : ℕ→ℝ} {N L : ℕ}
    (hR : 0≤R) (hM : 0≤M)
    (hp : ∀a≤N,∀b i,|p a b i|≤A) (hr : ∀a≤N,∀b,|r a b|≤R)
    (hs : ∀a≤N,TraceControl (Es a) (Cs a)) (hf : ∀a≤N,TraceControl (Ef a) (Cf a))
    (hw : WordTestBound J A M L) :
    ∀a≤N,
      (∀w:OrdinaryWord n,w.length+2*a+1≤L→wordBounded A w→
        |trace (matrixWord J w*E a)|≤(errorBudget R Cs Cf a).1*M) ∧
      (∀w:OrdinaryWord n,w.length+2*a+2≤L→wordBounded A w→
        |trace (matrixWord J w*F a)|≤(errorBudget R Cs Cf a).2*M) := by
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro ha
    have hs₀ : 0≤Cs a := (hs a ha).nonneg
    have hf₀ : 0≤Cf a := (hf a ha).nonneg
    have hprev (b : Fin a) := ih b b.isLt (b.isLt.le.trans ha)
    have hCs (w : OrdinaryWord n) (hlen : w.length≤L) (hwb : wordBounded A w) :
        |trace (matrixWord J w*Es a)|≤Cs a*M := by
      apply (hs a ha).bound _ |>.trans
      simpa only [mul_comm] using mul_le_mul (hw w hlen hwb) (le_refl (Cs a)) hs₀ hM
    have hCf (w : OrdinaryWord n) (hlen : w.length≤L) (hwb : wordBounded A w) :
        |trace (matrixWord J w*Ef a)|≤Cf a*M :=
      (hf a ha).bound _ |>.trans (mul_le_mul_of_nonneg_left (hw w hlen hwb) hf₀)
    have hsource : ∀w:OrdinaryWord n,w.length+2*a+1≤L→wordBounded A w→
        |trace (matrixWord J w*E a)|≤(errorBudget R Cs Cf a).1*M := by
      intro w hlen hwb
      have hterms (b : Fin a) : |trace (matrixWord J w*(Matrix.diagonal (p a b)*F b))|≤
          (errorBudget R Cs Cf b).2*M := by
        have H:=(hprev b).2 (w++[.diag (p a b)]) (by simp only [List.length_append,List.length_singleton]; omega)
          (wordBounded_diag hwb _ (hp a ha b))
        simpa only [matrixWord_append,matrixWord,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
          matrixLetter,List.map_append,List.prod_append,mul_one,mul_assoc] using H
      rw [hE a,mul_add,trace_add,errorBudget]
      dsimp only
      have H:=(Finset.abs_sum_le_sum_abs (s:=Finset.univ) (f:=fun b:Fin a=>trace (matrixWord J w*(Matrix.diagonal (p a b)*F b)))).trans
        (Finset.sum_le_sum fun b _=>hterms b)
      rw [←trace_sum,←Matrix.mul_sum,←Finset.sum_mul] at H
      exact ((abs_add_le _ _).trans (add_le_add H (hCs w (by omega) hwb))).trans_eq (by ring)
    refine ⟨hsource,?_⟩
    intro w hlen hwb
    have hsnew:=hsource (w++[.noise]) (by simp only [List.length_append,List.length_singleton]; omega)
      (wordBounded_noise hwb)
    have Hs : |trace (matrixWord J w*(J*E a))|≤(errorBudget R Cs Cf a).1*M := by
      simpa only [matrixWord_append,matrixWord,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
        matrixLetter,List.map_append,List.prod_append,mul_one,mul_assoc] using hsnew
    have hterms (b : Fin a) : |trace (matrixWord J w*(r a b • E b))|≤
        R*(errorBudget R Cs Cf b).1*M := by
      have H:=(hprev b).1 w (by omega) hwb
      rw [Matrix.mul_smul,trace_smul,smul_eq_mul,abs_mul]
      exact ((mul_le_mul_of_nonneg_right (hr a ha b) (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_left H hR)).trans_eq (by ring)
    have H:=(Finset.abs_sum_le_sum_abs (s:=Finset.univ) (f:=fun b:Fin a=>trace (matrixWord J w*(r a b • E b)))).trans
      (Finset.sum_le_sum fun b _=>hterms b)
    rw [←trace_sum,←Matrix.mul_sum] at H
    rw [hF a,mul_add,mul_sub,trace_add,trace_sub]
    apply ((abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add Hs H))
      (hCf w (by omega) hwb))).trans_eq
    rw [errorBudget]
    dsimp only
    rw [←Finset.sum_mul,←Finset.mul_sum]
    ring

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_RecipeNodeTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe.OrdinaryData
open Primary Matrix SKGap.Noncrossing.Primary
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]
variable (D : OrdinaryData n ι κ σ)

lemma source_error_nodes (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) :
    D.sourceDerivativeError T x a=
      (∑b:Fin a,Matrix.diagonal (D.auxCoefficient a b x)*D.fieldDerivativeError T x b)+
      D.nodeSourceError T x a := by
  rw [D.source_error_recursion,nodeSourceError]; abel
lemma field_error_nodes (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) :
    D.fieldDerivativeError T x a=D.J*D.sourceDerivativeError T x a-
      (∑b:Fin a,(D.j*siteMean (D.auxCoefficient a b) x) • D.sourceDerivativeError T x b)+
      D.nodeFieldError T x a := by
  rw [D.field_error_recursion,nodeFieldError]; abel

lemma nodeSource_control (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ)
    {C Q R L V Z : ℝ} {B : Fin a→ℝ} {Cp E : ι→ℝ}
    (hC : 0≤C) (hQ : 0≤Q) (hR : 0≤R) (hL : 0≤L) (hV : 0≤V)
    (hY : ∀b:Fin a,SmallBound (D.auxiliary b) x (B b))
    (hp : ∀l,SmallBound (D.sourcePartial a l) x (Cp l))
    (hE : ∀l,‖derivativeMatrix (D.H l) x-SourceTree.fieldMatrix D.j D.J (T l)‖≤E l)
    (hs : ∀s,SegmentRegular D.H D.θ (D.seedFunction a s) (D.seedDerivative a s) x C)
    (ha : ∀b,SegmentRegular D.H D.θ (D.auxFunction a b) (D.auxDerivative a b) x C)
    (ht : vectorNorm (parameterIncrement D.θ x)≤V)
    (hQ4 : (∑i,∑k,(primaryIncrement D.H x i k)^4)≤Q^4)
    (hQr : ∀i,(∑k,(primaryIncrement D.H x i k)^2)≤R^2)
    (hQd : (∑i,(primaryIncrement D.H x i i)^2)≤L^2)
    (hZ : (∑α,‖derivativeVector (D.θ α) x‖)+4*(Q^2+R*V+V^2)+2*(Q+L+V)≤Z) :
    TraceControl (D.nodeSourceError T x a)
      (((∑s,C*vectorNorm (D.seed s)*Z)+(∑b:Fin a,C*B b*Z))+∑l,Cp l*E l) := by
  have hc (s : VectorFields n) {S : ℝ} (hS : SmallBound s x S)
      (F : Fin n→Args (ι:=ι) (κ:=κ)→ℝ)
      (F' : Fin n→Args (ι:=ι) (κ:=κ)→Args (ι:=ι) (κ:=κ)→L[ℝ]ℝ)
      (hF : SegmentRegular D.H D.θ F F' x C) : TraceControl (sourceError D.H D.θ F F' s x) (C*S*Z) :=
    (sourceError_control D.H D.θ F F' s x hF hS.nonneg hV hQ hR hL hS.size hS.derivative ht hQ4 hQr hQd).mono
      (mul_le_mul_of_nonneg_left hZ (mul_nonneg hC hS.nonneg))
  have hs' := TraceControl.sum (fun s=>hc (fun _=>D.seed s) (SmallBound.seed _ x) _ _ (hs s))
  have ha' := TraceControl.sum (fun b:Fin a=>hc (D.auxiliary b) (hY b) _ _ (ha b))
  have hp' := TraceControl.sum (fun l=>(small_diagonal_control
    (derivativeMatrix (D.H l) x-SourceTree.fieldMatrix D.j D.J (T l)) (D.sourcePartial a l x)).mono
      (mul_le_mul (hp l).size (hE l) (norm_nonneg _) (hp l).nonneg))
  exact (hs'.add ha').add hp'

lemma nodeField_control (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (a : ℕ) (hn : 0<n)
    {P R : ℝ} {B : Fin a→ℝ} {Cp E : ι→ℝ} (hP : 0≤P) (hR : 0≤R)
    (hW : ∀b:Fin a,SmallBound (D.source b) x (B b))
    (hp : ∀l,SmallBound (D.sourcePartial a l) x (Cp l))
    (hE : ∀l,‖derivativeMatrix (D.predecessor l) x-SourceTree.sourceMatrix D.j D.J (T l)‖≤E l)
    (hm : ∀l i,|D.predecessor l x i|≤1)
    (hdm : ∀l,SKGap.opNorm (derivativeMatrix (D.predecessor l) x)≤P)
    (hda : ∀b i,∑k,(derivativeMatrix (D.auxCoefficient a b) x i k)^2≤R^2) :
    TraceControl (D.nodeFieldError T x a)
      ((∑l,|D.j| *(Cp l*E l))+|D.j| *((∑l,Cp l*(1+2*P))+(∑b:Fin a,3*B b*R))) := by
  have hmE (l : ι) : TraceControl
      ((D.j*siteMean (D.sourcePartial a l) x) •
        (derivativeMatrix (D.predecessor l) x-SourceTree.sourceMatrix D.j D.J (T l)))
      (|D.j| *(Cp l*E l)) := by
    simpa only [smul_smul] using ((small_mean_control
      (derivativeMatrix (D.predecessor l) x-SourceTree.sourceMatrix D.j D.J (T l))
      (D.sourcePartial a l) x hn).mono
        (mul_le_mul (hp l).size (hE l) (norm_nonneg _) (hp l).nonneg)).smul D.j
  have hpE (l : ι) := primary_averageError_control (D.sourcePartial a l) (D.predecessor l) x hn
    (hp l).nonneg hP (hp l).derivative (hm l) (hdm l)
  have haE (b : Fin a) : TraceControl (averageError (siteMean (D.auxCoefficient a b)) (D.source b) x) (3*B b*R) := by
    apply (averageError_control (siteMean (D.auxCoefficient a b)) (D.source b) x).mono
    have H:=coefficient_mean_difference (D.auxCoefficient a b) x hR (hda b)
    have h1 := add_le_add (hW b).size (mul_le_mul_of_nonneg_left (hW b).derivative (by norm_num : (0:ℝ)≤2))
    exact (mul_le_mul h1 H (norm_nonneg _) (by linarith [(hW b).nonneg])).trans_eq (by ring)
  exact (TraceControl.sum hmE).neg.sub (((TraceControl.sum hpE).add (TraceControl.sum haE)).smul D.j)

theorem derivative_error_words (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n)
    {N L : ℕ} {A R M : ℝ} {Cs Cf : ℕ→ℝ} (hR : 0≤R) (hM : 0≤M)
    (hp : ∀a≤N,∀b i,|D.auxCoefficient a b x i|≤A)
    (hr : ∀a≤N,∀b,|D.j*siteMean (D.auxCoefficient a b) x|≤R)
    (hs : ∀a≤N,TraceControl (D.nodeSourceError T x a) (Cs a))
    (hf : ∀a≤N,TraceControl (D.nodeFieldError T x a) (Cf a))
    (hw : WordTestBound D.J A M L) :
    ∀a≤N,
      (∀w:OrdinaryWord n,w.length+2*a+1≤L→wordBounded A w→
        |trace (SKGap.Noncrossing.Primary.matrixWord D.J w*D.sourceDerivativeError T x a)|≤(errorBudget R Cs Cf a).1*M) ∧
      (∀w:OrdinaryWord n,w.length+2*a+2≤L→wordBounded A w→
        |trace (SKGap.Noncrossing.Primary.matrixWord D.J w*D.fieldDerivativeError T x a)|≤(errorBudget R Cs Cf a).2*M) :=
  finite_graph_trace D.J (D.sourceDerivativeError T x) (D.fieldDerivativeError T x)
    (D.nodeSourceError T x) (D.nodeFieldError T x) (fun a b=>D.auxCoefficient a b x)
    (fun a b=>D.j*siteMean (D.auxCoefficient a b) x)
    (D.source_error_nodes T x) (D.field_error_nodes T x) hR hM hp hr hs hf hw

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_RecipeTraceBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.MarkedPolynomial
open Diagram
variable {n : ℕ}

lemma budget_nonneg (P : MarkedPolynomial n) : 0≤P.budget := by
  unfold budget
  exact List.sum_nonneg (by intro r hr; obtain ⟨t,_,rfl⟩:=List.mem_map.mp hr; exact mul_nonneg (abs_nonneg _) (SKGapCutoff.Recipe.vectorNorm_nonneg _))

lemma smallBranch_budget (j : ℝ) (p : Fin n→ℝ) (T : SourceTree (Fin n→ℝ)) (V : Pair n) :
    pairBudget (smallBranch j p T V)=
      SKGapCutoff.Recipe.vectorNorm p*(2*mass (T.words j).2+|j| *mass (T.words j).1)+pairBudget V := by
  simp only [pairBudget,smallBranch,budget_append,budget_prefix,budget_diagonalWords,budget_averageWords,abs_neg]
  ring
lemma boundedBranch_budget (j : ℝ) (p : Fin n→ℝ) (U V : Pair n) {A : ℝ}
    (hp : |Diagram.mean p|≤A) :
    pairBudget (boundedBranch j p U V) ≤ (2+|j| *A)*pairBudget U+pairBudget V := by
  simp only [pairBudget,boundedBranch,budget_append,budget_prefix,budget_scale,abs_neg,abs_mul]
  have h:=mul_le_mul_of_nonneg_left hp (mul_nonneg (abs_nonneg j) (budget_nonneg U.1))
  nlinarith [budget_nonneg U.1,budget_nonneg U.2,
    mul_nonneg (mul_nonneg (abs_nonneg j) (le_trans (abs_nonneg _) hp)) (budget_nonneg U.2)]

lemma fold_budget {α : Type*} (xs : List α) (step : α→Pair n→Pair n) (cost : α→ℝ)
    (hstep : ∀a V,pairBudget (step a V) ≤ cost a+pairBudget V) :
    pairBudget (xs.foldr step zeroPair)≤(xs.map cost).sum := by
  induction xs with
  | nil => simp [zeroPair,pairBudget,budget,SmallMark.vector]
  | cons a xs ih =>
    exact (hstep a _).trans (by simpa only [List.map_cons,List.sum_cons] using add_le_add (le_refl (cost a)) ih)

end SKGap.Noncrossing.Primary.MarkedPolynomial
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap.Noncrossing.Primary MarkedPolynomial
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

namespace OrdinaryData
variable (D : OrdinaryData n ι κ σ)
theorem markedRecipe_budget (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (N : ℕ)
    (W : ℕ→ℝ) {A M : ℝ} (hA : 0≤A) (hM : 0≤M)
    (hp : ∀a≤N,∀l,vectorNorm (D.sourcePartial a l x)≤W a)
    (hm : ∀l,mass ((T l).words D.j).1≤M ∧ mass ((T l).words D.j).2≤M)
    (ha : ∀a≤N,∀b:Fin a,|siteMean (D.auxCoefficient a b) x|≤A) :
    ∀a≤N,pairBudget (D.markedRecipe T x a)≤
      traceBudget ((Fintype.card ι:ℝ)*((2+|D.j|)*M)) (2+|D.j| *A) W a := by
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro haN
    rw [markedRecipe]
    let L : ℝ := (2+|D.j|)*M
    let K : ℝ := 2+|D.j| *A
    have hL : 0≤L := by dsimp [L]; positivity
    have hK : 0≤K := by dsimp [K]; positivity
    have H:=fold_budget (Finset.univ.toList.map (Sum.inl : ι→ι⊕Fin a)++Finset.univ.toList.map Sum.inr)
      (fun e V=>match e with
        | .inl l=>smallBranch D.j (D.sourcePartial a l x) (T l) V
        | .inr b=>boundedBranch D.j (D.auxCoefficient a b x) (D.markedRecipe T x b) V)
      (Sum.elim (fun _ : ι=>L*W a) (fun b:Fin a=>K*pairBudget (D.markedRecipe T x b)))
      (by
        intro e V
        cases e with
        | inl l=>
          rw [smallBranch_budget]
          apply add_le_add _ le_rfl
          have hc : 2*mass ((T l).words D.j).2+|D.j| *mass ((T l).words D.j).1≤L := by
            dsimp [L]
            nlinarith [(hm l).2,mul_le_mul_of_nonneg_left (hm l).1 (abs_nonneg D.j)]
          exact (mul_le_mul_of_nonneg_left hc (vectorNorm_nonneg _)).trans
            (by simpa [mul_comm] using mul_le_mul_of_nonneg_right (hp a haN l) hL)
        | inr b=>
          exact boundedBranch_budget D.j _ _ _ (by simpa only [siteMean,SKGap.Noncrossing.Diagram.mean,Fintype.card_fin] using ha a haN b))
    have hs : (∑b:Fin a,pairBudget (D.markedRecipe T x b))≤
        ∑b:Fin a,traceBudget ((Fintype.card ι:ℝ)*((2+|D.j|)*M)) K W b := by
      apply Finset.sum_le_sum; intro b _; exact ih b b.isLt (b.isLt.le.trans haN)
    apply H.trans
    simp only [List.map_append,List.sum_append,List.map_map,Function.comp_def,Sum.elim_inl,Sum.elim_inr]
    rw [traceBudget]
    have he : (List.map (fun b:Fin a=>K*pairBudget (D.markedRecipe T x b)) Finset.univ.toList).sum=
        K*∑b:Fin a,pairBudget (D.markedRecipe T x b) := by simp [Finset.mul_sum]
    have he0 : (List.map (fun _ : ι=>L*W a) Finset.univ.toList).sum=(Fintype.card ι:ℝ)*(L*W a) := by simp
    rw [he,he0]
    convert! add_le_add (le_refl ((Fintype.card ι:ℝ)*L*W a)) (mul_le_mul_of_nonneg_left hs hK) using 1
    all_goals try with_reducible_and_instances rfl
    try dsimp [L,K]
    ring

end OrdinaryData
end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma diagonal_abs_sum_of_tests (M : Matrix ι ι ℝ) {C : ℝ}
    (h : ∀d:ι→ℝ,(∀i,|d i|≤1)→|trace (Matrix.diagonal d*M)|≤C) :
    (∑i,|M i i|)≤C := by
  let d : ι→ℝ := fun i=>if 0≤M i i then 1 else -1
  have hd : ∀i,|d i|≤1 := by intro i; dsimp [d]; split_ifs <;> norm_num
  have ht : trace (Matrix.diagonal d*M)=∑i,|M i i| := by
    simp only [trace,diag,Matrix.diagonal_mul]
    apply Finset.sum_congr rfl; intro i _
    dsimp [d]; split_ifs with hi
    · simp [abs_of_nonneg hi]
    · simp [abs_of_neg (lt_of_not_ge hi)]
  have H:=h d hd
  rw [ht,abs_of_nonneg (Finset.sum_nonneg fun i _=>abs_nonneg _)] at H
  exact H

end SKGap.Noncrossing
namespace SKGapCutoff.Recipe.OrdinaryData
open SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Diagram Matrix MarkedPolynomial
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

theorem retainedSource_diagonal (D : OrdinaryData n ι κ σ) (T : ι→SourceTree (Fin n→ℝ))
    (x : Spin n) (a : ℕ) (hn : 0<n) {B : ℝ} (hB : 0≤B)
    (hb : ∀d:Fin n→ℝ,(∀i,|d i|≤1)→∀t∈(D.markedRecipe T x a).1,
      SKGap.diagonalSeminorm (matrixWord D.J (t.2.diagnostic d)-
        Matrix.diagonal (Diagram.prediction D.j (t.2.diagnostic d)))≤B) :
    (∑i,|D.retainedSource T x a i i|)≤(D.markedRecipe T x a).1.budget*B := by
  apply diagonal_abs_sum_of_tests
  intro d hd
  have H:=MarkedPolynomial.trace_error D.j D.J hn d hd (D.markedRecipe T x a).1 hB (hb d hd)
  have he : (D.markedRecipe T x a).1.plain=((D.retainedTree T x a).words D.j).1 :=
    congrArg Prod.fst (D.markedRecipe_plain T x a)
  rw [he] at H
  have hz : ∀i,polynomialPrediction D.j ((D.retainedTree T x a).words D.j).1 i=0 :=
    fun i=>(D.retained_prediction_zero T x a i).1
  simpa only [hz,mul_zero,Finset.sum_const_zero,sub_zero,retainedSource,SourceTree.sourceMatrix] using H

theorem retainedField_diagonal (D : OrdinaryData n ι κ σ) (T : ι→SourceTree (Fin n→ℝ))
    (x : Spin n) (a : ℕ) (hn : 0<n) {B : ℝ} (hB : 0≤B)
    (hb : ∀d:Fin n→ℝ,(∀i,|d i|≤1)→∀t∈(D.markedRecipe T x a).2,
      SKGap.diagonalSeminorm (matrixWord D.J (t.2.diagnostic d)-
        Matrix.diagonal (Diagram.prediction D.j (t.2.diagnostic d)))≤B) :
    (∑i,|D.retainedField T x a i i|)≤(D.markedRecipe T x a).2.budget*B := by
  apply diagonal_abs_sum_of_tests
  intro d hd
  have H:=MarkedPolynomial.trace_error D.j D.J hn d hd (D.markedRecipe T x a).2 hB (hb d hd)
  have he : (D.markedRecipe T x a).2.plain=((D.retainedTree T x a).words D.j).2 :=
    congrArg Prod.snd (D.markedRecipe_plain T x a)
  rw [he] at H
  have hz : ∀i,polynomialPrediction D.j ((D.retainedTree T x a).words D.j).2 i=0 :=
    fun i=>(D.retained_prediction_zero T x a i).2
  simpa only [hz,mul_zero,Finset.sum_const_zero,sub_zero,retainedField,SourceTree.fieldMatrix] using H

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_OrdinaryClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap.Noncrossing SKGap.Noncrossing.Primary MarkedPolynomial

namespace LocalConstants
variable (c : LocalConstants)
lemma A_nonneg : 0 ≤ c.A := le_trans (by norm_num) c.one_le_A
lemma argument_nonneg (d : ℕ) : 0 ≤ c.argument d := by unfold argument; positivity [c.P_nonneg,c.V_nonneg]
lemma row_nonneg (d : ℕ) : 0 ≤ c.row d := mul_nonneg c.C_nonneg (c.argument_nonneg d)
lemma traceCost_nonneg (d : ℕ) : 0 ≤ c.traceCost d := by unfold traceCost; positivity [c.P_nonneg,c.V_nonneg]
end LocalConstants

variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

namespace LocalOrdinaryInput
variable {D : OrdinaryData n ι κ σ} {T : ι→SourceTree (Fin n→ℝ)}
variable {x : Spin n} {N : ℕ} {c : LocalConstants}
variable (h : LocalOrdinaryInput D T x N c)
include h

lemma argument_bound : (∑l,SKGap.opNorm (derivativeMatrix (D.H l) x))+
    (∑α,‖derivativeVector (D.θ α) x‖) ≤ c.argument (Fintype.card ι) := by
  apply add_le_add _ h.parameter
  exact (Finset.sum_le_sum fun l _=>(h.primaryShape l).1).trans_eq (by simp)
lemma seed_bound (a : ℕ) (ha : a≤N) (s : σ) :
    CoefficientBound (D.seedCoefficient a s) x c.A (c.row (Fintype.card ι)) :=
  (h.seedRegular a ha s).coefficient_bound c.A_nonneg (c.argument_nonneg _) (h.seedValue a ha s) h.argument_bound
lemma aux_bound (a : ℕ) (ha : a≤N) (b : Fin a) :
    CoefficientBound (D.auxCoefficient a b) x c.A (c.row (Fintype.card ι)) :=
  (h.auxRegular a ha b).coefficient_bound c.A_nonneg (c.argument_nonneg _) (h.auxValue a ha b) h.argument_bound
lemma seed_partial_bound (a : ℕ) (ha : a≤N) (l : ι) (s : σ) :
    CoefficientBound (D.seedPartial a l s) x c.A (c.row (Fintype.card ι)) :=
  (h.seedRegular a ha s).partial_bound_coefficient (.inl l) c.A_nonneg (c.argument_nonneg _) c.C_le_A h.argument_bound
lemma aux_partial_bound (a : ℕ) (ha : a≤N) (l : ι) (b : Fin a) :
    CoefficientBound (D.auxPartial a l b) x c.A (c.row (Fintype.card ι)) :=
  (h.auxRegular a ha b).partial_bound_coefficient (.inl l) c.A_nonneg (c.argument_nonneg _) c.C_le_A h.argument_bound

lemma small (a : ℕ) (ha : a≤N) :
    SmallBound (D.source a) x (c.normBudget D.j (Fintype.card ι) a) ∧
    SmallBound (D.auxiliary a) x (c.normBudget D.j (Fintype.card ι) a) ∧
    ∀l,SmallBound (D.sourcePartial a l) x (c.normBudget D.j (Fintype.card ι) a) :=
  D.evaluation_small N x h.dimension c.A_nonneg (c.row_nonneg _) c.L_nonneg c.P_nonneg c.S_nonneg
    h.interaction h.seed h.primaryValue h.primaryDerivative h.seed_bound h.aux_bound h.seed_partial_bound h.aux_partial_bound a ha

lemma source_control (a : ℕ) (ha : a≤N) :
    TraceControl (D.nodeSourceError T x a) (c.sourceCost D.j (Fintype.card ι) (Fintype.card σ) a) := by
  let d:=Fintype.card ι
  let W:=c.normBudget D.j d
  have hn (s : σ) : vectorNorm (D.seed s) ≤ c.S :=
    (Finset.single_le_sum (fun s _=>vectorNorm_nonneg (D.seed s)) (Finset.mem_univ s)).trans h.seed
  have H:=D.nodeSource_control T x a c.C_nonneg
    (show 0≤2*(d:ℝ)*c.P by positivity [c.P_nonneg])
    (show 0≤(d:ℝ)*c.P by positivity [c.P_nonneg])
    (show 0≤(d:ℝ)*c.P by positivity [c.P_nonneg]) c.V_nonneg
    (fun b:Fin a=>(h.small b (b.isLt.le.trans ha)).2.1) (h.small a ha).2.2 h.primaryFieldError
    (h.seedRegular a ha) (h.auxRegular a ha)
    ((parameterIncrement_bound D.θ x).trans h.parameter)
    (primaryIncrement_fourth D.H x c.P_nonneg h.primaryShape)
    (primaryIncrement_row D.H x c.P_nonneg (fun l=>(h.primaryShape l).1))
    (primaryIncrement_diagonal D.H x c.P_nonneg (fun l=>(h.primaryShape l).2.1))
    (show _ ≤ c.traceCost d from add_le_add (add_le_add h.parameter le_rfl) le_rfl)
  apply H.mono
  have hs : (∑s,c.C*vectorNorm (D.seed s)*c.traceCost d)≤(Fintype.card σ:ℝ)*(c.C*c.S*c.traceCost d) :=
    (Finset.sum_le_sum fun s _=>mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hn s) c.C_nonneg) (c.traceCost_nonneg d)).trans_eq (by simp)
  dsimp only [LocalConstants.sourceCost]
  have hp : (∑_l:ι,c.normBudget D.j d a*c.E)=(d:ℝ)*(c.normBudget D.j d a*c.E) := by simp [d]
  rw [hp]
  exact add_le_add (add_le_add hs le_rfl) le_rfl

lemma field_control (a : ℕ) (ha : a≤N) :
    TraceControl (D.nodeFieldError T x a) (c.fieldCost D.j (Fintype.card ι) a) := by
  have H:=D.nodeField_control T x a h.dimension c.P_nonneg (c.row_nonneg _)
    (fun b:Fin a=>(h.small b (b.isLt.le.trans ha)).1) (h.small a ha).2.2 h.primarySourceError
    h.primaryValue h.primaryDerivative (fun b=>(h.aux_bound a ha b).difference)
  simpa only [LocalConstants.fieldCost,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using H

lemma mean_bound (a : ℕ) (ha : a≤N) (b : Fin a) : |siteMean (D.auxCoefficient a b) x| ≤ c.A :=
  coefficient_mean_value (D.auxCoefficient a b) x c.A_nonneg (h.auxValue a ha b)

end LocalOrdinaryInput

namespace OrdinaryData
variable (D : OrdinaryData n ι κ σ)

theorem ordinary_local_closure_oai (T : ι→SourceTree (Fin n→ℝ)) (x : Spin n) (N : ℕ)
    (c : LocalConstants) (h : LocalOrdinaryInput D T x N c)
    {M B Q : ℝ} (hM : 0≤M) (hB : 0≤B) (hQ : 0≤Q)
    (hm : ∀l,mass ((T l).words D.j).1≤Q ∧ mass ((T l).words D.j).2≤Q)
    (hw : WordTestBound D.J c.A M (2*N+3))
    (hd : ∀a≤N,∀d:Fin n→ℝ,(∀i,|d i|≤1)→
      (∀t∈(D.markedRecipe T x a).1,SKGap.diagonalSeminorm (matrixWord D.J (t.2.diagnostic d)-
        Matrix.diagonal (Diagram.prediction D.j (t.2.diagnostic d)))≤B) ∧
      (∀t∈(D.markedRecipe T x a).2,SKGap.diagonalSeminorm (matrixWord D.J (t.2.diagnostic d)-
        Matrix.diagonal (Diagram.prediction D.j (t.2.diagnostic d)))≤B)) :
    let W:=c.normBudget D.j (Fintype.card ι)
    let R:=errorBudget (|D.j| *c.A) (c.sourceCost D.j (Fintype.card ι) (Fintype.card σ))
      (c.fieldCost D.j (Fintype.card ι))
    let V:=traceBudget ((Fintype.card ι:ℝ)*((2+|D.j|)*Q)) (2+|D.j| *c.A) W
    ∀a≤N,SmallBound (D.source a) x (W a) ∧ SmallBound (D.auxiliary a) x (W a) ∧
      (∑i,|derivativeMatrix (D.source a) x i i|)≤V a*B+(R a).1*M ∧
      (∑i,|derivativeMatrix (D.auxiliary a) x i i|)≤V a*B+(R a).2*M := by
  dsimp only
  let W:=c.normBudget D.j (Fintype.card ι)
  let R:=errorBudget (|D.j| *c.A) (c.sourceCost D.j (Fintype.card ι) (Fintype.card σ))
    (c.fieldCost D.j (Fintype.card ι))
  let V:=traceBudget ((Fintype.card ι:ℝ)*((2+|D.j|)*Q)) (2+|D.j| *c.A) W
  have herr:=D.derivative_error_words T x (mul_nonneg (abs_nonneg _) c.A_nonneg) hM h.auxValue
    (fun a ha b=>by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (h.mean_bound a ha b) (abs_nonneg _))
    h.source_control h.field_control hw
  have hmark:=D.markedRecipe_budget T x N W c.A_nonneg hQ (fun a ha l=>(h.small a ha).2.2 l |>.size) hm h.mean_bound
  intro a ha
  have hbounds := h.small a ha
  have hretS : (∑i,|D.retainedSource T x a i i|)≤V a*B := by
    apply (D.retainedSource_diagonal T x a h.dimension hB (fun d hd'=>(hd a ha d hd').1)).trans
    apply mul_le_mul_of_nonneg_right _ hB
    exact (le_add_of_nonneg_right (budget_nonneg _)).trans (hmark a ha)
  have hretF : (∑i,|D.retainedField T x a i i|)≤V a*B := by
    apply (D.retainedField_diagonal T x a h.dimension hB (fun d hd'=>(hd a ha d hd').2)).trans
    apply mul_le_mul_of_nonneg_right _ hB
    exact (le_add_of_nonneg_left (budget_nonneg _)).trans (hmark a ha)
  have herrorS : (∑i,|D.sourceDerivativeError T x a i i|)≤(R a).1*M := by
    apply diagonal_abs_sum_of_tests
    intro d hd'
    have H:=(herr a ha).1 [.diag d] (by simp; omega) (by
      intro l hl; have he : l=Letter.diag d := List.mem_singleton.mp hl; subst l
      exact fun i=>(hd' i).trans c.one_le_A)
    simpa [matrixWord,matrixLetter] using H
  have herrorF : (∑i,|D.fieldDerivativeError T x a i i|)≤(R a).2*M := by
    apply diagonal_abs_sum_of_tests
    intro d hd'
    have H:=(herr a ha).2 [.diag d] (by simp; omega) (by
      intro l hl; have he : l=Letter.diag d := List.mem_singleton.mp hl; subst l
      exact fun i=>(hd' i).trans c.one_le_A)
    simpa [matrixWord,matrixLetter] using H
  refine ⟨hbounds.1,hbounds.2.1,?_,?_⟩
  · calc
      _ = ∑i,|D.retainedSource T x a i i+D.sourceDerivativeError T x a i i| := by
        simp only [sourceDerivativeError,Matrix.sub_apply]; congr 1; funext i; congr 1; ring
      _ ≤ (∑i,|D.retainedSource T x a i i|)+(∑i,|D.sourceDerivativeError T x a i i|) :=
        (Finset.sum_le_sum fun i _=>abs_add_le _ _).trans_eq Finset.sum_add_distrib
      _ ≤ _ := add_le_add hretS herrorS
  · calc
      _ = ∑i,|D.retainedField T x a i i+D.fieldDerivativeError T x a i i| := by
        simp only [fieldDerivativeError,Matrix.sub_apply]; congr 1; funext i; congr 1; ring
      _ ≤ (∑i,|D.retainedField T x a i i|)+(∑i,|D.fieldDerivativeError T x a i i|) :=
        (Finset.sum_le_sum fun i _=>abs_add_le _ _).trans_eq Finset.sum_add_distrib
      _ ≤ _ := add_le_add hretF herrorF

end OrdinaryData
end SKGapCutoff.Recipe

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.SKGapCutoff.Recipe.OrdinaryData.ordinary_local_closure_oai.{u_1, u_2, u_3} := @OAI.SKGapCutoff.Recipe.OrdinaryData.ordinary_local_closure_oai.{u_1, u_2, u_3}
