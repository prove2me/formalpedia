-- Prove2me | solution 1 for OAI.SKGapCutoff.Recipe.OrdinaryData.implicit_started_diagonal_local
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:56:42.652869+00:00
-- url     : https://prove2.me/submissions/7837736c-4caf-4143-921d-a2a98521991c

import Mathlib
import Definitions.Def_OAIQ072A002

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_InverseSubSquareMul
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
namespace SKGap.ResolventIdentity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {𝕜 : Type*} [RCLike 𝕜]

lemma inverse_one_sub_square_mul_unit (D V : Matrix ι ι 𝕜)
    (hS : IsUnit (1-D*V*D)) : IsUnit (1-D*D*V) := by
  have hSS : (1-D*V*D)*(1-D*V*D)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (((1-D*V*D).isUnit_iff_isUnit_det).mp hS)
  apply ((1-D*D*V).isUnit_iff_isUnit_det).mpr
  have hh : (1-D*D*V)*(1+D*(1-D*V*D)⁻¹*D*V) = 1 := by
    calc
      _ = (1-D*D*V)+D*((1-D*V*D)*(1-D*V*D)⁻¹)*D*V := by noncomm_ring
      _ = 1 := by rw [hSS]; noncomm_ring
  exact Matrix.isUnit_det_of_right_inverse hh

end SKGap.ResolventIdentity

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
-- module Solutions.OAIQ072_SK.SKGap_Brownian_PathAgreement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap ComplexOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma pathDiagonal_square {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    pathDiagonal a 1*pathDiagonal a 1=diagonal a := by
  simp only [pathDiagonal,sqrt_one,one_mul,diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_self_sqrt (ha i)

end SKGap
end
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

end Fock
end SKGap.Noncrossing.Primary
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
lemma annihilation_diagonal_creation (a : ι→ℝ) (v : Space (ι:=ι)) :
    annihilation (diagonal a (creation v))=Diagram.mean a • v := by
  ext i I
  simp [annihilation,diagonal,creation,Diagram.mean,←Finset.sum_mul,mul_div_right_comm]
omit [Fintype ι] in
lemma project_diagonal_creation (a : ι→ℝ) (v : Space (ι:=ι)) :
    project (diagonal a (creation v))=0 := by ext i; simp [project,diagonal,creation]
omit [Fintype ι] in
lemma project_creation (v : Space (ι:=ι)) : project (creation v)=0 := rfl
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
lemma act_shift (A : Space (ι:=ι)→ₗ[ℝ] Space (ι:=ι)) (v : Seq (ι:=ι)) :
    act A (shift v)=shift (act A v) := by ext n; cases n <;> simp

variable [Fintype ι]

lemma inverse_equation (j : ℝ) (a : ι→ℝ) (v : Seq (ι:=ι)) :
    inverse j a v=v+shift (act ((diagonal a).comp (noise j)) (inverse j a v))-
      (j*Diagram.mean a) • shift (shift (act (diagonal a) (inverse j a v))) := by
  funext n
  rcases n with _|n
  · simp [inverse,inverseSeq]
  rcases n with _|n
  · simp [inverse,inverseSeq]
  · rfl

lemma inverse_unique (j : ℝ) (a : ι→ℝ) (v u : Seq (ι:=ι))
    (hu : u=v+shift (act ((diagonal a).comp (noise j)) u)-
      (j*Diagram.mean a) • shift (shift (act (diagonal a) u))) :
    u=inverse j a v := by
  funext n
  induction n using Nat.twoStepInduction with
  | zero => have h:=congrFun hu 0; simpa [inverse,inverseSeq] using h
  | one =>
    have h0:=congrFun hu 0
    have h1:=congrFun hu 1
    simp only [Pi.add_apply,Pi.sub_apply,shift_zero,Pi.smul_apply,smul_zero,add_zero,sub_zero] at h0
    simpa [inverse,inverseSeq,h0] using h1
  | more n ih0 ih1 =>
    have h:=congrFun hu (n+2)
    simp only [Pi.add_apply,Pi.sub_apply,shift_succ,act_apply,LinearMap.comp_apply,Pi.smul_apply] at h
    rw [ih0,ih1] at h
    exact h

lemma inverse_shift (j : ℝ) (a : ι→ℝ) (v : Seq (ι:=ι)) :
    inverse j a (shift v)=shift (inverse j a v) := by
  symm
  apply inverse_unique
  have h:=congrArg shift (inverse_equation j a v)
  simpa only [map_add,map_sub,map_smul,act_shift] using h

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

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.Tensor.Series
open Diagram Loop
variable {ι : Type*} [Fintype ι]

lemma noise_vacuum (j : ℝ) : noise j (vacuum (ι:=ι))=creation vacuum := by
  rw [vacuum,←realize_noise]
  have h : Primary.noise j (Primary.vacuum (ι:=ι))=Primary.creation Primary.vacuum := by
    simp [Primary.noise,Primary.vacuum]
  rw [h,realize_creation]

lemma branch_field_creation (j : ℝ) (p : ι→ℝ) (U V : Seq (ι:=ι)×Seq (ι:=ι))
    (hU : U.2=shift (act creation U.1)) (hV : V.2=shift (act creation V.1)) :
    branchField j p U V=shift (act creation (branchSource p U V)) := by
  funext n
  cases n with
  | zero => simp [branchField,branchSource,hV]
  | succ n =>
    cases n with
    | zero => simp [branchField,branchSource,hU,hV]
    | succ n =>
      simp only [branchField,branchSource,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,
        hU,hV,shift_succ,act_apply,noise,LinearMap.add_apply,LinearMap.smul_apply,
        annihilation_diagonal_creation,map_add,smul_smul]
      abel

lemma ordinary_field_creation (j : ℝ) (t : SourceTree (ι→ℝ)) :
    (ordinary j t).2=shift (act creation (ordinary j t).1) := by
  induction t with
  | leaf c =>
    funext n
    cases n with
    | zero => rfl
    | succ n =>
      simp only [ordinary,shift_succ,act_apply,ofVector]
      split_ifs <;> simp [noise_vacuum]
  | branch p t u ih1 ih2 => exact branch_field_creation j p _ _ ih1 ih2

lemma loop_source_equation (j : ℝ) (a p : ι→ℝ) (t : SourceTree (ι→ℝ)) :
    loopSource j a p t=act (diagonal a) (loopField j a p t)+
      act (diagonal p) (ordinary j t).2 := by
  have h := inverse_equation j a
    (act (diagonal p) (ordinary j t).2-
      (j*Diagram.mean p) • shift (shift (act (diagonal a) (ordinary j t).1)))
  change loopSource j a p t =
    act (diagonal p) (ordinary j t).2-
      (j*Diagram.mean p) • shift (shift (act (diagonal a) (ordinary j t).1))+
      shift (act ((diagonal a).comp (noise j)) (loopSource j a p t))-
      (j*Diagram.mean a) • shift (shift (act (diagonal a) (loopSource j a p t))) at h
  refine h.trans ?_
  change _=act (diagonal a) (shift (act (noise j) (loopSource j a p t))-
    (j*Diagram.mean a) • shift (shift (loopSource j a p t))-
    (j*Diagram.mean p) • shift (shift (ordinary j t).1))+
      act (diagonal p) (ordinary j t).2
  simp only [map_sub,map_smul,act_shift]
  have hc : act ((diagonal a).comp (noise j)) (loopSource j a p t)=
      act (diagonal a) (act (noise j) (loopSource j a p t)) := rfl
  rw [hc]
  abel

lemma loop_source_zero (j : ℝ) (a p : ι→ℝ) (t : SourceTree (ι→ℝ)) :
    loopSource j a p t 0=0 := by
  have h:=congrFun (loop_source_equation j a p t) 0
  simpa [loopField,ordinary_field_creation j t] using h

theorem loop_field_creation (j : ℝ) (a p : ι→ℝ) (t : SourceTree (ι→ℝ)) :
    loopField j a p t=shift (act creation (loopSource j a p t)) := by
  have ht := ordinary_field_creation j t
  have hs := loop_source_equation j a p t
  have h (n : ℕ) : loopField j a p t (n+1)=creation (loopSource j a p t n) := by
    induction n with
    | zero => simp [loopField,loop_source_zero]
    | succ n ih =>
      have he := congrFun hs (n+1)
      simp only [Pi.add_apply,act_apply,ih,ht,shift_succ] at he
      change _ = creation (loopSource j a p t (n+1))
      simp only [loopField,Pi.sub_apply,Pi.smul_apply,shift_succ,act_apply]
      rw [noise,LinearMap.add_apply,LinearMap.smul_apply,he]
      simp only [map_add,annihilation_diagonal_creation,smul_add,smul_smul]
      abel
  funext n
  cases n with
  | zero => simp [loopField]
  | succ n => exact h n

theorem ClosedTree.field_creation (j : ℝ) (a : ι→ℝ) (t : ClosedTree (ι→ℝ)) :
    (t.series j a).2=shift (act creation (t.series j a).1) := by
  induction t with
  | leaf c => exact ordinary_field_creation j (.leaf c)
  | implicit p t => exact loop_field_creation j a p t
  | branch p t u ih1 ih2 => exact branch_field_creation j p _ _ ih1 ih2

theorem ClosedTree.project_field (j : ℝ) (a : ι→ℝ) (t : ClosedTree (ι→ℝ)) (n : ℕ) :
    project ((t.series j a).2 n)=0 := by
  rw [t.field_creation]
  cases n with
  | zero => simp
  | succ n => simp [project_creation]

theorem ClosedTree.project_source (j : ℝ) (a : ι→ℝ) (t : ClosedTree (ι→ℝ)) (n : ℕ) :
    project ((t.series j a).1 n)=if n=0 then (fun _ : ι => t.leafMass) else 0 := by
  induction t with
  | leaf c =>
    simp only [series,ordinary,ofVector,leafMass]
    split_ifs <;> simp [vacuum,project_realize,Primary.vacuum]
    ext index
    simp
  | implicit p t =>
    simp only [series,leafMass]
    simp only [Pi.zero_def,ite_self]
    rw [loop_source_equation,Pi.add_apply,act_apply,act_apply,
      loop_field_creation,ordinary_field_creation]
    cases n with
    | zero => simp; rfl
    | succ n => simp [project_diagonal_creation]; rfl
  | branch p t u ih1 ih2 =>
    simp only [series,branchSource,Pi.add_apply,act_apply,leafMass]
    rw [t.field_creation]
    cases n with
    | zero => simpa using ih2
    | succ n => simpa [project_diagonal_creation] using ih2

end SKGap.Noncrossing.Primary.Tensor.Series

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

lemma letter_shift (j : ℝ) (a : ι→ℝ) (l : WordLetter ι) (v : Seq (ι:=ι)) :
    letterOperator j a l (shift v)=shift (letterOperator j a l v) := by
  cases l with
  | diag d => exact act_shift _ _
  | noise => exact act_shift _ _
  | inverse => exact inverse_shift _ _ _
lemma letter_shifts (j : ℝ) (a : ι→ℝ) (l : WordLetter ι) (n : ℕ) (v : Seq (ι:=ι)) :
    letterOperator j a l (shifts n v)=shifts n (letterOperator j a l v) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [shifts,LinearMap.comp_apply,letter_shift] using congrArg shift ih
lemma wordSeq_cons (j : ℝ) (a : ι→ℝ) (l : WordLetter ι) (F : List (WordLetter ι)) :
    wordSeq j a (l::F)=letterOperator j a l (wordSeq j a F) := by cases l <;> rfl

namespace GradedWords

lemma seq_scalar (j c : ℝ) (a : ι→ℝ) : seq j a (scalar c)=ofVector (c • vacuum) := by
  simp only [seq,scalar,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,shifts,
    LinearMap.id_coe,wordSeq,wordOperator]
  funext n
  simp only [Pi.smul_apply,ofVector]
  split_ifs <;> simp_all [ofVector]
lemma seq_append (j : ℝ) (a : ι→ℝ) (P Q : GradedWords ι) :
    seq j a (P++Q)=seq j a P+seq j a Q := by simp [seq]
lemma seq_scale (j c : ℝ) (a : ι→ℝ) (P : GradedWords ι) :
    seq j a (scale c P)=c • seq j a P := by
  induction P with
  | nil => simp [seq,scale]
  | cons t P ih =>
    simp only [scale,List.map_cons,seq,List.sum_cons]
    change (c*t.1) • _+seq j a (scale c P)=c • (t.1 • _+seq j a P)
    rw [ih,smul_add,smul_smul]
lemma seq_bump (j : ℝ) (a : ι→ℝ) (P : GradedWords ι) :
    seq j a (bump P)=shift (seq j a P) := by
  simp [seq,bump,List.map_map,Function.comp_def,shifts,map_list_sum]
lemma seq_prepend (j : ℝ) (a : ι→ℝ) (P : GradedWords ι) (l : WordLetter ι) :
    seq j a (prepend l P)=letterOperator j a l (seq j a P) := by
  simp [seq,prepend,List.map_map,Function.comp_def,wordSeq_cons,map_list_sum,letter_shifts]
lemma predictionPolynomial_eval (j : ℝ) (a : ι→ℝ) (z : ℝ) (P : GradedWords ι) (i : ι) :
    Polynomial.eval z (predictionPolynomial j a P i)=prediction j a z P i := by
  simp only [predictionPolynomial,prediction,polynomial_eval_list_sum,List.map_map,
    Function.comp_def,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  congr 1
  apply List.map_congr_left
  intro t _
  rw [(wordPredictionPolynomial_spec j a _ i).2 z]

end GradedWords

omit [Fintype ι] in
lemma projectSeries_shift (i : ι) (v : Seq (ι:=ι)) :
    projectSeries i (shift v)=PowerSeries.X*projectSeries i v := by
  ext n
  cases n with
  | zero => simp
  | succ n => simp
omit [Fintype ι] in
lemma projectSeries_shifts (i : ι) (v : Seq (ι:=ι)) (d : ℕ) :
    projectSeries i (shifts d v)=PowerSeries.X^d*projectSeries i v := by
  induction d with
  | zero => simp [shifts]
  | succ d ih => simp only [shifts,LinearMap.comp_apply,projectSeries_shift,ih,pow_succ']; ring
lemma projectSeries_word (j : ℝ) (a : ι→ℝ) (F : List (WordLetter ι)) (hF : inverseCount F≤1) (i : ι) :
    projectSeries i (wordSeq j a F)=(wordPredictionPolynomial j a F i : PowerSeries ℝ) := by
  ext n
  simp only [projectSeries_coeff,Polynomial.coeff_coe,wordSeq_project_coeff j a F hF]

namespace GradedWords

theorem projectSeries_eq (j : ℝ) (a : ι→ℝ) (P : GradedWords ι)
    (hP : ∀ t∈P,inverseCount t.2.2≤1) (i : ι) :
    projectSeries i (seq j a P)=(predictionPolynomial j a P i : PowerSeries ℝ) := by
  induction P with
  | nil => simp [seq,predictionPolynomial]
  | cons t P ih =>
    simp only [seq,predictionPolynomial,List.map_cons,List.sum_cons,map_add,map_smul,
      Polynomial.coe_add,Polynomial.coe_mul,Polynomial.coe_pow,Polynomial.coe_C,Polynomial.coe_X]
    change _ + projectSeries i (seq j a P)=_+(predictionPolynomial j a P i : PowerSeries ℝ)
    rw [ih (by intro s hs; exact hP s (List.mem_cons_of_mem _ hs)),
      projectSeries_shifts,projectSeries_word j a _ (hP t (by simp))]
    simp [Algebra.smul_def,mul_assoc]

theorem prediction_zero_of_project (j : ℝ) (a : ι→ℝ) (P : GradedWords ι)
    (hP : ∀ t∈P,inverseCount t.2.2≤1) (i : ι)
    (hz : ∀ n,project (seq j a P n) i=0) (z : ℝ) : prediction j a z P i=0 := by
  have hp : predictionPolynomial j a P i=0 := by
    apply Polynomial.ext
    intro n
    have h:=congrArg (PowerSeries.coeff n) (projectSeries_eq j a P hP i)
    simp only [projectSeries_coeff,Polynomial.coeff_coe,hz] at h
    simpa using h.symm
  rw [←predictionPolynomial_eval,hp,Polynomial.eval_zero]
end GradedWords
end SKGap.Noncrossing.Primary.Tensor.Series

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ClosedPrediction
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
namespace GradedWords

lemma pairSeq_branch (j : ℝ) (a p : ι→ℝ) (U V : GradedWords ι×GradedWords ι) :
    pairSeq j a (branch j p U V)=
      (branchSource p (pairSeq j a U) (pairSeq j a V),
       branchField j p (pairSeq j a U) (pairSeq j a V)) := by
  simp [pairSeq,branch,branchSource,branchField,seq_append,seq_bump,seq_prepend,
    seq_scale,letterOperator,sub_eq_add_neg,add_assoc]
lemma pairSeq_ordinary (j : ℝ) (a : ι→ℝ) (t : SourceTree (ι→ℝ)) :
    pairSeq j a (ordinaryWords j t)=ordinary j t := by
  induction t with
  | leaf c =>
    simp [ordinaryWords,pairSeq,seq_scalar,seq_bump,seq_prepend,letterOperator,
      ordinary,act_ofVector]
  | branch p t u ih1 ih2 => simp only [ordinaryWords,pairSeq_branch,ih1,ih2,ordinary]
lemma seq_implicitSource (j : ℝ) (a p : ι→ℝ) (t : SourceTree (ι→ℝ)) :
    seq j a (implicitSource j a p t)=loopSource j a p t := by
  have h1:=congrArg Prod.fst (pairSeq_ordinary j a t)
  have h2:=congrArg Prod.snd (pairSeq_ordinary j a t)
  simp only [pairSeq] at h1 h2
  simp [implicitSource,seq_prepend,seq_append,seq_scale,seq_bump,letterOperator,
    h1,h2,loopSource,sub_eq_add_neg]
lemma seq_implicitField (j : ℝ) (a p : ι→ℝ) (t : SourceTree (ι→ℝ)) :
    seq j a (implicitField j a p t)=loopField j a p t := by
  have h1:=congrArg Prod.fst (pairSeq_ordinary j a t)
  simp only [pairSeq] at h1
  simp [implicitField,seq_prepend,seq_append,seq_scale,seq_bump,letterOperator,
    h1,seq_implicitSource,loopField,sub_eq_add_neg,add_assoc]

section
omit [Fintype ι]

lemma bounded_mono {k l : ℕ} (hkl : k≤l) {P : GradedWords ι} (h : bounded k P) : bounded l P :=
  fun t ht=>(h t ht).trans hkl
lemma bounded_scalar (k : ℕ) (c : ℝ) : bounded k (scalar (ι:=ι) c) := by
  rintro t ht
  simp only [scalar,List.mem_singleton] at ht
  subst t
  simp [inverseCount]
lemma bounded_append {k : ℕ} {P Q : GradedWords ι} (hP : bounded k P) (hQ : bounded k Q) :
    bounded k (P++Q) := by
  intro t ht
  rcases List.mem_append.mp ht with h|h
  · exact hP t h
  · exact hQ t h
lemma bounded_scale {k : ℕ} {P : GradedWords ι} (c : ℝ) (hP : bounded k P) : bounded k (scale c P) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩:=List.mem_map.mp ht
  exact hP s hs
lemma bounded_bump {k : ℕ} {P : GradedWords ι} (hP : bounded k P) : bounded k (bump P) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩:=List.mem_map.mp ht
  exact hP s hs
lemma bounded_diag {k : ℕ} {P : GradedWords ι} (d : ι→ℝ) (hP : bounded k P) :
    bounded k (prepend (.diag d) P) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩:=List.mem_map.mp ht
  exact hP s hs
lemma bounded_noise {k : ℕ} {P : GradedWords ι} (hP : bounded k P) :
    bounded k (prepend .noise P) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩:=List.mem_map.mp ht
  exact hP s hs
lemma bounded_inverse {k : ℕ} {P : GradedWords ι} (hP : bounded k P) :
    bounded (k+1) (prepend .inverse P) := by
  intro t ht
  obtain ⟨s,hs,rfl⟩:=List.mem_map.mp ht
  simpa only [inverseCount_inverse] using Nat.add_le_add_right (hP s hs) 1

end

lemma bounded_branch {k : ℕ} (j : ℝ) (p : ι→ℝ) {U V : GradedWords ι×GradedWords ι}
    (hU : bounded k U.1 ∧ bounded k U.2) (hV : bounded k V.1 ∧ bounded k V.2) :
    bounded k (branch j p U V).1 ∧ bounded k (branch j p U V).2 := by
  exact ⟨bounded_append (bounded_diag _ hU.2) hV.1,
    bounded_append (bounded_append (bounded_bump (bounded_noise (bounded_diag _ hU.2)))
      (bounded_scale _ (bounded_bump (bounded_bump hU.1)))) hV.2⟩
lemma bounded_ordinary (j : ℝ) (t : SourceTree (ι→ℝ)) :
    bounded 0 (ordinaryWords j t).1 ∧ bounded 0 (ordinaryWords j t).2 := by
  induction t with
  | leaf c => exact ⟨bounded_scalar 0 c,bounded_bump (bounded_noise (bounded_scalar 0 c))⟩
  | branch p t u ih1 ih2 => exact bounded_branch j p ih1 ih2
lemma bounded_implicitSource (j : ℝ) (a p : ι→ℝ) (t : SourceTree (ι→ℝ)) :
    bounded 1 (implicitSource j a p t) := by
  have h:=bounded_ordinary j t
  exact bounded_inverse (bounded_append (bounded_diag _ h.2)
    (bounded_scale _ (bounded_bump (bounded_bump (bounded_diag _ h.1)))))
lemma bounded_implicitField (j : ℝ) (a p : ι→ℝ) (t : SourceTree (ι→ℝ)) :
    bounded 1 (implicitField j a p t) := by
  have h:=bounded_implicitSource j a p t
  exact bounded_append (bounded_append (bounded_bump (bounded_noise h))
    (bounded_scale _ (bounded_bump (bounded_bump h))))
    (bounded_scale _ (bounded_bump (bounded_bump (bounded_mono (by omega) (bounded_ordinary j t).1))))
end GradedWords

namespace ClosedTree
open GradedWords

lemma words_series (j : ℝ) (a : ι→ℝ) (t : ClosedTree (ι→ℝ)) :
    pairSeq j a (t.words j a)=t.series j a := by
  induction t with
  | leaf c => exact pairSeq_ordinary j a (.leaf c)
  | implicit p t => exact Prod.ext (seq_implicitSource j a p t) (seq_implicitField j a p t)
  | branch p t u ih1 ih2 => simp only [words,pairSeq_branch,ih1,ih2,series]
lemma words_bounded (j : ℝ) (a : ι→ℝ) (t : ClosedTree (ι→ℝ)) :
    bounded 1 (t.words j a).1 ∧ bounded 1 (t.words j a).2 := by
  induction t with
  | leaf c =>
    exact ⟨bounded_mono (by omega) (bounded_ordinary j (.leaf c)).1,
      bounded_mono (by omega) (bounded_ordinary j (.leaf c)).2⟩
  | implicit p t => exact ⟨bounded_implicitSource j a p t,bounded_implicitField j a p t⟩
  | branch p t u ih1 ih2 => exact bounded_branch j p ih1 ih2

theorem field_prediction_zero (j : ℝ) (a : ι→ℝ) (t : ClosedTree (ι→ℝ)) (z : ℝ) (i : ι) :
    prediction j a z (t.words j a).2 i=0 := by
  apply prediction_zero_of_project j a _ (t.words_bounded j a).2
  intro n
  have h:=congrArg Prod.snd (t.words_series j a)
  change seq j a (t.words j a).2=(t.series j a).2 at h
  rw [h]
  exact t.project_field j a n ▸ rfl

theorem source_prediction_zero (j : ℝ) (a : ι→ℝ) (t : ClosedTree (ι→ℝ))
    (ht : t.leafMass=0) (z : ℝ) (i : ι) : prediction j a z (t.words j a).1 i=0 := by
  apply prediction_zero_of_project j a _ (t.words_bounded j a).1
  intro n
  have h:=congrArg Prod.fst (t.words_series j a)
  change seq j a (t.words j a).1=(t.series j a).1 at h
  rw [h,t.project_source,ht]
  split_ifs <;> rfl
end ClosedTree
end SKGap.Noncrossing.Primary.Tensor.Series

end
end

end OAI
end

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

end SKGapCutoff

open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set

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

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ}

lemma vectorNorm_smul (c : ℝ) (u : Fin n→ℝ) :
    vectorNorm (c • u)=|c| *vectorNorm u := by
  exact norm_smul c (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))

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
variable {n : ℕ}

lemma derivativeMatrix_add (U V : VectorFields n) (x : Spin n) :
    derivativeMatrix (fun x i=>U x i+V x i) x=derivativeMatrix U x+derivativeMatrix V x := by
  ext i k; simp only [derivativeMatrix,halfDiff,Matrix.add_apply]; ring

lemma derivativeMatrix_sum {ι : Type*} [Fintype ι] (U : ι→VectorFields n) (x : Spin n) :
    derivativeMatrix (fun x i=>∑l,U l x i) x=∑l,derivativeMatrix (U l) x := by
  ext i k; simp only [Matrix.sum_apply,derivativeMatrix,halfDiff_sum]

end SKGapCutoff.Recipe

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

lemma average_norm_product (hn : 0<n) (s d : Fin n→ℝ) (hd : ∀i,|d i|≤1) :
    |Diagram.mean s| * SKGapCutoff.Recipe.vectorNorm d ≤ SKGapCutoff.Recipe.vectorNorm s := by
  have H:=SKGapCutoff.Recipe.primary_mean_size (fun _=>s) (fun _=>d) (fun _=>false) hn
    (fun i=>hd i)
  change SKGapCutoff.Recipe.vectorNorm ((SKGapCutoff.Primary.siteMean (fun _=>s) (fun _=>false)) • d)≤_ at H
  rw [SKGapCutoff.Recipe.vectorNorm_smul] at H
  simpa only [SKGapCutoff.Primary.siteMean,Diagram.mean,Fintype.card_fin] using H

end SmallMark

end SKGap.Noncrossing.Primary

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

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ClosedMarked
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.Noncrossing.ClosedMarked
open Matrix
variable {n : ℕ}

lemma ungrade_matrix (j : ℝ) (a : Fin n→ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (P : Primary.Tensor.Series.GradedWords (Fin n)) :
    matrixValue j a J (ungrade P)=Primary.Tensor.Series.GradedWords.matrixValue j a J P := by
  simp [matrixValue,ungrade,Primary.Tensor.Series.GradedWords.matrixValue,List.map_map,Function.comp_def]
lemma ungrade_prediction (j : ℝ) (a : Fin n→ℝ) (P : Primary.Tensor.Series.GradedWords (Fin n)) :
    prediction j a (ungrade P)=Primary.Tensor.Series.GradedWords.prediction j a 1 P := by
  funext i
  simp [prediction,ungrade,Primary.Tensor.Series.GradedWords.prediction,List.map_map,Function.comp_def]

namespace Mark

lemma prefix_scalar (P : Word n) (t : Mark n) : (t.prepend P).scalar=t.scalar := by cases t <;> rfl
lemma prefix_word (P : Word n) (t : Mark n) : (t.prepend P).word=P++t.word := by
  cases t <;> simp [prepend,word,List.append_assoc]

lemma trace_error (j : ℝ) (a : Fin n→ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (hn : 0<n) (d : Fin n→ℝ) (hd : ∀i,|d i|≤1) (t : Mark n)
    (ht : inverseCount t.word≤1) {B : ℝ} (hB : 0≤B)
    (hb : diagonalSeminorm (exactWord j a (t.diagnostic d) J-
      Matrix.diagonal (wordPrediction j a 1 (t.diagnostic d)))≤B) :
    |t.scalar*(trace (Matrix.diagonal d*exactWord j a t.word J)-
      ∑i,d i*wordPrediction j a 1 t.word i)|≤SKGapCutoff.Recipe.vectorNorm t.vector*B := by
  cases t with
  | diagonal P s Q =>
    simpa only [scalar,one_mul,word,diagnostic,vector,SKGapCutoff.Recipe.vectorNorm] using
      (rotated_small_word_trace_error j a d s J P Q ht).trans
        (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
  | average s P =>
    have H:=trace_small_diagonal_error d (wordPrediction j a 1 P) (exactWord j a P J)
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left H (abs_nonneg _)).trans (by
      change |Diagram.mean s| *(SKGapCutoff.Recipe.vectorNorm d*_)≤SKGapCutoff.Recipe.vectorNorm s*B
      calc
        _ ≤ |Diagram.mean s| *(SKGapCutoff.Recipe.vectorNorm d*B) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (norm_nonneg _)) (abs_nonneg _)
        _ = (|Diagram.mean s| *SKGapCutoff.Recipe.vectorNorm d)*B := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (Primary.SmallMark.average_norm_product hn s d hd) hB)
end Mark

namespace Marked

lemma plain_prefix (F : Word n) (P : Marked n) :
    (P.prepend F).plain=P.plain.map (fun t=>(t.1,F++t.2)) := by
  simp [prepend,plain,List.map_map,Function.comp_def,Mark.prefix_scalar,Mark.prefix_word]
lemma plain_scale (c : ℝ) (P : Marked n) : (P.scale c).plain=P.plain.map (fun t=>(c*t.1,t.2)) := by
  simp [scale,plain,List.map_map,Function.comp_def,mul_assoc]
lemma plain_append (P Q : Marked n) : (P++Q).plain=P.plain++Q.plain := by simp [plain]

theorem trace_error (j : ℝ) (a : Fin n→ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (hn : 0<n)
    (d : Fin n→ℝ) (hd : ∀i,|d i|≤1) (P : Marked n)
    (hI : ∀t∈P,inverseCount t.2.word≤1) {B : ℝ} (hB : 0≤B)
    (hb : ∀t∈P,diagonalSeminorm (exactWord j a (t.2.diagnostic d) J-
      Matrix.diagonal (wordPrediction j a 1 (t.2.diagnostic d)))≤B) :
    |trace (Matrix.diagonal d*matrixValue j a J P.plain)-
      ∑i,d i*prediction j a P.plain i|≤P.budget*B := by
  induction P with
  | nil => simp [plain,budget,matrixValue,prediction]
  | cons t P ih =>
    have ht:=Mark.trace_error j a J hn d hd t.2 (hI t (by simp)) hB (hb t (by simp))
    have hh:=ih (fun s hs=>hI s (List.mem_cons_of_mem _ hs)) (fun s hs=>hb s (List.mem_cons_of_mem _ hs))
    simp only [plain,List.map_cons,matrixValue,List.sum_cons,prediction,budget] at *
    simp only [mul_add,mul_smul_comm,trace_add,trace_smul,smul_eq_mul,Finset.sum_add_distrib,add_mul]
    have he : (∑i,d i*(t.1*t.2.scalar*wordPrediction j a 1 t.2.word i))=
        t.1*t.2.scalar*(∑i,d i*wordPrediction j a 1 t.2.word i) := by
      rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro i _;ring
    rw [he]
    have hc:=mul_le_mul_of_nonneg_left ht (abs_nonneg t.1)
    rw [←abs_mul] at hc
    calc
      _ = |t.1*(t.2.scalar*(trace (Matrix.diagonal d*exactWord j a t.2.word J)-
            ∑i,d i*wordPrediction j a 1 t.2.word i))+
          (trace (Matrix.diagonal d*(List.map (fun p=>p.1 • exactWord j a p.2 J)
            (List.map (fun t=>(t.1*t.2.scalar,t.2.word)) P)).sum)-
            ∑i,d i*(List.map (fun p=>p.1*wordPrediction j a 1 p.2 i)
              (List.map (fun t=>(t.1*t.2.scalar,t.2.word)) P)).sum)| := by congr 1;ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add (by convert! hc using 1; ring) hh)
end Marked
end SKGap.Noncrossing.ClosedMarked

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGap.Noncrossing.ClosedMarked
open Matrix Primary Primary.Tensor.Series
variable {n : ℕ}

lemma ungrade_append (P Q : GradedWords (Fin n)) : ungrade (P++Q)=ungrade P++ungrade Q := by simp [ungrade]
lemma ungrade_bump (P : GradedWords (Fin n)) : ungrade (GradedWords.bump P)=ungrade P := by
  simp [ungrade,GradedWords.bump,List.map_map,Function.comp_def]
lemma ungrade_prepend (l : WordLetter (Fin n)) (P : GradedWords (Fin n)) :
    ungrade (GradedWords.prepend l P)=(ungrade P).map (fun t=>(t.1,l::t.2)) := by
  simp [ungrade,GradedWords.prepend,List.map_map,Function.comp_def]
lemma ungrade_scale (c : ℝ) (P : GradedWords (Fin n)) :
    ungrade (GradedWords.scale c P)=(ungrade P).map (fun t=>(c*t.1,t.2)) := by
  simp [ungrade,GradedWords.scale,List.map_map,Function.comp_def]

namespace Marked

lemma plain_diagonalWords (s : Fin n→ℝ) (P : GradedWords (Fin n)) :
    (diagonalWords s P).plain=ungrade (GradedWords.prepend (.diag s) P) := by
  simp [diagonalWords,plain,ungrade,GradedWords.prepend,List.map_map,Function.comp_def,Mark.scalar,Mark.word]
lemma plain_averageWords (c : ℝ) (s : Fin n→ℝ) (P : GradedWords (Fin n)) :
    (averageWords c s P).plain=ungrade (GradedWords.scale (c*Diagram.mean s) P) := by
  simp only [averageWords,plain,ungrade,GradedWords.scale,List.map_map,Function.comp_def,Mark.scalar,Mark.word]
  congr 1;funext t;congr 1;ring

lemma bounded_of_plain (P : Marked n) (Q : GradedWords (Fin n)) (h : P.plain=ungrade Q)
    (hQ : GradedWords.bounded 1 Q) : ∀t∈P,inverseCount t.2.word≤1 := by
  intro t ht
  have hp : (t.1*t.2.scalar,t.2.word)∈ungrade Q := h ▸ List.mem_map.mpr ⟨t,ht,rfl⟩
  obtain ⟨q,hq,he⟩:=List.mem_map.mp hp
  have hword : q.2.2=t.2.word := congrArg Prod.snd he
  rw [←hword]
  exact hQ q hq
end Marked

lemma zeroPair_plain (j : ℝ) : pairPlain (zeroPair (n:=n))=pairUngrade (GradedWords.ordinaryWords j (.leaf 0)) := by
  simp [pairPlain,pairUngrade,zeroPair,Marked.plain,Mark.scalar,Mark.word,GradedWords.ordinaryWords,
    GradedWords.scalar,GradedWords.bump,GradedWords.prepend,ungrade]

lemma implicitPair_plain (j : ℝ) (a p : Fin n→ℝ) (t : SourceTree (Fin n→ℝ)) :
    pairPlain (implicitPair j a p t)=pairUngrade (GradedWords.implicitSource j a p t,GradedWords.implicitField j a p t) := by
  have hs : (implicitPair j a p t).1.plain=ungrade (GradedWords.implicitSource j a p t) := by
    simp only [implicitPair,Marked.plain_append,Marked.plain_prefix,Marked.plain_diagonalWords,
      Marked.plain_averageWords,GradedWords.implicitSource,ungrade_prepend,ungrade_append,
      ungrade_scale,ungrade_bump,List.map_append,List.map_map,Function.comp_def,
      List.cons_append,List.nil_append,neg_mul]
  apply Prod.ext hs
  dsimp only [pairPlain,pairUngrade]
  change ((implicitPair j a p t).1.prepend [.noise]++
    (implicitPair j a p t).1.scale (-(j*Diagram.mean a))++Marked.averageWords (-j) p (GradedWords.ordinaryWords j t).1).plain=_
  rw [Marked.plain_append,Marked.plain_append,Marked.plain_prefix,Marked.plain_scale,hs,Marked.plain_averageWords]
  simp [GradedWords.implicitField,ungrade_append,ungrade_bump,ungrade_scale,ungrade_prepend,neg_mul]

lemma smallBranch_plain (j : ℝ) (p : Fin n→ℝ) (T V : GradedWords (Fin n)×GradedWords (Fin n))
    (Q : Pair n) (hQ : pairPlain Q=pairUngrade V) :
    pairPlain (smallBranch j p T Q)=pairUngrade (GradedWords.branch j p T V) := by
  have h₁ : Q.1.plain=ungrade V.1 := congrArg Prod.fst hQ
  have h₂ : Q.2.plain=ungrade V.2 := congrArg Prod.snd hQ
  simp [pairPlain,smallBranch,Marked.plain_append,Marked.plain_prefix,Marked.plain_diagonalWords,
    Marked.plain_averageWords,h₁,h₂,pairUngrade,GradedWords.branch,ungrade_append,ungrade_bump,
    ungrade_prepend,ungrade_scale,List.map_map,Function.comp_def,neg_mul]
lemma boundedBranch_plain (j : ℝ) (p : Fin n→ℝ) (T V : GradedWords (Fin n)×GradedWords (Fin n))
    (P Q : Pair n) (hP : pairPlain P=pairUngrade T) (hQ : pairPlain Q=pairUngrade V) :
    pairPlain (boundedBranch j p P Q)=pairUngrade (GradedWords.branch j p T V) := by
  have h₁ : P.1.plain=ungrade T.1 := congrArg Prod.fst hP
  have h₂ : P.2.plain=ungrade T.2 := congrArg Prod.snd hP
  have h₃ : Q.1.plain=ungrade V.1 := congrArg Prod.fst hQ
  have h₄ : Q.2.plain=ungrade V.2 := congrArg Prod.snd hQ
  simp [pairPlain,boundedBranch,Marked.plain_append,Marked.plain_prefix,Marked.plain_scale,
    h₁,h₂,h₃,h₄,pairUngrade,GradedWords.branch,ungrade_append,ungrade_bump,ungrade_prepend,
    ungrade_scale,List.map_map,Function.comp_def]

namespace SmallTree

lemma leafMass (T : SmallTree n) : T.tree.leafMass=0 := by
  induction T with
  | zero=>rfl
  | implicit=>rfl
  | small p U V ih=>exact ih
  | bounded p U V ih1 ih2=>exact ih2
lemma plain (j : ℝ) (a : Fin n→ℝ) (T : SmallTree n) :
    pairPlain (T.marked j a)=pairUngrade (T.tree.words j a) := by
  induction T with
  | zero=>exact zeroPair_plain j
  | implicit p U=>exact implicitPair_plain j a p U
  | small p U V ih=>exact smallBranch_plain j p (U.words j a) (V.tree.words j a) (V.marked j a) ih
  | bounded p U V ih1 ih2 =>
    exact boundedBranch_plain j p (U.tree.words j a) (V.tree.words j a)
      (U.marked j a) (V.marked j a) ih1 ih2

theorem diagonal (j : ℝ) (a : Fin n→ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (hn : 0<n)
    (T : SmallTree n) {B : ℝ} (hB : 0≤B)
    (hb : ∀d:Fin n→ℝ,(∀i,|d i|≤1)→∀P∈[ (T.marked j a).1,(T.marked j a).2 ],∀t∈P,
      diagonalSeminorm (exactWord j a (t.2.diagnostic d) J-
        Matrix.diagonal (wordPrediction j a 1 (t.2.diagnostic d)))≤B) :
    (∑i,|GradedWords.matrixValue j a J (T.tree.words j a).1 i i|)≤(T.marked j a).1.budget*B ∧
    (∑i,|GradedWords.matrixValue j a J (T.tree.words j a).2 i i|)≤(T.marked j a).2.budget*B := by
  have hs : (T.marked j a).1.plain=ungrade (T.tree.words j a).1 := congrArg Prod.fst (T.plain j a)
  have hf : (T.marked j a).2.plain=ungrade (T.tree.words j a).2 := congrArg Prod.snd (T.plain j a)
  have hbound (P : Marked n) (Q : GradedWords (Fin n)) (hp : P.plain=ungrade Q)
      (hQ : GradedWords.bounded 1 Q) (hz : ∀i,GradedWords.prediction j a 1 Q i=0)
      (hP : P∈[(T.marked j a).1,(T.marked j a).2]) :
      (∑i,|GradedWords.matrixValue j a J Q i i|)≤P.budget*B := by
    apply diagonal_abs_sum_of_tests
    intro d hd
    have H:=Marked.trace_error j a J hn d hd P (P.bounded_of_plain Q hp hQ) hB (hb d hd P hP)
    rw [hp,ungrade_matrix,ungrade_prediction] at H
    simpa only [hz,mul_zero,Finset.sum_const_zero,sub_zero] using H
  exact ⟨hbound _ _ hs (T.tree.words_bounded j a).1 (T.tree.source_prediction_zero j a T.leafMass 1) (by simp),
    hbound _ _ hf (T.tree.words_bounded j a).2 (T.tree.field_prediction_zero j a 1) (by simp)⟩
end SmallTree
end SKGap.Noncrossing.ClosedMarked

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

end OrdinaryData
end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_StartedRecipe
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

lemma startedSource_eq (w y : VectorFields n) {a : ℕ} (ha : 0<a) :
    D.startedSource w y a=D.sourceOf a (fun b=>D.startedAuxiliary w y b) := by
  obtain ⟨a,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : a≠0)
  rw [startedSource,startedEvaluate];rfl
lemma startedAuxiliary_eq (w y : VectorFields n) {a : ℕ} (ha : 0<a) :
    D.startedAuxiliary w y a=D.fieldOf a (fun b=>D.startedSource w y b) (fun b=>D.startedAuxiliary w y b) := by
  obtain ⟨a,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : a≠0)
  rw [startedAuxiliary,startedEvaluate];rfl

lemma started_source_derivative (w y : VectorFields n) {a : ℕ} (ha : 0<a) (x : Spin n) :
    derivativeMatrix (D.startedSource w y a) x=
      (∑l,Matrix.diagonal (D.startedPartial w y a l x)*derivativeMatrix (D.H l) x)+
      (∑b:Fin a,Matrix.diagonal (D.auxCoefficient a b x)*derivativeMatrix (D.startedAuxiliary w y b) x)+
      D.sourceAtoms a (fun b=>D.startedAuxiliary w y b) x := by
  rw [D.startedSource_eq w y ha,D.sourceOf_derivative]
  dsimp only [startedPartial]
  abel

lemma started_field_derivative (w y : VectorFields n) {a : ℕ} (ha : 0<a) (x : Spin n) :
    derivativeMatrix (D.startedAuxiliary w y a) x=
      D.J*derivativeMatrix (D.startedSource w y a) x-
      (∑l,(D.j*siteMean (D.startedPartial w y a l) x) • derivativeMatrix (D.predecessor l) x)-
      (∑b:Fin a,(D.j*siteMean (D.auxCoefficient a b) x) • derivativeMatrix (D.startedSource w y b) x)-
      D.j • ((∑l,averageError (siteMean (D.startedPartial w y a l)) (D.predecessor l) x)+
        ∑b:Fin a,averageError (siteMean (D.auxCoefficient a b)) (D.startedSource w y b) x) := by
  rw [D.startedAuxiliary_eq w y ha,D.fieldOf_derivative,D.startedSource_eq w y ha]
  rfl

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_ClosedMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.Tensor.Series.GradedWords
open Matrix Diagram InverseDiagram
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrixValue_append (j : ℝ) (a : ι→ℝ) (J : Matrix ι ι ℝ) (P Q : GradedWords ι) :
    matrixValue j a J (P++Q)=matrixValue j a J P+matrixValue j a J Q := by
  simp [matrixValue]
lemma matrixValue_scalar (j c : ℝ) (a : ι→ℝ) (J : Matrix ι ι ℝ) :
    matrixValue j a J (scalar c)=c • 1 := by
  simp [matrixValue,scalar,exactWord,matrixFactorProduct]
lemma matrixValue_bump (j : ℝ) (a : ι→ℝ) (J : Matrix ι ι ℝ) (P : GradedWords ι) :
    matrixValue j a J (bump P)=matrixValue j a J P := by
  simp [matrixValue,bump,List.map_map,Function.comp_def]
lemma matrixValue_scale (j c : ℝ) (a : ι→ℝ) (J : Matrix ι ι ℝ) (P : GradedWords ι) :
    matrixValue j a J (scale c P)=c • matrixValue j a J P := by
  induction P with
  | nil => simp [matrixValue,scale]
  | cons t P ih =>
    simp only [scale,List.map_cons,matrixValue,List.sum_cons]
    change (c*t.1) • _+matrixValue j a J (scale c P)=c • (t.1 • _+matrixValue j a J P)
    rw [ih,smul_add,smul_smul]
lemma matrixValue_prepend (j : ℝ) (a : ι→ℝ) (J : Matrix ι ι ℝ) (P : GradedWords ι) (l : WordLetter ι) :
    matrixValue j a J (prepend l P)=l.exactEval j a J*matrixValue j a J P := by
  induction P with
  | nil => simp [matrixValue,prepend]
  | cons t P ih =>
    simp only [prepend,List.map_cons,matrixValue,List.sum_cons]
    change t.1 • (l.exactEval j a J*exactWord j a t.2.2 J)+matrixValue j a J (prepend l P)=_
    rw [ih,mul_add,mul_smul_comm]
    rfl
lemma matrixValue_ordinaryWords (j : ℝ) (a : ι→ℝ) (J : Matrix ι ι ℝ) (t : SourceTree (ι→ℝ)) :
    (matrixValue j a J (ordinaryWords j t).1,matrixValue j a J (ordinaryWords j t).2)=
      (t.sourceMatrix j J,t.fieldMatrix j J) := by
  induction t with
  | leaf c => simp [ordinaryWords,matrixValue_bump,matrixValue_prepend,matrixValue_scalar,
      SourceTree.sourceMatrix_leaf,SourceTree.fieldMatrix_leaf,WordLetter.exactEval]
  | branch p t u ht hu =>
    have hs:=congrArg Prod.fst ht
    have hf:=congrArg Prod.snd ht
    have us:=congrArg Prod.fst hu
    have uf:=congrArg Prod.snd hu
    dsimp only at hs hf us uf
    simp only [ordinaryWords,branch,matrixValue_append,matrixValue_bump,matrixValue_prepend,
      matrixValue_scale,WordLetter.exactEval,hs,hf,us,uf,
      SourceTree.sourceMatrix_branch,SourceTree.fieldMatrix_branch,neg_smul,sub_eq_add_neg]
lemma matrixValue_implicitSource (j : ℝ) (a p : ι→ℝ) (J : Matrix ι ι ℝ) (t : SourceTree (ι→ℝ)) :
    matrixValue j a J (implicitSource j a p t)=WordLetter.inverse.exactEval j a J*
      (Matrix.diagonal p*t.fieldMatrix j J-(j*Diagram.mean p) • (Matrix.diagonal a*t.sourceMatrix j J)) := by
  have hs:=congrArg Prod.fst (matrixValue_ordinaryWords j a J t)
  have hf:=congrArg Prod.snd (matrixValue_ordinaryWords j a J t)
  dsimp only at hs hf
  simp only [implicitSource,matrixValue_prepend,matrixValue_append,matrixValue_scale,
    matrixValue_bump,WordLetter.exactEval,hs,hf,neg_smul,sub_eq_add_neg]
lemma matrixValue_implicitField (j : ℝ) (a p : ι→ℝ) (J : Matrix ι ι ℝ) (t : SourceTree (ι→ℝ)) :
    matrixValue j a J (implicitField j a p t)=
      (J-(j*Diagram.mean a) • 1)*matrixValue j a J (implicitSource j a p t)-
        (j*Diagram.mean p) • t.sourceMatrix j J := by
  have hs:=congrArg Prod.fst (matrixValue_ordinaryWords j a J t)
  dsimp only at hs
  simp only [implicitField,matrixValue_append,matrixValue_bump,matrixValue_prepend,
    matrixValue_scale,WordLetter.exactEval,hs,neg_smul,smul_mul_assoc,one_mul,
    sub_eq_add_neg,add_mul,neg_mul]

end SKGap.Noncrossing.Primary.Tensor.Series.GradedWords

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_ClosedTreeMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.Tensor.Series.ClosedTree
open Matrix GradedWords
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma words_ofOrdinary (j : ℝ) (a : ι→ℝ) (t : SourceTree (ι→ℝ)) :
    (ofOrdinary t).words j a=ordinaryWords j t := by
  induction t with
  | leaf c => rfl
  | branch p t u ht hu => simp only [ofOrdinary,words,ordinaryWords,ht,hu]

lemma sourceMatrix_ofOrdinary (j : ℝ) (a : ι→ℝ) (J : Matrix ι ι ℝ) (t : SourceTree (ι→ℝ)) :
    (ofOrdinary t).sourceMatrix j a J=t.sourceMatrix j J := by
  rw [sourceMatrix,words_ofOrdinary]
  exact congrArg Prod.fst (matrixValue_ordinaryWords j a J t)
lemma fieldMatrix_ofOrdinary (j : ℝ) (a : ι→ℝ) (J : Matrix ι ι ℝ) (t : SourceTree (ι→ℝ)) :
    (ofOrdinary t).fieldMatrix j a J=t.fieldMatrix j J := by
  rw [fieldMatrix,words_ofOrdinary]
  exact congrArg Prod.snd (matrixValue_ordinaryWords j a J t)
lemma sourceMatrix_leaf (j c : ℝ) (a : ι→ℝ) (J : Matrix ι ι ℝ) :
    (ClosedTree.leaf c).sourceMatrix j a J=c • 1 := by
  simp [sourceMatrix,words,ordinaryWords,matrixValue_scalar]
lemma fieldMatrix_leaf (j c : ℝ) (a : ι→ℝ) (J : Matrix ι ι ℝ) :
    (ClosedTree.leaf c).fieldMatrix j a J=c • J := by
  simp [fieldMatrix,words,ordinaryWords,matrixValue_bump,matrixValue_prepend,
    matrixValue_scalar,WordLetter.exactEval]
lemma sourceMatrix_branch (j : ℝ) (a p : ι→ℝ) (J : Matrix ι ι ℝ) (t u : ClosedTree (ι→ℝ)) :
    (ClosedTree.branch p t u).sourceMatrix j a J=
      Matrix.diagonal p*t.fieldMatrix j a J+u.sourceMatrix j a J := by
  simp [sourceMatrix,fieldMatrix,words,GradedWords.branch,matrixValue_append,matrixValue_prepend,
    WordLetter.exactEval]
lemma fieldMatrix_branch (j : ℝ) (a p : ι→ℝ) (J : Matrix ι ι ℝ) (t u : ClosedTree (ι→ℝ)) :
    (ClosedTree.branch p t u).fieldMatrix j a J=
      J*(Matrix.diagonal p*t.fieldMatrix j a J)-
      (j*Diagram.mean p) • t.sourceMatrix j a J+u.fieldMatrix j a J := by
  simp [sourceMatrix,fieldMatrix,words,GradedWords.branch,matrixValue_append,matrixValue_prepend,
    matrixValue_bump,matrixValue_scale,WordLetter.exactEval,sub_eq_add_neg]
  abel

lemma branches_source (j : ℝ) (a : ι→ℝ) (J : Matrix ι ι ℝ)
    (xs : List ((ι→ℝ)×ClosedTree (ι→ℝ))) :
    (branches xs).sourceMatrix j a J=
      (xs.map (fun t=>Matrix.diagonal t.1*t.2.fieldMatrix j a J)).sum := by
  induction xs with
  | nil => simp [branches,sourceMatrix_leaf]
  | cons t xs ih =>
    simpa only [branches,List.foldr_cons,sourceMatrix_branch,List.map_cons,List.sum_cons] using
      (congrArg (fun Z=>Matrix.diagonal t.1*t.2.fieldMatrix j a J+Z) ih)
lemma branches_field (j : ℝ) (a : ι→ℝ) (J : Matrix ι ι ℝ)
    (xs : List ((ι→ℝ)×ClosedTree (ι→ℝ))) :
    (branches xs).fieldMatrix j a J=J*(branches xs).sourceMatrix j a J-
      (xs.map (fun t=>(j*Diagram.mean t.1) • t.2.sourceMatrix j a J)).sum := by
  induction xs with
  | nil => simp [branches,sourceMatrix_leaf,fieldMatrix_leaf]
  | cons t xs ih =>
    change (ClosedTree.branch t.1 t.2 (branches xs)).fieldMatrix j a J=_
    rw [fieldMatrix_branch,ih]
    change _=J*(ClosedTree.branch t.1 t.2 (branches xs)).sourceMatrix j a J-_
    rw [sourceMatrix_branch,mul_add]
    simp only [List.map_cons,List.sum_cons]
    abel

end SKGap.Noncrossing.Primary.Tensor.Series.ClosedTree

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_StartedGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe.OrdinaryData
open Primary Matrix SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.Tensor.Series
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

lemma startedTree_pos (D : OrdinaryData n ι κ σ) (w y : VectorFields n)
    (T : ι→SourceTree (Fin n→ℝ)) (t₀ : ClosedTree (Fin n→ℝ)) (x : Spin n)
    {a : ℕ} (ha : 0<a) : D.startedTree w y T t₀ x a=ClosedTree.branches
      ((Finset.univ.toList.map (fun l=>(D.startedPartial w y a l x,ClosedTree.ofOrdinary (T l))))++
       (Finset.univ.toList.map (fun b : Fin a=>(D.auxCoefficient a b x,D.startedTree w y T t₀ x b)))) := by
  obtain ⟨a,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : a≠0)
  rw [startedTree]

variable (D : OrdinaryData n ι κ σ) (w y : VectorFields n)
    (T : ι→SourceTree (Fin n→ℝ)) (t₀ : ClosedTree (Fin n→ℝ)) (a₀ : Fin n→ℝ) (x : Spin n)

lemma startedRetainedSource_eq {a : ℕ} (ha : 0<a) :
    D.startedRetainedSource w y T t₀ a₀ x a=
      (∑l,Matrix.diagonal (D.startedPartial w y a l x)*SourceTree.fieldMatrix D.j D.J (T l))+
      ∑b:Fin a,Matrix.diagonal (D.auxCoefficient a b x)*D.startedRetainedField w y T t₀ a₀ x b := by
  rw [startedRetainedSource,D.startedTree_pos w y T t₀ x ha,ClosedTree.branches_source]
  simp [List.map_append,List.sum_append,List.map_map,Function.comp_def,startedRetainedField,
    ClosedTree.fieldMatrix_ofOrdinary]

lemma startedRetainedField_eq {a : ℕ} (ha : 0<a) :
    D.startedRetainedField w y T t₀ a₀ x a=D.J*D.startedRetainedSource w y T t₀ a₀ x a-
      (∑l,(D.j*siteMean (D.startedPartial w y a l) x) • SourceTree.sourceMatrix D.j D.J (T l))-
      ∑b:Fin a,(D.j*siteMean (D.auxCoefficient a b) x) • D.startedRetainedSource w y T t₀ a₀ x b := by
  have h:=ClosedTree.branches_field D.j a₀ D.J
    ((Finset.univ.toList.map (fun l=>(D.startedPartial w y a l x,ClosedTree.ofOrdinary (T l))))++
      (Finset.univ.toList.map (fun b:Fin a=>(D.auxCoefficient a b x,D.startedTree w y T t₀ x b))))
  rw [←D.startedTree_pos w y T t₀ x ha] at h
  simpa [List.map_append,List.sum_append,List.map_map,Function.comp_def,
    startedRetainedField,startedRetainedSource,siteMean,SKGap.Noncrossing.Diagram.mean,
    sub_add_eq_sub_sub,ClosedTree.sourceMatrix_ofOrdinary] using h

end SKGapCutoff.Recipe.OrdinaryData

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe.OrdinaryData
open Primary Matrix SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.Tensor.Series
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]
variable (D : OrdinaryData n ι κ σ) (w y : VectorFields n)
    (T : ι→SourceTree (Fin n→ℝ)) (t₀ : ClosedTree (Fin n→ℝ)) (a₀ : Fin n→ℝ) (x : Spin n)

lemma started_source_error_recursion {a : ℕ} (ha : 0<a) :
    D.startedSourceError w y T t₀ a₀ x a=
      (∑b:Fin a,Matrix.diagonal (D.auxCoefficient a b x)*D.startedFieldError w y T t₀ a₀ x b)+
      (∑l,Matrix.diagonal (D.startedPartial w y a l x)*
        (derivativeMatrix (D.H l) x-SourceTree.fieldMatrix D.j D.J (T l)))+
      D.sourceAtoms a (fun b=>D.startedAuxiliary w y b) x := by
  rw [startedSourceError,D.started_source_derivative w y ha,D.startedRetainedSource_eq w y T t₀ a₀ x ha]
  simp only [startedFieldError,mul_sub,Finset.sum_sub_distrib]
  abel

lemma started_field_error_recursion {a : ℕ} (ha : 0<a) :
    D.startedFieldError w y T t₀ a₀ x a=D.J*D.startedSourceError w y T t₀ a₀ x a-
      (∑b:Fin a,(D.j*siteMean (D.auxCoefficient a b) x) • D.startedSourceError w y T t₀ a₀ x b)+
      (-(∑l,(D.j*siteMean (D.startedPartial w y a l) x) •
        (derivativeMatrix (D.predecessor l) x-SourceTree.sourceMatrix D.j D.J (T l)))-
      D.j • ((∑l,averageError (siteMean (D.startedPartial w y a l)) (D.predecessor l) x)+
        ∑b:Fin a,averageError (siteMean (D.auxCoefficient a b)) (D.startedSource w y b) x)) := by
  rw [startedFieldError,D.started_field_derivative w y ha,D.startedRetainedField_eq w y T t₀ a₀ x ha]
  simp only [startedSourceError,smul_sub,Finset.sum_sub_distrib,mul_sub]
  abel

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_StartedMarked
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.ClosedMarked.SmallTree
open Primary Primary.Tensor.Series
variable {n : ℕ}

lemma tree_smallBranches (xs : List ((Fin n→ℝ)×ClosedTree (Fin n→ℝ))) (U : SmallTree n) :
    (smallBranches xs U).tree=xs.foldr (fun t v=>ClosedTree.branch t.1 t.2 v) U.tree := by
  induction xs with
  | nil => rfl
  | cons t xs ih => simpa only [smallBranches,List.foldr_cons,tree] using congrArg (ClosedTree.branch t.1 t.2) ih
lemma tree_boundedBranches (xs : List ((Fin n→ℝ)×SmallTree n)) (U : SmallTree n) :
    (boundedBranches xs U).tree=(xs.map (fun t=>(t.1,t.2.tree))).foldr (fun t v=>ClosedTree.branch t.1 t.2 v) U.tree := by
  induction xs with
  | nil => rfl
  | cons t xs ih =>
    simpa only [boundedBranches,List.foldr_cons,tree,List.map_cons] using congrArg (ClosedTree.branch t.1 t.2.tree) ih
end SKGap.Noncrossing.ClosedMarked.SmallTree

namespace SKGapCutoff.Recipe.OrdinaryData
open Primary Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.Tensor.Series
open SKGap.Noncrossing.ClosedMarked
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

lemma startedSmallTree_tree (D : OrdinaryData n ι κ σ) (w y : VectorFields n)
    (T : ι→SourceTree (Fin n→ℝ)) (t₀ : SmallTree n) (x : Spin n) (a : ℕ) :
    (D.startedSmallTree w y T t₀ x a).tree=D.startedTree w y T t₀.tree x a := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    cases a with
    | zero => simp only [startedSmallTree,startedTree]
    | succ a =>
      rw [startedSmallTree,SmallTree.tree_smallBranches,SmallTree.tree_boundedBranches,startedTree]
      simp only [ClosedTree.branches,List.foldr_append,List.map_map,Function.comp_def,SmallTree.tree]
      congr 2
      apply List.map_congr_left
      intro b hb
      exact congrArg (fun t=>(D.auxCoefficient (a+1) b x,t)) (ih b b.isLt)

theorem started_retained_diagonal (D : OrdinaryData n ι κ σ) (w y : VectorFields n)
    (T : ι→SourceTree (Fin n→ℝ)) (t₀ : SmallTree n) (a₀ : Fin n→ℝ) (x : Spin n)
    (a : ℕ) (hn : 0<n) {B : ℝ} (hB : 0≤B)
    (hb : ∀d:Fin n→ℝ,(∀i,|d i|≤1)→∀P∈[
        ((D.startedSmallTree w y T t₀ x a).marked D.j a₀).1,
        ((D.startedSmallTree w y T t₀ x a).marked D.j a₀).2],∀t∈P,
      diagonalSeminorm (exactWord D.j a₀ (t.2.diagnostic d) D.J-
        Matrix.diagonal (wordPrediction D.j a₀ 1 (t.2.diagnostic d)))≤B) :
    (∑i,|D.startedRetainedSource w y T t₀.tree a₀ x a i i|)≤
        ((D.startedSmallTree w y T t₀ x a).marked D.j a₀).1.budget*B ∧
    (∑i,|D.startedRetainedField w y T t₀.tree a₀ x a i i|)≤
        ((D.startedSmallTree w y T t₀ x a).marked D.j a₀).2.budget*B := by
  have H:=(D.startedSmallTree w y T t₀ x a).diagonal D.j a₀ D.J hn hB hb
  rw [D.startedSmallTree_tree w y T t₀ x a] at H
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

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_ClosedErrorTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Diagram
variable {n : ℕ}

theorem finite_graph_trace_tested (J : Interaction n) (E F Es Ef : ℕ→Interaction n)
    (p : (a : ℕ)→Fin a→Fin n→ℝ) (r : (a : ℕ)→Fin a→ℝ)
    (hE : ∀a,E a=(∑b:Fin a,Matrix.diagonal (p a b)*F b)+Es a)
    (hF : ∀a,F a=J*E a-(∑b:Fin a,r a b • E b)+Ef a)
    {A R M : ℝ} {Cs Cf : ℕ→ℝ} {N L : ℕ}
    (_ : 0≤R) (_ : 0≤M)
    (hp : ∀a≤N,∀b i,|p a b i|≤A) (hr : ∀a≤N,∀b,|r a b|≤R)
    (hsn : ∀a≤N,0≤Cs a) (hfn : ∀a≤N,0≤Cf a)
    (hs : ∀a≤N,∀w:OrdinaryWord n,w.length≤L→wordBounded A w→
      |trace (matrixWord J w*Es a)|≤Cs a*M)
    (hf : ∀a≤N,∀w:OrdinaryWord n,w.length≤L→wordBounded A w→
      |trace (matrixWord J w*Ef a)|≤Cf a*M) :
    ∀a≤N,
      (∀w:OrdinaryWord n,w.length+2*a+1≤L→wordBounded A w→
        |trace (matrixWord J w*E a)|≤(errorBudget R Cs Cf a).1*M) ∧
      (∀w:OrdinaryWord n,w.length+2*a+2≤L→wordBounded A w→
        |trace (matrixWord J w*F a)|≤(errorBudget R Cs Cf a).2*M) := by
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro ha
    have hs₀ : 0≤Cs a := hsn a ha
    have hf₀ : 0≤Cf a := hfn a ha
    have hprev (b : Fin a) := ih b b.isLt (b.isLt.le.trans ha)
    have hCs (w : OrdinaryWord n) (hlen : w.length≤L) (hwb : wordBounded A w) :
        |trace (matrixWord J w*Es a)|≤Cs a*M :=
      hs a ha w hlen hwb
    have hCf (w : OrdinaryWord n) (hlen : w.length≤L) (hwb : wordBounded A w) :
        |trace (matrixWord J w*Ef a)|≤Cf a*M :=
      hf a ha w hlen hwb
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
      have hB : 0≤(errorBudget R Cs Cf b).1*M := (abs_nonneg _).trans H
      rw [Matrix.mul_smul,trace_smul,smul_eq_mul,abs_mul]
      exact ((mul_le_mul_of_nonneg_left H (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (hr a ha b) hB)).trans_eq (by ring)
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

lemma closedWordBounded_append {A : ℝ} {P Q : List (WordLetter (Fin n))}
    (hP : closedWordBounded A P) (hQ : closedWordBounded A Q) : closedWordBounded A (P++Q) := by
  intro l hl;rcases List.mem_append.mp hl with hl|hl
  · exact hP l hl
  · exact hQ l hl
lemma closedWordBounded_lift {A : ℝ} {w : OrdinaryWord n} (hw : wordBounded A w) :
    closedWordBounded A (liftWord w) := by
  intro l hl
  obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hl
  cases q with
  | diag p=>exact hw _ hq
  | noise=>trivial

lemma implicit_error_elimination (A J K E F Es Ef : Interaction n) (q : ℝ)
    (hK : K*(1-A*(J-q • 1))=1)
    (hE : E=A*F+Es) (hF : F=(J-q • 1)*E+Ef) :
    E=K*(Es+A*Ef) := by
  have he : (1-A*(J-q • 1))*E=Es+A*Ef := by
    rw [sub_mul,one_mul,mul_assoc]
    rw [hF,mul_add] at hE
    nth_rw 1 [hE]
    abel
  have hk:=congrArg (fun P:Interaction n=>K*P) he
  rw [←mul_assoc,hK,one_mul] at hk
  exact hk

theorem implicit_trace_bound (j : ℝ) (a : Fin n→ℝ) (J Es Ef : Interaction n)
    {C D A M : ℝ} {L : ℕ} (hs : TraceControl Es C) (hf : TraceControl Ef D)
    (ha : ∀i,|a i|≤A) (hw : ClosedWordTestBound j a J A M L)
    (w : OrdinaryWord n) (hlen : w.length+2≤L) (hwb : wordBounded A w) :
    |trace (matrixWord J w*((WordLetter.inverse.exactEval j a J)*(Es+Matrix.diagonal a*Ef)))|
      ≤(C+D)*M := by
  have hb₁ : closedWordBounded (n:=n) A [WordLetter.inverse] := by
    intro l hl;have hl₀:=List.mem_singleton.mp hl;subst l;trivial
  have hb₂ : closedWordBounded A [WordLetter.inverse,.diag a] := by
    intro l hl;simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
    rcases hl with rfl|rfl
    · trivial
    · exact ha
  have h₁ := hw (liftWord w++[.inverse])
    (by simpa only [liftWord,List.length_map,List.length_append,List.length_singleton] using (show w.length+1≤L by omega))
    (by rw [inverseCount_append,inverseCount_lift];simp [inverseCount]) (closedWordBounded_append (closedWordBounded_lift hwb) hb₁)
  have h₂ := hw (liftWord w++[.inverse,.diag a])
    (by simpa only [liftWord,List.length_map,List.length_append,List.length_cons,List.length_nil] using hlen)
    (by rw [inverseCount_append,inverseCount_lift];simp [inverseCount]) (closedWordBounded_append (closedWordBounded_lift hwb) hb₂)
  rw [exactWord_append,exactWord_lift] at h₁ h₂
  simp only [exactWord,matrixFactorProduct,List.map_cons,List.map_nil,
    List.prod_cons,List.prod_nil,mul_one,WordLetter.exactEval] at h₁ h₂
  have H₁:=(hs.bound (matrixWord J w*WordLetter.inverse.exactEval j a J)).trans
    (mul_le_mul_of_nonneg_left h₁ hs.nonneg)
  have H₂:=(hf.bound (matrixWord J w*WordLetter.inverse.exactEval j a J*Matrix.diagonal a)).trans
    (mul_le_mul_of_nonneg_left (by simpa only [mul_assoc,WordLetter.exactEval] using h₂) hf.nonneg)
  rw [mul_add,mul_add,trace_add]
  exact ((abs_add_le _ _).trans (add_le_add
    (by simpa only [mul_assoc] using H₁) (by simpa only [mul_assoc] using H₂))).trans_eq (by ring)

lemma ClosedWordTestBound.ordinary {j : ℝ} {a : Fin n→ℝ} {J : Interaction n}
    {A M : ℝ} {L : ℕ} (h : ClosedWordTestBound j a J A M L) : WordTestBound J A M L := by
  intro w hw hb
  have H:=h (liftWord w) (by simpa only [liftWord,List.length_map] using hw)
    (by simp) (closedWordBounded_lift hb)
  simpa only [exactWord_lift] using H

theorem closed_finite_graph_trace (j : ℝ) (a₀ : Fin n→ℝ) (J : Interaction n)
    (E F Es Ef : ℕ→Interaction n) (P Q : Interaction n) (q : ℝ)
    (p : (a : ℕ)→Fin a→Fin n→ℝ) (r : (a : ℕ)→Fin a→ℝ)
    (hE : ∀a,E a=(∑b:Fin a,Matrix.diagonal (p a b)*F b)+Es a)
    (hF : ∀a,F a=J*E a-(∑b:Fin a,r a b • E b)+Ef a)
    (hEs : Es 0=WordLetter.inverse.exactEval j a₀ J*(P+Matrix.diagonal a₀*Q))
    (hEf : Ef 0=(-q) • Es 0+Q)
    {C D A R M : ℝ} {Cs Cf : ℕ→ℝ} {N L : ℕ}
    (hP : TraceControl P C) (hQ : TraceControl Q D)
    (hR : 0≤R) (hM : 0≤M) (ha : ∀i,|a₀ i|≤A)
    (hp : ∀a≤N,∀b i,|p a b i|≤A) (hr : ∀a≤N,∀b,|r a b|≤R)
    (hs : ∀a≤N,0<a→TraceControl (Es a) (Cs a))
    (hf : ∀a≤N,0<a→TraceControl (Ef a) (Cf a))
    (hw : ClosedWordTestBound j a₀ J A M (L+2)) :
    let Bs:=fun a=>if a=0 then C+D else Cs a
    let Bf:=fun a=>if a=0 then |q| *(C+D)+D else Cf a
    ∀a≤N,
      (∀w:OrdinaryWord n,w.length+2*a+1≤L→wordBounded A w→
        |trace (matrixWord J w*E a)|≤(errorBudget R Bs Bf a).1*M) ∧
      (∀w:OrdinaryWord n,w.length+2*a+2≤L→wordBounded A w→
        |trace (matrixWord J w*F a)|≤(errorBudget R Bs Bf a).2*M) := by
  dsimp only
  have hsource (w : OrdinaryWord n) (hlen : w.length≤L) (hwb : wordBounded A w) :
      |trace (matrixWord J w*Es 0)|≤(C+D)*M := by
    rw [hEs]
    exact implicit_trace_bound j a₀ J P Q hP hQ ha hw w (by omega) hwb
  have hfield (w : OrdinaryWord n) (hlen : w.length≤L) (hwb : wordBounded A w) :
      |trace (matrixWord J w*Ef 0)|≤(|q| *(C+D)+D)*M := by
    have H₁:=hsource w hlen hwb
    have H₂:=(hQ.bound (matrixWord J w)).trans (mul_le_mul_of_nonneg_left
      (hw.ordinary w (by omega) hwb) hQ.nonneg)
    rw [hEf,mul_add,Matrix.mul_smul,trace_add,trace_smul,smul_eq_mul]
    have H₃ : |(-q)*trace (matrixWord J w*Es 0)|≤|q| *((C+D)*M) := by
      rw [abs_mul,abs_neg];exact mul_le_mul_of_nonneg_left H₁ (abs_nonneg q)
    exact ((abs_add_le _ _).trans (add_le_add H₃ H₂)).trans_eq (by ring)
  apply finite_graph_trace_tested J E F Es Ef p r hE hF hR hM hp hr
  · intro a haN;split_ifs with h
    · exact add_nonneg hP.nonneg hQ.nonneg
    · exact (hs a haN (Nat.pos_of_ne_zero h)).nonneg
  · intro a haN;split_ifs with h
    · exact add_nonneg (mul_nonneg (abs_nonneg _) (add_nonneg hP.nonneg hQ.nonneg)) hQ.nonneg
    · exact (hf a haN (Nat.pos_of_ne_zero h)).nonneg
  · intro a haN w hlen hwb
    by_cases ha0 : a=0
    · subst a;simpa only [ite_true] using hsource w hlen hwb
    · simpa only [ite_eq_right ha0] using (hs a haN (Nat.pos_of_ne_zero ha0)).bound (matrixWord J w) |>.trans
        (mul_le_mul_of_nonneg_left (hw.ordinary w (by omega) hwb) (hs a haN (Nat.pos_of_ne_zero ha0)).nonneg)
  · intro a haN w hlen hwb
    by_cases ha0 : a=0
    · subst a;simpa only [ite_true] using hfield w hlen hwb
    · simpa only [ite_eq_right ha0] using (hf a haN (Nat.pos_of_ne_zero ha0)).bound (matrixWord J w) |>.trans
        (mul_le_mul_of_nonneg_left (hw.ordinary w (by omega) hwb) (hf a haN (Nat.pos_of_ne_zero ha0)).nonneg)

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_StartedNodeTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe.OrdinaryData
open Primary Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.Tensor.Series
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]
variable (D : OrdinaryData n ι κ σ) (w y : VectorFields n)
    (T : ι→SourceTree (Fin n→ℝ)) (t₀ : ClosedTree (Fin n→ℝ)) (a₀ : Fin n→ℝ) (x : Spin n)

theorem started_derivative_error_words (P Q : Interaction n) (q : ℝ)
    (hE₀ : D.startedSourceError w y T t₀ a₀ x 0=
      WordLetter.inverse.exactEval D.j a₀ D.J*(P+Matrix.diagonal a₀*Q))
    (hF₀ : D.startedFieldError w y T t₀ a₀ x 0=
      (D.J-q • 1)*D.startedSourceError w y T t₀ a₀ x 0+Q)
    {C F A R M : ℝ} {Cs Cf : ℕ→ℝ} {N L : ℕ}
    (hP : TraceControl P C) (hQ : TraceControl Q F)
    (hR : 0≤R) (hM : 0≤M) (ha : ∀i,|a₀ i|≤A)
    (hp : ∀a≤N,∀b i,|D.auxCoefficient a b x i|≤A)
    (hr : ∀a≤N,∀b,|D.j*siteMean (D.auxCoefficient a b) x|≤R)
    (hs : ∀a≤N,0<a→TraceControl (D.startedNodeSourceError w y T x a) (Cs a))
    (hf : ∀a≤N,0<a→TraceControl (D.startedNodeFieldError w y T x a) (Cf a))
    (hw : ClosedWordTestBound D.j a₀ D.J A M (L+2)) :
    let Bs:=fun a=>if a=0 then C+F else Cs a
    let Bf:=fun a=>if a=0 then |q| *(C+F)+F else Cf a
    ∀a≤N,
      (∀v:OrdinaryWord n,v.length+2*a+1≤L→wordBounded A v→
        |trace (matrixWord D.J v*D.startedSourceError w y T t₀ a₀ x a)|≤(errorBudget R Bs Bf a).1*M) ∧
      (∀v:OrdinaryWord n,v.length+2*a+2≤L→wordBounded A v→
        |trace (matrixWord D.J v*D.startedFieldError w y T t₀ a₀ x a)|≤(errorBudget R Bs Bf a).2*M) := by
  let Es:=fun a=>if a=0 then D.startedSourceError w y T t₀ a₀ x 0 else D.startedNodeSourceError w y T x a
  let Ef:=fun a=>if a=0 then (-q) • Es 0+Q else D.startedNodeFieldError w y T x a
  apply closed_finite_graph_trace D.j a₀ D.J
    (D.startedSourceError w y T t₀ a₀ x) (D.startedFieldError w y T t₀ a₀ x)
    Es Ef P Q q (fun a b=>D.auxCoefficient a b x) (fun a b=>D.j*siteMean (D.auxCoefficient a b) x)
    _ _ _ _ hP hQ hR hM ha hp hr _ _ hw
  · intro a
    by_cases ha0:a=0
    · subst a;simp [Es]
    · rw [D.started_source_error_recursion w y T t₀ a₀ x (Nat.pos_of_ne_zero ha0)]
      simp only [Es,ite_eq_right ha0,startedNodeSourceError]
      abel
  · intro a
    by_cases ha0:a=0
    · subst a
      simp only [Ef,Es,ite_true,Finset.univ_eq_empty,Finset.sum_empty,sub_zero]
      rw [hF₀,sub_mul,smul_mul_assoc,one_mul,neg_smul]
      abel
    · rw [D.started_field_error_recursion w y T t₀ a₀ x (Nat.pos_of_ne_zero ha0)]
      simp only [Ef,ite_eq_right ha0,startedNodeFieldError]
  · simpa only [Es,ite_true] using hE₀
  · rfl
  · intro a haN ha0;simpa only [Es,ite_eq_right (by omega : a≠0)] using hs a haN ha0
  · intro a haN ha0;simpa only [Ef,ite_eq_right (by omega : a≠0)] using hf a haN ha0

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_ImplicitNode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe.OrdinaryData
open Primary Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary
open SKGap.Noncrossing.Primary.Tensor.Series
variable {n : ℕ} {κ σ : Type*} [Fintype κ] [DecidableEq κ] [Fintype σ]
variable (D : OrdinaryData n Unit κ σ)

lemma mean_implicit (F : VectorFields n) (x : Spin n) : Diagram.mean (F x)=siteMean F x := by
  simp [Diagram.mean,siteMean]

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_ImplicitTraceControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe.OrdinaryData
open Primary Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary
variable {n : ℕ} {κ σ : Type*} [Fintype κ] [DecidableEq κ] [Fintype σ]
variable (D : OrdinaryData n Unit κ σ)

omit [Fintype σ] in
lemma implicit_inverse_left (x : Spin n) (ha : ∀i,0≤D.implicitCoefficient x i)
    (hS : (1-SKGap.pathDiagonal (D.implicitCoefficient x) 1*
      (D.J-(D.j*siteMean D.implicitCoefficient x) • 1)*SKGap.pathDiagonal (D.implicitCoefficient x) 1).PosDef) :
    WordLetter.inverse.exactEval D.j (D.implicitCoefficient x) D.J*
      (1-Matrix.diagonal (D.implicitCoefficient x)*(D.J-(D.j*siteMean D.implicitCoefficient x) • 1))=1 := by
  have hu:=SKGap.ResolventIdentity.inverse_one_sub_square_mul_unit
    (SKGap.pathDiagonal (D.implicitCoefficient x) 1) (D.J-(D.j*siteMean D.implicitCoefficient x) • 1) hS.isUnit
  rw [SKGap.pathDiagonal_square ha] at hu
  have hi:=Matrix.nonsing_inv_mul _ (((1-Matrix.diagonal (D.implicitCoefficient x)*(D.J-(D.j*siteMean D.implicitCoefficient x) • 1)).isUnit_iff_isUnit_det).mp hu)
  have hq : (D.j/(n:ℝ))*(∑i,D.implicitCoefficient x i)=D.j*siteMean D.implicitCoefficient x := by
    simp only [siteMean];ring
  simpa only [WordLetter.exactEval,Fintype.card_fin,hq] using hi

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_LocalImplicitNode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Primary
variable {n : ℕ}
lemma derivativeMatrix_congr_on_flips (F G : VectorFields n) (x : Spin n)
    (hx : F x=G x) (hf : ∀i,F (flip x i)=G (flip x i)) :
    derivativeMatrix F x=derivativeMatrix G x := by
  ext i k
  simp only [derivativeMatrix,halfDiff_as_flip,hx,hf]
end SKGapCutoff.Primary

namespace SKGapCutoff.Recipe.OrdinaryData
open Primary Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary
open SKGap.Noncrossing.Primary.Tensor.Series
variable {n : ℕ} {κ σ : Type*} [Fintype κ] [DecidableEq κ] [Fintype σ]
variable (D : OrdinaryData n Unit κ σ)

lemma implicit_source_derivative_local (t : SourceTree (Fin n→ℝ)) (w y : VectorFields n) (x : Spin n)
    (hw : w x=D.sourceOf 1 (fun _=>y) x)
    (hwf : ∀i,w (flip x i)=D.sourceOf 1 (fun _=>y) (flip x i)) :
    derivativeMatrix w x=Matrix.diagonal (D.implicitCoefficient x)*derivativeMatrix y x+
      Matrix.diagonal (D.implicitPartial y x)*t.fieldMatrix D.j D.J+D.implicitSourcePrimitive t y x := by
  rw [derivativeMatrix_congr_on_flips w _ x hw hwf,D.sourceOf_derivative]
  simp only [Fintype.sum_unique,implicitCoefficient,implicitPartial,implicitSourcePrimitive,mul_sub]
  have hd : (default : Fin 1)=0 := Subsingleton.elim _ _
  rw [hd]
  abel

lemma implicit_field_derivative_local (t : SourceTree (Fin n→ℝ)) (w y : VectorFields n) (x : Spin n)
    (hw : w x=D.sourceOf 1 (fun _=>y) x)
    (hwf : ∀i,w (flip x i)=D.sourceOf 1 (fun _=>y) (flip x i))
    (hy : y x=D.fieldOf 1 (fun _=>w) (fun _=>y) x)
    (hyf : ∀i,y (flip x i)=D.fieldOf 1 (fun _=>w) (fun _=>y) (flip x i)) :
    derivativeMatrix y x=(D.J-(D.j*siteMean D.implicitCoefficient x) • 1)*derivativeMatrix w x-
      (D.j*siteMean (D.implicitPartial y) x) • t.sourceMatrix D.j D.J+D.implicitFieldPrimitive t w y x := by
  have H:=derivativeMatrix_congr_on_flips y _ x hy hyf
  have HW:=derivativeMatrix_congr_on_flips w _ x hw hwf
  rw [D.fieldOf_derivative,←HW] at H
  simp only [Fintype.sum_unique] at H
  rw [H]
  simp only [implicitCoefficient,implicitPartial,implicitFieldPrimitive,neg_smul,smul_sub,
    sub_mul,smul_mul_assoc,one_mul]
  abel
theorem implicit_error_solved_local (t : SourceTree (Fin n→ℝ)) (w y : VectorFields n)
    (x : Spin n)
    (hw : w x=D.sourceOf 1 (fun _=>y) x)
    (hwf : ∀i,w (flip x i)=D.sourceOf 1 (fun _=>y) (flip x i))
    (hy : y x=D.fieldOf 1 (fun _=>w) (fun _=>y) x)
    (hyf : ∀i,y (flip x i)=D.fieldOf 1 (fun _=>w) (fun _=>y) (flip x i))
    (hK : WordLetter.inverse.exactEval D.j (D.implicitCoefficient x) D.J*
      (1-Matrix.diagonal (D.implicitCoefficient x)*(D.J-(D.j*siteMean D.implicitCoefficient x) • 1))=1) :
    derivativeMatrix w x-D.implicitRetainedSource t y x=
      WordLetter.inverse.exactEval D.j (D.implicitCoefficient x) D.J*
        (D.implicitSourcePrimitive t y x+Matrix.diagonal (D.implicitCoefficient x)*D.implicitFieldPrimitive t w y x) ∧
    derivativeMatrix y x-D.implicitRetainedField t y x=
      (D.J-(D.j*siteMean D.implicitCoefficient x) • 1)*
        (derivativeMatrix w x-D.implicitRetainedSource t y x)+D.implicitFieldPrimitive t w y x := by
  have hsource:=D.implicit_source_derivative_local t w y x hw hwf
  have hfield:=D.implicit_field_derivative_local t w y x hw hwf hy hyf
  have hs : derivativeMatrix w x=Matrix.diagonal (D.implicitCoefficient x)*derivativeMatrix y x+
      (Matrix.diagonal (D.implicitPartial y x)*t.fieldMatrix D.j D.J+D.implicitSourcePrimitive t y x) := by rw [hsource];abel
  have hf : derivativeMatrix y x=(D.J-(D.j*siteMean D.implicitCoefficient x) • 1)*derivativeMatrix w x+
      (-(D.j*siteMean (D.implicitPartial y) x) • t.sourceMatrix D.j D.J+D.implicitFieldPrimitive t w y x) := by
    rw [hfield];simp only [neg_smul];abel
  have H:=implicit_error_elimination _ _ _ _ _ _ _ _ hK hs hf
  constructor
  · rw [H,implicitRetainedSource,GradedWords.matrixValue_implicitSource,mean_implicit]
    simp only [mul_add,mul_sub,neg_smul,mul_neg,mul_smul_comm]
    abel
  · rw [hfield,implicitRetainedField,GradedWords.matrixValue_implicitField,mean_implicit,mean_implicit]
    change _-((D.J-(D.j*siteMean D.implicitCoefficient x) • 1)*D.implicitRetainedSource t y x-
      (D.j*siteMean (D.implicitPartial y) x) • t.sourceMatrix D.j D.J)=_
    rw [mul_sub]
    abel

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_LocalStartedImplicit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe.OrdinaryData
open Primary Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.Tensor.Series
variable {n : ℕ} {ι κ σ κ₀ σ₀ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]
variable [Fintype κ₀] [DecidableEq κ₀] [Fintype σ₀]
variable (D : OrdinaryData n ι κ σ) (I : OrdinaryData n Unit κ₀ σ₀)
variable (w y : VectorFields n) (T : ι→SourceTree (Fin n→ℝ)) (t : SourceTree (Fin n→ℝ))

lemma started_implicit_initial_errors_local (hj : D.j=I.j) (hJ : D.J=I.J)
    (x : Spin n)
    (hW : w x=I.sourceOf 1 (fun _=>y) x)
    (hWf : ∀i,w (flip x i)=I.sourceOf 1 (fun _=>y) (flip x i))
    (hY : y x=I.fieldOf 1 (fun _=>w) (fun _=>y) x)
    (hYf : ∀i,y (flip x i)=I.fieldOf 1 (fun _=>w) (fun _=>y) (flip x i))
    (ha : ∀i,0≤I.implicitCoefficient x i)
    (hS : (1-SKGap.pathDiagonal (I.implicitCoefficient x) 1*
      (I.J-(I.j*siteMean I.implicitCoefficient x) • 1)*SKGap.pathDiagonal (I.implicitCoefficient x) 1).PosDef) :
    let t₀:=ClosedTree.implicit (I.implicitPartial y x) t
    let a₀:=I.implicitCoefficient x
    D.startedSourceError w y T t₀ a₀ x 0=
      WordLetter.inverse.exactEval D.j a₀ D.J*
        (I.implicitSourcePrimitive t y x+Matrix.diagonal a₀*I.implicitFieldPrimitive t w y x) ∧
    D.startedFieldError w y T t₀ a₀ x 0=
      (D.J-(I.j*siteMean I.implicitCoefficient x) • 1)*D.startedSourceError w y T t₀ a₀ x 0+
        I.implicitFieldPrimitive t w y x := by
  have H:=I.implicit_error_solved_local t w y x hW hWf hY hYf (I.implicit_inverse_left x ha hS)
  dsimp only
  simp only [startedSourceError_zero,startedFieldError_zero,hj,hJ,ClosedTree.sourceMatrix,
    ClosedTree.fieldMatrix,ClosedTree.words]
  exact H

theorem implicit_started_error_words_local (hj : D.j=I.j) (hJ : D.J=I.J)
    (x : Spin n)
    (hW : w x=I.sourceOf 1 (fun _=>y) x)
    (hWf : ∀i,w (flip x i)=I.sourceOf 1 (fun _=>y) (flip x i))
    (hY : y x=I.fieldOf 1 (fun _=>w) (fun _=>y) x)
    (hYf : ∀i,y (flip x i)=I.fieldOf 1 (fun _=>w) (fun _=>y) (flip x i))
    (ha0 : ∀i,0≤I.implicitCoefficient x i)
    (hS : (1-SKGap.pathDiagonal (I.implicitCoefficient x) 1*
      (I.J-(I.j*siteMean I.implicitCoefficient x) • 1)*SKGap.pathDiagonal (I.implicitCoefficient x) 1).PosDef)
    {C F A R M : ℝ} {Cs Cf : ℕ→ℝ} {N L : ℕ}
    (hP : TraceControl (I.implicitSourcePrimitive t y x) C)
    (hQ : TraceControl (I.implicitFieldPrimitive t w y x) F)
    (hR : 0≤R) (hM : 0≤M) (ha : ∀i,|I.implicitCoefficient x i|≤A)
    (hp : ∀a≤N,∀b i,|D.auxCoefficient a b x i|≤A)
    (hr : ∀a≤N,∀b,|D.j*siteMean (D.auxCoefficient a b) x|≤R)
    (hs : ∀a≤N,0<a→TraceControl (D.startedNodeSourceError w y T x a) (Cs a))
    (hf : ∀a≤N,0<a→TraceControl (D.startedNodeFieldError w y T x a) (Cf a))
    (hw : ClosedWordTestBound D.j (I.implicitCoefficient x) D.J A M (L+2)) :
    let t₀:=ClosedTree.implicit (I.implicitPartial y x) t
    let a₀:=I.implicitCoefficient x
    let q:=I.j*siteMean I.implicitCoefficient x
    let Bs:=fun a=>if a=0 then C+F else Cs a
    let Bf:=fun a=>if a=0 then |q| *(C+F)+F else Cf a
    ∀a≤N,
      (∀v:OrdinaryWord n,v.length+2*a+1≤L→wordBounded A v→
        |trace (matrixWord D.J v*D.startedSourceError w y T t₀ a₀ x a)|≤(errorBudget R Bs Bf a).1*M) ∧
      (∀v:OrdinaryWord n,v.length+2*a+2≤L→wordBounded A v→
        |trace (matrixWord D.J v*D.startedFieldError w y T t₀ a₀ x a)|≤(errorBudget R Bs Bf a).2*M) := by
  obtain ⟨HE,HF⟩:=D.started_implicit_initial_errors_local I w y T t hj hJ x hW hWf hY hYf ha0 hS
  exact D.started_derivative_error_words w y T _ _ x
    (I.implicitSourcePrimitive t y x) (I.implicitFieldPrimitive t w y x)
    (I.j*siteMean I.implicitCoefficient x) HE HF hP hQ hR hM ha hp hr hs hf hw

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LocalStartedDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe.OrdinaryData
open Primary Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.Tensor.Series
open SKGap.Noncrossing.ClosedMarked
variable {n : ℕ} {ι κ σ κ₀ σ₀ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]
variable [Fintype κ₀] [DecidableEq κ₀] [Fintype σ₀]
variable (D : OrdinaryData n ι κ σ) (I : OrdinaryData n Unit κ₀ σ₀)
variable (w y : VectorFields n) (T : ι→SourceTree (Fin n→ℝ)) (t : SourceTree (Fin n→ℝ))

theorem implicit_started_diagonal_local_oai (hj : D.j=I.j) (hJ : D.J=I.J)
    (x : Spin n)
    (hW : w x=I.sourceOf 1 (fun _=>y) x)
    (hWf : ∀i,w (flip x i)=I.sourceOf 1 (fun _=>y) (flip x i))
    (hY : y x=I.fieldOf 1 (fun _=>w) (fun _=>y) x)
    (hYf : ∀i,y (flip x i)=I.fieldOf 1 (fun _=>w) (fun _=>y) (flip x i)) (hn : 0<n)
    (ha0 : ∀i,0≤I.implicitCoefficient x i)
    (hS : (1-SKGap.pathDiagonal (I.implicitCoefficient x) 1*
      (I.J-(I.j*siteMean I.implicitCoefficient x) • 1)*SKGap.pathDiagonal (I.implicitCoefficient x) 1).PosDef)
    {C F A R M B : ℝ} {Cs Cf : ℕ→ℝ} {N : ℕ}
    (hP : TraceControl (I.implicitSourcePrimitive t y x) C)
    (hQ : TraceControl (I.implicitFieldPrimitive t w y x) F)
    (hR : 0≤R) (hM : 0≤M) (hB : 0≤B) (hA : 1≤A) (ha : ∀i,|I.implicitCoefficient x i|≤A)
    (hp : ∀a≤N,∀b i,|D.auxCoefficient a b x i|≤A)
    (hr : ∀a≤N,∀b,|D.j*siteMean (D.auxCoefficient a b) x|≤R)
    (hs : ∀a≤N,0<a→TraceControl (D.startedNodeSourceError w y T x a) (Cs a))
    (hf : ∀a≤N,0<a→TraceControl (D.startedNodeFieldError w y T x a) (Cf a))
    (hw : ClosedWordTestBound D.j (I.implicitCoefficient x) D.J A M (2*N+5))
    (hd : ∀a≤N,∀d:Fin n→ℝ,(∀i,|d i|≤1)→∀P∈[
        ((D.startedSmallTree w y T (.implicit (I.implicitPartial y x) t) x a).marked D.j (I.implicitCoefficient x)).1,
        ((D.startedSmallTree w y T (.implicit (I.implicitPartial y x) t) x a).marked D.j (I.implicitCoefficient x)).2],∀v∈P,
      diagonalSeminorm (exactWord D.j (I.implicitCoefficient x) (v.2.diagnostic d) D.J-
        Matrix.diagonal (wordPrediction D.j (I.implicitCoefficient x) 1 (v.2.diagnostic d)))≤B) :
    let q:=I.j*siteMean I.implicitCoefficient x
    let Bs:=fun a=>if a=0 then C+F else Cs a
    let Bf:=fun a=>if a=0 then |q| *(C+F)+F else Cf a
    ∀a≤N,
      (∑i,|derivativeMatrix (D.startedSource w y a) x i i|)≤
        ((D.startedSmallTree w y T (.implicit (I.implicitPartial y x) t) x a).marked D.j (I.implicitCoefficient x)).1.budget*B+
        (errorBudget R Bs Bf a).1*M ∧
      (∑i,|derivativeMatrix (D.startedAuxiliary w y a) x i i|)≤
        ((D.startedSmallTree w y T (.implicit (I.implicitPartial y x) t) x a).marked D.j (I.implicitCoefficient x)).2.budget*B+
        (errorBudget R Bs Bf a).2*M := by
  have H:=D.implicit_started_error_words_local I w y T t hj hJ x hW hWf hY hYf ha0 hS hP hQ hR hM ha hp hr hs hf
    (L:=2*N+3) (by simpa only [Nat.add_assoc] using hw)
  dsimp only at H ⊢
  intro a haN
  let t₀:SmallTree n:=.implicit (I.implicitPartial y x) t
  let a₀:=I.implicitCoefficient x
  have hret:=D.started_retained_diagonal w y T t₀ a₀ x a hn hB (hd a haN)
  have hword (d : Fin n→ℝ) (hd' : ∀i,|d i|≤1) : wordBounded A [.diag d] := by
    intro l hl
    have he:l=Letter.diag d:=List.mem_singleton.mp hl
    subst l
    exact fun i=>(hd' i).trans hA
  have herrorS : (∑i,|D.startedSourceError w y T t₀.tree a₀ x a i i|)≤
      (errorBudget R (fun a=>if a=0 then C+F else Cs a)
        (fun a=>if a=0 then |I.j*siteMean I.implicitCoefficient x| *(C+F)+F else Cf a) a).1*M := by
    apply diagonal_abs_sum_of_tests
    intro d hd'
    have HH:=(H a haN).1 [.diag d] (by simp only [List.length_singleton];omega) (hword d hd')
    simpa [matrixWord,matrixLetter,t₀,a₀,SmallTree.tree] using HH
  have herrorF : (∑i,|D.startedFieldError w y T t₀.tree a₀ x a i i|)≤
      (errorBudget R (fun a=>if a=0 then C+F else Cs a)
        (fun a=>if a=0 then |I.j*siteMean I.implicitCoefficient x| *(C+F)+F else Cf a) a).2*M := by
    apply diagonal_abs_sum_of_tests
    intro d hd'
    have HH:=(H a haN).2 [.diag d] (by simp only [List.length_singleton];omega) (hword d hd')
    simpa [matrixWord,matrixLetter,t₀,a₀,SmallTree.tree] using HH
  have hadd (Q R : Interaction n) : (∑i,|Q i i|)≤(∑i,|R i i|)+(∑i,|(Q-R) i i|) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    simpa only [Matrix.sub_apply,add_sub_cancel] using abs_add_le (R i i) (Q i i-R i i)
  exact ⟨(hadd _ _).trans (add_le_add hret.1 herrorS),(hadd _ _).trans (add_le_add hret.2 herrorF)⟩

end SKGapCutoff.Recipe.OrdinaryData

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.SKGapCutoff.Recipe.OrdinaryData.implicit_started_diagonal_local_oai.{u_1, u_2, u_3, u_4, u_5} := @OAI.SKGapCutoff.Recipe.OrdinaryData.implicit_started_diagonal_local_oai.{u_1, u_2, u_3, u_4, u_5}
