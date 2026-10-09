-- Prove2me | solution 1 for OAI.Erdos3.physicalBoxResidual_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T17:29:34.607781+00:00
-- url     : https://prove2.me/submissions/6883d0f4-ebc6-4e8f-af84-5a679981be37

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteProductCellMean
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finite_cell_energy_aggregate {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
    (p : FiniteProbabilityWeights X) (C : X → A) (e : X → ℝ) {E : ℝ}
    (he : ∀ a, finiteCellMean p C (fun x => e x ^ 2) a ≤ E * (finiteCellWeights p C).weight a) :
    p.mean (fun x => e x ^ 2) ≤ E := by
  rw [← finiteCellMean_sum p C]
  calc
    _ ≤ ∑ a, E * (finiteCellWeights p C).weight a := Finset.sum_le_sum (fun a _ => he a)
    _ = E := by rw [← Finset.mul_sum, (finiteCellWeights p C).total, mul_one]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem uniform_subtype_mean {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) [DecidablePred P] (f : Ω → ℝ) :
    (FiniteProbabilityWeights.uniform Ω).mean (fun z => if P z then f z else 0) =
      (Fintype.card {z // P z} : ℝ) / Fintype.card Ω * (𝔼 z : {z // P z}, f z.val) := by
  classical
  rw [FiniteProbabilityWeights.uniform_mean, Fintype.expect_eq_sum_div_card]
  have hsum : (∑ z, if P z then f z else 0) = ∑ z : {z // P z}, f z.val := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) f
  rw [hsum, ← Fintype.card_mul_expect (fun z : {z // P z} => f z.val)]
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finiteCellMean_uniform {X A : Type*} [Fintype X] [Nonempty X] [DecidableEq A]
    (C : X → A) (f : X → ℝ) (a : A) :
    finiteCellMean (FiniteProbabilityWeights.uniform X) C f a =
      (Fintype.card {x // C x = a} : ℝ) / Fintype.card X *
        (𝔼 x : {x // C x = a}, f x.val) :=
  uniform_subtype_mean (fun x => C x = a) f

theorem finiteCellWeights_uniform {X A : Type*}
    [Fintype X] [Nonempty X] [Fintype A] [DecidableEq A]
    (C : X → A) (a : A) :
    (finiteCellWeights (FiniteProbabilityWeights.uniform X) C).weight a =
      (Fintype.card {x // C x = a} : ℝ) / Fintype.card X := by
  change finiteCellMean (FiniteProbabilityWeights.uniform X) C (fun _ => 1) a = _
  rw [finiteCellMean_uniform]
  by_cases h : Nonempty {x // C x = a}
  · let : Nonempty {x // C x = a} := h
    simp
  · let : IsEmpty {x // C x = a} := not_nonempty_iff.mp h
    simp

theorem finiteCellMean_uniform_weighted {X A : Type*}
    [Fintype X] [Nonempty X] [Fintype A] [DecidableEq A]
    (C : X → A) (f : X → ℝ) (a : A) :
    finiteCellMean (FiniteProbabilityWeights.uniform X) C f a =
      (finiteCellWeights (FiniteProbabilityWeights.uniform X) C).weight a *
        (𝔼 x : {x // C x = a}, f x.val) := by
  rw [finiteCellWeights_uniform, finiteCellMean_uniform]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {X T A B : Type*} [Fintype X] [Fintype T] [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalCellResidual
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem physical_cell_residual_energy {X A ι σ : Type*}
    [Fintype X] [Nonempty X] [Fintype A] [DecidableEq A]
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (C : X → A) (c : A) (e : X → ℝ)
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (b : ℕ) (f : (σ → ℤ) → ℝ) (eta : ℝ)
    (hcontrol : ResiduePhysicalTruncationControl lo N M a hne q b f eta)
    (E : {x // C x = c} ≃ IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (M : ℤ)) a)
    (he : ∀ x : {x // C x = c}, e x.val =
      f (fun k => (E x k).val) - residuePhysicalTruncation lo N M a hne q b f (fun k => (E x k).val)) :
    finiteCellMean (FiniteProbabilityWeights.uniform X) C (fun x => e x ^ 2) c ≤
      (1 + eta * residueTruncationCap ι b eta ^ 2) * (finiteCellWeights (FiniteProbabilityWeights.uniform X) C).weight c := by
  have hmean := Fintype.expect_equiv E (fun x => e x.val ^ 2)
    (fun z => (f (fun k => (z k).val) - residuePhysicalTruncation lo N M a hne q b f
      (fun k => (z k).val)) ^ 2) (fun x => by rw [he x])
  rw [finiteCellMean_uniform_weighted, hmean]
  exact (mul_le_mul_of_nonneg_left hcontrol.2.1
    ((finiteCellWeights (FiniteProbabilityWeights.uniform X) C).nonneg c)).trans_eq (mul_comm _ _)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalBoxControl
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I ι : Type*} [Fintype I] [DecidableEq I] [Fintype ι] [DecidableEq ι]

theorem physicalBoxResidual_on_cell (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ j, NeZero (q j)] (b : ℕ) (f : (I → ℤ) → ℝ)
    (c : ∀ i, (P i).Label) (x : {x : translatedIntegerBox lo N // physicalBoxCell lo N P x = c}) :
    physicalBoxResidual lo N P hpos q b f x.val.val = f x.val.val -
      residuePhysicalTruncation (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q b f x.val.val := by
  simp only [physicalBoxResidual, if_pos x.val.property,
    physicalBoxTruncation, dif_pos x.val.property]
  rw [x.property]

theorem physicalBoxResidual_cell_energy (lo : I → ℤ) (N : I → ℕ)
    [Nonempty (translatedIntegerBox lo N)]
    (P : ∀ i, FiniteProgressionPartition (N i)) (hstep : ∀ i c, (P i).step c = 1)
    (hpos : ∀ i c, 0 < (P i).length c) (q : ι → ℕ) [∀ j, NeZero (q j)]
    (b : ℕ) (f : (I → ℤ) → ℝ) (eta : ℝ) (c : ∀ i, (P i).Label)
    (hc : ResiduePhysicalTruncationControl (fun i => intervalCellLower (lo i) (P i) (c i))
      (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q b f eta) :
    finiteCellMean (FiniteProbabilityWeights.uniform (translatedIntegerBox lo N)) (physicalBoxCell lo N P)
      (fun x => physicalBoxResidual lo N P hpos q b f x.val ^ 2) c ≤
      (1 + eta * residueTruncationCap ι b eta ^ 2) *
        (finiteCellWeights (FiniteProbabilityWeights.uniform (translatedIntegerBox lo N)) (physicalBoxCell lo N P)).weight c := by
  exact physical_cell_residual_energy (physicalBoxCell lo N P) c
    (fun x => physicalBoxResidual lo N P hpos q b f x.val) _ _ 1 (fun _ => 0)
    (physicalBoxCell_nonempty lo N P hpos c) q b f eta hc (physicalBoxCellEquiv lo N P hstep hpos c)
    (physicalBoxResidual_on_cell lo N P hpos q b f c)

theorem physicalBoxResidual_energy (lo : I → ℤ) (N : I → ℕ)
    [Nonempty (translatedIntegerBox lo N)]
    (P : ∀ i, FiniteProgressionPartition (N i)) (hstep : ∀ i c, (P i).step c = 1)
    (hpos : ∀ i c, 0 < (P i).length c) (q : ι → ℕ) [∀ j, NeZero (q j)]
    (b : ℕ) (f : (I → ℤ) → ℝ) (eta : ℝ)
    (hc : ∀ c : (∀ i, (P i).Label), ResiduePhysicalTruncationControl (fun i => intervalCellLower (lo i) (P i) (c i))
      (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q b f eta) :
    (FiniteProbabilityWeights.uniform (translatedIntegerBox lo N)).mean
      (fun x => physicalBoxResidual lo N P hpos q b f x.val ^ 2) ≤
      1 + eta * residueTruncationCap ι b eta ^ 2 := by
  exact finite_cell_energy_aggregate (FiniteProbabilityWeights.uniform (translatedIntegerBox lo N))
    (physicalBoxCell lo N P) (fun x => physicalBoxResidual lo N P hpos q b f x.val)
    (fun c => physicalBoxResidual_cell_energy lo N P hstep hpos q b f eta c (hc c))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.physicalBoxResidual_energy.{u_1, u_2} := @OAI.Erdos3.physicalBoxResidual_energy.{u_1, u_2}
