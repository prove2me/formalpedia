-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank.actualRank_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:41:48.937861+00:00
-- url     : https://prove2.me/submissions/4b128ae3-4df6-41d5-8663-19ea66fc0dd9

import Mathlib
import Definitions.Def_OAIQ081S107
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutNumerator_centered_rationalDefect_rank_relative
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProducedMatrix_literalHead_rank
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutRank_blocks_data_total_rank_le

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_MulticolorTypes
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Multicolor universal types and consistent incidence slots

The number `r` of colors is an explicit natural parameter throughout. No
finiteness instance or cardinality identity treats it as a fixed constant.
The joint fiber uses a head color different from the selected slot color,
as required by Sections 3.1 and 3.4 of the subexponential construction.
-/

namespace SubexponentialSAT.MulticolorTypes

variable {r Q Δ : ℕ}

theorem card_joint_le_side (t : Fin Q) (g : Fin r) (i : Fin Δ) :
    Fintype.card (Joint t g i) ≤ Fintype.card (Side (Δ := Δ) t g) :=
  Fintype.card_le_of_injective (fun u : Joint t g i => (⟨u.val, u.property.1⟩ : Side t g))
    (fun _ _ h => Subtype.ext (congrArg (fun z : Side (Δ := Δ) t g => z.val) h))

end SubexponentialSAT.MulticolorTypes

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutRank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Rational row-space bounds for literal integer constraint families. -/

namespace SubexponentialSAT.SqrtLog.LayoutRank

open scoped BigOperators
open Module LayoutPullback LayoutExactBuckets LayoutRowSelection

variable {J I V : Type*} [Fintype J] [Fintype I] [Fintype V]

theorem rowRank_eq_matrix_rank (C : J → V → ℤ) :
    rowRank C = Matrix.rank (rationalRows C : Matrix J V ℚ) := by
  unfold rowRank rowSpace
  exact (Matrix.rank_eq_finrank_span_row (rationalRows C : Matrix J V ℚ)).symm

variable [DecidableEq V]

omit [Fintype J] in
omit [Fintype V] in
theorem rowSpace_pullback (owner : I → V) (C : J → I → ℤ) :
    rowSpace (pulledConstraints owner C) = (rowSpace C).map (rowLinear owner) := by
  rw [rowSpace, rowSpace, LinearMap.map_span, ← Set.range_comp]
  apply congrArg (Submodule.span ℚ)
  apply congrArg Set.range
  funext j v
  exact row_map (Int.castRingHom ℚ) owner (C j) v

omit [Fintype J] in
omit [Fintype V] in
/-- Literal incidence pullback never increases rational constraint rank. -/
theorem rowRank_pullback_le (owner : I → V) (C : J → I → ℤ) :
    rowRank (pulledConstraints owner C) ≤ rowRank C := by
  unfold rowRank
  rw [rowSpace_pullback]
  exact Submodule.finrank_map_le _ _

omit [Fintype J] [Fintype V] [DecidableEq V] in
theorem rowSpace_reindex {K : Type*} [Fintype K] (C : J → V → ℤ)
    (e : K → J) (he : Function.Surjective e) :
    rowSpace (fun k => C (e k)) = rowSpace C := by
  unfold rowSpace
  congr 1
  exact he.range_comp (rationalRows C)

omit [Fintype J] [Fintype V] [DecidableEq V] in
theorem rowRank_reindex {K : Type*} [Fintype K] (C : J → V → ℤ)
    (e : K → J) (he : Function.Surjective e) :
    rowRank (fun k => C (e k)) = rowRank C := by
  unfold rowRank
  rw [rowSpace_reindex C e he]

end SubexponentialSAT.SqrtLog.LayoutRank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProducedMatrixRank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Selecting columns in their physical order cannot increase the rational
rank. The map may omit or repeat columns; no runtime permutation is assumed. -/
namespace SubexponentialSAT.SqrtLog.LayoutRank
open Module LayoutExactBuckets LayoutRowSelection

variable {J K V W : Type*} [Fintype J] [Fintype K] [Fintype V] [Fintype W]

omit [Fintype J] [Fintype V] [Fintype W] in
theorem rowSpace_columns (C : J → V → ℤ) (e : W → V) :
    rowSpace (fun j w => C j (e w)) = (rowSpace C).map (columnSelection e) := by
  rw [rowSpace,rowSpace,LinearMap.map_span,←Set.range_comp]
  rfl

omit [Fintype J] [Fintype W] in
theorem rowRank_columns_le (C : J → V → ℤ) (e : W → V) :
    rowRank (fun j w => C j (e w)) ≤ rowRank C := by
  unfold rowRank
  rw [rowSpace_columns]
  exact Submodule.finrank_map_le _ _

end SubexponentialSAT.SqrtLog.LayoutRank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutRankCounts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Disjoint head counts and the single total uncovered-coordinate budget. -/

namespace SubexponentialSAT.SqrtLog.LayoutRank

open scoped BigOperators
open SubexponentialSAT.MulticolorTypes

variable {I U G : Type*} [Fintype I] [Fintype U] [Fintype G]
variable [DecidableEq I] [DecidableEq G]

omit [DecidableEq I] in
theorem sum_card_heads (head : I → G) :
    (∑ g, Fintype.card {i : I // head i = g}) = Fintype.card I := by
  simpa using Fintype.sum_fiberwise head (fun _ : I => (1 : ℕ))

variable {b : ℕ} {label : I → U}

/-- Complete joint fibers occupy disjoint subsets of the universal heads.
There is a single ambient block cardinality, not one per color. -/
theorem sum_card_joint_le {r Q Δ : ℕ} (t : Fin Q) (i : Fin Δ) :
    (∑ g : Fin r, Fintype.card (Joint t g i)) ≤
      Fintype.card (UniversalType r Q Δ) := by
  calc
    _ ≤ ∑ g : Fin r, Fintype.card (Side (Δ := Δ) t g) :=
      Finset.sum_le_sum (fun g _ => card_joint_le_side t g i)
    _ = _ := sum_card_heads (fun u : UniversalType r Q Δ => u.head t)

end SubexponentialSAT.SqrtLog.LayoutRank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutRankBlocks
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Rank accumulation for the concrete complete-block layout and its pullback. -/

namespace SubexponentialSAT.SqrtLog.LayoutRank

open scoped BigOperators
open SubexponentialSAT.MulticolorTypes LayoutPullback LayoutExactBuckets

variable {U I V F G O : Type*}
variable [Fintype U] [DecidableEq U] [Fintype I] [DecidableEq I]
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [CommRing O]
variable {Q R b : ℕ} {label : I → U}

omit [Fintype G] in
theorem blocks_data_rank_eq
    (C : Layout.Data (O := O) (G := G) (id : U → U) (id : U → U) Q R)
    (P : SubexponentialSAT.BlockPacking.CompleteBlocks label b) (factor : I → F)
    (color : F → Fin Q → G)
    (hcolor : ∀ i t, C.color (label i) t = color (factor i) t)
    (t : Fin Q) (g : G) :
    rowRank ((LayoutBlocks.data C P factor color hcolor).constraints t g) =
      rowRank (LayoutBlocks.constraints C P t g) := by
  change rowRank (fun j => LayoutBlocks.constraints C P t g
    ((Fintype.equivFin (LayoutBlocks.RowIndex C P t g)).symm j)) = _
  exact rowRank_reindex _ _ (Equiv.surjective _)

end SubexponentialSAT.SqrtLog.LayoutRank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutRankUniversal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual universal spectral bound, summed once over all heads. -/

namespace SubexponentialSAT.SqrtLog.LayoutRank

open scoped BigOperators
open Module Matrix
open SubexponentialSAT.MulticolorTypes LayoutScaledMatrices

variable {r Q : ℕ}

theorem universal_constraints_rank_le (A R : ℕ) (t : Fin Q) (g : Fin r) :
    rowRank (LayoutUniversal.constraints A R t g) ≤
      finrank ℚ (LinearMap.range (LayoutNumerator.rationalDefect (0 : Fin 1) t g A R).mulVecLin) := by
  calc
    _ ≤ rowRank (clearedDefect (LayoutNumerator.denominator R)
        (LayoutNumerator.joint (0 : Fin 1) t g A R)) := rowRank_pullback_le _ _
    _ = _ := by
      change rowRank (fun i j =>
        (clearedDefect (LayoutNumerator.denominator R)
          (LayoutNumerator.joint (0 : Fin 1) t g A R)) i j) = _
      rw [rowRank_eq_matrix_rank]
      rfl

theorem universal_centered_rank_relative (R : ℕ) (t : Fin Q) (g : Fin r)
    (ε : ℚ) (hr : 2 ≤ r) (hQ : 2 ≤ Q) (hR : 4 ≤ R) (hsize : 4 * R ≤ Q)
    (hε : 0 < ε)
    (hwidth : 32 * ((Q - 1 : ℕ) : ℝ) * Real.log (2 / (ε : ℝ)) ≤ (R : ℝ) ^ 2) :
    (rowRank (LayoutUniversal.constraints
      (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R t g) : ℚ) ≤
        ε * Fintype.card (Joint t g (0 : Fin 1)) := by
  exact le_trans (by exact_mod_cast (universal_constraints_rank_le
    (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R t g))
      (LayoutNumerator.centered_rationalDefect_rank_relative t g 0 R ε
        hr hQ hR hsize hε hwidth)

variable {O : Type*} [CommRing O] {node : Fin Q → O}

theorem universal_data_rank_eq (A R : ℕ) (denom : Oˣ)
    (hdenom : (denom : O) = (LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node) (t : Fin Q) (g : Fin r) :
    rowRank ((LayoutUniversal.data A R denom hdenom units).constraints t g) =
      rowRank (LayoutUniversal.constraints A R t g) := by
  change rowRank (fun j => LayoutUniversal.constraints A R t g
    ((Fintype.equivFin (Joint t g (0 : Fin 1))).symm j)) = _
  exact rowRank_reindex _ _ (Equiv.surjective _)

/-- The sum over heads costs one ambient universal block, not r blocks. -/
theorem universal_total_rank_le (R : ℕ) (denom : Oˣ)
    (hdenom : (denom : O) = (LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node) (t : Fin Q)
    (ε : ℚ) (hr : 2 ≤ r) (hQ : 2 ≤ Q) (hR : 4 ≤ R) (hsize : 4 * R ≤ Q)
    (hε : 0 < ε)
    (hwidth : 32 * ((Q - 1 : ℕ) : ℝ) * Real.log (2 / (ε : ℝ)) ≤ (R : ℝ) ^ 2) :
    (∑ g : Fin r, (rowRank ((LayoutUniversal.data (r := r)
      (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R denom hdenom units).constraints t g) : ℚ)) ≤
        ε * Fintype.card (UniversalType r Q 1) := by
  simp_rw [universal_data_rank_eq]
  calc
    _ ≤ ∑ g : Fin r, ε * (Fintype.card (Joint t g (0 : Fin 1)) : ℚ) := by
      apply Finset.sum_le_sum
      intro g _
      exact universal_centered_rank_relative R t g ε hr hQ hR hsize hε hwidth
    _ = ε * ∑ g : Fin r, (Fintype.card (Joint t g (0 : Fin 1)) : ℚ) := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast sum_card_joint_le t (0 : Fin 1)) hε.le

end SubexponentialSAT.SqrtLog.LayoutRank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProducedMatrix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual integer entry program is a literal owner-fiber sum. Restricting
its columns to the emitted head IDs has exactly the canonical pulled row span,
up to harmless column omission/repetition. All incidence rows are retained. -/
namespace SubexponentialSAT.SqrtLog.LayoutProducedMatrix
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LayoutPullback LayoutExactBuckets LayoutProgram

variable {r Q : ℕ} {I V O : Type*}
variable [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] [CommRing O]
variable {node : Fin Q → O}

theorem selected_literal_rank_le {K : Type*} [Fintype K]
    (P : PackingData I (UniversalType r Q 1)) (owner : I → V)
    (head : Fin Q → V → Fin r)
    (hhead : ∀ i t,(P.label i).head t=head t (owner i))
    (A R : ℕ) (denom : Oˣ)
    (hdenom : (denom : O)=(LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node) (t : Fin Q) (g : Fin r)
    (selected : K → {v : V // head t v=g}) :
    LayoutRank.rowRank (fun j k=>literalMatrix P owner A R t j (selected k).val) ≤
    LayoutRank.rowRank (pulledConstraints (headOwner P owner head hhead t g)
      (LayoutBlocks.constraints (LayoutUniversal.data A R denom hdenom units)
        P.completeBlocks t g)) := by
  have h := LayoutRank.rowRank_columns_le
    (fun j (v : {v : V // head t v=g})=>literalMatrix P owner A R t j v.val) selected
  rw [literalHead_rank P owner head hhead A R denom hdenom units t g] at h
  exact h

end SubexponentialSAT.SqrtLog.LayoutProducedMatrix

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProducedMatrixNatural
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Natural-address interface for the produced row-major matrix. Row indices
are incidence-plan positions; columns are the emitted original variable IDs. -/
namespace SubexponentialSAT.SqrtLog.LayoutProducedMatrix
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LayoutExactBuckets LayoutProgram

variable {r Q D N : ℕ} {O : Type*} [CommRing O] {node : Fin Q → O}

theorem selected_nat_rank_le
    (P : PackingData (Fin D) (UniversalType r Q 1)) (owner : Fin D → Fin N)
    (head : Fin Q → Fin N → Fin r)
    (hhead : ∀ i t,(P.label i).head t=head t (owner i))
    (A R : ℕ) (denom : Oˣ)
    (hdenom : (denom : O)=(LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node) (t : Fin Q) (g : Fin r)
    (js : List ℕ) (hjs : ∀ v∈js,v < N)
    (hjshead : ∀ v (hv : v∈js),head t ⟨v,hjs v hv⟩=g) :
    LayoutRank.rowRank (fun (j : Fin D) (i : Fin js.length)=>
      literalNat P owner A R t j.val (js.get i)) ≤
    LayoutRank.rowRank (pulledConstraints (headOwner P owner head hhead t g)
      (LayoutBlocks.constraints (LayoutUniversal.data A R denom hdenom units)
        P.completeBlocks t g)) := by
  let selected : Fin js.length → {v : Fin N // head t v=g} := fun i=>
    ⟨⟨js.get i,hjs _ (List.get_mem ..)⟩,hjshead _ (List.get_mem ..)⟩
  have h := selected_literal_rank_le P owner head hhead A R denom hdenom units t g selected
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext j i
  have hi : js.get i < N := hjs _ (List.get_mem ..)
  change literalNat P owner A R t j.val (js.get i) =
    literalMatrix P owner A R t j ⟨js.get i,hi⟩
  unfold literalNat
  rw [dite_eq_left j.isLt,dite_eq_left hi]

/-- Canonical pulled constraints summed over the actual variable heads. The
factor labels do not enter this rank statement. -/
theorem canonical_total_rank_le
    (P : PackingData (Fin D) (UniversalType r Q 1)) (owner : Fin D → Fin N)
    (head : Fin Q → Fin N → Fin r)
    (hhead : ∀ i t,(P.label i).head t=head t (owner i))
    (R : ℕ) (denom : Oˣ)
    (hdenom : (denom : O)=(LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node) (t : Fin Q)
    (ε : ℚ) (hr : 2 ≤ r) (hQ : 2 ≤ Q) (hR : 4 ≤ R) (hsize : 4*R ≤ Q)
    (hε : 0 < ε)
    (hwidth : 32 * ((Q-1 : ℕ) : ℝ) * Real.log (2 / (ε : ℝ)) ≤ (R : ℝ)^2)
    (hcover : (1-ε)*(D:ℚ) ≤ P.blockCount*(Fintype.card (UniversalType r Q 1):ℚ)) :
    (∑ g : Fin r,(LayoutRank.rowRank (pulledConstraints
      (headOwner P owner head hhead t g)
      (LayoutBlocks.constraints (LayoutUniversal.data
        (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R denom hdenom units)
        P.completeBlocks t g)) : ℚ)) ≤ 2*ε*D := by
  let C := LayoutUniversal.data (r := r)
    (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R denom hdenom units
  have h := LayoutRank.blocks_data_total_rank_le C P.completeBlocks
    (id : Fin D → Fin D) (fun i t=>(P.label i).slot 0 t) (by intros; rfl)
    t ε hε.le (LayoutRank.universal_total_rank_le R denom hdenom units t
      ε hr hQ hR hsize hε hwidth) (by simpa using hcover)
  have hblocks :
    (∑ g : Fin r,(LayoutRank.rowRank (LayoutBlocks.constraints C P.completeBlocks t g) : ℚ))
      ≤ 2*ε*D := by
    calc
      _ = ∑ g : Fin r, (LayoutRank.rowRank
          ((LayoutBlocks.data C P.completeBlocks (id : Fin D → Fin D)
            (fun i t => (P.label i).slot 0 t) (by intros; rfl)).constraints t g) : ℚ) := by
            apply Finset.sum_congr rfl
            intro g _
            exact_mod_cast (LayoutRank.blocks_data_rank_eq C P.completeBlocks
              (id : Fin D → Fin D) (fun i t => (P.label i).slot 0 t)
              (by intros; rfl) t g).symm
      _ ≤ 2 * ε * D := by simpa only [Fintype.card_fin] using h
  apply le_trans _ hblocks
  apply Finset.sum_le_sum
  intro g _
  exact_mod_cast LayoutRank.rowRank_pullback_le (headOwner P owner head hhead t g)
    (LayoutBlocks.constraints C P.completeBlocks t g)

theorem selected_nat_total_rank_le
    (P : PackingData (Fin D) (UniversalType r Q 1)) (owner : Fin D → Fin N)
    (head : Fin Q → Fin N → Fin r)
    (hhead : ∀ i t,(P.label i).head t=head t (owner i))
    (R : ℕ) (denom : Oˣ)
    (hdenom : (denom : O)=(LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node) (t : Fin Q)
    (js : Fin r → List ℕ) (hjs : ∀ g v,v∈js g→v < N)
    (hjshead : ∀ g v (hv : v∈js g),head t ⟨v,hjs g v hv⟩=g)
    (ε : ℚ) (hr : 2 ≤ r) (hQ : 2 ≤ Q) (hR : 4 ≤ R) (hsize : 4*R ≤ Q)
    (hε : 0 < ε)
    (hwidth : 32 * ((Q-1 : ℕ) : ℝ) * Real.log (2 / (ε : ℝ)) ≤ (R : ℝ)^2)
    (hcover : (1-ε)*(D:ℚ) ≤ P.blockCount*(Fintype.card (UniversalType r Q 1):ℚ)) :
    (∑ g : Fin r,(LayoutRank.rowRank (fun (j : Fin D) (i : Fin (js g).length)=>
      literalNat P owner (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R t
        j.val ((js g).get i)) : ℚ)) ≤ 2*ε*D := by
  apply le_trans _ (canonical_total_rank_le P owner head hhead R denom hdenom units t
    ε hr hQ hR hsize hε hwidth hcover)
  apply Finset.sum_le_sum
  intro g _
  exact_mod_cast selected_nat_rank_le P owner head hhead
    (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R denom hdenom units t g
    (js g) (hjs g) (hjshead g)

end SubexponentialSAT.SqrtLog.LayoutProducedMatrix

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramProducedRankJoin
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual produced matrices, attained head tables and Cartesian inventory
share one proof-only maximum rank. Selection is in the emitted original-ID
order, and the canonical rank bound is discharged by literal pullback. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LeafHeadSetupProgram

variable {r Q D n : ℕ}

theorem actualRank_sum_le_oai {O : Type*} [CommRing O] {node : Fin Q → O}
    (P : PackingData (Fin D) (UniversalType r Q 1)) (owner : Fin D → Fin n)
    (head : Fin Q → Fin n → Fin r)
    (hhead : ∀ i t,(P.label i).head t=head t (owner i))
    (R : ℕ) (denom : Oˣ) (hdenom : (denom : O)=(LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node) (t : Fin Q)
    (rows : List (List Bool)) (low : List Bool)
    (hselected : ∀ (g : Fin r) (v : Fin n),v.val∈selectedHeads n rows low (t.val*r+g.val)→head t v=g)
    (ε : ℚ) (hr : 2 ≤ r) (hQ : 2 ≤ Q) (hR : 4 ≤ R) (hsize : 4*R ≤ Q) (hε : 0 < ε)
    (hwidth : 32*((Q-1 : ℕ):ℝ)*Real.log (2 / (ε:ℝ)) ≤ (R:ℝ)^2)
    (hcover : (1-ε)*(D:ℚ) ≤ P.blockCount*(Fintype.card (UniversalType r Q 1):ℚ)) :
    (∑ g : Fin r,(actualRank P owner (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R)
      R rows low t g : ℚ)) ≤ 2*ε*D := by
  exact LayoutProducedMatrix.selected_nat_total_rank_le P owner head hhead R denom hdenom units t
    (fun g=>selectedHeads n rows low (t.val*r+g.val))
    (fun g=>HeadIdentifierProgram.chosenIds_bound _ n)
    (fun g v hv=>hselected g ⟨v,HeadIdentifierProgram.chosenIds_bound _ n v hv⟩ hv)
    ε hr hQ hR hsize hε hwidth hcover

end SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank

end
end OAI.Algorithms
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank.actualRank_sum_le_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank.actualRank_sum_le_oai.{u_1}
