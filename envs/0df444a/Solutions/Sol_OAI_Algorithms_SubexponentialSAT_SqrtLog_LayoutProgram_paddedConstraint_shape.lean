-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.paddedConstraint_shape
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:51:33.488653+00:00
-- url     : https://prove2.me/submissions/33f940e2-981f-4829-adb5-eebca4c0eb6a

import Mathlib
import Definitions.Def_OAIQ081S107
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutCoefficientAlgorithm_scalarEntry_cast

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutCoefficientBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit exponential-in-R bounds for the existing integer parity coefficients. -/

namespace SubexponentialSAT.SqrtLog.LayoutCoefficientBounds

open scoped BigOperators
open SubexponentialSAT.BinomialInterpolation
open Matrix

theorem pascal_power_sum (R : ℕ) (d : Fin R) :
    (∑ j : Fin R, (d.val.choose j.val : ℤ) * (-2 : ℤ) ^ j.val) =
      (-1 : ℤ) ^ d.val := by
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => (d.val.choose j : ℤ) * (-2 : ℤ) ^ j) R]
  calc
    (∑ j ∈ Finset.range R, (d.val.choose j : ℤ) * (-2 : ℤ) ^ j) =
        ∑ j ∈ Finset.range (d.val + 1), (d.val.choose j : ℤ) * (-2 : ℤ) ^ j := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro j hj hjd
      have h : d.val < j := by simpa using hjd
      simp [Nat.choose_eq_zero_of_lt h]
    _ = (-1 : ℤ) ^ d.val := by
      have h := add_pow (-2 : ℤ) 1 d.val
      norm_num only [one_pow, mul_one, show (-2 : ℤ) + 1 = -1 by norm_num] at h
      simpa [mul_comm] using h.symm

theorem upper_mulVec_parity (A R : ℕ) :
    (SubexponentialSAT.BinomialMatrix.U ℤ A R) *ᵥ parityCoefficients (K := ℤ) A R =
      fun j => (-1 : ℤ) ^ A * (-2 : ℤ) ^ j.val := by
  let c := parityCoefficients (K := ℤ) A R
  let g : Fin R → ℤ := fun j => (-1 : ℤ) ^ A * (-2 : ℤ) ^ j.val
  have hg : (SubexponentialSAT.BinomialMatrix.L ℤ R) *ᵥ g =
      fun d => (-1 : ℤ) ^ (A + d.val) := by
    funext d
    simp only [Matrix.mulVec, dotProduct, SubexponentialSAT.BinomialMatrix.L_apply, g]
    calc
      (∑ j : Fin R, (d.val.choose j.val : ℤ) *
          ((-1 : ℤ) ^ A * (-2 : ℤ) ^ j.val)) =
          (-1 : ℤ) ^ A * ∑ j : Fin R,
            (d.val.choose j.val : ℤ) * (-2 : ℤ) ^ j.val := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = (-1 : ℤ) ^ (A + d.val) := by rw [pascal_power_sum, pow_add]
  have hc : (SubexponentialSAT.BinomialMatrix.L ℤ R) *ᵥ
        ((SubexponentialSAT.BinomialMatrix.U ℤ A R) *ᵥ c) =
      fun d => (-1 : ℤ) ^ (A + d.val) := by
    rw [Matrix.mulVec_mulVec, ← SubexponentialSAT.BinomialMatrix.factorization]
    exact mulVec_coefficients _ (isUnit_det_binomial A R) _
  have hu : IsUnit (SubexponentialSAT.BinomialMatrix.L ℤ R).det := by simp
  have h1 := coefficients_unique _ hu _ _ hc
  have h2 := coefficients_unique _ hu _ _ hg
  exact h1.trans h2.symm

theorem parity_upper_recurrence (A R : ℕ) (j : Fin R) :
    parityCoefficients (K := ℤ) A R j =
      (-1 : ℤ) ^ A * (-2 : ℤ) ^ j.val -
        ∑ k : Fin R, if j.val < k.val then
          (A.choose (k.val - j.val) : ℤ) * parityCoefficients (K := ℤ) A R k
          else 0 := by
  have heq := congrFun (upper_mulVec_parity A R) j
  simp only [Matrix.mulVec, dotProduct] at heq
  have hsplit :
      (∑ k : Fin R, SubexponentialSAT.BinomialMatrix.U ℤ A R j k *
        parityCoefficients (K := ℤ) A R k) =
      parityCoefficients (K := ℤ) A R j +
        ∑ k : Fin R, if j.val < k.val then
          (A.choose (k.val - j.val) : ℤ) * parityCoefficients (K := ℤ) A R k
          else 0 := by
    calc
      _ = ∑ k : Fin R,
          ((if k = j then parityCoefficients (K := ℤ) A R j else 0) +
          (if j.val < k.val then (A.choose (k.val - j.val) : ℤ) *
            parityCoefficients (K := ℤ) A R k else 0)) := by
        apply Finset.sum_congr rfl
        intro k hk
        by_cases h : k = j
        · subst k
          simp [SubexponentialSAT.BinomialMatrix.U]
        · by_cases hjk : j.val < k.val
          · simp [SubexponentialSAT.BinomialMatrix.U, h, hjk, Nat.le_of_lt hjk]
          · have hn : ¬j.val ≤ k.val := by
              have hne : k.val ≠ j.val := fun he => h (Fin.ext he)
              omega
            simp [SubexponentialSAT.BinomialMatrix.U, h, hjk, hn]
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  rw [hsplit] at heq
  omega

end SubexponentialSAT.SqrtLog.LayoutCoefficientBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutCoefficientAlgorithm
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Computable descending triangular solution for the original parity coefficients.
There are R coordinate updates, each scanning R potential upper entries.
No matrix inverse is executed. -/

namespace SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm

open scoped BigOperators
open SubexponentialSAT.BinomialInterpolation
open SubexponentialSAT.SqrtLog.LayoutCoefficientBounds

theorem solve_processed (A R n : ℕ) (hn : n ≤ R) (j : Fin R)
    (hj : R - n ≤ j.val) :
    solve A R n j = parityCoefficients (K := ℤ) A R j := by
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
    have hnr : n < R := by omega
    have hnle : n ≤ R := by omega
    let i : Fin R := ⟨R - 1 - n, by omega⟩
    change (if h : n < R then
      Function.update (solve A R n) (⟨R - 1 - n, by omega⟩ : Fin R)
        (target A (R - 1 - n) -
          upperTail A R (⟨R - 1 - n, by omega⟩ : Fin R) (solve A R n))
      else solve A R n) j = _
    rw [dite_eq_left hnr]
    by_cases hji : j = i
    · rw [hji]
      dsimp [i]
      simp only [Function.update, dite_true]
      rw [parity_upper_recurrence A R i]
      congr 1
      unfold upperTail
      apply Finset.sum_congr rfl
      intro k hk
      split_ifs with hik
      · rw [ih hnle k (by dsimp [i] at hik; omega)]
      · rfl
    · simp only [Function.update, dite_eq_right (by simpa only [i] using hji)]
      apply ih hnle j
      have hne : j.val ≠ R - 1 - n := fun he => hji (Fin.ext he)
      omega

theorem solve_eq (A R : ℕ) :
    solve A R R = parityCoefficients (K := ℤ) A R := by
  funext j
  exact solve_processed A R R (by omega) j (by omega)

end SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutCoefficientAlgorithmEntry
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Computable scalar formulas for the exact cleared integer matrix entries. -/

namespace SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm

open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.BinomialInterpolation
open SubexponentialSAT.Subexp.MatrixEntryKernel SubexponentialSAT.Subexp.MatrixSupport

theorem coefficientAt_eq (A R j : ℕ) :
    coefficientAt A R j = extendCoefficients (parityCoefficients (K := ℤ) A R) j := by
  simp [coefficientAt, extendCoefficients, solve_eq]

variable {r Q Δ : ℕ}

/-- Equality with the semantic integer numerator used in all rank and support proofs. -/
theorem scalarEntry_eq_entry (i : Fin Δ) (t : Fin Q) (A R : ℕ)
    (u y : UniversalType r Q Δ) :
    scalarEntry i t A R u y = LayoutNumerator.entry i t A R u y := by
  have he := scalarEntry_cast i t A R u y
  have hc := LayoutNumerator.entry_cast ℚ (by norm_num) i t A R u y
  have hcoeff : (fun j => (coefficientAt A R j : ℚ)) =
      extendCoefficients (parityCoefficients (K := ℚ) A R) := by
    funext j
    rw [coefficientAt_eq, LayoutNumerator.extend_parityCoefficients_intCast]
  rw [hcoeff] at he
  exact_mod_cast he.trans hc.symm

end SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramBlockEntries
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact dispatch formulas for the integer block matrix. These identify the
results of metadata equality tests and scalar-array reads with the raw layout
constraints, before the owner-fiber sum is performed. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.Subexp.ConstructivePacking LayoutPullback

variable {U I G O : Type*}
variable [Fintype U] [DecidableEq U] [Fintype I] [DecidableEq I]
variable [Fintype G] [DecidableEq G] [CommRing O]
variable {Q R : ℕ}

omit [Fintype I] [Fintype G] in
theorem embedHead_injective
    (C : Layout.Data (O := O) (G := G) (id : U → U) (id : U → U) Q R)
    (P : PackingData I U) (t : Fin Q) (g : G) (j : Fin P.blockCount) :
    Function.Injective (LayoutBlocks.embedHead C P.completeBlocks t g j) := by
  intro x y h
  apply Subtype.ext
  have hh := P.completeBlocks.embed.injective (congrArg Subtype.val h)
  exact congrArg Prod.snd hh

omit [Fintype I] [Fintype G] in
theorem blockConstraint_covered
    (C : Layout.Data (O := O) (G := G) (id : U → U) (id : U → U) Q R)
    (P : PackingData I U) (t : Fin Q) (g : G)
    (j k : Fin P.blockCount) (a : Fin (C.rowCount t g))
    (u : {u : U // C.head t u = g}) :
    LayoutBlocks.constraints C P.completeBlocks t g (.inl (j,a))
      (LayoutBlocks.embedHead C P.completeBlocks t g k u) =
      if j = k then C.constraints t g a u else 0 := by
  by_cases hj : j = k
  · subst k
    simp only [LayoutBlocks.constraints ]
    exact row_apply_injective _ (embedHead_injective C P t g j) _ u
  · have hout : LayoutBlocks.embedHead C P.completeBlocks t g k u ∉
        Set.range (LayoutBlocks.embedHead C P.completeBlocks t g j) := by
      rintro ⟨y,hy⟩
      have hh := P.completeBlocks.embed.injective (congrArg Subtype.val hy)
      exact hj (congrArg Prod.fst hh)
    simp only [LayoutBlocks.constraints, ite_eq_right hj]
    exact row_eq_zero _ _ _ hout

omit [Fintype G] in
omit [Fintype I] in
theorem blockConstraint_uncovered
    (C : Layout.Data (O := O) (G := G) (id : U → U) (id : U → U) Q R)
    (P : PackingData I U) (t : Fin Q) (g : G)
    (j : Fin P.blockCount) (a : Fin (C.rowCount t g))
    (v : {i : I // LayoutBlocks.copyHead C P.label t i = g})
    (hv : v.val ∉ Set.range P.completeBlocks.embed) :
    LayoutBlocks.constraints C P.completeBlocks t g (.inl (j,a)) v = 0 := by
  have hout : v ∉ Set.range (LayoutBlocks.embedHead C P.completeBlocks t g j) := by
    rintro ⟨u,hu⟩
    exact hv ⟨(j,u.val), congrArg Subtype.val hu⟩
  exact row_eq_zero _ _ _ hout

omit [Fintype I] [Fintype G] in
theorem singletonConstraint
    (C : Layout.Data (O := O) (G := G) (id : U → U) (id : U → U) Q R)
    (P : PackingData I U) (t : Fin Q) (g : G)
    (v : {v : {i : I // LayoutBlocks.copyHead C P.label t i = g} //
      v.val ∉ Set.range P.completeBlocks.embed})
    (w : {i : I // LayoutBlocks.copyHead C P.label t i = g}) :
    LayoutBlocks.constraints C P.completeBlocks t g (.inr v) w =
      if w.val = v.val.val then 1 else 0 := by
  simp [LayoutBlocks.constraints, Pi.single_apply, Subtype.ext_iff ]

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntries
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Executable scalar specifications in the physical side/joint list order.
These definitions do not assert a primitive runtime bound: their exact
identification lets the separately traced scan/arithmetic producer feed the
semantic layout without an arbitrary finite-type ordering oracle. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.MulticolorTypes
open LayoutPullback LayoutExactBuckets LayoutScaledMatrices

variable {r Q : ℕ}

theorem headEntry_eq (A R : ℕ) (t : Fin Q) (g : Fin r)
    (u : Joint t g (0 : Fin 1)) (y : LayoutUniversal.Head t g) :
    headEntry A R t g u y = LayoutUniversal.constraints A R t g u y := by
  classical
  have inj : Function.Injective (LayoutUniversal.jointOwner t g) := by
    intro a b h
    exact Subtype.ext (congrArg (fun z => z.val) h)
  by_cases hy : y.val ∈ joint t g (0 : Fin 1)
  · let yy : Joint t g (0 : Fin 1) := ⟨y.val,hy⟩
    have he : LayoutUniversal.jointOwner t g yy = y := Subtype.ext rfl
    change headEntry A R t g u y =
      row (LayoutUniversal.jointOwner t g)
        (clearedDefect (LayoutNumerator.denominator R)
          (LayoutNumerator.joint (0 : Fin 1) t g A R) u) y
    rw [← he, row_apply_injective _ inj]
    simp only [headEntry, he, ite_eq_left hy, clearedDefect]
    rw [LayoutCoefficientAlgorithm.scalarEntry_eq_entry]
    have heq : u = yy ↔ u.val = y.val := Subtype.ext_iff
    simp only [heq, LayoutNumerator.denominator, LayoutNumerator.joint]
    rfl
  · have hout : y ∉ Set.range (LayoutUniversal.jointOwner t g) := by
      rintro ⟨z,hz⟩
      apply hy
      have hh : z.val = y.val := congrArg Subtype.val hz
      exact hh ▸ z.property
    change headEntry A R t g u y =
      row (LayoutUniversal.jointOwner t g)
        (clearedDefect (LayoutNumerator.denominator R)
          (LayoutNumerator.joint (0 : Fin 1) t g A R) u) y
    rw [row_eq_zero _ _ _ hout]
    simp [headEntry, hy]

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramPadded
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A computable integer row for every incidence position. Inactive covered
positions and non-head uncovered positions are zero. Active rows are precisely
the raw block constraints, with repetitions and zero padding permitted. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking

variable {r Q : ℕ} {I O : Type*}
variable [Fintype I] [DecidableEq I] [CommRing O]

omit [Fintype I] in
theorem paddedEntry_covered (P : PackingData I (UniversalType r Q 1))
    (A R : ℕ) (t : Fin Q) (g : Fin r)
    (j k : Fin P.blockCount) (u y : UniversalType r Q 1) :
    paddedEntry P A R t g (P.vertexAt j u) (P.vertexAt k y) =
      if j = k ∧ u ∈ joint t g (0 : Fin 1) ∧ y ∈ joint t g (0 : Fin 1) then
        (if u = y then (2 : ℤ)^(R-1) else 0) -
          LayoutCoefficientAlgorithm.scalarEntry (0 : Fin 1) t A R u y
      else 0 := by
  simp only [paddedEntry,P.lookup_at]

omit [Fintype I] in
theorem paddedConstraint_inactive (P : PackingData I (UniversalType r Q 1))
    (A R : ℕ) (t : Fin Q) (g : Fin r)
    (j : Fin P.blockCount) (u : UniversalType r Q 1)
    (hu : u ∉ joint t g (0 : Fin 1)) :
    paddedConstraint P A R t g (P.vertexAt j u) = 0 := by
  funext w
  simp only [paddedConstraint,paddedEntry,P.lookup_at]
  cases hw : P.lookup w.val with
  | none => rfl
  | some z => rcases z with ⟨k,y⟩; simp [hu]

omit [Fintype I] in
theorem paddedConstraint_uncovered_inactive
    (P : PackingData I (UniversalType r Q 1))
    (A R : ℕ) (t : Fin Q) (g : Fin r) (v : I)
    (hv : P.lookup v = none) (hg : (P.label v).head t ≠ g) :
    paddedConstraint P A R t g v = 0 := by
  funext w
  simp [paddedConstraint,paddedEntry,hv,hg]

variable {node : Fin Q → O}

omit [Fintype I] in
theorem paddedConstraint_covered_eq
    (P : PackingData I (UniversalType r Q 1))
    (A R : ℕ) (denom : Oˣ)
    (hdenom : (denom : O) = (LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node)
    (t : Fin Q) (g : Fin r) (j : Fin P.blockCount)
    (u : Joint t g (0 : Fin 1)) :
    paddedConstraint P A R t g (P.vertexAt j u.val) =
      LayoutBlocks.constraints (LayoutUniversal.data A R denom hdenom units)
        P.completeBlocks t g
        (.inl (j,(Fintype.equivFin (Joint t g (0 : Fin 1))) u)) := by
  classical
  let C := LayoutUniversal.data (r := r) A R denom hdenom units
  funext w
  change paddedEntry P A R t g (P.vertexAt j u.val) w.val = _
  by_cases hw : w.val ∈ Set.range P.completeBlocks.embed
  · obtain ⟨⟨k,y⟩,hy⟩ := hw
    have hyhead : y.head t = g := by
      have hhead : (P.label (P.completeBlocks.embed (k,y))).head t = g := by
        rw [hy]
        exact w.property
      simpa only [P.completeBlocks_apply,P.label_at] using hhead
    let yy : LayoutUniversal.Head t g := ⟨y, hyhead⟩
    have he : LayoutBlocks.embedHead (LayoutUniversal.data (r := r) A R denom hdenom units)
        P.completeBlocks t g k yy = w :=
      Subtype.ext hy
    have hb := blockConstraint_covered
      (C := LayoutUniversal.data (r := r) A R denom hdenom units)
      (P := P) (t := t) (g := g) j k
      ((Fintype.equivFin (Joint t g (0 : Fin 1))) u) yy
    have hbw : LayoutBlocks.constraints (LayoutUniversal.data (r := r) A R denom hdenom units)
        P.completeBlocks t g (.inl (j, (Fintype.equivFin (Joint t g (0 : Fin 1))) u)) w =
        if j = k then (LayoutUniversal.data (r := r) A R denom hdenom units).constraints
          t g ((Fintype.equivFin (Joint t g (0 : Fin 1))) u) yy else 0 := by
      rw [← he]
      exact hb
    rw [hbw, ← hy]
    change paddedEntry P A R t g (P.vertexAt j u.val) (P.vertexAt k y) = _
    have hc : C.constraints t g
        ((Fintype.equivFin (Joint t g (0 : Fin 1))) u) yy =
        LayoutUniversal.constraints A R t g u yy := by
      simp [C, LayoutUniversal.data, Layout.ofIndexed]
    by_cases hj : j = k
    · subst k
      rw [ite_eq_left rfl]
      rw [paddedEntry_covered]
      calc
        (if j = j ∧ u.val ∈ joint t g (0 : Fin 1) ∧ y ∈ joint t g (0 : Fin 1) then
            (if u.val = y then (2 : ℤ) ^ (R - 1) else 0) -
              LayoutCoefficientAlgorithm.scalarEntry (0 : Fin 1) t A R u.val y
          else 0) = headEntry A R t g u yy := by
            simp [headEntry, u.property, yy, hyhead]
        _ = LayoutUniversal.constraints A R t g u yy := headEntry_eq A R t g u yy
        _ = C.constraints t g ((Fintype.equivFin (Joint t g (0 : Fin 1))) u) yy := hc.symm
    · rw [paddedEntry_covered]
      simp [hj]
  · rw [blockConstraint_uncovered C P t g j
        ((Fintype.equivFin (Joint t g (0 : Fin 1))) u) w hw]
    have hn := (P.lookup_none_iff w.val).mpr hw
    simp [paddedEntry,P.lookup_at,hn]

omit [Fintype I] in
theorem paddedConstraint_uncovered_eq
    (P : PackingData I (UniversalType r Q 1))
    (A R : ℕ) (denom : Oˣ)
    (hdenom : (denom : O) = (LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node)
    (t : Fin Q) (g : Fin r) (v : IncidenceHead P t g)
    (hv : v.val ∉ Set.range P.completeBlocks.embed) :
    paddedConstraint P A R t g v.val =
      LayoutBlocks.constraints (LayoutUniversal.data A R denom hdenom units)
        P.completeBlocks t g (.inr ⟨v,hv⟩) := by
  classical
  funext w
  have hs := singletonConstraint
    (C := LayoutUniversal.data (r := r) A R denom hdenom units)
    (P := P) (t := t) (g := g) ⟨v, hv⟩ w
  change paddedEntry P A R t g v.val w.val = _
  rw [hs]
  have hn := (P.lookup_none_iff v.val).mpr hv
  simp [paddedEntry,hn,v.property]

omit [Fintype I] in
/-- Every emitted row is either zero or one of the old raw constraints. -/
theorem paddedConstraint_shape_oai
    (P : PackingData I (UniversalType r Q 1))
    (A R : ℕ) (denom : Oˣ)
    (hdenom : (denom : O) = (LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node)
    (t : Fin Q) (g : Fin r) (v : I) :
    paddedConstraint P A R t g v = 0 ∨
      ∃ a, paddedConstraint P A R t g v =
        LayoutBlocks.constraints (LayoutUniversal.data A R denom hdenom units)
          P.completeBlocks t g a := by
  classical
  cases hv : P.lookup v with
  | none =>
    by_cases hg : (P.label v).head t = g
    · exact Or.inr ⟨.inr ⟨⟨v,hg⟩,(P.lookup_none_iff v).mp hv⟩,
        paddedConstraint_uncovered_eq P A R denom hdenom units t g ⟨v,hg⟩
          ((P.lookup_none_iff v).mp hv)⟩
    · exact Or.inl (paddedConstraint_uncovered_inactive P A R t g v hv hg)
  | some z =>
    rcases z with ⟨j,u⟩
    have he := P.lookup_sound v (j,u) hv
    rw [← he]
    by_cases hu : u ∈ joint t g (0 : Fin 1)
    · exact Or.inr ⟨.inl (j,(Fintype.equivFin (Joint t g (0 : Fin 1))) ⟨u,hu⟩),
        paddedConstraint_covered_eq P A R denom hdenom units t g j ⟨u,hu⟩⟩
    · exact Or.inl (paddedConstraint_inactive P A R t g j u hu)

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
end

theorem solution.{u_1, u_2} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.paddedConstraint_shape_oai.{u_1, u_2} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.paddedConstraint_shape_oai.{u_1, u_2}
