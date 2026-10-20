-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.Pruning.card_add_rank_matrixN_mul_matrixL_le_card_H_of_lifts
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:18:43.829112+00:00
-- url     : https://prove2.me/submissions/68e3742c-e89a-41d8-9933-0c8103b28afd

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/KernelIndependence.lean:L86-L113
-- (upload_full_project.md Phase 4): solution for node OAI.SeymourSecondNeighborhood.Pruning.card_add_rank_matrixN_mul_matrixL_le_card_H_of_lifts. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Tauto
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Basic
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ReductionCore
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Reindex
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MinimalCounterexample
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Deletion
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_TransitiveBlowup
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_PruningDefinitions
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Matching
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_AugmentedGraph
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatchingAugmented
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankMatching
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRank
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatrixMaps
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_KernelRestriction
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MaxSupportKernel
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_KernelConflict
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankCoefficients
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatrixMapsPolynomial
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankGlobalMinors
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_KernelBasisLifts
import Theorems.Thm_OAI_SeymourSecondNeighborhood_LinearAlgebra_MaxSupportKernel_kernel_support_of_max_rank
import Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_restrictFiber_mem_kernelD
import Theorems.Thm_OAI_SeymourSecondNeighborhood_Pruning_restrictFiber_mem_kernelD_transpose

-- ---- from OAI.Combinatorics.SecondNeighborhood.PruningDefinitions ----
namespace OAI

namespace SeymourSecondNeighborhood.Pruning

variable {V : Type*}

variable [Fintype V] [DecidableEq V]

noncomputable section

theorem conflict_corner_mem_Z {r : V → V → Prop} {R C : Finset (V × V)}
    {a b : V × V} (ha : a ∈ R) (hb : b ∈ C) (hc : Conflict r a b) :
    (b.1, a.2) ∈ Z r R C := by
  exact mem_Z.mpr ⟨a.1, b.2, by simpa using ha, by simpa using hb, hc.1, hc.2⟩

theorem conflict_corner_mem_H {r : V → V → Prop} {R C : Finset (V × V)}
    {a b : V × V} (ha : a ∈ R) (hb : b ∈ C) (hc : Conflict r a b) :
    (a.1, b.2) ∈ H r R C := by
  exact mem_H.mpr ⟨b.1, a.2, by simpa using ha, by simpa using hb, hc.1, hc.2⟩

end
end SeymourSecondNeighborhood.Pruning

end OAI

-- ---- from OAI.Combinatorics.SecondNeighborhood.KernelConflict ----
namespace OAI

namespace SeymourSecondNeighborhood.Pruning

open Matrix
open SeymourSecondNeighborhood.LinearAlgebra.MaxSupportKernel

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [Fintype X] [DecidableEq X] in
theorem matrixD_supported (r : X → X → Prop) (R C : Finset (X × X))
    (b : X → X → ℝ) (hb : SupportedCoefficients r b) (p i : X) :
    SupportedOn (localSupport r R C p i) (matrixD R C b p i) := by
  intro s j h
  exact hb s.1 j.1 h

theorem conflict_kernel_product_eq_zero (r : X → X → Prop)
    (R C : Finset (X × X)) (b : X → X → ℝ) (hb : SupportedCoefficients r b)
    (hmax : LocalMaximalRanks r R C b)
    (u : ↥R → ℝ) (hu : matrixB r R C b *ᵥ u = 0)
    (v : ↥C → ℝ) (hv : (matrixN r R C b)ᵀ *ᵥ v = 0)
    (left : ↥R) (right : ↥C) (hc : Conflict r left.1 right.1) :
    u left * v right = 0 := by
  let j : PairFiber R left.1.1 := ⟨left.1.2, left.2⟩
  let s : PairFiber C right.1.1 := ⟨right.1.2, right.2⟩
  have hx := restrictFiber_mem_kernelD r R C b hb left.1.1 right.1.1 hc.1 u hu
  have hy := restrictFiber_mem_kernelD_transpose r R C b hb
    left.1.1 right.1.1 hc.1 v hv
  have h := kernel_support_of_max_rank
    (matrixD_supported r R C b hb left.1.1 right.1.1)
    (hmax left.1.1 right.1.1 hc.1) hx hy (s := s) (j := j) hc.2
  simpa [restrictFiber, fiberIndex, j, s] using h

end SeymourSecondNeighborhood.Pruning

end OAI

-- ---- from OAI.Combinatorics.SecondNeighborhood.MatrixMapsCommute ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace SeymourSecondNeighborhood.Pruning

variable {X : Type*} [Fintype X] [DecidableEq X]

noncomputable section

omit [Fintype X] [DecidableEq X] in
private theorem conflict_of_product_ne_zero
    (r : X → X → Prop) (a b : X → X → ℝ)
    (ha : SupportedCoefficients r a) (hb : SupportedCoefficients r b)
    (left right : X × X)
    (h : a left.1 right.1 * b right.2 left.2 ≠ 0) :
    Conflict r left right := by
  constructor
  · by_contra hn
    exact h (by rw [ha _ _ hn, zero_mul])
  · by_contra hn
    exact h (by rw [hb _ _ hn, mul_zero])

theorem matrixN_mul_matrixL_apply
    (r : X → X → Prop) (R C : Finset (X × X)) (a b : X → X → ℝ)
    (ha : SupportedCoefficients r a) (hb : SupportedCoefficients r b)
    (right : {right : X × X // right ∈ C})
    (left : {left : X × X // left ∈ R}) :
    (matrixN r R C b * matrixL r R C a) right left =
      a left.val.1 right.val.1 * b right.val.2 left.val.2 := by
  classical
  by_cases hprod : a left.val.1 right.val.1 * b right.val.2 left.val.2 = 0
  · rw [hprod, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro z _
    by_cases hi : right.val.1 = z.val.1
    · by_cases hj : z.val.2 = left.val.2
      · rw [matrixN_apply, matrixL_apply, ite_eq_left hi, ite_eq_left hj, ← hi, hj, mul_comm]
        exact hprod
      · simp only [matrixL_apply, ite_eq_right hj, mul_zero]
    · simp only [matrixN_apply, ite_eq_right hi, zero_mul]
  · have hc : Conflict r left.val right.val :=
      conflict_of_product_ne_zero r a b ha hb left.val right.val hprod
    let z0 : {z : X × X // z ∈ Z r R C} :=
      ⟨(right.val.1, left.val.2),
        conflict_corner_mem_Z left.property right.property hc⟩
    calc
      (matrixN r R C b * matrixL r R C a) right left =
          matrixN r R C b right z0 * matrixL r R C a z0 left := by
        rw [Matrix.mul_apply]
        refine Finset.sum_eq_single_of_mem z0 (Finset.mem_univ _) ?_
        intro z _ hne
        by_cases hi : right.val.1 = z.val.1
        · by_cases hj : z.val.2 = left.val.2
          · have heq : z = z0 := by
              apply Subtype.ext
              exact Prod.ext hi.symm hj
            exact (hne heq).elim
          · simp only [matrixL_apply, ite_eq_right hj, mul_zero]
        · simp only [matrixN_apply, ite_eq_right hi, zero_mul]
      _ = a left.val.1 right.val.1 * b right.val.2 left.val.2 := by
        simp [matrixN_apply, matrixL_apply, z0, mul_comm]

theorem matrixA_mul_matrixB_apply
    (r : X → X → Prop) (R C : Finset (X × X)) (a b : X → X → ℝ)
    (ha : SupportedCoefficients r a) (hb : SupportedCoefficients r b)
    (right : {right : X × X // right ∈ C})
    (left : {left : X × X // left ∈ R}) :
    (matrixA r R C a * matrixB r R C b) right left =
      a left.val.1 right.val.1 * b right.val.2 left.val.2 := by
  classical
  by_cases hprod : a left.val.1 right.val.1 * b right.val.2 left.val.2 = 0
  · rw [hprod, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro h _
    by_cases hs : right.val.2 = h.val.2
    · by_cases hp : h.val.1 = left.val.1
      · rw [matrixA_apply, matrixB_apply, ite_eq_left hs, ite_eq_left hp, ← hs, hp]
        exact hprod
      · simp only [matrixB_apply, ite_eq_right hp, mul_zero]
    · simp only [matrixA_apply, ite_eq_right hs, zero_mul]
  · have hc : Conflict r left.val right.val :=
      conflict_of_product_ne_zero r a b ha hb left.val right.val hprod
    let h0 : {h : X × X // h ∈ H r R C} :=
      ⟨(left.val.1, right.val.2),
        conflict_corner_mem_H left.property right.property hc⟩
    calc
      (matrixA r R C a * matrixB r R C b) right left =
          matrixA r R C a right h0 * matrixB r R C b h0 left := by
        rw [Matrix.mul_apply]
        refine Finset.sum_eq_single_of_mem h0 (Finset.mem_univ _) ?_
        intro h _ hne
        by_cases hs : right.val.2 = h.val.2
        · by_cases hp : h.val.1 = left.val.1
          · have heq : h = h0 := by
              apply Subtype.ext
              exact Prod.ext hp hs.symm
            exact (hne heq).elim
          · simp only [matrixB_apply, ite_eq_right hp, mul_zero]
        · simp only [matrixA_apply, ite_eq_right hs, zero_mul]
      _ = a left.val.1 right.val.1 * b right.val.2 left.val.2 := by
        simp [matrixA_apply, matrixB_apply, h0]

theorem matrixN_mul_matrixL_eq_matrixA_mul_matrixB
    (r : X → X → Prop) (R C : Finset (X × X)) (a b : X → X → ℝ)
    (ha : SupportedCoefficients r a) (hb : SupportedCoefficients r b) :
    matrixN r R C b * matrixL r R C a = matrixA r R C a * matrixB r R C b := by
  ext right left
  rw [matrixN_mul_matrixL_apply r R C a b ha hb,
    matrixA_mul_matrixB_apply r R C a b ha hb]

end
end SeymourSecondNeighborhood.Pruning

end OAI

-- ---- from OAI.Combinatorics.SecondNeighborhood.KernelIndependence ----
namespace OAI

namespace SeymourSecondNeighborhood.Pruning

open Matrix
open scoped BigOperators Classical

variable {X : Type*} [Fintype X] [DecidableEq X]

noncomputable section

theorem kernelB_vanishes_at_matched_left
    (r : X → X → Prop) (R C : Finset (X × X)) (b : X → X → ℝ)
    (hb : SupportedCoefficients r b) (hmax : LocalMaximalRanks r R C b)
    (left : ↥R) (right : ↥C) (hc : Conflict r left.val right.val)
    (v : ↥C → ℝ) (hv : (matrixN r R C b)ᵀ *ᵥ v = 0)
    (hcoordinate : v right = 1)
    (u : ↥R → ℝ) (hu : matrixB r R C b *ᵥ u = 0) : u left = 0 := by
  have h := conflict_kernel_product_eq_zero r R C b hb hmax
    u hu v hv left right hc
  simpa only [hcoordinate, mul_one] using h

theorem matrixB_lifts_linearIndependent
    {E : Type*} [Fintype E]
    (r : X → X → Prop) (R C : Finset (X × X)) (b : X → X → ℝ)
    (hb : SupportedCoefficients r b) (hmax : LocalMaximalRanks r R C b)
    (left : E → ↥R) (right : E → ↥C)
    (U : E → (↥R → ℝ)) (W : E → (↥C → ℝ))
    (hW : ∀ e, (matrixN r R C b)ᵀ *ᵥ W e = 0)
    (hWcoordinate : ∀ e, W e (right e) = 1)
    (hUcoordinate : ∀ e f, U e (left f) = if e = f then 1 else 0)
    (hconflict : ∀ e, Conflict r (left e).val (right e).val) :
    LinearIndependent ℝ (fun e => matrixB r R C b *ᵥ U e) := by
  apply Fintype.linearIndependent_iff.mpr
  intro coefficients hrelation e
  let u : ↥R → ℝ := ∑ f, coefficients f • U f
  have hu : matrixB r R C b *ᵥ u = 0 := by
    change (matrixB r R C b).mulVecLin (∑ f, coefficients f • U f) = 0
    simpa only [map_sum, map_smul, Matrix.mulVecLin_apply] using hrelation
  have hzero : u (left e) = 0 :=
    kernelB_vanishes_at_matched_left r R C b hb hmax
      (left e) (right e) (hconflict e) (W e) (hW e) (hWcoordinate e) u hu
  have hcoordinate : u (left e) = coefficients e := by
    simp [u, Finset.sum_apply, Pi.smul_apply, hUcoordinate, smul_eq_mul, mul_ite]
  exact hcoordinate.symm.trans hzero

theorem matrixB_lift_mem_ker_matrixA
    (r : X → X → Prop) (R C : Finset (X × X)) (a b : X → X → ℝ)
    (ha : SupportedCoefficients r a) (hb : SupportedCoefficients r b)
    (u : ↥R → ℝ) (hu : matrixL r R C a *ᵥ u = 0) :
    matrixB r R C b *ᵥ u ∈ LinearMap.ker (matrixA r R C a).mulVecLin := by
  rw [LinearMap.mem_ker]
  change matrixA r R C a *ᵥ (matrixB r R C b *ᵥ u) = 0
  rw [Matrix.mulVec_mulVec,
    ← matrixN_mul_matrixL_eq_matrixA_mul_matrixB r R C a b ha hb,
    ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_zero]

theorem card_le_finrank_ker_matrixA_of_lifts
    {E : Type*} [Fintype E]
    (r : X → X → Prop) (R C : Finset (X × X)) (a b : X → X → ℝ)
    (ha : SupportedCoefficients r a) (hb : SupportedCoefficients r b)
    (hmax : LocalMaximalRanks r R C b)
    (left : E → ↥R) (right : E → ↥C)
    (U : E → (↥R → ℝ)) (W : E → (↥C → ℝ))
    (hU : ∀ e, matrixL r R C a *ᵥ U e = 0)
    (hW : ∀ e, (matrixN r R C b)ᵀ *ᵥ W e = 0)
    (hWcoordinate : ∀ e, W e (right e) = 1)
    (hUcoordinate : ∀ e f, U e (left f) = if e = f then 1 else 0)
    (hconflict : ∀ e, Conflict r (left e).val (right e).val) :
    Fintype.card E ≤ Module.finrank ℝ (LinearMap.ker (matrixA r R C a).mulVecLin) := by
  let images : E → LinearMap.ker (matrixA r R C a).mulVecLin := fun e =>
    ⟨matrixB r R C b *ᵥ U e,
      matrixB_lift_mem_ker_matrixA r R C a b ha hb (U e) (hU e)⟩
  have hindependent : LinearIndependent ℝ images := by
    apply LinearIndependent.of_comp (LinearMap.ker (matrixA r R C a).mulVecLin).subtype
    change LinearIndependent ℝ (fun e => matrixB r R C b *ᵥ U e)
    exact matrixB_lifts_linearIndependent r R C b hb hmax left right U W
      hW hWcoordinate hUcoordinate hconflict
  exact hindependent.fintype_card_le_finrank

theorem card_add_rank_matrixN_mul_matrixL_le_card_H_of_lifts
    {E : Type*} [Fintype E]
    (r : X → X → Prop) (R C : Finset (X × X)) (a b : X → X → ℝ)
    (ha : SupportedCoefficients r a) (hb : SupportedCoefficients r b)
    (hmax : LocalMaximalRanks r R C b)
    (left : E → ↥R) (right : E → ↥C)
    (U : E → (↥R → ℝ)) (W : E → (↥C → ℝ))
    (hU : ∀ e, matrixL r R C a *ᵥ U e = 0)
    (hW : ∀ e, (matrixN r R C b)ᵀ *ᵥ W e = 0)
    (hWcoordinate : ∀ e, W e (right e) = 1)
    (hUcoordinate : ∀ e f, U e (left f) = if e = f then 1 else 0)
    (hconflict : ∀ e, Conflict r (left e).val (right e).val) :
    Fintype.card E + (matrixN r R C b * matrixL r R C a).rank ≤ (H r R C).card := by
  have hcard := card_le_finrank_ker_matrixA_of_lifts r R C a b ha hb hmax
    left right U W hU hW hWcoordinate hUcoordinate hconflict
  have hnull : (matrixA r R C a).rank +
      Module.finrank ℝ (LinearMap.ker (matrixA r R C a).mulVecLin) = (H r R C).card := by
    simpa only [Matrix.rank, Module.finrank_pi, Fintype.card_coe] using
      LinearMap.finrank_range_add_finrank_ker (matrixA r R C a).mulVecLin
  rw [matrixN_mul_matrixL_eq_matrixA_mul_matrixB r R C a b ha hb]
  calc
    Fintype.card E + (matrixA r R C a * matrixB r R C b).rank ≤
        Module.finrank ℝ (LinearMap.ker (matrixA r R C a).mulVecLin) +
          (matrixA r R C a).rank :=
      Nat.add_le_add hcard (Matrix.rank_mul_le_left _ _)
    _ = (matrixA r R C a).rank +
        Module.finrank ℝ (LinearMap.ker (matrixA r R C a).mulVecLin) := Nat.add_comm _ _
    _ = (H r R C).card := hnull

end
end SeymourSecondNeighborhood.Pruning

end OAI

-- ---- platform node ----
open OAI OAI.SeymourSecondNeighborhood OAI.SeymourSecondNeighborhood.Pruning
open Matrix
open scoped BigOperators Classical


theorem solution : type_of% @_root_.OAI.SeymourSecondNeighborhood.Pruning.card_add_rank_matrixN_mul_matrixL_le_card_H_of_lifts := @_root_.OAI.SeymourSecondNeighborhood.Pruning.card_add_rank_matrixN_mul_matrixL_le_card_H_of_lifts
