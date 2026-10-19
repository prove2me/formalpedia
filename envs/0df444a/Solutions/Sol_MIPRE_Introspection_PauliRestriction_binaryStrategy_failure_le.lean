-- Prove2me | solution 1 for MIPRE.Introspection.PauliRestriction.binaryStrategy_failure_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:16:20.62673+00:00
-- url     : https://prove2.me/submissions/c719bd82-ad49-460b-81dc-d249e834d099

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Introspection/PauliRestriction.lean (solution of MIPRE.Introspection.PauliRestriction.binaryStrategy_failure_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Pi
import Mathlib.Order.Fin.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_Pasting
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Definitions.Def_MIPRE_LCS_NonlocalGame
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_MIPRE_LCS_MagicSquare_Strategy
import Definitions.Def_MIPRE_LCS_MagicSquare_Game
import Definitions.Def_MIPRE_Background_QLD_Game
import Definitions.Def_MIPRE_Background_QLD_CLPresentation
import Definitions.Def_MIPRE_Background_QLD_CLBinary
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_Introspection_Types
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingPrefix
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_CommutatorParseval
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_EPR
import Definitions.Def_MIPRE_Foundations_Introspection_BlockRetention
import Definitions.Def_MIPRE_Foundations_Introspection_PauliMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterTransport
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterEPR
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryChecks
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPredicate
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation
import Definitions.Def_MIPRE_Foundations_Introspection_TypedEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_PauliRestriction
import Definitions.Def_MIPRE_Background_QLD_CLTransport
import Definitions.Def_MIPRE_Background_Introspection_PauliRestriction
import Theorems.Thm_MIPRE_Introspection_TypeGraph_adj_pauli
import Theorems.Thm_MIPRE_Introspection_TypedEstimates_completed_pauli_condFail_le
import Theorems.Thm_MIPRE_Introspection_TypedEstimates_typed_edge_mean_failure_le
import Theorems.Thm_MIPRE_QLD_adj_symm
import Theorems.Thm_MIPRE_TensorProductStrategy_value_eq_povmValue

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.TensorProductStrategy
section
open Matrix Kronecker Finset
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
variable {G : Game X Y A B}
/-- The value is the `μ`-average of the conditional success probability. -/
theorem value_eq_sum_succAt (S : TensorProductStrategy G) :
    S.value = ∑ x, ∑ y, G.μ x y * S.succAt x y := by
  unfold value succAt
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by rw [born]; ring
end
end MIPRE.TensorProductStrategy

namespace MIPRE.TensorProductStrategy
section
open Matrix Kronecker Finset
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
variable {G : Game X Y A B}
/-- **The failure probability, decomposed by question pair.** -/
theorem one_sub_value_eq_sum_failAt (S : TensorProductStrategy G) :
    1 - S.value = ∑ x, ∑ y, G.μ x y * S.failAt x y := by
  have hsplit : ∑ x, ∑ y, G.μ x y * S.failAt x y
      = (∑ x, ∑ y, G.μ x y) - ∑ x, ∑ y, G.μ x y * S.succAt x y := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by simp only [failAt]; ring
  rw [hsplit, G.μ_sum_one, value_eq_sum_succAt]
end
end MIPRE.TensorProductStrategy

namespace MIPRE.Introspection.PauliRestriction
noncomputable section
open Matrix Finset Classical
set_option linter.unusedSectionVars false
variable {F F₀ ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Field F₀] [Fintype F₀] [DecidableEq F₀]
  [Fintype ι] [DecidableEq ι] [Fintype A] {m t d ℓ : ℕ} [NeZero m]
variable (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun F₀ ι ℓ) (project : QLD.Answer F m d → ι → F₀)
  (D : (ι → F₀) → (ι → F₀) → A → A → Bool)
  (S : TensorProductStrategy (fullGame hm b L project D))
theorem binaryStrategy_failAt_le (a₀ b₀ : QLD.Answer F m d)
    (x y : QLD.PauliCL.BinaryQuestion m t) :
    (binaryStrategy hm b L project D S a₀ b₀).failAt x y ≤
      S.failAt (.inl x.1,x.2) (.inl y.1,y.2) :=
  TypedEstimates.completed_pauli_condFail_le QLD.adj (.pauli .X) (.pauli .Z)
    (QLD.PauliCL.binaryPresentation hm b) L project D (pauliCheck hm b)
    (QLD.PauliCL.binaryGame hm b) (fun _ _ _ _ => rfl) S.ψ
    S.PA.toPOVM S.PB.toPOVM a₀ b₀ x y
end
end MIPRE.Introspection.PauliRestriction

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.PauliRestriction
open Matrix Finset Classical
set_option linter.unusedSectionVars false
variable {F F₀ ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Field F₀] [Fintype F₀] [DecidableEq F₀]
  [Fintype ι] [DecidableEq ι] [Fintype A] {m t d ℓ : ℕ} [NeZero m]
variable (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun F₀ ι ℓ) (project : QLD.Answer F m d → ι → F₀)
  (D : (ι → F₀) → (ι → F₀) → A → A → Bool)
  (S : TensorProductStrategy (fullGame hm b L project D))
set_option backward.isDefEq.respectTransparency false in
theorem _root_.solution (a₀ b₀ : QLD.Answer F m d) {ε : ℝ}
    (hS : 1 - S.value ≤ ε) :
    1 - (binaryStrategy hm b L project D S a₀ b₀).value ≤
      (TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card * ε := by
  let R := binaryStrategy hm b L project D S a₀ b₀
  let n : ℝ := Fintype.card (Fin ((3*m+3)*t) → ZMod 2)
  let c : ℝ := (TypeGraph.edges QLD.adj (.pauli .X) (.pauli .Z) ℓ).card * ε
  have hn : 0 < n := by dsimp [n]; exact_mod_cast Fintype.card_pos
  let : Nonempty QLD.TyEdge := ⟨⟨(.pair,.pair), by decide⟩⟩
  have he : (0 : ℝ) < Fintype.card QLD.TyEdge := by exact_mod_cast Fintype.card_pos
  have havg (e : QLD.TyEdge) :
      (∑ z : Fin ((3*m+3)*t) → ZMod 2,
        R.failAt (e.val.1, (QLD.PauliCL.binaryPresentation hm b e.val.1).eval z)
          (e.val.2, (QLD.PauliCL.binaryPresentation hm b e.val.2).eval z)) / n ≤ c := by
    have hedge : TypeGraph.Adj (ℓ := ℓ) QLD.adj (.pauli .X) (.pauli .Z)
        (.inl e.val.1) (.inl e.val.2) := by
      change TypeGraph.adj _ _ _ _ _ = true
      rw [TypeGraph.adj_pauli QLD.adj _ _ QLD.adj_symm QLD.adj_self]
      exact e.property
    have hf := TypedEstimates.typed_edge_mean_failure_le QLD.adj (.pauli .X) (.pauli .Z)
      (QLD.PauliCL.binaryPresentation hm b)
      (TypedEstimates.questionCheck L (.pauli .X) (.pauli .Z) project D (pauliCheck hm b))
      S.ψ S.ψ_unit S.PA.toPOVM S.PB.toPOVM
      (by simpa only [TensorProductStrategy.value_eq_povmValue, fullGame,
        TypedEstimates.parsedGame] using hS)
      (.inl e.val.1) (.inl e.val.2) hedge
    apply le_trans (div_le_div_of_nonneg_right (Finset.sum_le_sum (fun z _ =>
      binaryStrategy_failAt_le hm b L project D S a₀ b₀ _ _)) hn.le)
    exact hf
  have hs := Finset.sum_le_sum (fun e (_ : e ∈ (univ : Finset QLD.TyEdge)) => havg e)
  have hform : 1 - R.value =
      (∑ e : QLD.TyEdge, (∑ z : Fin ((3*m+3)*t) → ZMod 2,
        R.failAt (e.val.1, (QLD.PauliCL.binaryPresentation hm b e.val.1).eval z)
          (e.val.2, (QLD.PauliCL.binaryPresentation hm b e.val.2).eval z)) / n) /
        Fintype.card QLD.TyEdge := by
    rw [R.one_sub_value_eq_sum_failAt]
    change (∑ x, ∑ y, SampledGame.dist (QLD.PauliCL.binaryQuery hm b false)
      (QLD.PauliCL.binaryQuery hm b true) x y * R.failAt x y) = _
    rw [SampledGame.sum_dist_mul]
    simp only [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
      QLD.PauliCL.binaryQuery, Bool.false_eq_true, ↓reduceIte, ← Finset.sum_div, div_div, n]
    congr 1
    ring
  rw [hform]
  calc _ ≤ (∑ _ : QLD.TyEdge, c) / Fintype.card QLD.TyEdge :=
      div_le_div_of_nonneg_right hs he.le
    _ = c := by simp [he.ne']
end MIPRE.Introspection.PauliRestriction
