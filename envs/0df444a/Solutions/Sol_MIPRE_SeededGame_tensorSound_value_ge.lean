-- Prove2me | solution 1 for MIPRE.SeededGame.tensorSound_value_ge
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:49:21.890813+00:00
-- url     : https://prove2.me/submissions/1b9f08e5-1760-4e10-85fb-0a2e050e116a

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/OracularTensor.lean (solution of MIPRE.SeededGame.tensorSound_value_ge);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_OracularGame
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OracularSound
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_OracularTensor
import Theorems.Thm_MIPRE_SeededGame_succAt_tensorSound_ge
import Theorems.Thm_MIPRE_SeededGame_sum_dist_mul
import Theorems.Thm_MIPRE_SeededGame_sum_failAt_four_le
import Theorems.Thm_MIPRE_TensorProductStrategy_failAt_nonneg

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
section
open Finset ComplexOrder Matrix
variable {n : Type*} [Fintype n]
/-- `𝔼_μ √f ≤ √(𝔼_μ 1) · √(𝔼_μ f)`, which for a probability distribution is Jensen's
inequality for the square root. It is Cauchy--Schwarz applied to `√μ` and `√(μ f)`. -/
theorem sum_mul_sqrt_le {ι : Type*} (s : Finset ι) (μ f : ι → ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hf : ∀ i, 0 ≤ f i) :
    ∑ i ∈ s, μ i * √(f i) ≤ √(∑ i ∈ s, μ i) * √(∑ i ∈ s, μ i * f i) := by
  have key : ∀ i, μ i * √(f i) = √(μ i) * √(μ i * f i) := by
    intro i
    rw [Real.sqrt_mul (hμ i), ← mul_assoc, Real.mul_self_sqrt (hμ i)]
  rw [Finset.sum_congr rfl fun i _ => key i]
  exact Real.sum_sqrt_mul_sqrt_le _ hμ (fun i => mul_nonneg (hμ i) (hf i))
end
end MIPRE

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

namespace MIPRE.SeededGame
section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {A : Type*} [Fintype A] [DecidableEq A] [Inhabited A]
variable (S : SeededGame V A)
variable {S}
/-- The value of the extracted strategy is the average over the seed of its conditional success
at the question pair the seed determines. -/
theorem tensorSound_value_eq (N : TensorProductStrategy S.oracular.toGame) :
    (S.tensorSound N).value
      = (Fintype.card V : ℝ)⁻¹ * ∑ z, (S.tensorSound N).succAt (S.LA z) (S.LB z) := by
  rw [TensorProductStrategy.value_eq_sum_succAt]
  exact S.sum_dist_mul _
end
end MIPRE.SeededGame

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SeededGame
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {A : Type*} [Fintype A] [DecidableEq A] [Inhabited A]
variable (S : SeededGame V A)
variable {S}
theorem _root_.solution (N : TensorProductStrategy S.oracular.toGame) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hval : 1 - ε ≤ N.value) :
    1 - 24 * √ε ≤ (S.tensorSound N).value := by
  have hcardV : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hW : (0 : ℝ) < (Fintype.card V : ℝ)⁻¹ := by positivity
  set F : V → ℝ := fun z => N.failAt (Role.alice, S.LA z) (Role.alice, S.LA z)
    + N.failAt (Role.oracle, z) (Role.alice, S.LA z)
    + N.failAt (Role.oracle, z) (Role.bob, S.LB z) with hF
  set Gm : V → ℝ := fun z => N.failAt (Role.oracle, z) (Role.oracle, z) with hGm
  have hF0 : ∀ z, 0 ≤ F z := fun z =>
    add_nonneg (add_nonneg (N.failAt_nonneg _ _) (N.failAt_nonneg _ _)) (N.failAt_nonneg _ _)
  have hG0 : ∀ z, 0 ≤ Gm z := fun z => N.failAt_nonneg _ _
  -- the budget, split between the game check and the three consistencies
  have hbud : (Fintype.card V : ℝ)⁻¹ * ∑ z, Gm z + (Fintype.card V : ℝ)⁻¹ * ∑ z, F z
      ≤ 9 * ε := by
    have h := sum_failAt_four_le N
    rw [← mul_add, ← Finset.sum_add_distrib]
    linarith
  have hGbud : (Fintype.card V : ℝ)⁻¹ * ∑ z, Gm z ≤ 9 * ε := by
    have : 0 ≤ (Fintype.card V : ℝ)⁻¹ * ∑ z, F z :=
      mul_nonneg hW.le (Finset.sum_nonneg fun z _ => hF0 z)
    linarith
  have hFbud : (Fintype.card V : ℝ)⁻¹ * ∑ z, F z ≤ 9 * ε := by
    have : 0 ≤ (Fintype.card V : ℝ)⁻¹ * ∑ z, Gm z :=
      mul_nonneg hW.le (Finset.sum_nonneg fun z _ => hG0 z)
    linarith
  -- the averaging step: `𝔼 √(6 F) ≤ √(54 ε)`
  have hjensen : (Fintype.card V : ℝ)⁻¹ * ∑ z, √(6 * F z) ≤ √(54 * ε) := by
    have hj0 := sum_mul_sqrt_le (univ : Finset V) (fun _ => (Fintype.card V : ℝ)⁻¹)
      (fun z => 6 * F z) (fun _ => hW.le) fun z => mul_nonneg (by norm_num) (hF0 z)
    have hj1 : (∑ _z : V, (Fintype.card V : ℝ)⁻¹) = 1 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
    rw [hj1, Real.sqrt_one, one_mul, ← Finset.mul_sum, ← Finset.mul_sum] at hj0
    refine hj0.trans (Real.sqrt_le_sqrt ?_)
    have h6 : (Fintype.card V : ℝ)⁻¹ * ∑ z, 6 * F z
        = 6 * ((Fintype.card V : ℝ)⁻¹ * ∑ z, F z) := by
      rw [← Finset.mul_sum]
      ring
    rw [h6]
    linarith
  -- put the seeds together
  rw [tensorSound_value_eq]
  have hmono : (Fintype.card V : ℝ)⁻¹ * ∑ z, (1 - Gm z - 2 * √(6 * F z))
      ≤ (Fintype.card V : ℝ)⁻¹ * ∑ z, (S.tensorSound N).succAt (S.LA z) (S.LB z) :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ => succAt_tensorSound_ge N z) hW.le
  refine le_trans ?_ hmono
  have hexp : (Fintype.card V : ℝ)⁻¹ * ∑ z, (1 - Gm z - 2 * √(6 * F z))
      = 1 - (Fintype.card V : ℝ)⁻¹ * (∑ z, Gm z)
        - 2 * ((Fintype.card V : ℝ)⁻¹ * ∑ z, √(6 * F z)) := by
    rw [show (∑ z : V, (1 - Gm z - 2 * √(6 * F z)))
        = ((∑ _z : V, (1 : ℝ)) - ∑ z, Gm z) - 2 * ∑ z, √(6 * F z) from by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.mul_sum],
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, mul_sub, mul_sub,
      inv_mul_cancel₀ hcardV.ne']
    ring
  rw [hexp]
  -- and the final arithmetic
  have heps : ε ≤ √ε := by
    have h1 : √(ε ^ 2) ≤ √ε := Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq hε0] at h1
  have hs54 : √(54 * ε) ≤ (7.35 : ℝ) * √ε := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 54)]
    have h54 : √(54 : ℝ) ≤ 7.35 := by
      rw [show (7.35 : ℝ) = √(7.35 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    exact mul_le_mul_of_nonneg_right h54 (Real.sqrt_nonneg ε)
  nlinarith [hjensen, hGbud, heps, hs54, Real.sqrt_nonneg ε]
end MIPRE.SeededGame
