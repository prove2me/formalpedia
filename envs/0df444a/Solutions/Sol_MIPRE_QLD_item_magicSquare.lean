-- Prove2me | solution 1 for MIPRE.QLD.item_magicSquare
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:42:29.951274+00:00
-- url     : https://prove2.me/submissions/e6337c3e-3fb1-4d45-8240-aae222d82cd7

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/WinMS.lean (solution of MIPRE.QLD.item_magicSquare);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
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
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
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
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
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
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
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
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Background_QLD_Win
import Definitions.Def_MIPRE_Background_QLD_Anticomm
import Definitions.Def_MIPRE_Background_QLD_WinMS
import Theorems.Thm_MIPRE_POVM_posSemidef
import Theorems.Thm_MIPRE_POVM_sum_val
import Theorems.Thm_MIPRE_QLD_MS_close_of_fail
import Theorems.Thm_MIPRE_QLD_MS_snorm_anti
import Theorems.Thm_MIPRE_QLD_MS_snorm_bOp_eq
import Theorems.Thm_MIPRE_QLD_condFail_ms_le
import Theorems.Thm_MIPRE_QLD_incidence_of_questionDist_ne_zero
import Theorems.Thm_MIPRE_QLD_sum_msEps_le
import Theorems.Thm_MIPRE_bornProb_nonneg
import Theorems.Thm_MIPRE_exists_projective_dilation
import Theorems.Thm_MIPRE_sum_bornProb

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
theorem condWin_le_one (hψ : star ψ ⬝ᵥ ψ = 1) (x : X) (y : Y) :
    condWin G ψ MA MB x y ≤ 1 := by
  rw [← sum_bornProb hψ (MA x) (MB y)]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  have hb : 0 ≤ bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val) :=
    bornProb_nonneg ψ ((MA x).posSemidef a) ((MB y).posSemidef b)
  by_cases h : G.D x y a b
  · rw [if_pos h, one_mul]
  · rw [if_neg h, zero_mul]
    exact hb
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
theorem condFail_nonneg (hψ : star ψ ⬝ᵥ ψ = 1) (x : X) (y : Y) :
    0 ≤ condFail G ψ MA MB x y :=
  sub_nonneg.mpr (condWin_le_one hψ x y)
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
/-- **The failure probability is the average of the conditional failures.** -/
theorem one_sub_povmValue_eq :
    1 - povmValue G ψ MA MB = ∑ x, ∑ y, G.μ x y * condFail G ψ MA MB x y := by
  have h : ∑ x, ∑ y, G.μ x y * condFail G ψ MA MB x y
      = (∑ x, ∑ y, G.μ x y) - ∑ x, ∑ y, G.μ x y * condWin G ψ MA MB x y := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by rw [condFail]; ring
  rw [h, G.μ_sum_one, povmValue]
end
end MIPRE

namespace MIPRE.LCS.MagicSquare
section
open MIPRE.LCS
theorem V_eq_cells (c : Fin layout.r) : layout.V c = {cell c 0, cell c 1, cell c 2} := by
  fin_cases c <;> decide
end
end MIPRE.LCS.MagicSquare

namespace MIPRE.LCS.MagicSquare
section
open MIPRE.LCS
theorem cell_ne_01 (c : Fin layout.r) : cell c 0 ≠ cell c 1 := by fin_cases c <;> decide
end
end MIPRE.LCS.MagicSquare

namespace MIPRE.LCS.MagicSquare
section
open MIPRE.LCS
theorem cell_ne_02 (c : Fin layout.r) : cell c 0 ≠ cell c 2 := by fin_cases c <;> decide
end
end MIPRE.LCS.MagicSquare

namespace MIPRE.LCS.MagicSquare
section
open MIPRE.LCS
theorem cell_ne_12 (c : Fin layout.r) : cell c 1 ≠ cell c 2 := by fin_cases c <;> decide
end
end MIPRE.LCS.MagicSquare

namespace MIPRE.LCS.MagicSquare
section
open MIPRE.LCS
/-- A sum over a constraint's support is the sum over its three cells. -/
theorem sum_cells (c : Fin layout.r) (a : Fin layout.s → ZMod 2) :
    ∑ k ∈ layout.V c, a k = a (cell c 0) + a (cell c 1) + a (cell c 2) := by
  classical
  rw [V_eq_cells, Finset.sum_insert (by simp [cell_ne_01 c, cell_ne_02 c]),
    Finset.sum_insert (by simp [cell_ne_12 c]), Finset.sum_singleton, add_assoc]
end
end MIPRE.LCS.MagicSquare

namespace MIPRE.LCS.MagicSquare
section
open MIPRE.LCS
theorem cell_cellIdx {c : Fin layout.r} {j : Fin layout.s} (h : j ∈ layout.V c) :
    cell c (cellIdx c j) = j := by
  revert h; revert j; revert c; decide
end
end MIPRE.LCS.MagicSquare

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LCS.MagicSquare
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
omit [DecidableEq F] [NeZero m] in
theorem gam_ne_zero_of_mem_acommSet {c : Content F m} (hc : c ∈ acommSet) :
    gam c.omega ≠ 0 := (Finset.mem_filter.mp hc).2
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LCS.MagicSquare
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}
/-- The three components of an acceptance. -/
theorem of_accepts {x y : Question F m} {a b : Answer F m d}
    (h : accepts hm x y a b = true) :
    x.fmtOk a = true ∧ y.fmtOk b = true ∧ subtests hm x y a b = true := by
  rw [accepts, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LCS.MagicSquare
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}
omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem eq_bit_of_fmtOk_var {j : Fin layout.s} {ω : Omega F m} {a : Answer F m d}
    (h : (Question.var j ω).fmtOk a = true) : ∃ b, a = .bit b := by
  cases a <;> first | exact ⟨_, rfl⟩ | simp [Question.fmtOk] at h
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LCS.MagicSquare
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}
omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem eq_bitTriple_of_fmtOk {i : Fin layout.r} {ω : Omega F m} {a : Answer F m d}
    (h : (Question.con i ω).fmtOk a = true) : ∃ α, a = .bitTriple α := by
  cases a <;> first | exact ⟨_, rfl⟩ | simp [Question.fmtOk] at h
end
end MIPRE.QLD

namespace MIPRE.QLD.MS
noncomputable section
open Finset Matrix Kronecker MIPRE MIPRE.LCS MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem repPOVM_eq (MA : layout.Question → POVM layout.Answer dA) (c : Fin layout.r) (k : PV) :
    repPOVM MA c k
      = ∑ d ∈ {d ∈ (univ : Finset layout.Answer) | rep c d = k},
          ((MA (Sum.inl c)).mats d).val := rfl
end
end MIPRE.QLD.MS

namespace MIPRE.QLD.MS
noncomputable section
open Finset Matrix Kronecker MIPRE MIPRE.LCS MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem repPOVM_nonneg (MA : layout.Question → POVM layout.Answer dA) (c : Fin layout.r)
    (k : PV) : (0 : Matrix dA dA ℂ) ≤ repPOVM MA c k :=
  Finset.sum_nonneg fun d _ => Subtype.coe_le_coe.mpr ((MA (Sum.inl c)).nonneg d)
end
end MIPRE.QLD.MS

namespace MIPRE.QLD.MS
noncomputable section
open Finset Matrix Kronecker MIPRE MIPRE.LCS MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem repPOVM_posSemidef (MA : layout.Question → POVM layout.Answer dA) (c : Fin layout.r)
    (k : PV) : (repPOVM MA c k).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (repPOVM_nonneg MA c k)
end
end MIPRE.QLD.MS

namespace MIPRE.QLD.MS
noncomputable section
open Finset Matrix Kronecker MIPRE MIPRE.LCS MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem sum_repPOVM (MA : layout.Question → POVM layout.Answer dA) (c : Fin layout.r) :
    ∑ k, repPOVM MA c k = (1 : Matrix dA dA ℂ) := by
  classical
  rw [Finset.sum_congr rfl fun k (_ : k ∈ univ) => repPOVM_eq MA c k,
    Finset.sum_fiberwise (univ : Finset layout.Answer) (rep c)
      fun d => ((MA (Sum.inl c)).mats d).val]
  exact POVM.sum_val _
end
end MIPRE.QLD.MS

namespace MIPRE.QLD.MS
noncomputable section
open Finset Matrix Kronecker MIPRE MIPRE.LCS MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem nonempty_dilated (MA : layout.Question → POVM layout.Answer dA) :
    Nonempty (Dilated MA) := by
  obtain ⟨P, hsa, hidem, hsum, hcomp⟩ := exists_projective_dilation ((0, 0) : PV)
    (E := repPOVM MA) (fun c k => repPOVM_posSemidef MA c k) (sum_repPOVM MA)
  exact ⟨{ P := P
           isPVM := fun c => ⟨fun k => by
              rw [← Matrix.star_eq_conjTranspose]; exact hsa c k, hidem c, hsum c⟩
           compress := hcomp }⟩
end
end MIPRE.QLD.MS

namespace MIPRE.QLD.MS
noncomputable section
open Finset Matrix Kronecker MIPRE MIPRE.LCS MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {MA : layout.Question → POVM layout.Answer dA}
variable {MB : layout.Question → POVM layout.Answer dB}
variable {MA : layout.Question → POVM layout.Answer dA}
/-- **Direct Magic Square anticommutation** (blueprint `lem:ms-direct-anticomm`), for the player
who receives the variable questions. No projectivity, no isometry, no extracted EPR pairs: the
bound is on the original observables and the original state. -/
theorem ms_direct_anticomm {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (MA : layout.Question → POVM layout.Answer dA)
    (MB : layout.Question → POVM layout.Answer dB)
    {ε : ℝ} (hε : 0 ≤ ε) (hfail : 1 - povmValue nonlocalGame ψ MA MB ≤ ε) :
    ‖stateVecB ψ (anti MB)‖ ^ 2 ≤ 186624 * ε := by
  obtain ⟨D⟩ := nonempty_dilated MA
  have h36 := snorm_anti (MB := MB) (close_of_fail (MB := MB) hψ D hε hfail)
  rw [snorm_bOp_eq] at h36
  have hs : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt hε
  have hb : ‖stateVecB ψ (anti MB)‖ ≤ 432 * Real.sqrt ε := by
    calc ‖stateVecB ψ (anti MB)‖ ≤ 36 * (12 * Real.sqrt ε) := h36
      _ = 432 * Real.sqrt ε := by ring
  nlinarith [norm_nonneg (stateVecB ψ (anti MB)), Real.sqrt_nonneg ε, hb, hs]
end
end MIPRE.QLD.MS

namespace MIPRE.QLD.MS
noncomputable section
open Finset Matrix Kronecker MIPRE MIPRE.LCS MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {MA : layout.Question → POVM layout.Answer dA}
variable {MB : layout.Question → POVM layout.Answer dB}
variable {MA : layout.Question → POVM layout.Answer dA}
/-- **The averaged form.** The bound is pointwise, so averaging it over a family of strategies
on the same pair of spaces costs nothing --- no Jensen step, and the same constant. -/
theorem ms_direct_anticomm_avg {Ω : Type*} [Fintype Ω] (ν : Ω → ℝ) (hν : ∀ ω, 0 ≤ ν ω)
    (ψ : Ω → dA × dB → ℂ) (hψ : ∀ ω, star (ψ ω) ⬝ᵥ ψ ω = 1)
    (MA : Ω → layout.Question → POVM layout.Answer dA)
    (MB : Ω → layout.Question → POVM layout.Answer dB)
    (ε : Ω → ℝ) (hε : ∀ ω, 0 ≤ ε ω)
    (hfail : ∀ ω, 1 - povmValue nonlocalGame (ψ ω) (MA ω) (MB ω) ≤ ε ω) :
    ∑ ω, ν ω * ‖stateVecB (ψ ω) (anti (MB ω))‖ ^ 2 ≤ 186624 * ∑ ω, ν ω * ε ω := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun ω _ => ?_
  have h := ms_direct_anticomm (hψ ω) (MA ω) (MB ω) (hε ω) (hfail ω)
  calc ν ω * ‖stateVecB (ψ ω) (anti (MB ω))‖ ^ 2 ≤ ν ω * (186624 * ε ω) :=
        mul_le_mul_of_nonneg_left h (hν ω)
    _ = 186624 * (ν ω * ε ω) := by ring
end
end MIPRE.QLD.MS

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE MIPRE.LCS.MagicSquare
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem cell_injective (i : Fin layout.r) : Function.Injective (cell i) :=
  Function.LeftInverse.injective (cellIdx_cell i)
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE MIPRE.LCS.MagicSquare
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem msAssign_cell (i : Fin layout.r) (α : Fin 3 → ZMod 2) (t : Fin 3) :
    msAssign (d := d) (F := F) (m := m) i (.bitTriple α) (cell i t) = α t := by
  show (∑ t' : Fin 3, if cell i t' = cell i t then α t' else 0) = α t
  rw [Finset.sum_eq_single t (fun t' _ h => if_neg fun hh => h ((cell_injective i) hh))
    fun h => absurd (Finset.mem_univ t) h]
  exact if_pos rfl
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE MIPRE.LCS.MagicSquare
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem sum_msAssign (i : Fin layout.r) (α : Fin 3 → ZMod 2) :
    ∑ k ∈ layout.V i, msAssign (d := d) (F := F) (m := m) i (.bitTriple α) k = ∑ t, α t := by
  rw [sum_cells, msAssign_cell, msAssign_cell, msAssign_cell, Fin.sum_univ_three]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE MIPRE.LCS.MagicSquare
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
omit [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] [NeZero m] in
theorem msAssign_mem (i : Fin layout.r) (α : Fin 3 → ZMod 2) {j : Fin layout.s}
    (hj : j ∈ layout.V i) :
    msAssign (d := d) (F := F) (m := m) i (.bitTriple α) j = α (cellIdx i j) := by
  obtain ⟨t, rfl⟩ : ∃ t, cell i t = j := ⟨cellIdx i j, cell_cellIdx hj⟩
  rw [msAssign_cell, cellIdx_cell]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE MIPRE.LCS.MagicSquare
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem accepts_ms_of_accepts {hm : m ∣ Fintype.card F} {i : Fin layout.r} {j : Fin layout.s}
    {ω : Omega F m} {a b : Answer F m d} (hγ : gam ω ≠ 0)
    (h : accepts hm (.con i ω) (.var j ω) a b = true) :
    game.accepts (.inl i) (.inr j) (msAns (.inl i) a) (msAns (.inr j) b) = true := by
  obtain ⟨hfa, hfb, hs⟩ := of_accepts h
  obtain ⟨α, rfl⟩ := eq_bitTriple_of_fmtOk hfa
  obtain ⟨b', rfl⟩ := eq_bit_of_fmtOk_var hfb
  have hs' : (j ∈ layout.V i ∧ (∑ t, α t) = game.b i) ∧ α (cellIdx i j) = b' := by
    simpa [subtests, Question.ty, pairTest, hγ] using hs
  have h1 : j ∈ layout.V i := hs'.1.1
  have h2 : ∑ k ∈ layout.V i, msAssign (d := d) (F := F) (m := m) i (.bitTriple α) k = game.b i := by
    rw [sum_msAssign]; exact hs'.1.2
  have h3 : msAssign (d := d) (F := F) (m := m) i (.bitTriple α) j = b' := by
    rw [msAssign_mem i α h1]; exact hs'.2
  simp [msAns, MIPRE.LCS.Game.accepts, rdBit, h1, h2, h3]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE MIPRE.LCS.MagicSquare
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem accepts_ms_of_accepts' {hm : m ∣ Fintype.card F} {i : Fin layout.r} {j : Fin layout.s}
    {ω : Omega F m} {a b : Answer F m d} (hγ : gam ω ≠ 0)
    (h : accepts hm (.var j ω) (.con i ω) a b = true) :
    game.accepts (.inr j) (.inl i) (msAns (.inr j) a) (msAns (.inl i) b) = true := by
  obtain ⟨hfa, hfb, hs⟩ := of_accepts h
  obtain ⟨b', rfl⟩ := eq_bit_of_fmtOk_var hfa
  obtain ⟨α, rfl⟩ := eq_bitTriple_of_fmtOk hfb
  have hs' : (j ∈ layout.V i ∧ (∑ t, α t) = game.b i) ∧ α (cellIdx i j) = b' := by
    simpa [subtests, Question.ty, pairTest, hγ] using hs
  have h1 : j ∈ layout.V i := hs'.1.1
  have h2 : ∑ k ∈ layout.V i, msAssign (d := d) (F := F) (m := m) i (.bitTriple α) k = game.b i := by
    rw [sum_msAssign]; exact hs'.1.2
  have h3 : msAssign (d := d) (F := F) (m := m) i (.bitTriple α) j = b' := by
    rw [msAssign_mem i α h1]; exact hs'.2
  simp [msAns, MIPRE.LCS.Game.accepts, rdBit, h1, h2, h3]
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE MIPRE.LCS.MagicSquare
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
theorem msEps_nonneg (hψ : star ψ ⬝ᵥ ψ = 1) (ω : Omega F m) : 0 ≤ msEps hm ψ MA MB ω :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg (layout.questionDist_nonneg _ _) (condFail_nonneg hψ _ _)
end
end MIPRE.QLD

namespace MIPRE.QLD
noncomputable section
open Finset MIPRE MIPRE.LCS.MagicSquare
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
/-- **The conditional Magic Square strategy of an anticommuting tuple fails by at most
`msEps`.** -/
theorem one_sub_povmValue_ms_le {ω : Omega F m} (hγ : gam ω ≠ 0) :
    1 - povmValue nonlocalGame ψ (msPOVM MA ω) (msPOVM MB ω) ≤ msEps hm ψ MA MB ω := by
  rw [one_sub_povmValue_eq, msEps]
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
  by_cases h : layout.questionDist x y = 0
  · rw [show nonlocalGame.μ x y = layout.questionDist x y from rfl, h, zero_mul, zero_mul]
  · rw [show nonlocalGame.μ x y = layout.questionDist x y from rfl]
    refine mul_le_mul_of_nonneg_left ?_ (layout.questionDist_nonneg x y)
    rcases incidence_of_questionDist_ne_zero h with ⟨i, j, _, rfl, rfl⟩ | ⟨i, j, _, rfl, rfl⟩
    · exact condFail_ms_le ω _ _ fun a b hab => accepts_ms_of_accepts hγ hab
    · exact condFail_ms_le ω _ _ fun a b hab => accepts_ms_of_accepts' hγ hab
end
end MIPRE.QLD

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD
open Finset MIPRE MIPRE.LCS.MagicSquare
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
theorem _root_.solution (hψ : star ψ ⬝ᵥ ψ = 1) {ε : ℝ}
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) :
    ∑ c ∈ acommSet, (Fintype.card (Content F m) : ℝ)⁻¹ *
        ‖stateVecB ψ (MS.anti (msPOVM MB c.omega))‖ ^ 2
      ≤ 16049664 * ε := by
  classical
  have havg := MS.ms_direct_anticomm_avg (Ω := ↥(acommSet : Finset (Content F m)))
    (fun _ => (Fintype.card (Content F m) : ℝ)⁻¹) (fun _ => by positivity)
    (fun _ => ψ) (fun _ => hψ)
    (fun c => msPOVM MA c.val.omega) (fun c => msPOVM MB c.val.omega)
    (fun c => msEps hm ψ MA MB c.val.omega) (fun c => msEps_nonneg hψ _)
    fun c => one_sub_povmValue_ms_le (gam_ne_zero_of_mem_acommSet c.2)
  rw [Finset.sum_coe_sort acommSet fun c => (Fintype.card (Content F m) : ℝ)⁻¹ *
      ‖stateVecB ψ (MS.anti (msPOVM MB c.omega))‖ ^ 2,
    Finset.sum_coe_sort acommSet fun c => (Fintype.card (Content F m) : ℝ)⁻¹ *
      msEps hm ψ MA MB c.omega] at havg
  refine le_trans havg ?_
  rw [show (16049664 : ℝ) * ε = 186624 * (86 * ε) from by ring]
  exact mul_le_mul_of_nonneg_left (sum_msEps_le hψ hfail) (by norm_num)
end MIPRE.QLD
