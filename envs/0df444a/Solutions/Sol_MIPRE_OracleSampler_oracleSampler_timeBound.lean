-- Prove2me | solution 1 for MIPRE.OracleSampler.oracleSampler_timeBound
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:50:42.444827+00:00
-- url     : https://prove2.me/submissions/a689dc85-b88d-43f7-b173-31ef3614b557

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/OracularSampler.lean (solution of MIPRE.OracleSampler.oracleSampler_timeBound);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
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
import Definitions.Def_MIPRE_Foundations_OracularComplete
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_OracularTyped
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCall
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgRoute
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Repeat_Prims
import Definitions.Def_MIPRE_Foundations_Repeat_MapLoop
import Definitions.Def_MIPRE_Foundations_Repeat_Sampler
import Definitions.Def_MIPRE_Foundations_CL_Repeat
import Definitions.Def_MIPRE_Foundations_Repeat_Bits
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Pipeline_Budget
import Definitions.Def_MIPRE_Foundations_Pipeline_Repetition
import Definitions.Def_MIPRE_Foundations_Repeat_RepSampler
import Definitions.Def_MIPRE_Foundations_Repeat_Dom
import Definitions.Def_MIPRE_Foundations_Repeat_SamplerCost
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCost
import Definitions.Def_MIPRE_Foundations_OracularSampler
import Theorems.Thm_MIPRE_Cost_hardcode_time
import Theorems.Thm_MIPRE_OracleSampler_core_runs_within

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Repeat.Dom
section
variable {W X K : ℕ}
theorem le {c m e v : ℕ} (h : Dom W X K c m e v) : v ≤ c * (W + 1) ^ m * X ^ (e * (K + 1)) := h
end
end MIPRE.Repeat.Dom

namespace MIPRE.Repeat.Dom
section
variable {W X K : ℕ}
theorem of_le {c m e v v' : ℕ} (h : Dom W X K c m e v) (hv : v' ≤ v) : Dom W X K c m e v' :=
  hv.trans h
end
end MIPRE.Repeat.Dom

namespace MIPRE.Repeat.Dom
section
variable {W X K : ℕ}
theorem const (c : ℕ) : Dom W X K c 0 0 c := by simp [Dom]
end
end MIPRE.Repeat.Dom

namespace MIPRE.Repeat.Dom
section
variable {W X K : ℕ}
theorem ofLeW {v : ℕ} (h : v ≤ W) : Dom W X K 1 1 0 v := by simp [Dom]; omega
end
end MIPRE.Repeat.Dom

namespace MIPRE.Repeat.Dom
section
variable {W X K : ℕ}
/-- An affine function of `W` is dominated by `(a + b)(W + 1)`. -/
theorem ofAffine {a b v : ℕ} (h : v ≤ a * W + b) : Dom W X K (a + b) 1 0 v := by
  simp only [Dom, pow_one, zero_mul, pow_zero, mul_one]
  nlinarith
end
end MIPRE.Repeat.Dom

namespace MIPRE.Repeat.Dom
section
variable {W X K : ℕ}
theorem ofLeX (hX : 1 ≤ X) {v : ℕ} (h : v ≤ X) : Dom W X K 1 0 1 v := by
  simp only [Dom, one_mul, pow_zero, one_mul]
  exact h.trans (Nat.le_self_pow (by omega) X)
end
end MIPRE.Repeat.Dom

namespace MIPRE.Repeat.Dom
section
variable {W X K : ℕ}
theorem mono (hX : 1 ≤ X) {c c' m m' e e' v : ℕ} (h : Dom W X K c m e v) (hc : c ≤ c') (hm : m ≤ m')
    (he : e ≤ e') : Dom W X K c' m' e' v := by
  unfold Dom at h ⊢
  refine h.trans ?_
  gcongr <;> first | omega | exact Nat.mul_le_mul_right _ he
end
end MIPRE.Repeat.Dom

namespace MIPRE.Repeat.Dom
section
variable {W X K : ℕ}
theorem add (hX : 1 ≤ X) {c₁ c₂ m₁ m₂ e₁ e₂ v₁ v₂ : ℕ} (h₁ : Dom W X K c₁ m₁ e₁ v₁)
    (h₂ : Dom W X K c₂ m₂ e₂ v₂) : Dom W X K (c₁ + c₂) (max m₁ m₂) (max e₁ e₂) (v₁ + v₂) := by
  have h₁' := h₁.mono hX (c' := c₁) (m' := max m₁ m₂) (e' := max e₁ e₂) le_rfl (le_max_left _ _)
    (le_max_left _ _)
  have h₂' := h₂.mono hX (c' := c₂) (m' := max m₁ m₂) (e' := max e₁ e₂) le_rfl (le_max_right _ _)
    (le_max_right _ _)
  unfold Dom at h₁' h₂' ⊢
  rw [Nat.add_mul, Nat.add_mul]
  omega
end
end MIPRE.Repeat.Dom

namespace MIPRE.Repeat.Dom
section
variable {W X K : ℕ}
theorem mul {c₁ c₂ m₁ m₂ e₁ e₂ v₁ v₂ : ℕ} (h₁ : Dom W X K c₁ m₁ e₁ v₁) (h₂ : Dom W X K c₂ m₂ e₂ v₂) :
    Dom W X K (c₁ * c₂) (m₁ + m₂) (e₁ + e₂) (v₁ * v₂) := by
  unfold Dom at h₁ h₂ ⊢
  calc v₁ * v₂ ≤ (c₁ * (W + 1) ^ m₁ * X ^ (e₁ * (K + 1))) * (c₂ * (W + 1) ^ m₂ * X ^ (e₂ * (K + 1))) :=
        Nat.mul_le_mul h₁ h₂
    _ = c₁ * c₂ * (W + 1) ^ (m₁ + m₂) * X ^ ((e₁ + e₂) * (K + 1)) := by
        rw [pow_add, Nat.add_mul, pow_add]; ring
end
end MIPRE.Repeat.Dom

namespace MIPRE.Repeat.Dom
section
variable {W X K : ℕ}
theorem pow {c m e v : ℕ} (h : Dom W X K c m e v) (p : ℕ) :
    Dom W X K (c ^ p) (m * p) (e * p) (v ^ p) := by
  induction p with
  | zero => simpa using const 1
  | succ p ih =>
    have := ih.mul h
    simpa [pow_succ, Nat.mul_succ] using this
end
end MIPRE.Repeat.Dom

namespace MIPRE.Repeat.Dom
section
variable {W X K : ℕ}
/-- `X^K` itself: one unit of the exponent. -/
theorem powK (hX : 1 ≤ X) : Dom W X K 1 0 1 (X ^ K) := by
  simp only [Dom, one_mul, pow_zero]
  exact Nat.pow_le_pow_right hX (by omega)
end
end MIPRE.Repeat.Dom

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
variable {ℓ : ℕ} (S : CL.Sampler ℓ) (lam tau n : ℕ) (R : Budget) (W : ℕ)
theorem nat_size_le_self (x : ℕ) : Nat.size x ≤ x := Nat.size_le.mpr Nat.lt_two_pow_self
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
variable {ℓ : ℕ} (S : CL.Sampler ℓ) (lam tau n : ℕ) (R : Budget) (W : ℕ)
theorem esize_nat_le' (x : ℕ) : esize x ≤ 4 * x + 1 :=
  (esize_nat_le x).trans (by have := nat_size_le_self x; omega)
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
variable {ℓ : ℕ} (S : CL.Sampler ℓ) (lam tau n : ℕ) (R : Budget) (W : ℕ)
variable {W X K : ℕ}
theorem dom_esize {x : ℕ} (hx : x ≤ W) : Dom W X K (4 + 1) 1 0 (esize x) :=
  Dom.ofAffine (by have := esize_nat_le' x; omega)
end
end MIPRE.Repeat

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.OracleSampler
open Cost Cost.PolyTimeFun
open OracleSampler CL
open Repeat
variable {ℓ : ℕ} (S : Sampler (ℓ + 1))
variable {ℓ : ℕ} (S : Sampler (ℓ + 1))
theorem _root_.solution : ∃ c m e, ∀ {ℓ : ℕ} (S : Sampler (ℓ + 1)) (n B k W : ℕ),
    B ≤ W → esize S.prog ≤ W → n ≤ W → S.TimeBoundAt n B k →
    (oracleSampler S).TimeBoundAt n (c * (W + 1) ^ m) (e * (k + 1)) := by
  -- the three polynomials, at dominated arguments
  have dom_poly : ∀ (Q : Polynomial ℕ) (cy my ey : ℕ), ∃ c m e, ∀ (W X K : ℕ) {y : ℕ}, 1 ≤ X →
      1 ≤ y → Dom W X K cy my ey y → Dom W X K c m e (Q.eval y) := fun Q cy my ey =>
    ⟨_, _, _, fun W X K {y} _ hy h =>
      ((Dom.const _).mul (h.pow Q.natDegree)).of_le (polynomial_eval_le_sum_coeff_mul_pow Q hy)⟩
  -- the size of the core's input
  have dom_xs : ∃ c m e, ∀ (W X K : ℕ) {p n D : ℕ}, 1 ≤ X → p ≤ W → n ≤ W → D + 1 = X →
      Dom W X K c m e (p + esize n + D + 2) := ⟨_, _, _, fun W X K {p n D} hX hp hn hD => by
    subst hD
    exact (((Dom.ofLeW hp).add hX (dom_esize hn)).add hX (Dom.ofLeX hX (by omega))).add hX
      (Dom.const 2)⟩
  obtain ⟨cx, mx, ex, hxs⟩ := dom_xs
  obtain ⟨cR, mR, eR, hR⟩ := dom_poly route.timeBound cx mx ex
  -- the argument of the universal machine's bound
  have dom_uarg : ∃ c m e, ∀ (W X K : ℕ) {xs B : ℕ}, 1 ≤ X → 1 ≤ xs → B ≤ W →
      Dom W X K cx mx ex xs → Dom W X K c m e (xs + route.timeBound.eval xs + B * X ^ (5 * K)) :=
    ⟨_, _, _, fun W X K {xs B} hX hxs1 hB h => by
      have hp : Dom W X K 1 0 5 (X ^ (5 * K)) := by
        have := (Dom.powK (W := W) (K := K) hX).pow 5
        simpa [pow_mul, mul_comm] using this
      exact (h.add hX (hR W X K hX hxs1 h)).add hX ((Dom.ofLeW hB).mul hp)⟩
  obtain ⟨cA, mA, eA, hA⟩ := dom_uarg
  obtain ⟨cU', mU', eU', hU⟩ := dom_poly selfUniversal.bound cA mA eA
  have dom_tU2 : ∃ c m e, ∀ (W X K : ℕ) {y : ℕ}, 1 ≤ X → Dom W X K cU' mU' eU' y →
      Dom W X K c m e (y + 2) := ⟨_, _, _, fun W X K {y} hX h => h.add hX (Dom.const 2)⟩
  obtain ⟨c2, m2, e2, h2⟩ := dom_tU2
  obtain ⟨cP, mP, eP, hP⟩ := dom_poly post.timeBound c2 m2 e2
  exact ⟨_, _, _, fun {ℓ} S n B k W hB hsp hn hS d => by
    obtain ⟨r, t, ht, run⟩ := core_runs_within S n hS d
    refine ⟨r, _, ?_, hardcode_time core_closed run⟩
    have hX : 1 ≤ d.size + 1 := by omega
    have hxsz : (Data.cons (encode S.prog) (.cons (encode n) d)).size =
        esize S.prog + esize n + d.size + 2 := by
      simp only [Data.size_cons, esize]
      omega
    have hx := hxs W (d.size + 1) k hX hsp hn rfl
    rw [← hxsz] at hx
    have hx1 : 1 ≤ (Data.cons (encode S.prog) (.cons (encode n) d)).size := Data.size_pos _
    have hRt := hR W (d.size + 1) k hX hx1 hx
    have hua := hA W (d.size + 1) k hX hx1 hB hx
    have hu := hU W (d.size + 1) k hX (by omega) hua
    have hp := hP W (d.size + 1) k hX (by omega) (h2 W (d.size + 1) k hX hu)
    have hcore : Dom W (d.size + 1) k _ _ _
        (coreCost (Data.cons (encode S.prog) (.cons (encode n) d)).size B k (d.size + 1)) :=
      ((((Dom.const 5).mul hRt).add hX ((Dom.const 2).mul hu)).add hX hp).add hX (Dom.const 25)
    have hsz1 : (encode S.prog : Data).size ≤ W := hsp
    have hin : (Data.cons (encode n) d).size = esize n + d.size + 1 := by
      simp only [Data.size_cons, esize]
    have htot := (((hcore.add hX (Dom.ofLeW hsz1)).add hX
      (((dom_esize hn).add hX (Dom.ofLeX hX (le_refl _))).add hX (Dom.const 1))).add hX
      (Dom.const 3))
    refine le_trans ?_ htot.le
    rw [hin]
    omega⟩
end MIPRE.OracleSampler
