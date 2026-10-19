-- Prove2me | solution 1 for MIPRE.Repeat.repSampler_timeBound
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:56:39.102134+00:00
-- url     : https://prove2.me/submissions/50d2b85d-8ecf-4077-97b0-a77a5d1554b0

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/SamplerCost.lean (solution of MIPRE.Repeat.repSampler_timeBound);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Pipeline_Budget
import Definitions.Def_MIPRE_Foundations_Pipeline_Repetition
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Repeat_Prims
import Definitions.Def_MIPRE_Foundations_Repeat_MapLoop
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Repeat_Sampler
import Definitions.Def_MIPRE_Foundations_CL_Repeat
import Definitions.Def_MIPRE_Foundations_Repeat_Bits
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Repeat_RepSampler
import Definitions.Def_MIPRE_Foundations_Repeat_Dom
import Definitions.Def_MIPRE_Foundations_Repeat_SamplerCost
import Theorems.Thm_MIPRE_Repeat_repSampler_halts_within

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
theorem univ_bound_le {y : ℕ} (hy : 1 ≤ y) : selfUniversal.bound.eval y ≤ cU * y ^ dU :=
  polynomial_eval_le_sum_coeff_mul_pow _ hy
end
end MIPRE.Repeat

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

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
variable {ℓ : ℕ} (S : CL.Sampler ℓ) (lam tau n : ℕ) (R : Budget) (W : ℕ)
variable {W X K : ℕ}
theorem dom_toUnaryCost : ∃ c m e, ∀ (W X K : ℕ) {x : ℕ}, 1 ≤ X → x ≤ W →
    Dom W X K c m e (toUnaryCost x) := by
  exact ⟨_, _, _, fun W X K {x} hX hx => by
    unfold toUnaryCost
    have h1 : Dom W X K (1 + 2) 1 0 (Nat.size x + 2) :=
      Dom.ofAffine (by have := nat_size_le_self x; omega)
    have h2 : Dom W X K (1 + 1) 1 0 (x + 1) := Dom.ofAffine (by omega)
    have h3 : Dom W X K (4 + 14) 1 0 (4 * x + 14) := Dom.ofAffine (by omega)
    have h5 : Dom W X K (8 + 0) 1 0 (8 * x) := Dom.ofAffine (by omega)
    exact h1.mul ((((h2.mul h3).add hX ((Dom.const 7).mul (dom_esize hx))).add hX h5).add hX
      (Dom.const 90))⟩
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
variable {ℓ : ℕ} (S : CL.Sampler ℓ) (lam tau n : ℕ) (R : Budget) (W : ℕ)
variable {W X K : ℕ}
theorem dom_powCost : ∃ c m e', ∀ (W X K : ℕ) {e L sz : ℕ}, 1 ≤ X → e ≤ W → L ≤ 2 * W →
    sz ≤ 12 * W + 3 → Dom W X K c m e' (powCost e L sz) := by
  exact ⟨_, _, _, fun W X K {e L sz} hX he hL hsz => by
    unfold powCost
    have h1 : Dom W X K (1 + 1) 1 0 (e + 1) := Dom.ofAffine (by omega)
    have h2 : Dom W X K (2 + 1) 1 0 (L + 1) := Dom.ofAffine (by omega)
    have h3 : Dom W X K (12 + 3) 1 0 sz := Dom.ofAffine hsz
    have h4 : Dom W X K (2 + 0) 1 0 L := Dom.ofAffine (by omega)
    exact h1.mul (((Dom.const 8).mul h2).mul (((h3.add hX (((Dom.const 2).mul (Dom.ofLeW he)).mul
      h4)).add hX (Dom.ofLeW he)).add hX (Dom.const 14)))⟩
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
variable {ℓ : ℕ} (S : CL.Sampler ℓ) (lam tau n : ℕ) (R : Budget) (W : ℕ)
variable {W X K : ℕ}
theorem dom_dimCost : ∃ c m e, ∀ (W X K : ℕ) {tau L Λ N Ssz : ℕ}, 1 ≤ X → tau ≤ W →
    L ≤ 2 * W → Λ ≤ 4 * W + 1 → N ≤ 4 * W + 1 → Ssz ≤ 4 * W + 1 →
    Dom W X K c m e (dimCost tau L Λ N Ssz) := by
  obtain ⟨c₁, m₁, e₁, h₁⟩ := dom_toUnaryCost
  obtain ⟨c₂, m₂, e₂, h₂⟩ := dom_powCost
  exact ⟨_, _, _, fun W X K {tau L Λ N Ssz} hX ht hL hΛ hN hS => by
    unfold dimCost
    have hsz : Λ + N + Ssz ≤ 12 * W + 3 := by omega
    have hΛ' : Dom W X K (4 + 1) 1 0 Λ := Dom.ofAffine hΛ
    have hN' : Dom W X K (4 + 1) 1 0 N := Dom.ofAffine hN
    have hS' : Dom W X K (4 + 1) 1 0 Ssz := Dom.ofAffine hS
    exact ((((((h₁ W X K hX ht).add hX (dom_esize ht)).add hX (h₂ W X K hX ht hL hsz)).add hX
      ((Dom.const 2).mul (Dom.ofLeW ht))).add hX hΛ').add hX hN').add hX hS' |>.add hX
      (Dom.const 20)⟩
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
variable {ℓ : ℕ} (S : CL.Sampler ℓ) (lam tau n : ℕ) (R : Budget) (W : ℕ)
variable {W X K : ℕ}
theorem dom_mapIter (cZ mZ eZ : ℕ) : ∃ c m e, ∀ (W X K : ℕ) {Z : ℕ}, 1 ≤ X →
    Dom W X K cZ mZ eZ Z → Dom W X K c m e (mapIter Z) := by
  exact ⟨_, _, _, fun W X K {Z} hX hZ => by
    unfold mapIter
    exact (Dom.const 22).mul ((hZ.add hX (Dom.const 30)).pow 2)⟩
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
variable {ℓ : ℕ} (S : CL.Sampler ℓ) (lam tau n : ℕ) (R : Budget) (W : ℕ)
variable {W X K : ℕ}
theorem dom_zBound (cT mT eT : ℕ) : ∃ c m e, ∀ (W X K : ℕ) {sD : Data} {n s D Tu : ℕ},
    1 ≤ X → Dom W X K cT mT eT Tu → sD.size ≤ W → n ≤ W → s ≤ W → D + 1 ≤ X →
    Dom W X K c m e (zBound sD n s D Tu) := by
  exact ⟨_, _, _, fun W X K {sD n s D Tu} hX hT hsD hn hs hD => by
    unfold zBound
    have hD' : Dom W X K 1 0 1 D := Dom.ofLeX hX (by omega)
    exact (((((Dom.ofLeW hs).add hX ((Dom.const 3).mul hD')).add hX
      ((((Dom.ofLeW hsD).add hX (dom_esize hn)).add hX hD').add hX (Dom.const 4))).add hX
      (Dom.const 1)).add hX (hD'.mul (hT.add hX (Dom.const 1)))).add hX hT⟩
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
variable {ℓ : ℕ} (S : CL.Sampler ℓ) (lam tau n : ℕ) (R : Budget) (W : ℕ)
variable {W X K : ℕ}
theorem dom_lockCost (cC mC eC cZ mZ eZ : ℕ) : ∃ c m e, ∀ (W X K : ℕ) {s C U Y Z : ℕ},
    1 ≤ X → s ≤ W → Dom W X K cC mC eC C → U + 1 ≤ X → Y + 1 ≤ X → Dom W X K cZ mZ eZ Z →
    Dom W X K c m e (lockCost s C U Y Z) := by
  obtain ⟨c₁, m₁, e₁, h₁⟩ := dom_toUnaryCost
  obtain ⟨c₂, m₂, e₂, h₂⟩ := dom_mapIter cZ mZ eZ
  exact ⟨_, _, _, fun W X K {s C U Y Z} hX hs hC hU hY hZ => by
    unfold lockCost
    have hU' : Dom W X K 1 0 1 U := Dom.ofLeX hX (by omega)
    have hY' : Dom W X K 1 0 1 Y := Dom.ofLeX hX (by omega)
    exact ((((((((dom_esize hs).add hX (h₁ W X K hX hs)).add hX ((Dom.const 4).mul hC)).add hX
      ((Dom.const 4).mul (Dom.ofLeW hs))).add hX ((Dom.const 4).mul hU')).add hX
      ((Dom.const 4).mul hY')).add hX ((Dom.ofLeX hX hU).mul (h₂ W X K hX hZ))).add hX
      ((hZ.add hX (Dom.const 2)).mul (hZ.add hX (Dom.const 13)))).add hX
      ((Dom.const 3).mul hZ) |>.add hX (Dom.const 60)⟩
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
variable {ℓ : ℕ} (S : CL.Sampler ℓ) (lam tau n : ℕ) (R : Budget) (W : ℕ)
variable {W X K : ℕ}
theorem dom_anyCost (cd md ed cT mT eT : ℕ) : ∃ c m e, ∀ (W X K : ℕ) {lam tau n : ℕ}
    {sD : Data} {s D td Tu : ℕ}, 1 ≤ X → Dom W X K cd md ed td → Dom W X K cT mT eT Tu →
    sD.size ≤ W → lam ≤ W → tau ≤ W → n ≤ W → s ≤ W → D + 1 ≤ X →
    Dom W X K c m e (anyCost lam tau n sD s D td Tu) := by
  obtain ⟨c₁, m₁, e₁, h₁⟩ := dom_dimCost
  obtain ⟨c₂, m₂, e₂, h₂⟩ := dom_zBound cT mT eT
  obtain ⟨c₃, m₃, e₃, h₃⟩ := dom_lockCost (1 + (4 + 1) + 1 + 4) 1 1 c₂ m₂ e₂
  exact ⟨_, _, _, fun W X K {lam tau n sD s D td Tu} hX htd hTu hsD hlam htau hn hs hD => by
    unfold anyCost
    have hD' : Dom W X K 1 0 1 D := Dom.ofLeX hX (by omega)
    have hC : Dom W X K (1 + (4 + 1) + 1 + 4) 1 1 (sD.size + esize n + D + 4) := by
      have := (((Dom.ofLeW hsD).add hX (dom_esize hn)).add hX hD').add hX (Dom.const 4)
      simpa using this
    have hL : Nat.size lam + Nat.size n ≤ 2 * W := by
      have := nat_size_le_self lam; have := nat_size_le_self n; omega
    have hlam' : esize lam ≤ 4 * W + 1 := (esize_nat_le' lam).trans (by omega)
    have hn' : esize n ≤ 4 * W + 1 := (esize_nat_le' n).trans (by omega)
    have hs' : esize s ≤ 4 * W + 1 := (esize_nat_le' s).trans (by omega)
    have b1 := ((htd.add hX ((Dom.const 2).mul ((Dom.ofLeW hsD).add hX (dom_esize hn)))).add hX
      (Dom.const 40))
    have b2 := (((Dom.const 2).mul ((((dom_esize hs).add hX (dom_esize hlam)).add hX
      (dom_esize hn)).add hX (dom_esize htau))).add hX (Dom.const 20)).add hX
      (h₁ W X K hX htau hL hlam' hn' hs')
    have b3 := ((((((((Dom.const 2).mul ((((Dom.ofLeW hsD).add hX (dom_esize hn)).add hX
      (dom_esize hs)).add hX hD')).add hX (Dom.const 40)).add hX
      (h₃ W X K hX hs hC hD hD (h₂ W X K hX hTu hsD hn hs hD))).add hX
      (Dom.const (esize 0))).add hX (Dom.const (toUnaryCost 0))).add hX (Dom.ofLeW hsD)).add hX
      (dom_esize hn)).add hX ((Dom.const 3).mul hD')
    exact (b1.add hX b2).add hX b3⟩
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
variable {ℓ : ℕ} (S : CL.Sampler ℓ) (lam tau n : ℕ) (R : Budget) (W : ℕ)
variable {W X K : ℕ}
/-- The self-interpreter's overhead polynomial at a dominated argument. -/
theorem dom_univ_bound (cy my ey : ℕ) : ∃ c m e, ∀ (W X K : ℕ) {y : ℕ}, 1 ≤ X → 1 ≤ y →
    Dom W X K cy my ey y → Dom W X K c m e (selfUniversal.bound.eval y) := by
  exact ⟨_, _, _, fun W X K {y} _ hy h => ((Dom.const cU).mul (h.pow dU)).of_le (univ_bound_le hy)⟩
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
variable {ℓ : ℕ} (S : CL.Sampler ℓ) (lam tau n : ℕ) (R : Budget) (W : ℕ)
variable {W X K : ℕ}
/-- The argument of the dimension query's bound. -/
theorem dom_yd : ∃ c m e, ∀ (W X K : ℕ) {p n RS pk : ℕ}, 1 ≤ X → p ≤ W → n ≤ W → RS ≤ W →
    pk ≤ W → Dom W X K c m e (p + (esize n + 10) + RS * pk) := by
  exact ⟨_, _, _, fun W X K {p n RS pk} hX hp hn hRS hpk =>
    ((Dom.ofLeW hp).add hX ((dom_esize hn).add hX (Dom.const 10))).add hX
      ((Dom.ofLeW hRS).mul (Dom.ofLeW hpk))⟩
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
variable {ℓ : ℕ} (S : CL.Sampler ℓ) (lam tau n : ℕ) (R : Budget) (W : ℕ)
variable {W X K : ℕ}
/-- The argument of the block queries' bound. -/
theorem dom_yT : ∃ c m e, ∀ (W X K : ℕ) {p n RS D : ℕ}, 1 ≤ X → p ≤ W → n ≤ W → RS ≤ W →
    D + 1 = X → Dom W X K c m e (p + (esize n + D + 1) + RS * (D + 1) ^ K) := by
  exact ⟨_, _, _, fun W X K {p n RS D} hX hp hn hRS hD => by
    subst hD
    exact ((Dom.ofLeW hp).add hX (((dom_esize hn).add hX (Dom.ofLeX hX (by omega))).add hX
      (Dom.const 1))).add hX ((Dom.ofLeW hRS).mul (Dom.powK hX))⟩
end
end MIPRE.Repeat

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Repeat
open Cost Cost.Data Cost.Prog CL
variable {ℓ : ℕ} (S : CL.Sampler ℓ) (lam tau n : ℕ) (R : Budget) (W : ℕ)
theorem _root_.solution : ∃ c m e, ∀ {ℓ : ℕ} (S : CL.Sampler ℓ) (lam tau n : ℕ)
    (R : Budget) (W : ℕ), SampDom S lam tau n R W → S.TimeBoundAt n R.S R.k →
    (repSampler S lam tau).TimeBoundAt n (c * (W + 1) ^ m) (e * (R.k + 1)) := by
  obtain ⟨cd, md, ed, hd⟩ := dom_yd
  obtain ⟨cd', md', ed', hd'⟩ := dom_univ_bound cd md ed
  obtain ⟨cT, mT, eT, hT⟩ := dom_yT
  obtain ⟨cT', mT', eT', hT'⟩ := dom_univ_bound cT mT eT
  obtain ⟨cA, mA, eA, hA⟩ := dom_anyCost cd' md' ed' cT' mT' eT'
  exact ⟨_, _, _, fun {ℓ} S lam tau n R W hW hS d => by
    obtain ⟨r, t, ht, run⟩ := repSampler_halts_within S lam tau n R hS d
    refine ⟨r, t, ?_, run⟩
    have hX : 1 ≤ d.size + 1 := by omega
    have hsD : (encode S.prog : Data).size ≤ W := hW.size_le
    have hD' : Dom W (d.size + 1) R.k 1 0 1 d.size := Dom.ofLeX hX (by omega)
    have h1 := hA W (d.size + 1) R.k hX
      (hd' W _ R.k hX (by omega) (hd W _ R.k hX hW.size_le hW.n_le hW.S_le hW.pow_le))
      (hT' W _ R.k hX (by omega) (hT W _ R.k hX hW.size_le hW.n_le hW.S_le rfl))
      hsD hW.lam_le hW.tau_le hW.n_le hW.dim_le le_rfl
    have h2 := ((h1.add hX ((((Dom.ofLeW hW.size_le).add hX (dom_esize hW.lam_le)).add hX
      (dom_esize hW.tau_le)).add hX (Dom.const 2))).add hX
      (((dom_esize hW.n_le).add hX hD').add hX (Dom.const 1))).add hX (Dom.const 3)
    exact (h2.of_le ht).le⟩
end MIPRE.Repeat
