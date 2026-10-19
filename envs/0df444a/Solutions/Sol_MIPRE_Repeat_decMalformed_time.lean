-- Prove2me | solution 1 for MIPRE.Repeat.decMalformed_time
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:48:45.540666+00:00
-- url     : https://prove2.me/submissions/40174f00-d54d-4003-883f-0fa4ea1cd699

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/DeciderCost.lean (solution of MIPRE.Repeat.decMalformed_time);
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
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Repeat_DecLoop
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Repeat_DecMain
import Definitions.Def_MIPRE_Foundations_Repeat_RepDecider
import Definitions.Def_MIPRE_Foundations_Repeat_DeciderCost
import Theorems.Thm_MIPRE_Cost_Prog_repDecCore_runs_malformed
import Theorems.Thm_MIPRE_Cost_Prog_repDecCore_wellScoped
import Theorems.Thm_MIPRE_Cost_hardcode_time

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
theorem encode_decParams (sp dp : Prog) (lam tau beta : ℕ) :
    (encode ((sp, dp), lam, tau, beta) : Data) =
      decParams (encode sp) (encode dp) (encode lam) (encode tau) (encode beta) := rfl
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
variable {W X K : ℕ}
theorem dom_esize' {x : ℕ} (hx : x ≤ W) : Dom W X K (4 + 1) 1 0 (encode x : Data).size :=
  dom_esize hx
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
/-- The size of the parameters datum. -/
theorem size_encode_decParams_le {ℓ : ℕ} {S : CL.Sampler ℓ} {D : Decider} {lam tau beta n : ℕ}
    {R : Budget} {W : ℕ} (hW : DecDom S D lam tau beta n R W) :
    (encode ((S.prog, D.prog), lam, tau, beta) : Data).size ≤ 14 * W + 7 := by
  have h1 := hW.sizeS_le
  have h2 := hW.sizeD_le
  have h3 := (esize_nat_le' lam).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hW.lam_le) 1)
  have h4 := (esize_nat_le' tau).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hW.tau_le) 1)
  have h5 := (esize_nat_le' beta).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hW.beta_le) 1)
  simp only [encode_prod, size_cons, esize] at *
  omega
end
end MIPRE.Repeat

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Repeat
open Cost Cost.Data Cost.Prog CL
theorem _root_.solution : ∃ c m e, ∀ {ℓ : ℕ} (S : CL.Sampler ℓ) (D : Decider)
    (lam tau beta n : ℕ) (R : Budget) (W : ℕ) (d : Data), DecDom S D lam tau beta n R W →
    (d = .nil ∨ (∃ xD, d = .cons xD .nil) ∨ ∃ xD yD, d = .cons xD (.cons yD .nil)) →
    ∃ r t, t ≤ c * (W + 1) ^ m * (d.size + 1) ^ (e * (R.k + 1)) ∧
      (repDeciderProg S.prog D.prog lam tau beta).Runs (.cons (encode n) d) r t := by
  exact ⟨_, _, _, fun {ℓ} S D lam tau beta n R W d hW hd => by
    obtain ⟨t, ht, run⟩ := repDecCore_runs_malformed selfUniversal.univ (encode S.prog)
      (encode D.prog) (encode lam) (encode tau) (encode beta) (encode n) d hd
    refine ⟨.nil, _, ?_, hardcode_time (repDecCore_wellScoped selfUniversal.closed) run⟩
    have hX : 1 ≤ d.size + 1 := by omega
    have hpar := size_encode_decParams_le hW
    have hdsz : Dom W (d.size + 1) R.k 1 0 1 d.size := Dom.ofLeX hX (by omega)
    have chain := (((Dom.const 10).add hX (Dom.ofAffine (W := W) (X := d.size + 1) (K := R.k)
      (a := 14) (b := 7) hpar)).add hX (((dom_esize' hW.n_le).add hX hdsz).add hX
      (Dom.const 1))).add hX (Dom.const 3)
    rw [encode_decParams] at hpar chain ⊢
    refine (chain.of_le ?_).le
    simp only [size_cons]
    omega⟩
end MIPRE.Repeat
