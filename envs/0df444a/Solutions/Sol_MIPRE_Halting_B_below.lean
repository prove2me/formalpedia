-- Prove2me | solution 1 for MIPRE.Halting.B_below
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T21:53:56.267612+00:00
-- url     : https://prove2.me/submissions/c10b473a-460b-4113-b0a4-2b376184c009

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Paper/Induction.lean (solution of MIPRE.Halting.B_below);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Computability.Halting
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawInt
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_ValueApprox
import Definitions.Def_MIPRE_Foundations_ValueApprox_Cayley
import Definitions.Def_MIPRE_Foundations_ValueApprox_Projective
import Definitions.Def_MIPRE_Foundations_ValueApprox_Gaussian
import Definitions.Def_MIPRE_Foundations_ValueApprox_Norms
import Definitions.Def_MIPRE_Foundations_ValueApprox_Dense
import Definitions.Def_MIPRE_Foundations_ValueApprox_Strategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_HaltingGameValue
import Definitions.Def_MIPRE_Foundations_GameDescription
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawStrategy
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawSemantics
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawComplete
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawPrimrec
import Definitions.Def_MIPRE_Foundations_ValueApprox_RE
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Definitions.Def_MIPRE_Foundations_Cost_Partrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Semidecide
import Definitions.Def_MIPRE_Foundations_ClassMIPStarComputable
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Halting_Freeze
import Definitions.Def_MIPRE_Foundations_Halting_Classes
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Halting_Wrapper
import Definitions.Def_MIPRE_Foundations_Halting_Enumerate
import Definitions.Def_MIPRE_Foundations_Cost_BoundedEval
import Definitions.Def_MIPRE_Foundations_Halting_Tabulate
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery
import Definitions.Def_MIPRE_Foundations_Cost_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Clocked
import Definitions.Def_MIPRE_Foundations_Cost_Threshold
import Definitions.Def_MIPRE_Foundations_Compression
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_Cost_ManyOne
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded
import Definitions.Def_MIPRE_Foundations_Halting_CostBudget
import Definitions.Def_MIPRE_Foundations_Halting_Instantiation
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Halting_Semidecider
import Definitions.Def_MIPRE_Foundations_Halting_WrapperCost
import Definitions.Def_MIPRE_Foundations_Halting_Strings
import Definitions.Def_MIPRE_Foundations_Halting_Reduction
import Definitions.Def_MIPRE_Foundations_Halting_Compressor
import Definitions.Def_MIPRE_Foundations_Halting_Paper_TabulateL
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Decider
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Induction
import Theorems.Thm_MIPRE_Halting_accepts_iff

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.TensorProductStrategy
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B}
/-- Accepting more answer tuples raises the value of a strategy. -/
theorem value_copy_le (S : TensorProductStrategy G) (G' : Game X Y A B)
    (hμ : ∀ x y, G'.μ x y = G.μ x y)
    (hD : ∀ x y a b, G.D x y a b = true → G'.D x y a b = true) :
    S.value ≤ (S.copy G').value := by
  unfold value
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
    Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  rw [hμ]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (G.μ_nonneg x y))
    (S.re_dotProduct_nonneg x y a b)
  cases h : G.D x y a b with
  | false => by_cases h' : G'.D x y a b = true <;> simp [h']
  | true => rw [hD x y a b h]
end MIPRE.TensorProductStrategy

namespace MIPRE
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
/-- Accepting more answer tuples, on the same alphabets and distribution, raises the quantum
value. -/
theorem quantumValue_mono (G G' : Game X Y A B) (hμ : ∀ x y, G'.μ x y = G.μ x y)
    (hD : ∀ x y a b, G.D x y a b = true → G'.D x y a b = true) :
    quantumValue G ≤ quantumValue G' := by
  refine Real.iSup_le (fun S => ?_) (quantumValue_nonneg _)
  exact (S.value_copy_le G' hμ hD).trans
    (le_ciSup (TensorProductStrategy.bddAbove_range_value G') (S.copy G'))
end MIPRE

namespace MIPRE
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
/-- A game whose decision predicate rejects everything has quantum value `0`. -/
theorem quantumValue_eq_zero_of_reject (G : Game X Y A B) (hD : ∀ x y a b, G.D x y a b = false) :
    quantumValue G = 0 := by
  refine le_antisymm (Real.iSup_le (fun S => ?_) le_rfl) (quantumValue_nonneg G)
  unfold TensorProductStrategy.value
  simp [hD]
end MIPRE

namespace MIPRE.Cost
open Polynomial
theorem evalWithin_isSome_iff (c : Prog) (v : Data) (k : ℕ) :
    (evalWithin c v k).isSome = true ↔ ∃ r t, t ≤ k ∧ c.Runs v r t := by
  unfold evalWithin
  split <;> simp_all
end MIPRE.Cost

namespace MIPRE.Verifier
open Cost
variable {ℓ : ℕ} (V : Verifier ℓ)
/-- With the same sampler, a decider accepting more at index `n` gives a larger `val*`. -/
theorem valStar_le_of_accepts_imp {V W : Verifier ℓ} {n T : ℕ} (hS : W.sampler = V.sampler)
    (h : ∀ x y a b, V.decider.Accepts n x y a b → W.decider.Accepts n x y a b) :
    V.valStar n T ≤ W.valStar n T := by
  obtain ⟨SW, DW, hW⟩ := W
  obtain ⟨SV, DV, hV⟩ := V
  simp only at hS
  subst hS
  refine quantumValue_mono _ _ (fun _ _ => rfl) fun x y a b hd => ?_
  rw [game_D] at hd ⊢
  exact h _ _ _ _ hd
end MIPRE.Verifier

namespace MIPRE.Verifier
open Cost
variable {ℓ : ℕ} (V : Verifier ℓ)
/-- With the same sampler, deciders accepting the same tuples at index `n` give the same
`val*`. -/
theorem valStar_congr {V W : Verifier ℓ} {n T : ℕ} (hS : W.sampler = V.sampler)
    (h : ∀ x y a b, V.decider.Accepts n x y a b ↔ W.decider.Accepts n x y a b) :
    V.valStar n T = W.valStar n T :=
  le_antisymm (valStar_le_of_accepts_imp hS fun x y a b => (h x y a b).1)
    (valStar_le_of_accepts_imp hS.symm fun x y a b => (h x y a b).2)
end MIPRE.Verifier

namespace MIPRE.Verifier
open Cost
variable {ℓ : ℕ} (V : Verifier ℓ)
/-- A decider that accepts nothing at index `n` gives quantum value `0`. -/
theorem valStar_eq_zero_of_rejects_all {n T : ℕ}
    (hrej : ∀ x y a b, ¬ V.decider.Accepts n x y a b) : V.valStar n T = 0 := by
  classical
  refine quantumValue_eq_zero_of_reject _ fun x y a b => ?_
  exact decide_eq_false (hrej _ _ _ _)
end MIPRE.Verifier

namespace MIPRE.Halting
open Cost Cost.Prog
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
theorem two_le_C : 2 ≤ C G := le_max_right _ _
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
theorem C₀_le_C : G.C₀ ≤ C G := le_max_left _ _
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
theorem C_le_lv : ∀ j, C G ≤ lv G j
  | 0 => le_rfl
  | j + 1 => by
    rw [lv_succ]
    exact (C_le_lv j).trans Nat.lt_two_pow_self.le
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
theorem lv_mono {j k : ℕ} (h : j ≤ k) : lv G j ≤ lv G k := by
  induction k with
  | zero => rw [Nat.le_zero.1 h]
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with hlt | hge
    · exact (ih (Nat.lt_succ_iff.1 hlt)).trans (by rw [lv_succ]; exact Nat.lt_two_pow_self.le)
    · rw [Nat.le_antisymm h hge]
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable {S' : Prog} (hS' : S'.WellScoped 1)
  (hsem : ∀ x : BitStr, Halts S' (encode x) ↔
    (1 : ℝ) / 2 < quantumValue (tabL G U x (C G)).game)
  (M : Prog) (lam : ℕ)
  (hb : (Vhalt G U UT S' M lam).IsBounded lam)
  (hpoly : ∀ n, 2 ≤ n → G.bound.eval (n + lam) ≤ n ^ lam)
include hS' hsem hb hpoly
omit hS' hsem hb hpoly in
theorem branch_mono {p : Prog} {n n' : ℕ} (h : Nat.size n ≤ Nat.size n')
    (hp : (evalWithin p .nil (Nat.size n)).isSome = true) :
    (evalWithin p .nil (Nat.size n')).isSome = true := by
  obtain ⟨r, t, ht, hr⟩ := (evalWithin_isSome_iff _ _ _).1 hp
  exact (evalWithin_isSome_iff _ _ _).2 ⟨r, t, ht.trans h, hr⟩
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable {S' : Prog} (hS' : S'.WellScoped 1)
  (hsem : ∀ x : BitStr, Halts S' (encode x) ↔
    (1 : ℝ) / 2 < quantumValue (tabL G U x (C G)).game)
  (M : Prog) (lam : ℕ)
  (hb : (Vhalt G U UT S' M lam).IsBounded lam)
  (hpoly : ∀ n, 2 ≤ n → G.bound.eval (n + lam) ≤ n ^ lam)
include hS' hsem hb hpoly
omit hS' hsem hb hpoly in
theorem rejects_all_of_branch2 {n : ℕ} (h1 : ¬ branch1 M n) (h2 : branch2 G U UT S' M lam n)
    (x y a b : BitStr) : ¬ (Vhalt G U UT S' M lam).decider.Accepts n x y a b := by
  unfold branch1 at h1
  unfold branch2 at h2
  rw [accepts_iff, if_neg h1, if_pos h2]
  exact fun h => h.2.2
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable {S' : Prog} (hS' : S'.WellScoped 1)
  (hsem : ∀ x : BitStr, Halts S' (encode x) ↔
    (1 : ℝ) / 2 < quantumValue (tabL G U x (C G)).game)
  (M : Prog) (lam : ℕ)
  (hb : (Vhalt G U UT S' M lam).IsBounded lam)
  (hpoly : ∀ n, 2 ≤ n → G.bound.eval (n + lam) ≤ n ^ lam)
include hS' hsem hb hpoly
omit hS' hsem hb hpoly in
theorem accepts_iff_W {n : ℕ} (h1 : ¬ branch1 M n) (h2 : ¬ branch2 G U UT S' M lam n)
    (x y a b : BitStr) :
    (Vhalt G U UT S' M lam).decider.Accepts n x y a b ↔
      (W G U UT S' M lam).decider.Accepts n x y a b := by
  unfold branch1 at h1
  unfold branch2 at h2
  rw [accepts_iff, if_neg h1, if_neg h2]
  constructor
  · exact fun h => h.2.2
  · intro h
    have hl := (W G U UT S' M lam).accepts_length n x y a b h
    rw [G.output_sampler] at hl
    exact ⟨hl.1, hl.2, h⟩
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable {S' : Prog} (hS' : S'.WellScoped 1)
  (hsem : ∀ x : BitStr, Halts S' (encode x) ↔
    (1 : ℝ) / 2 < quantumValue (tabL G U x (C G)).game)
  (M : Prog) (lam : ℕ)
  (hb : (Vhalt G U UT S' M lam).IsBounded lam)
  (hpoly : ∀ n, 2 ≤ n → G.bound.eval (n + lam) ≤ n ^ lam)
include hS' hsem hb hpoly
omit hS' hsem hb hpoly in
theorem W_sampler : (W G U UT S' M lam).sampler = (Vhalt G U UT S' M lam).sampler :=
  G.output_sampler _ _
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable {S' : Prog} (hS' : S'.WellScoped 1)
  (hsem : ∀ x : BitStr, Halts S' (encode x) ↔
    (1 : ℝ) / 2 < quantumValue (tabL G U x (C G)).game)
  (M : Prog) (lam : ℕ)
  (hb : (Vhalt G U UT S' M lam).IsBounded lam)
  (hpoly : ∀ n, 2 ≤ n → G.bound.eval (n + lam) ≤ n ^ lam)
include hS' hsem hb hpoly
omit hS' hsem hb hpoly in
/-- Below the first branch, `𝒱^halt` rejects every answer longer than the compressed bound. -/
theorem rejectsLong_of_not_branch1 {n : ℕ} (h1 : ¬ branch1 M n) :
    (Vhalt G U UT S' M lam).RejectsLong n (G.bound.eval (n + lam)) := by
  intro x y a b hab hacc
  unfold branch1 at h1
  rw [accepts_iff, if_neg h1] at hacc
  split_ifs at hacc with h2
  · exact hacc.2.2
  · exact G.output_rejects_long _ _ _ _ _ _ _ hab hacc.2.2
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable {S' : Prog} (hS' : S'.WellScoped 1)
  (hsem : ∀ x : BitStr, Halts S' (encode x) ↔
    (1 : ℝ) / 2 < quantumValue (tabL G U x (C G)).game)
  (M : Prog) (lam : ℕ)
  (hb : (Vhalt G U UT S' M lam).IsBounded lam)
  (hpoly : ∀ n, 2 ≤ n → G.bound.eval (n + lam) ≤ n ^ lam)
include hS' hsem hb hpoly
omit hS' hsem hb hpoly in
theorem B_of_branch2 {n : ℕ} (h1 : ¬ branch1 M n) (h2 : branch2 G U UT S' M lam n) :
    B G U UT S' M lam n := by
  unfold B
  rw [(Vhalt G U UT S' M lam).valStar_eq_zero_of_rejects_all
    (rejects_all_of_branch2 G U UT M lam h1 h2)]
  norm_num
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable {S' : Prog} (hS' : S'.WellScoped 1)
  (hsem : ∀ x : BitStr, Halts S' (encode x) ↔
    (1 : ℝ) / 2 < quantumValue (tabL G U x (C G)).game)
  (M : Prog) (lam : ℕ)
  (hb : (Vhalt G U UT S' M lam).IsBounded lam)
  (hpoly : ∀ n, 2 ≤ n → G.bound.eval (n + lam) ≤ n ^ lam)
include hS' hsem hb hpoly
omit hS' hsem in
/-- **Soundness carried down a level**, where neither branch fires. -/
theorem B_step {n : ℕ} (hn : C G ≤ n) (h1 : ¬ branch1 M n) (h2 : ¬ branch2 G U UT S' M lam n)
    (hB : B G U UT S' M lam (2 ^ n)) : B G U UT S' M lam n := by
  have hW := G.soundness _ lam n hb ((C₀_le_C G).trans hn) hB
  have hV : (Vhalt G U UT S' M lam).valStar n (G.bound.eval (n + lam)) ≤ 1 / 2 := by
    rw [(Vhalt G U UT S' M lam).valStar_congr (W_sampler G U UT M lam)
      (accepts_iff_W G U UT M lam h1 h2)]
    exact hW
  unfold B
  rw [(Vhalt G U UT S' M lam).valStar_eq_of_rejects (hpoly n ((two_le_C G).trans hn))
    (rejectsLong_of_not_branch1 G U UT M lam h1)]
  exact hV
end MIPRE.Halting

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Halting
open Cost Cost.Prog
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable {S' : Prog} (hS' : S'.WellScoped 1)
  (hsem : ∀ x : BitStr, Halts S' (encode x) ↔
    (1 : ℝ) / 2 < quantumValue (tabL G U x (C G)).game)
  (M : Prog) (lam : ℕ)
  (hb : (Vhalt G U UT S' M lam).IsBounded lam)
  (hpoly : ∀ n, 2 ≤ n → G.bound.eval (n + lam) ≤ n ^ lam)
include hS' hsem hb hpoly
omit hS' hsem in
theorem _root_.solution (j₀ : ℕ) (hnot : ¬ branch1 M (lv G j₀))
    (hfire : branch2 G U UT S' M lam (lv G j₀)) :
    ∀ i j, j + i = j₀ → B G U UT S' M lam (lv G j) := by
  intro i
  induction i with
  | zero =>
    intro j hj
    rw [Nat.add_zero] at hj
    subst hj
    exact B_of_branch2 G U UT M lam hnot hfire
  | succ i ih =>
    intro j hj
    have hjle : Nat.size (lv G j) ≤ Nat.size (lv G j₀) :=
      Nat.size_le_size (lv_mono G (by omega))
    have h1 : ¬ branch1 M (lv G j) := fun h => hnot (branch_mono hjle h)
    by_cases h2 : branch2 G U UT S' M lam (lv G j)
    · exact B_of_branch2 G U UT M lam h1 h2
    · have hnext := ih (j + 1) (by omega)
      rw [lv_succ] at hnext
      exact B_step G U UT M lam hb hpoly (C_le_lv G j) h1 h2 hnext
end MIPRE.Halting
