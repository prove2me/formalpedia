-- Prove2me | solution 1 for MIPRE.CL.Detyping.sampler_time
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:06:04.077093+00:00
-- url     : https://prove2.me/submissions/f89ab06f-64cc-4d75-ad80-94012dfa661b

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingDeciderCost.lean (solution of MIPRE.CL.Detyping.sampler_time);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
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
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryDegreeArithmetic
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
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Repeat_Dom
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCost
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderRoute
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderProg
import Definitions.Def_MIPRE_Foundations_CL_DetypingDecider
import Definitions.Def_MIPRE_Foundations_Cost_While
import Definitions.Def_MIPRE_Foundations_Pipeline_UnaryArith
import Definitions.Def_MIPRE_Foundations_Pipeline_PowDom
import Definitions.Def_MIPRE_Foundations_Pipeline_PowDomRun
import Theorems.Thm_MIPRE_CL_Detyping_Program_route_preserves
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_haltsWithin
import Theorems.Thm_MIPRE_Pipeline_PDom_ofPoweredCall
import Theorems.Thm_MIPRE_Pipeline_PDom_poly

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Prog
section
open PolyTimeFun Polynomial
theorem routeCost_natDegree_le (route : PolyTimeFun Data (Bool × Data))
    (post : PolyTimeFun (Data × Data) Data) (B k : ℕ) :
    (routeCost route post B k).natDegree ≤ routeDegree route post k := by
  let R := route.timeBound
  let F := C B * (R + 1) ^ k
  let A := R.natDegree * (k + 1)
  have hR : R.natDegree ≤ A := by dsimp [A]; nlinarith
  have hR1 : (R + 1).natDegree ≤ R.natDegree :=
    natDegree_add_le_of_degree_le le_rfl (by simp)
  have hF : F.natDegree ≤ A := by
    exact (natDegree_C_mul_le _ _).trans ((natDegree_pow_le_of_le k hR1).trans
      (by dsimp [A]; nlinarith))
  have hRF : (R + F).natDegree ≤ A := natDegree_add_le_of_degree_le hR hF
  have hRF1 : (R + F + 1).natDegree ≤ A :=
    natDegree_add_le_of_degree_le hRF (by simp)
  have hP : (post.timeBound.comp (R + F + 1)).natDegree ≤ post.timeBound.natDegree * A :=
    natDegree_comp_le.trans (Nat.mul_le_mul_left _ hRF1)
  have hA : A ≤ routeDegree route post k := by
    change A ≤ A * (post.timeBound.natDegree + 1)
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left A
      (Nat.succ_le_succ (Nat.zero_le post.timeBound.natDegree))
  have hPA : post.timeBound.natDegree * A ≤ routeDegree route post k := by
    dsimp [A, R, routeDegree]
    nlinarith
  exact (natDegree_C_mul_le _ _).trans (natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le (hRF.trans hA) (hP.trans hPA)) (by simp))
end
end MIPRE.Cost.Prog

namespace MIPRE.CL.Detyping
section
open Cost Polynomial
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T] {ℓ : ℕ}
variable (E : T → T → Prop) [DecidableRel E] (S : TypedSampler ℓ T)
theorem samplerCost_natDegree_le (n B k : ℕ) :
    (samplerCost E n B k).natDegree ≤ samplerDegree E k := by
  have hi : (X + C (esize n + 1) : Polynomial ℕ).natDegree ≤ 1 :=
    natDegree_add_le_of_degree_le (by simp only [natDegree_X]; omega)
      (by simp only [natDegree_C]; omega)
  exact natDegree_comp_le.trans ((Nat.mul_le_mul
    (Prog.routeCost_natDegree_le _ _ B k) hi).trans (by simp [samplerDegree]))
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping
section
open Cost Polynomial
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T] {ℓ : ℕ}
variable (E : T → T → Prop) [DecidableRel E] (S : TypedSampler ℓ T)
theorem sampler_haltsWithin (hℓ : 0 < ℓ) (n B k : ℕ) (h : S.TimeBoundAt n B k) (q : Data) :
    HaltsWithin (sampler E S hℓ).prog (.cons (encode n) q)
      ((samplerCost E n B k).eval q.size) := by
  have hr := Prog.routeOneCall_haltsWithin (Program.route E) S.closed
    (Program.post (graphDim T)) n B k q h (Program.route_preserves E n q)
  simpa only [sampler, samplerProg, samplerCost, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C, Data.size_cons, esize, encode_data,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hr
end
end MIPRE.CL.Detyping

namespace MIPRE.CL.Detyping
section
open Cost Polynomial
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T] {ℓ : ℕ}
variable (E : T → T → Prop) [DecidableRel E] (S : TypedSampler ℓ T)
/-- Detyping preserves a polynomial query bound with a degree independent of `n`. -/
theorem sampler_timeBoundAt_uniform_degree (hℓ : 0 < ℓ) (n B k : ℕ)
    (h : S.TimeBoundAt n B k) :
    (sampler E S hℓ).TimeBoundAt n (samplerCoefficient E n B k) (samplerDegree E k) := by
  let Q := samplerCost E n B k
  have hQ : (sampler E S hℓ).TimeBoundAt n (samplerCoefficient E n B k) Q.natDegree := by
    intro q
    obtain ⟨r, time, ht, hr⟩ := sampler_haltsWithin E S hℓ n B k h q
    exact ⟨r, time, ht.trans ((polynomial_eval_mono Q (Nat.le_succ q.size)).trans
      (polynomial_eval_le_sum_coeff_mul_pow Q (by omega))), hr⟩
  exact hQ.mono le_rfl (samplerCost_natDegree_le E n B k)
end
end MIPRE.CL.Detyping

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
/-- The coefficient and the degree. -/
theorem le_final {c m e v : ℕ} (h : PDom W X K c m e v) :
    v ≤ (c * (W + 1) ^ m) ^ (K + 1) * X ^ (e * (K + 1)) := by
  refine h.trans (le_of_eq ?_)
  rw [mul_pow, pow_mul]
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
theorem mono (hX : 1 ≤ X) {c c' m m' e e' v : ℕ} (h : PDom W X K c m e v) (hc : c ≤ c')
    (hm : m ≤ m') (he : e ≤ e') : PDom W X K c' m' e' v := by
  refine h.trans (Nat.pow_le_pow_left ?_ _)
  exact Nat.mul_le_mul (Nat.mul_le_mul hc (Nat.pow_le_pow_right (by omega) hm))
    (Nat.pow_le_pow_right hX he)
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
/-- A base of at least one is below its `(K + 1)`-st power. -/
theorem le_pow_succ {a : ℕ} : a ≤ a ^ (K + 1) :=
  Nat.le_self_pow (by omega) a
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
theorem const (c : ℕ) : PDom W X K (c + 1) 0 0 c := by
  simp only [PDom, pow_zero, Nat.mul_one]
  exact (Nat.le_succ c).trans (le_pow_succ)
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
theorem add (hX : 1 ≤ X) {c₁ c₂ m₁ m₂ e₁ e₂ v₁ v₂ : ℕ} (h₁ : PDom W X K c₁ m₁ e₁ v₁)
    (h₂ : PDom W X K c₂ m₂ e₂ v₂) :
    PDom W X K (c₁ + c₂) (max m₁ m₂) (max e₁ e₂) (v₁ + v₂) := by
  have h₁' := h₁.mono hX (c' := c₁) (m' := max m₁ m₂) (e' := max e₁ e₂) le_rfl (le_max_left _ _)
    (le_max_left _ _)
  have h₂' := h₂.mono hX (c' := c₂) (m' := max m₁ m₂) (e' := max e₁ e₂) le_rfl (le_max_right _ _)
    (le_max_right _ _)
  unfold PDom at h₁' h₂' ⊢
  refine (Nat.add_le_add h₁' h₂').trans ?_
  rw [Nat.add_mul, Nat.add_mul]
  exact pow_add_pow_le (Nat.zero_le _) (Nat.zero_le _) (by omega)
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
theorem mul {c₁ c₂ m₁ m₂ e₁ e₂ v₁ v₂ : ℕ} (h₁ : PDom W X K c₁ m₁ e₁ v₁)
    (h₂ : PDom W X K c₂ m₂ e₂ v₂) : PDom W X K (c₁ * c₂) (m₁ + m₂) (e₁ + e₂) (v₁ * v₂) := by
  unfold PDom at h₁ h₂ ⊢
  refine (Nat.mul_le_mul h₁ h₂).trans (le_of_eq ?_)
  rw [← mul_pow, pow_add, pow_add]
  ring_nf
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
/-- Below the unpowered monomial. -/
theorem ofMono {c m e v : ℕ} (h : v ≤ c * (W + 1) ^ m * X ^ e) : PDom W X K c m e v :=
  h.trans le_pow_succ
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline
section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.DegreeArithmetic
theorem esize_nat_le_four (x : ℕ) : esize x ≤ 4 * x + 1 :=
  (esize_nat_le x).trans (by have := Nat.size_le.mpr (Nat.lt_two_pow_self (n := x)); omega)
end
end MIPRE.Pipeline

namespace MIPRE.CL.Detyping
section
open Cost Pipeline Polynomial
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T] {ℓ : ℕ}
variable (E : T → T → Prop) [DecidableRel E]
/-- The detyped sampler's coefficient is its runtime polynomial's value at `1`: the router's cost
at the size of the index. -/
theorem samplerCoefficient_eq (n B k : ℕ) : samplerCoefficient E n B k =
    (Prog.routeCost (Program.route E) (Program.post (graphDim T)) B k).eval (esize n + 2) := by
  have h := Polynomial.eval_eq_sum_range (p := samplerCost E n B k) 1
  simp only [one_pow, Nat.mul_one] at h
  rw [samplerCoefficient, ← h, samplerCost, eval_comp]
  simp only [eval_add, eval_X, eval_C]
  congr 1
  omega
end
end MIPRE.CL.Detyping

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.Detyping
open Cost Pipeline Polynomial
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T] {ℓ : ℕ}
variable (E : T → T → Prop) [DecidableRel E]
theorem _root_.solution (cS mS eS : ℕ) : ∃ c m d, ∀ {W K : ℕ} (S : TypedSampler ℓ T) (hℓ : 0 < ℓ)
    (n : ℕ), n ≤ W →
    S.TimeBoundAt n ((cS * (W + 1) ^ mS) ^ (K + 1)) (eS * (K + 1)) →
    (sampler E S hℓ).TimeBoundAt n ((c * (W + 1) ^ m) ^ (K + 1)) (d * (K + 1)) := by
  set R := (Program.route E).timeBound
  set P := (Program.post (graphDim T)).timeBound
  set cR := (∑ i ∈ Finset.range (R.natDegree + 1), R.coeff i + 1) * 4 ^ R.natDegree + 1
  exact ⟨_, _, R.natDegree * (eS + 1) * (P.natDegree + 1), fun {W K} S hℓ n hn hS => by
    have h := sampler_timeBoundAt_uniform_degree E S hℓ n _ _ hS
    have h1 : (1 : ℕ) ≤ 1 := le_rfl
    have hy : esize n + 2 + 1 ≤ 4 * (W + 1) := by have := esize_nat_le_four n; omega
    have hRy : R.eval (esize n + 2) + 1 ≤ cR * (W + 1) ^ R.natDegree * 1 ^ 0 := by
      have e1 := (polynomial_eval_mono R (Nat.le_succ (esize n + 2))).trans
        (polynomial_eval_le_sum_coeff_mul_pow R (by omega : 1 ≤ esize n + 2 + 1))
      have e2 : (esize n + 2 + 1) ^ R.natDegree ≤ 4 ^ R.natDegree * (W + 1) ^ R.natDegree := by
        rw [← mul_pow]; exact Nat.pow_le_pow_left hy _
      have e3 : 1 ≤ (W + 1) ^ R.natDegree := Nat.one_le_pow _ _ (by omega)
      set sR := ∑ i ∈ Finset.range (R.natDegree + 1), R.coeff i
      have e4 : sR * (esize n + 2 + 1) ^ R.natDegree ≤
          sR * (4 ^ R.natDegree * (W + 1) ^ R.natDegree) := Nat.mul_le_mul_left _ e2
      have e1' : R.eval (esize n + 2) ≤ sR * (esize n + 2 + 1) ^ R.natDegree := e1
      have e5 : ((sR + 1) * 4 ^ R.natDegree + 1) * (W + 1) ^ R.natDegree =
          sR * (4 ^ R.natDegree * (W + 1) ^ R.natDegree) + 4 ^ R.natDegree * (W + 1) ^ R.natDegree +
            (W + 1) ^ R.natDegree := by ring
      show R.eval _ + 1 ≤ ((sR + 1) * 4 ^ R.natDegree + 1) * (W + 1) ^ R.natDegree * 1 ^ 0
      rw [pow_zero, Nat.mul_one, e5]
      omega
    have hRy' : PDom W 1 K cR R.natDegree 0 (R.eval (esize n + 2)) :=
      PDom.ofMono (by omega)
    have hF : PDom W 1 K _ _ _ ((cS * (W + 1) ^ mS) ^ (K + 1) *
        (R.eval (esize n + 2) + 1) ^ (eS * (K + 1))) :=
      PDom.ofPoweredCall (X := 1) le_rfl hRy le_rfl
    have hsum := (hRy'.add h1 hF)
    have htot := (PDom.const 10).mul (((hsum.add h1 ((hsum.add h1 (PDom.const 1)).poly h1 P)).add h1
      (PDom.const 10)))
    refine h.mono ?_ ?_
    · rw [samplerCoefficient_eq]
      have := htot.le_final
      simp only [one_pow, Nat.mul_one] at this
      refine le_trans (le_of_eq ?_) this
      simp only [Prog.routeCost, eval_mul, eval_add, eval_C, eval_pow, eval_one, eval_comp, R, P]
    · simp only [samplerDegree, Prog.routeDegree]
      have : eS * (K + 1) + 1 ≤ (eS + 1) * (K + 1) := by nlinarith
      calc R.natDegree * (eS * (K + 1) + 1) * (P.natDegree + 1)
          ≤ R.natDegree * ((eS + 1) * (K + 1)) * (P.natDegree + 1) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ this)
        _ = R.natDegree * (eS + 1) * (P.natDegree + 1) * (K + 1) := by ring⟩
end MIPRE.CL.Detyping
