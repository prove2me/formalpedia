-- Prove2me | solution 1 for MIPRE.CL.Detyping.DeciderProgram.prog_time
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:06:03.358977+00:00
-- url     : https://prove2.me/submissions/67f4022f-d079-48f3-8b4d-7c35a9ff07dc

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingDeciderCost.lean (solution of MIPRE.CL.Detyping.DeciderProgram.prog_time);
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
import Theorems.Thm_MIPRE_CL_Detyping_DeciderProgram_route_call_typed
import Theorems.Thm_MIPRE_CL_Detyping_Program_readNat_encode
import Theorems.Thm_MIPRE_Cost_Eval_deterministic
import Theorems.Thm_MIPRE_Cost_seqProg_closed
import Theorems.Thm_MIPRE_Cost_seqProg_runs
import Theorems.Thm_MIPRE_Pipeline_PDom_poly
import Theorems.Thm_MIPRE_Pipeline_PRuns_routeCall

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Prog
section
open PolyTimeFun Polynomial
theorem routeOneCall_direct_cost (route : PolyTimeFun Data (Bool × Data))
    (p : Prog) (post : PolyTimeFun (Data × Data) Data) (x r : Data)
    (h : route x = (false, r)) :
    ∃ t ≤ route.timeBound.eval x.size + r.size + 4,
      (routeOneCall route p post).Runs x r t := by
  obtain ⟨t, ht, hr⟩ := route.computes x
  rw [h] at hr
  refine ⟨_, ?_, Eval.let_ hr
    (Eval.elim_cons (i := 0) (a := Data.nil) (b := r) (by simp [encode, Data.ofBool])
      (Eval.elim_nil (i := 0) (by simp) (Eval.var_of_get (i := 1) (by simp))))⟩
  simp only [esize_data] at ht
  omega
end
end MIPRE.Cost.Prog

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
theorem of_le {c m e v v' : ℕ} (h : PDom W X K c m e v) (hv : v' ≤ v) : PDom W X K c m e v' :=
  hv.trans h
end
end MIPRE.Pipeline.PDom

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
/-- An affine function of `W`. -/
theorem ofAffine {a b v : ℕ} (h : v ≤ a * W + b) : PDom W X K (a + b + 1) 1 0 v := by
  simp only [PDom, pow_one, pow_zero, Nat.mul_one]
  refine h.trans ((?_ : a * W + b ≤ (a + b + 1) * (W + 1)).trans le_pow_succ)
  nlinarith
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
theorem ofLeX {v : ℕ} (h : v ≤ X) : PDom W X K 1 0 1 v := by
  simp only [PDom, pow_zero, pow_one, Nat.mul_one, Nat.one_mul]
  exact h.trans (le_pow_succ)
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

namespace MIPRE.Pipeline
section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.DegreeArithmetic
theorem esize_nat_le_four (x : ℕ) : esize x ≤ 4 * x + 1 :=
  (esize_nat_le x).trans (by have := Nat.size_le.mpr (Nat.lt_two_pow_self (n := x)); omega)
end
end MIPRE.Pipeline

namespace MIPRE.Pipeline
section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.DegreeArithmetic
/-- A pair of dominated data is dominated. -/
theorem PDom.consSize (c m e c' m' e' : ℕ) : ∃ C M E, ∀ {W X K : ℕ} (x r : Data), 1 ≤ X →
    PDom W X K c m e x.size → PDom W X K c' m' e' r.size → PDom W X K C M E (Data.cons x r).size :=
  ⟨_, _, _, fun x r hX hx hr => by
    simpa only [Data.size_cons] using (hx.add hX hr).add hX (PDom.const 1)⟩
end
end MIPRE.Pipeline

namespace MIPRE.Pipeline
section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.DegreeArithmetic
/-- An index and a datum of size below `X`. -/
theorem PDom.indexInput : ∃ c m e, ∀ {W X K : ℕ} (n : ℕ) (d : Data), 1 ≤ X → n ≤ W →
    d.size + 1 ≤ X → PDom W X K c m e (Data.cons (encode n) d).size := by
  exact ⟨_, _, _, fun {W X K} n d hX hn hd => by
    have en := esize_nat_le_four n
    refine ((PDom.ofAffine (a := 4) (b := 2) (by omega : esize n + 1 ≤ 4 * W + 2)).add hX
      (PDom.ofLeX (by omega : d.size ≤ X))).of_le ?_
    simp only [Data.size_cons]
    change esize n + d.size + 1 ≤ _
    omega⟩
end
end MIPRE.Pipeline

namespace MIPRE.Pipeline.PRuns
section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.DegreeArithmetic
variable {W X K : ℕ}
theorem size_le {c m e : ℕ} {p : Prog} {x r : Data} (h : PRuns W X K c m e p x r) :
    PDom W X K c m e r.size :=
  let ⟨_, ht, hr⟩ := h
  ht.of_le hr.size_le
end
end MIPRE.Pipeline.PRuns

namespace MIPRE.Pipeline.PRuns
section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.DegreeArithmetic
variable {W X K : ℕ}
theorem mono (hX : 1 ≤ X) {c m e c' m' e' : ℕ} {p : Prog} {x r : Data}
    (h : PRuns W X K c m e p x r) (hc : c ≤ c') (hm : m ≤ m') (he : e ≤ e') :
    PRuns W X K c' m' e' p x r :=
  let ⟨t, ht, hr⟩ := h
  ⟨t, ht.mono hX hc hm he, hr⟩
end
end MIPRE.Pipeline.PRuns

namespace MIPRE.Pipeline.PRuns
section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.DegreeArithmetic
variable {W X K : ℕ}
theorem seq (hX : 1 ≤ X) {c₁ m₁ e₁ c₂ m₂ e₂ : ℕ} {p q : Prog} (hq : q.WellScoped 1)
    {x y r : Data} (h₁ : PRuns W X K c₁ m₁ e₁ p x y) (h₂ : PRuns W X K c₂ m₂ e₂ q y r) :
    PRuns W X K (c₁ + c₂ + 2) (max (max m₁ m₂) 0) (max (max e₁ e₂) 0) (seqProg p q) x r :=
  let ⟨_, hs, hp⟩ := h₁
  let ⟨_, ht, hq'⟩ := h₂
  ⟨_, (hs.add hX ht).add hX (PDom.const 1), seqProg_runs hq hp hq'⟩
end
end MIPRE.Pipeline.PRuns

namespace MIPRE.Pipeline.PRuns
section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.DegreeArithmetic
variable {W X K : ℕ}
/-- **A direct answer** of a router. -/
theorem routeDirect (route : PolyTimeFun Data (Bool × Data)) (post : PolyTimeFun (Data × Data) Data)
    (c m e : ℕ) : ∃ C M E, ∀ {W X K : ℕ} (p : Prog) (x r : Data), 1 ≤ X → route x = (false, r) →
      PDom W X K c m e x.size → PRuns W X K C M E (Prog.routeOneCall route p post) x r :=
  ⟨_, _, _, fun {W X K} p x r hX hroute hx => by
    obtain ⟨t, ht, hr⟩ := Prog.routeOneCall_direct_cost route p post x r hroute
    have hR : PDom W X K _ _ _ (route.timeBound.eval x.size) := hx.poly hX route.timeBound
    have hsz := route.esize_apply_le x
    rw [hroute] at hsz
    simp only [esize_prod, esize_false, esize_data] at hsz
    exact ⟨t, (((PDom.const 2).mul hR).add hX (PDom.const 4)).of_le (by omega), hr⟩⟩
end
end MIPRE.Pipeline.PRuns

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.Detyping.DeciderProgram
open Cost Cost.PolyTimeFun Detyping.Program Pipeline
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
variable (E : T → T → Prop) [DecidableRel E]
variable {ℓ : ℕ}
theorem _root_.solution (cS mS eS cC mC eC cD mD eD : ℕ) : ∃ c m e, ∀ {W K : ℕ}
    (S : TypedSampler ℓ T) (D : TypedDecider T) (C : CutoffProgram) (n : ℕ), n ≤ W →
    S.TimeBoundAt n ((cS * (W + 1) ^ mS) ^ (K + 1)) (eS * (K + 1)) →
    (∀ {X : ℕ}, 1 ≤ X → PRuns W X K cC mC eC C.prog (encode n) (encode (C.inner n, C.outer n))) →
    (∀ {X : ℕ}, 1 ≤ X → ∀ (u v : T) (x y a b : BitStr), x.length = S.dim n →
      y.length = S.dim n → a.length ≤ C.inner n → b.length ≤ C.inner n →
      ∃ r, PRuns W X K cD mD eD D.prog (encode (n, u, x, v, y, a, b)) r) →
    (decider E S D C).TimeBoundAt n ((c * (W + 1) ^ m) ^ (K + 1)) (e * (K + 1)) := by
  obtain ⟨ci, mi, ei, hi⟩ := PDom.indexInput
  obtain ⟨c1, m1, e1, h1⟩ := PRuns.routeCall dimensionRoute pairPost ci mi ei (cS * 2 ^ eS) mS 0
  obtain ⟨cx, mx, ex, hx⟩ := PDom.consSize ci mi ei (cS * 2 ^ eS) mS 0
  obtain ⟨c2, m2, e2, h2⟩ := PRuns.routeCall cutoffRoute pairPost cx mx ex cC mC eC
  obtain ⟨cc, mc, ec, hc⟩ := PDom.consSize cx mx ex cC mC eC
  obtain ⟨c3, m3, e3, h3⟩ := PRuns.routeCall (route E) post cc mc ec cD mD eD
  obtain ⟨c4, m4, e4, h4⟩ := PRuns.routeDirect (route E) post cc mc ec
  exact ⟨_, _, _, fun {W K} S D C n hn hS hC hD d => by
    have hX : 1 ≤ d.size + 1 := by omega
    set input : Data := .cons (encode n) d with hinput
    have pin : PDom W (d.size + 1) K ci mi ei input.size := hi n d hX hn le_rfl
    -- the dimension
    obtain ⟨rd, td, htd, hrd⟩ := hS .nil
    obtain ⟨td', hrd'⟩ := S.runs_dimension n
    have hrd_eq : rd = encode (S.dim n) :=
      (Eval.deterministic (show S.prog.Runs (encode (n, (TypedSampler.Query.dimension :
        TypedSampler.Query T))) rd td from hrd) hrd').1
    subst hrd_eq
    have pS : PRuns W (d.size + 1) K (cS * 2 ^ eS) mS 0 S.prog (.cons (encode n) .nil)
        (encode (S.dim n)) := by
      refine ⟨td, htd.trans (le_of_eq ?_), hrd⟩
      simp only [Data.size_nil, pow_zero, Nat.mul_one]
      rw [mul_pow, mul_pow, ← pow_mul, Nat.mul_comm eS]
      ring
    have R1 := h1 S.closed input _ input _ hX (by simp [dimensionRoute, input, readNat_encode])
      pin pS
    have hp1 : pairPost (input, encode (S.dim n)) = .cons input (encode (S.dim n)) := rfl
    rw [hp1] at R1
    set x1 : Data := .cons input (encode (S.dim n)) with hx1def
    have px1 : PDom W (d.size + 1) K cx mx ex x1.size := hx input _ hX pin pS.size_le
    -- the cutoff
    have PC := hC hX
    have R2 := h2 C.closed x1 _ x1 _ hX
      (by simp [cutoffRoute, x1, input, readNat_encode]) px1 PC
    have hp2 : pairPost (x1, encode (C.inner n, C.outer n)) =
        context input (S.dim n) (C.inner n) (C.outer n) := rfl
    rw [hp2] at R2
    set c : Data := context input (S.dim n) (C.inner n) (C.outer n) with hcdef
    have pc : PDom W (d.size + 1) K cc mc ec c.size := hc x1 _ hX px1 PC.size_le
    -- the decision
    have R3 : ∃ r, PRuns W (d.size + 1) K (c3 + c4) (max m3 m4) (max e3 e4) (decisionStage E D)
        c r := by
      cases hroute : route E c with
      | mk call payload =>
        cases call with
        | false =>
          exact ⟨payload, (h4 D.prog c payload hX hroute pc).mono hX (by omega)
            (le_max_right _ _) (le_max_right _ _)⟩
        | true =>
          obtain ⟨u, v, x, y, a, b, rfl, hxl, hyl, ha, hb⟩ :=
            route_call_typed E n (S.dim n) (C.inner n) (C.outer n) d _ hroute
          obtain ⟨r, PD⟩ := hD hX u v x y a b hxl hyl ha hb
          exact ⟨_, (h3 D.closed c _ _ r hX hroute pc PD).mono hX (by omega) (le_max_left _ _)
            (le_max_left _ _)⟩
    obtain ⟨r, R3⟩ := R3
    obtain ⟨t, ht, hr⟩ := PRuns.seq hX (seqProg_closed (cutoffStage_closed C)
      (decisionStage_closed E D)) R1 (PRuns.seq hX (decisionStage_closed E D) R2 R3)
    exact ⟨r, t, ht.le_final, hr⟩⟩
end MIPRE.CL.Detyping.DeciderProgram
