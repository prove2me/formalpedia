-- Prove2me | solution 1 for MIPRE.Repeat.repDecider_accepts_iff
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:50:34.55364+00:00
-- url     : https://prove2.me/submissions/4c2201ff-959d-4dc0-ba57-f36208d88312

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/RepDecider.lean (solution of MIPRE.Repeat.repDecider_accepts_iff);
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
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Repeat_DecLoop
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Repeat_DecMain
import Definitions.Def_MIPRE_Foundations_Repeat_RepDecider
import Theorems.Thm_MIPRE_CL_chunk_map
import Theorems.Thm_MIPRE_Cost_Data_toList_encode_bitStr
import Theorems.Thm_MIPRE_Cost_Eval_deterministic
import Theorems.Thm_MIPRE_Cost_Prog_coordLoop_inv
import Theorems.Thm_MIPRE_Cost_Prog_coordLoop_of_acc
import Theorems.Thm_MIPRE_Cost_Prog_decMain_inv
import Theorems.Thm_MIPRE_Cost_Prog_prepProg_runs
import Theorems.Thm_MIPRE_Cost_Prog_repDecCore_inv
import Theorems.Thm_MIPRE_Cost_Prog_repDecCore_runs
import Theorems.Thm_MIPRE_Cost_Prog_repDecCore_wellScoped
import Theorems.Thm_MIPRE_Cost_hardcode_time
import Theorems.Thm_MIPRE_Cost_hardcode_time_rev
import Theorems.Thm_MIPRE_Repeat_DecAcc_iff

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Prog
section
open Data
theorem bitWalkBody_wellScoped : bitWalkBody.WellScoped 1 := by
  simp [bitWalkBody, WellScoped]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem bitWalkProg_wellScoped : bitWalkProg.WellScoped 1 :=
  ⟨Nat.zero_lt_one, bitWalkBody_wellScoped⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem pairTakeProg_wellScoped : pairTakeProg.WellScoped 1 := by
  simp [pairTakeProg, WellScoped, takeBody, callVar, revProg, revOntoProg, revOntoBody]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem finalProg_wellScoped : finalProg.WellScoped 1 := by simp [finalProg, WellScoped]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem preProg_wellScoped : preProg.WellScoped 1 := by
  simp only [preProg, WellScoped, callVar]
  refine ⟨by omega, trivial, by omega, trivial, by omega, trivial, by omega, trivial, by omega,
    trivial, by omega, trivial, by omega, trivial, by omega, trivial, by omega, trivial, by omega,
    trivial, ⟨by omega, by omega, by omega⟩, ⟨by omega, pairTakeProg_wellScoped.mono (by omega) _⟩,
    ⟨by omega, by omega⟩, ⟨by omega, bitWalkProg_wellScoped.mono (by omega) _⟩, by omega, trivial,
    by omega, ⟨⟨by omega, by omega⟩, ⟨by omega, bitWalkProg_wellScoped.mono (by omega) _⟩, by omega,
      trivial, by omega, ⟨by omega, trivial, by omega, trivial, by omega, trivial,
        ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩,
        ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩⟩, trivial⟩, trivial⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem stepProg_wellScoped {univ : Prog} (hU : univ.WellScoped 1) :
    (stepProg univ).WellScoped 1 := by
  simp only [stepProg, WellScoped, callVar]
  exact ⟨⟨by omega, preProg_wellScoped.mono (by omega) _⟩, by omega, ⟨trivial, trivial⟩,
    ⟨by omega, hU.mono (by omega) _⟩, by omega, ⟨trivial, trivial⟩, by omega, ⟨by omega,
      ⟨⟨trivial, trivial⟩, by omega⟩, ⟨trivial, trivial⟩⟩, ⟨trivial, trivial⟩⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem coordBody_wellScoped {univ : Prog} (hU : univ.WellScoped 1) :
    (coordBody univ).WellScoped 1 := by
  simp only [coordBody, WellScoped, callVar]
  exact ⟨by omega, trivial, by omega, ⟨by omega, finalProg_wellScoped.mono (by omega) _⟩,
    ⟨by omega, by omega⟩, by omega, (stepProg_wellScoped hU).mono (by omega) _⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem prepState_eq (dP : Data) (lam tau beta n s : ℕ) (x y a b : BitStr) :
    prepState dP lam tau beta n s x y a b =
      decState (ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)))) (x.map ofBool) (y.map ofBool)
        (toList (parse a)) (toList (parse b))
        (decCtx dP (encode n) s (2 ^ (beta * (Nat.size lam + Nat.size n)))) := by
  simp [prepState, decState, encode_bitStr_eq_list, list_toList]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem coordLoop_wellScoped {univ : Prog} (hU : univ.WellScoped 1) :
    (Prog.loop (coordBody univ)).WellScoped 1 := ⟨Nat.zero_lt_one, coordBody_wellScoped hU⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem decMain_runs_state {univ : Prog} (hU : univ.WellScoped 1) (inp st₀ st₁ : Data) {t₀ t₁ : ℕ}
    (hp : Eval [inp] (prepProg univ) (.cons st₀ st₁) t₀) {r : Data}
    (hl : Eval [Data.cons st₀ st₁] (.loop (coordBody univ)) r t₁) :
    Eval [inp] (decMain univ) r (t₀ + t₁ + (Data.cons st₀ st₁).size + 4) :=
  (Eval.let_ hp (Eval.elim_cons (i := 0) (a := st₀) (b := st₁) (by simp)
    (callVar_eval (coordLoop_wellScoped hU) (i := 2) (v := .cons st₀ st₁) (by simp) hl))).cast_cost
    (by omega)
end
end MIPRE.Cost.Prog

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
/-- The run of the repeated decider on a well-formed input, from a run of `decMain`. -/
theorem repDeciderProg_runs (sp dp : Prog) (lam tau beta n : ℕ) (x y a b : BitStr) {r : Data} {t : ℕ}
    (h : Eval [decInput (encode sp) (encode dp) (encode lam) (encode tau) (encode beta) (encode n)
      (encode x) (encode y) (encode a) (encode b)] (decMain selfUniversal.univ) r t) :
    ∃ t', (repDeciderProg sp dp lam tau beta).Runs (encode (n, x, y, a, b)) r t' :=
  ⟨_, hardcode_time (repDecCore_wellScoped selfUniversal.closed)
    (repDecCore_runs selfUniversal.closed _ _ _ _ _ _ _ _ _ _ h)⟩
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
/-- Conversely, a run of the repeated decider on a well-formed input is a run of `decMain`. -/
theorem repDeciderProg_inv (sp dp : Prog) (lam tau beta n : ℕ) (x y a b : BitStr) {r : Data} {t : ℕ}
    (h : (repDeciderProg sp dp lam tau beta).Runs (encode (n, x, y, a, b)) r t) :
    ∃ t', Eval [decInput (encode sp) (encode dp) (encode lam) (encode tau) (encode beta) (encode n)
      (encode x) (encode y) (encode a) (encode b)] (decMain selfUniversal.univ) r t' := by
  obtain ⟨t₁, -, h₁⟩ := hardcode_time_rev (repDecCore_wellScoped selfUniversal.closed) h
  exact repDecCore_inv selfUniversal.closed _ _ _ _ _ _ _ _ _ _ h₁
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
variable {ℓ : ℕ} (S : CL.Sampler ℓ) (D : Decider)
/-- The universal machine accepts a coordinate query iff the input decider does. -/
theorem univ_accepts_iff (n : ℕ) (xi yi ai bi : BitStr) :
    (∃ t, Eval [decQuery (encode D.prog) (encode n) (encode xi) (encode yi) (encode ai) (encode bi)]
      selfUniversal.univ (.cons .nil .nil) t) ↔ D.Accepts n xi yi ai bi := by
  constructor
  · rintro ⟨t, h⟩
    obtain ⟨t', h'⟩ := selfUniversal.halts_of _ _ _ _ h
    exact ⟨t', h'⟩
  · rintro ⟨t, h⟩
    obtain ⟨t', -, h'⟩ := selfUniversal.time_le _ _ _ _ h
    exact ⟨t', h'⟩
end
end MIPRE.Repeat

namespace MIPRE.Repeat
section
open Cost Cost.Data Cost.Prog CL
variable {ℓ : ℕ} (S : CL.Sampler ℓ) (D : Decider)
theorem bitsOf_toList_encode (x : BitStr) : bitsOf (toList (encode x)) = x := by
  rw [toList_encode_bitStr, bitsOf_map_ofBool]
end
end MIPRE.Repeat

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Repeat
open Cost Cost.Data Cost.Prog CL
variable {ℓ : ℕ} (S : CL.Sampler ℓ) (D : Decider)
theorem _root_.solution (lam tau beta n : ℕ) (x y a b : BitStr) :
    (repDecider S.prog D.prog lam tau beta).Accepts n x y a b ↔ RepAcc S D lam tau beta n x y a b := by
  obtain ⟨td, hdim⟩ := dim_call S n
  obtain ⟨tp, -, hp⟩ := prepProg_runs selfUniversal.closed (encode S.prog) (encode D.prog) lam tau beta
    n (S.dim n) (encode x) (encode y) (encode a) (encode b) hdim
  simp only [bitsOf_toList_encode] at hp
  -- the loop's predicate, in tuple form
  have hloop : DecAcc selfUniversal.univ (encode D.prog) (encode n) (S.dim n)
      (Repetition.parseBound lam beta n) (Repetition.reps lam tau n) (x.map ofBool) (y.map ofBool)
      (toList (parse a)) (toList (parse b)) ↔
      ∃ aa bb : Fin (Repetition.reps lam tau n) → BitStr,
        parse a = list (List.ofFn fun i => encode (aa i)) ∧ parse b = list (List.ofFn fun i => encode (bb i)) ∧
        ∀ i, (aa i).length ≤ Repetition.parseBound lam beta n ∧
          (bb i).length ≤ Repetition.parseBound lam beta n ∧
          D.Accepts n (chunk (S.dim n) i x) (chunk (S.dim n) i y) (aa i) (bb i) := by
    rw [DecAcc_iff]
    constructor
    · rintro ⟨aa, bb, hA, hB, hall⟩
      refine ⟨aa, bb, ?_, ?_, fun i => ?_⟩
      · rw [← list_toList (parse a), hA]
      · rw [← list_toList (parse b), hB]
      · obtain ⟨h1, h2, h3⟩ := hall i
        refine ⟨h1, h2, ?_⟩
        rw [← univ_accepts_iff]
        simpa [chunk_map, encode_bitStr_eq_list] using h3
    · rintro ⟨aa, bb, hA, hB, hall⟩
      refine ⟨aa, bb, ?_, ?_, fun i => ?_⟩
      · rw [hA, toList_list]
      · rw [hB, toList_list]
      · obtain ⟨h1, h2, h3⟩ := hall i
        refine ⟨h1, h2, ?_⟩
        rw [← univ_accepts_iff] at h3
        simpa [chunk_map, encode_bitStr_eq_list] using h3
  constructor
  · rintro ⟨t, h⟩
    obtain ⟨t₁, h₁⟩ := repDeciderProg_inv S.prog D.prog lam tau beta n x y a b h
    obtain ⟨p, t₀, hp', hcase⟩ := decMain_inv selfUniversal.closed _ h₁
    obtain ⟨rfl, -⟩ := hp'.deterministic hp
    by_cases hok : prepOk lam tau n (S.dim n) x y a b = true
    · rw [show prepResult (encode D.prog) lam tau beta n (S.dim n) x y a b =
          prepState (encode D.prog) lam tau beta n (S.dim n) x y a b by simp [prepResult, hok]] at hcase
      rcases hcase with ⟨h, -⟩ | ⟨st₀, st₁, hst, t₂, h₂⟩
      · simp [prepState] at h
      · rw [← hst, prepState_eq] at h₂
        have hacc := coordLoop_inv selfUniversal.closed (encode D.prog) (encode n) (S.dim n) _ _
          (x.map ofBool) (y.map ofBool) (toList (parse a)) (toList (parse b)) [] h₂
        simp only [prepOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
        obtain ⟨⟨⟨hx, hy⟩, ha⟩, hb⟩ := hok
        obtain ⟨aa, bb, hA, hB, hall⟩ := hloop.mp hacc
        exact ⟨hx, hy, aa, bb, by rw [← hA, ha], by rw [← hB, hb], hall⟩
    · rw [show prepResult (encode D.prog) lam tau beta n (S.dim n) x y a b = .nil by
          simp [prepResult, hok]] at hcase
      rcases hcase with ⟨-, h⟩ | ⟨st₀, st₁, hst, -⟩
      · cases h
      · cases hst
  · rintro ⟨hx, hy, aa, bb, hA, hB, hall⟩
    have hpa : parse a = list (List.ofFn fun i => encode (aa i)) := by rw [hA, parse_toBitsPost]
    have hpb : parse b = list (List.ofFn fun i => encode (bb i)) := by rw [hB, parse_toBitsPost]
    have hok : prepOk lam tau n (S.dim n) x y a b = true := by
      simp only [prepOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      exact ⟨⟨⟨hx, hy⟩, by rw [hpa, ← hA]⟩, by rw [hpb, ← hB]⟩
    rw [show prepResult (encode D.prog) lam tau beta n (S.dim n) x y a b =
        prepState (encode D.prog) lam tau beta n (S.dim n) x y a b by simp [prepResult, hok]] at hp
    have hacc := hloop.mpr ⟨aa, bb, hpa, hpb, hall⟩
    obtain ⟨t₂, h₂⟩ := coordLoop_of_acc selfUniversal.closed (encode D.prog) (encode n) (S.dim n) _ _
      (x.map ofBool) (y.map ofBool) (toList (parse a)) (toList (parse b)) [] hacc
    rw [← prepState_eq] at h₂
    obtain ⟨t', h'⟩ := repDeciderProg_runs S.prog D.prog lam tau beta n x y a b
      (decMain_runs_state selfUniversal.closed _ _ _ hp h₂)
    exact ⟨t', h'⟩
end MIPRE.Repeat
