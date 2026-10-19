-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Pad.formula_inputsLt
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:11:08.999983+00:00
-- url     : https://prove2.me/submissions/f26f270d-aac1-4378-9ddf-9b2f83724389

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Padded.lean (solution of MIPRE.TM.CookLevin.Pad.formula_inputsLt);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Language
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation
import Mathlib.Tactic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_CookLevin_Local
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_TM_CookLevin_Tableau
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Machine
import Definitions.Def_MIPRE_TM_CookLevin_Layout
import Definitions.Def_MIPRE_TM_CookLevin_FieldFml
import Definitions.Def_MIPRE_TM_CookLevin_Kinds
import Definitions.Def_MIPRE_TM_CookLevin_Families
import Definitions.Def_MIPRE_TM_CookLevin_Window
import Definitions.Def_MIPRE_TM_CookLevin_FamilyFml
import Definitions.Def_MIPRE_TM_Interp_Tape
import Definitions.Def_MIPRE_TM_Interp_Reach
import Definitions.Def_MIPRE_TM_Interp_Routines
import Definitions.Def_MIPRE_TM_Interp_Repr
import Definitions.Def_MIPRE_TM_Interp_CopyTree
import Definitions.Def_MIPRE_TM_Interp_GetEnv
import Definitions.Def_MIPRE_TM_Interp_Desc
import Definitions.Def_MIPRE_TM_Interp_Step
import Definitions.Def_MIPRE_TM_Interp_InputRoutines
import Definitions.Def_MIPRE_TM_Interp_Run
import Definitions.Def_MIPRE_Foundations_SAT_Table
import Definitions.Def_MIPRE_TM_CookLevin_Params
import Definitions.Def_MIPRE_TM_CookLevin_AnsEnd
import Definitions.Def_MIPRE_TM_CookLevin_Index
import Definitions.Def_MIPRE_TM_CookLevin_Describer
import Definitions.Def_MIPRE_TM_CookLevin_LayoutProg
import Definitions.Def_MIPRE_TM_CookLevin_FieldProg
import Definitions.Def_MIPRE_TM_CookLevin_FamilyProg
import Definitions.Def_MIPRE_TM_CookLevin_DescProg
import Definitions.Def_MIPRE_TM_CookLevin_Semantics
import Definitions.Def_MIPRE_TM_CookLevin_Correct
import Definitions.Def_MIPRE_TM_CookLevin_Sound
import Definitions.Def_MIPRE_TM_CookLevin_Sat
import Definitions.Def_MIPRE_TM_CookLevin_Assemble
import Definitions.Def_MIPRE_TM_CookLevin_Link
import Definitions.Def_MIPRE_TM_CookLevin_Decoupled
import Definitions.Def_MIPRE_TM_CookLevin_DecoupledProg
import Definitions.Def_MIPRE_Foundations_SAT_Padding
import Definitions.Def_MIPRE_Foundations_SAT_Rename
import Definitions.Def_MIPRE_Foundations_SAT_PowerPadding
import Definitions.Def_MIPRE_TM_CookLevin_Padded

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.xnor {n : ℕ} {f g : Fml} (hf : f.InputsLt n) (hg : g.InputsLt n) :
    (Fml.xnor f g).InputsLt n := ⟨⟨hf, hg⟩, hf, hg⟩
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.foldl_and {n : ℕ} (l : List Fml) (init : Fml) (hi : init.InputsLt n)
    (hl : ∀ f ∈ l, f.InputsLt n) : (l.foldl and init).InputsLt n := by
  induction l generalizing init with
  | nil => exact hi
  | cons f l ih =>
    exact ih (and init f) ⟨hi, hl f (List.mem_cons_self ..)⟩ fun g hg => hl g (List.mem_cons_of_mem _ hg)
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.andList {n : ℕ} (l : List Fml) (hl : ∀ f ∈ l, f.InputsLt n) : (Fml.andList l).InputsLt n :=
  InputsLt.foldl_and l _ trivial hl
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.foldl_or {n : ℕ} (l : List Fml) (init : Fml) (hi : init.InputsLt n)
    (hl : ∀ f ∈ l, f.InputsLt n) : (l.foldl or init).InputsLt n := by
  induction l generalizing init with
  | nil => exact hi
  | cons f l ih =>
    exact ih (or init f) ⟨hi, hl f (List.mem_cons_self ..)⟩ fun g hg => hl g (List.mem_cons_of_mem _ hg)
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.orList {n : ℕ} (l : List Fml) (hl : ∀ f ∈ l, f.InputsLt n) : (Fml.orList l).InputsLt n :=
  InputsLt.foldl_or l _ trivial hl
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.field {n a W : ℕ} (h : a + W ≤ n) : ∀ f ∈ Fml.field a W, f.InputsLt n := by
  intro f hf
  simp only [Fml.field, List.mem_map, List.mem_range'] at hf
  obtain ⟨i, ⟨hi1, hi2⟩, rfl⟩ := hf
  show i < n
  omega
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.padTo {n W : ℕ} {fs : List Fml} (h : ∀ f ∈ fs, f.InputsLt n) :
    ∀ f ∈ Fml.padTo W fs, f.InputsLt n := by
  intro f hf
  simp only [Fml.padTo, List.mem_append, List.mem_replicate] at hf
  rcases hf with hf | ⟨-, rfl⟩
  · exact h f hf
  · trivial
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.foldl_zip {n : ℕ} {γ : Type*} (step : Fml → Fml × γ → Fml)
    (hstep : ∀ acc p, acc.InputsLt n → p.1.InputsLt n → (step acc p).InputsLt n)
    (fs : List Fml) (c : List γ) (init : Fml) (hi : init.InputsLt n) (hl : ∀ f ∈ fs, f.InputsLt n) :
    ((fs.zip c).foldl step init).InputsLt n := by
  induction fs generalizing c init with
  | nil => exact hi
  | cons f fs ih =>
    cases c with
    | nil => exact hi
    | cons b c =>
      rw [List.zip_cons_cons, List.foldl_cons]
      exact ih c _ (hstep init (f, b) hi (hl f (List.mem_cons_self ..)))
        fun g hg => hl g (List.mem_cons_of_mem _ hg)
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.ltConst {n : ℕ} {fs : List Fml} (c : BitStr) (h : ∀ f ∈ fs, f.InputsLt n) :
    (Fml.ltConst fs c).InputsLt n :=
  InputsLt.foldl_zip Fml.ltStep (fun _ _ ha hp => ⟨⟨hp, trivial⟩, hp.xnor trivial, ha⟩) fs c _ trivial h
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost Cost.PolyTimeFun
theorem InputsLt.rename {n m : ℕ} {f : Fml} (hf : f.InputsLt n)
    (ρ : ℕ → ℕ) (hρ : ∀ i < n, ρ i < m) : (rename ρ f).InputsLt m := by
  induction f with
  | inp i => exact hρ i hf
  | const b => trivial
  | and f g ihf ihg => exact ⟨ihf hf.1, ihg hf.2⟩
  | or f g ihf ihg => exact ⟨ihf hf.1, ihg hf.2⟩
  | not f ih => exact ih hf
end
end MIPRE.SAT.Fml

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.Pad
open SAT Cost Cost.PolyTimeFun Fml Desc
theorem _root_.solution {ℓ r m : ℕ} (hℓ : ℓ ≤ m) (hr : r ≤ m)
    (f : Fml) (hf : f.InputsLt (2 * ℓ + 3 * r + 5)) :
    (formula ℓ r m f).InputsLt (5 * m + 5) := by
  have hlo (b old : ℕ) (hb : b + m ≤ 5 * m + 5) :
      (low b old m).InputsLt (5 * m + 5) :=
    Fml.InputsLt.ltConst _ (Fml.InputsLt.padTo (Fml.InputsLt.field hb))
  have hblank (b sign : ℕ) (hb : b < 5 * m + 5) (hs : sign < 5 * m + 5) :
      (blankSign b sign).InputsLt (5 * m + 5) :=
    Fml.InputsLt.xnor hs hb
  have hren : (Fml.rename (fun i => (layout ℓ r m).getD i 0) f).InputsLt (5 * m + 5) := by
    apply hf.rename
    intro i hi
    have hlen : i < (layout ℓ r m).length := by simpa using hi
    rw [List.getD_eq_getElem _ 0 hlen]
    exact mem_layout_lt hℓ hr (List.getElem_mem hlen)
  apply Fml.InputsLt.orList
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · refine ⟨Fml.InputsLt.andList _ ?_, hren⟩
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> exact hlo _ _ (by omega)
  · exact ⟨hlo _ _ (by omega), hblank _ _ (by omega) (by omega)⟩
  · exact ⟨hlo _ _ (by omega), hblank _ _ (by omega) (by omega)⟩
end MIPRE.TM.CookLevin.Pad
