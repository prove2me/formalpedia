-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Desc.InputsLt.linkFml
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:48:14.889975+00:00
-- url     : https://prove2.me/submissions/30e75c16-4abb-4eab-9abc-da4506ace35b

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Link.lean (solution of MIPRE.TM.CookLevin.Desc.InputsLt.linkFml);
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
theorem InputsLt.xor {n : ℕ} {f g : Fml} (hf : f.InputsLt n) (hg : g.InputsLt n) :
    (Fml.xor f g).InputsLt n := ⟨⟨hf, hg⟩, hf, hg⟩
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
theorem InputsLt.foldl_zip₂ {n : ℕ} (step : Fml → Fml × Fml → Fml)
    (hstep : ∀ acc p, acc.InputsLt n → p.1.InputsLt n → p.2.InputsLt n → (step acc p).InputsLt n)
    (fs gs : List Fml) (init : Fml) (hi : init.InputsLt n) (hf : ∀ f ∈ fs, f.InputsLt n)
    (hg : ∀ f ∈ gs, f.InputsLt n) : ((fs.zip gs).foldl step init).InputsLt n := by
  induction fs generalizing gs init with
  | nil => exact hi
  | cons f fs ih =>
    cases gs with
    | nil => exact hi
    | cons g gs =>
      rw [List.zip_cons_cons, List.foldl_cons]
      exact ih gs _ (hstep init (f, g) hi (hf f (List.mem_cons_self ..)) (hg g (List.mem_cons_self ..)))
        (fun x hx => hf x (List.mem_cons_of_mem _ hx)) fun x hx => hg x (List.mem_cons_of_mem _ hx)
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.eqFields {n : ℕ} {fs gs : List Fml} (h : ∀ f ∈ fs, f.InputsLt n)
    (hg : ∀ f ∈ gs, f.InputsLt n) : (Fml.eqFields fs gs).InputsLt n :=
  InputsLt.foldl_zip₂ Fml.eqFStep (fun _ _ ha hp hq => ⟨ha, hp.xnor hq⟩) fs gs _ trivial h hg
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
open Cost
theorem InputsLt.sum3 {n : ℕ} {f b c : Fml} (hf : f.InputsLt n) (hb : b.InputsLt n) (hc : c.InputsLt n) :
    (Fml.sum3 f b c).InputsLt n := (hf.xor hb).xor hc
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.maj3 {n : ℕ} {f b c : Fml} (hf : f.InputsLt n) (hb : b.InputsLt n) (hc : c.InputsLt n) :
    (Fml.maj3 f b c).InputsLt n := ⟨⟨hf, hb⟩, ⟨hf, hb⟩, hc⟩
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.addBits {n : ℕ} : ∀ (fs : List Fml) (c : BitStr) (cin : Fml),
    (∀ f ∈ fs, f.InputsLt n) → cin.InputsLt n →
    (∀ f ∈ (Fml.addBits fs c cin).1, f.InputsLt n) ∧ (Fml.addBits fs c cin).2.InputsLt n
  | f :: fs, b :: c, cin, hf, hc => by
    have hf0 : f.InputsLt n := hf f (List.mem_cons_self ..)
    have ih := InputsLt.addBits fs c (Fml.maj3 f (const b) cin)
      (fun g hg => hf g (List.mem_cons_of_mem _ hg))
      (InputsLt.maj3 (b := const b) hf0 trivial hc)
    refine ⟨?_, ih.2⟩
    intro g hg
    simp only [Fml.addBits, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact InputsLt.sum3 (b := const b) hf0 trivial hc
    · exact ih.1 g hg
  | [], _, cin, _, hc => ⟨fun g hg => absurd hg List.not_mem_nil, hc⟩
  | _ :: _, [], cin, _, hc => ⟨fun g hg => absurd hg List.not_mem_nil, hc⟩
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.addConstBits {n : ℕ} {fs : List Fml} (c : BitStr) (h : ∀ f ∈ fs, f.InputsLt n) :
    ∀ f ∈ Fml.addConstBits fs c, f.InputsLt n :=
  (InputsLt.addBits fs c (const false) h (trivial : (const false).InputsLt n)).1
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.addConstCarry {n : ℕ} {fs : List Fml} (c : BitStr) (h : ∀ f ∈ fs, f.InputsLt n) :
    (Fml.addConstCarry fs c).InputsLt n :=
  (InputsLt.addBits fs c (const false) h (trivial : (const false).InputsLt n)).2
end
end MIPRE.SAT.Fml

namespace MIPRE.SAT.Fml
section
open Cost
theorem InputsLt.addConstRel {n : ℕ} {fs gs : List Fml} (c : BitStr) (h : ∀ f ∈ fs, f.InputsLt n)
    (hg : ∀ f ∈ gs, f.InputsLt n) : (Fml.addConstRel fs gs c).InputsLt n :=
  ⟨InputsLt.eqFields hg (InputsLt.addConstBits c h), InputsLt.addConstCarry c h⟩
end
end MIPRE.SAT.Fml

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem InputsLt.not' {n : ℕ} {f : Fml} (hf : f.InputsLt n) : (Fml.not f).InputsLt n := hf
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem InputsLt.list_cons {n : ℕ} {f : Fml} {l : List Fml} (hf : f.InputsLt n) (hl : ∀ g ∈ l, g.InputsLt n) :
    ∀ g ∈ f :: l, g.InputsLt n := by
  simpa [List.forall_mem_cons] using ⟨hf, hl⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem InputsLt.list_nil {n : ℕ} : ∀ g ∈ ([] : List Fml), g.InputsLt n := by simp
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem InputsLt.headD {n : ℕ} {l : List Fml} (h : ∀ f ∈ l, f.InputsLt n) :
    (l.headD (const false)).InputsLt n := by
  cases l with
  | nil => trivial
  | cons a l => exact h a (List.mem_cons_self ..)
end
end MIPRE.TM.CookLevin.Desc

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.Desc.InputsLt
open Interp SAT Cost Fml
variable (ℓ r T : ℕ)
theorem _root_.solution (h : ℓ ≤ r) : (linkFml ℓ r T).InputsLt (2 * ℓ + 3 * r + 5) := by
  have hj₁ : ∀ f ∈ j₁F ℓ r, f.InputsLt (2 * ℓ + 3 * r + 5) :=
    InputsLt.padTo (InputsLt.field (by omega))
  have hj₂ : ∀ f ∈ j₂F ℓ r, f.InputsLt (2 * ℓ + 3 * r + 5) :=
    InputsLt.padTo (InputsLt.field (by omega))
  have hj₃ : ∀ f ∈ j₃F ℓ r, f.InputsLt (2 * ℓ + 3 * r + 5) := InputsLt.field (by omega)
  have hj₄ : ∀ f ∈ j₄F ℓ r, f.InputsLt (2 * ℓ + 3 * r + 5) := InputsLt.field (by omega)
  have hj₅ : ∀ f ∈ j₅F ℓ r, f.InputsLt (2 * ℓ + 3 * r + 5) := InputsLt.field (by omega)
  have hs₁ : (s₁F ℓ r).InputsLt (2 * ℓ + 3 * r + 5) := by
    show sgOff ℓ r < 2 * ℓ + 3 * r + 5; unfold sgOff; omega
  have hs₂ : (s₂F ℓ r).InputsLt (2 * ℓ + 3 * r + 5) := by
    show sgOff ℓ r + 1 < 2 * ℓ + 3 * r + 5; unfold sgOff; omega
  have hs₃ : (s₃F ℓ r).InputsLt (2 * ℓ + 3 * r + 5) := by
    show sgOff ℓ r + 2 < 2 * ℓ + 3 * r + 5; unfold sgOff; omega
  have hs₄ : (s₄F ℓ r).InputsLt (2 * ℓ + 3 * r + 5) := by
    show sgOff ℓ r + 3 < 2 * ℓ + 3 * r + 5; unfold sgOff; omega
  have hs₅ : (s₅F ℓ r).InputsLt (2 * ℓ + 3 * r + 5) := by
    show sgOff ℓ r + 4 < 2 * ℓ + 3 * r + 5; unfold sgOff; omega
  have hh₁ := InputsLt.headD (n := 2 * ℓ + 3 * r + 5) hj₁
  have hh₂ := InputsLt.headD (n := 2 * ℓ + 3 * r + 5) hj₂
  refine InputsLt.orList _ ?_
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.ltConst _ hj₁)
      (InputsLt.list_cons (InputsLt.eqFields hj₁ hj₃)
      (InputsLt.list_cons (InputsLt.xor hs₁ hs₃) InputsLt.list_nil)))
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.ltConst _ hj₂)
      (InputsLt.list_cons (InputsLt.addConstRel _ hj₂ hj₃)
      (InputsLt.list_cons (InputsLt.xor hs₂ hs₃) InputsLt.list_nil)))
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.not' (InputsLt.ltConst _ hj₁))
      (InputsLt.list_cons (InputsLt.not' hh₁) (InputsLt.list_cons hs₁ InputsLt.list_nil)))
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.not' (InputsLt.ltConst _ hj₁))
      (InputsLt.list_cons hh₁ (InputsLt.list_cons (InputsLt.not' hs₁) InputsLt.list_nil)))
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.not' (InputsLt.ltConst _ hj₂))
      (InputsLt.list_cons (InputsLt.not' hh₂) (InputsLt.list_cons hs₂ InputsLt.list_nil)))
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.not' (InputsLt.ltConst _ hj₂))
      (InputsLt.list_cons hh₂ (InputsLt.list_cons (InputsLt.not' hs₂) InputsLt.list_nil)))
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.eqFields hj₃ hj₄)
      (InputsLt.list_cons (InputsLt.xor hs₃ hs₄) InputsLt.list_nil))
  · exact InputsLt.andList _ (InputsLt.list_cons (InputsLt.eqFields hj₄ hj₅)
      (InputsLt.list_cons (InputsLt.xor hs₄ hs₅) InputsLt.list_nil))
end MIPRE.TM.CookLevin.Desc.InputsLt
