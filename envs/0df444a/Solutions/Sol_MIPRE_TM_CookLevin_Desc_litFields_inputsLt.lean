-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Desc.litFields_inputsLt
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:46:38.015381+00:00
-- url     : https://prove2.me/submissions/6b8600e9-068b-4d86-8651-8d1719792158

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/FamilyFml.lean (solution of MIPRE.TM.CookLevin.Desc.litFields_inputsLt);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Language
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Relation
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
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
theorem InputsLt.mux {n : ℕ} {s a b : Fml} (hs : s.InputsLt n) (ha : a.InputsLt n) (hb : b.InputsLt n) :
    (Fml.mux s a b).InputsLt n := ⟨⟨hs, ha⟩, hs, hb⟩
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
theorem InputsLt.constBits {n : ℕ} (c : BitStr) : ∀ f ∈ Fml.constBits c, f.InputsLt n := by
  intro f hf
  simp only [Fml.constBits, List.mem_map] at hf
  obtain ⟨b, -, rfl⟩ := hf
  trivial
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
theorem InputsLt.subConstBits {n : ℕ} {fs : List Fml} (c : BitStr) (h : ∀ f ∈ fs, f.InputsLt n) :
    ∀ f ∈ Fml.subConstBits fs c, f.InputsLt n := InputsLt.addConstBits _ h
end
end MIPRE.SAT.Fml

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem InputsLt.and' {n : ℕ} {f g : Fml} (hf : f.InputsLt n) (hg : g.InputsLt n) :
    (Fml.and f g).InputsLt n := ⟨hf, hg⟩
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem InputsLt.not' {n : ℕ} {f : Fml} (hf : f.InputsLt n) : (Fml.not f).InputsLt n := hf
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem InputsLt.muxList {n : ℕ} {s : Fml} {as bs : List Fml} (hs : s.InputsLt n)
    (ha : ∀ f ∈ as, f.InputsLt n) (hb : ∀ f ∈ bs, f.InputsLt n) :
    ∀ f ∈ muxList s as bs, f.InputsLt n := by
  intro f hf
  rw [Desc.muxList, List.mem_iff_getElem] at hf
  obtain ⟨i, hi, rfl⟩ := hf
  rw [List.getElem_zipWith]
  exact InputsLt.mux hs (ha _ (List.getElem_mem _)) (hb _ (List.getElem_mem _))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem InputsLt.cst {n w c : ℕ} : ∀ f ∈ cst w c, f.InputsLt n := InputsLt.constBits _
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem InputsLt.take {n : ℕ} {l : List Fml} (h : ∀ f ∈ l, f.InputsLt n) (k : ℕ) :
    ∀ f ∈ l.take k, f.InputsLt n := fun f hf => h f (List.mem_of_mem_take hf)
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem InputsLt.tail {n : ℕ} {l : List Fml} (h : ∀ f ∈ l, f.InputsLt n) :
    ∀ f ∈ l.tail, f.InputsLt n := fun f hf => h f (List.mem_of_mem_tail hf)
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

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G T b n : ℕ) (hn : b + mOf e G ≤ n)
include hn
theorem InputsLt.flagF : (flagF e G b).InputsLt n := by
  show b + flagOff e G < n
  unfold flagOff mOf at *
  omega
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G T b n : ℕ) (hn : b + mOf e G ≤ n)
include hn
theorem InputsLt.jF : ∀ f ∈ jF e G b, f.InputsLt n :=
  InputsLt.field (by unfold flagOff mOf at *; omega)
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G T b n : ℕ) (hn : b + mOf e G ≤ n)
include hn
theorem InputsLt.rF : ∀ f ∈ rF e G T b, f.InputsLt n :=
  InputsLt.muxList (InputsLt.ltConst _ (InputsLt.jF e G b n hn)) (InputsLt.jF e G b n hn)
    (InputsLt.subConstBits _ (InputsLt.jF e G b n hn))
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G T b n : ℕ) (hn : b + mOf e G ≤ n)
include hn
theorem InputsLt.pAnsF : ∀ f ∈ pAnsF e G T b, f.InputsLt n :=
  InputsLt.addConstBits _ (InputsLt.take (InputsLt.tail (InputsLt.rF e G T b n hn)) _)
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G T b n : ℕ) (hn : b + mOf e G ≤ n)
include hn
theorem InputsLt.fieldOff (off w : ℕ) (h : off + w ≤ mOf e G) : ∀ f ∈ field (b + off) w, f.InputsLt n :=
  InputsLt.field (by omega)
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G T b n : ℕ) (hn : b + mOf e G ≤ n)
include hn
omit hn in
theorem jsOff_add_le (k : Fin 13) : jsOff e k + W e ≤ mOf e G := by
  unfold jsOff mOf
  have : (k : ℕ) * W e + W e ≤ 13 * W e := by
    rw [← Nat.succ_mul]
    exact Nat.mul_le_mul_right _ (by have := k.isLt; omega)
  generalize Qb = q at *
  omega
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G T b n : ℕ) (hn : b + mOf e G ≤ n)
include hn
omit hn in
theorem qOff_add_le : qOff e + Qb ≤ mOf e G := by
  unfold qOff mOf
  generalize Qb = q
  omega
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
variable (e G T b n : ℕ) (hn : b + mOf e G ≤ n)
include hn
omit hn in
theorem gOff_add_le : gOff e + Gb G ≤ mOf e G := by
  unfold gOff mOf
  generalize Qb = q
  generalize Gb G = g
  omega
end
end MIPRE.TM.CookLevin.Desc

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.Desc
open Interp SAT Cost Fml
variable (e G T b n : ℕ) (hn : b + mOf e G ≤ n)
include hn
theorem _root_.solution : (litFields e G T b).InputsLt n := by
  have hf := InputsLt.flagF e G b n hn
  have hj := InputsLt.jF e G b n hn
  refine ⟨hf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact InputsLt.muxList hf (InputsLt.fieldOff e G b n hn tagOff 3 (by unfold tagOff mOf; omega)) InputsLt.cst
  · exact InputsLt.muxList hf (InputsLt.fieldOff e G b n hn tOff (W e) (by unfold tOff mOf; omega)) InputsLt.cst
  · exact InputsLt.muxList hf (InputsLt.fieldOff e G b n hn (dOff e) 4 (by unfold dOff mOf; omega))
      (InputsLt.muxList (InputsLt.ltConst _ hj) InputsLt.cst InputsLt.cst)
  · exact InputsLt.muxList hf (InputsLt.fieldOff e G b n hn (pOff e) (W e) (by unfold pOff mOf; omega))
      (InputsLt.pAnsF e G T b n hn)
  · exact InputsLt.muxList hf (InputsLt.fieldOff e G b n hn (vOff e) 3 (by unfold vOff mOf; omega))
      (InputsLt.muxList (InputsLt.headD (InputsLt.rF e G T b n hn)) InputsLt.cst InputsLt.cst)
  · exact InputsLt.muxList hf (InputsLt.fieldOff e G b n hn (qOff e) Qb (qOff_add_le e G)) InputsLt.cst
  · intro k
    exact InputsLt.muxList hf (InputsLt.fieldOff e G b n hn (jsOff e k) (W e) (jsOff_add_le e G k))
      InputsLt.cst
  · exact InputsLt.muxList hf (InputsLt.fieldOff e G b n hn (gOff e) (Gb G) (gOff_add_le e G))
      InputsLt.cst
  · exact InputsLt.and' (InputsLt.not' hf) (InputsLt.ltConst _ hj)
end MIPRE.TM.CookLevin.Desc
