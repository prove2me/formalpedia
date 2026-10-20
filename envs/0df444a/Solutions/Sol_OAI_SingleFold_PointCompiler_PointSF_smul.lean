-- Prove2me | solution 1 for OAI.SingleFold.PointCompiler.PointSF.smul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:06:28.667988+00:00
-- url     : https://prove2.me/submissions/33197b33-36ca-4883-8d77-20faeb724248

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/FunctionalCompiler.lean:L130-L145
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.PointCompiler.PointSF.smul. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Theorems.Thm_OAI_SingleFold_PointCompiler_mulRel_sf

-- ---- from OAI.NumberTheory.SingleFold.RationalCodes ----
namespace OAI

namespace SingleFold

namespace RationalCode

end RationalCode
end SingleFold

namespace SingleFold.Compiler.SF
variable {α β : Type} {R S : (α → ℕ) → Prop}

theorem congr (h : SF R) (he : ∀ x, R x ↔ S x) : SF S := by
  obtain ⟨r⟩ := h
  exact ⟨r.congr he⟩
theorem and (hR : SF R) (hS : SF S) : SF (fun x => R x ∧ S x) := by
  obtain ⟨r⟩ := hR; obtain ⟨s⟩ := hS
  exact ⟨r.and s⟩
theorem reindex (hR : SF R) (f : α → β) : SF (fun x => R (x ∘ f)) := by
  obtain ⟨r⟩ := hR; exact ⟨r.reindex f⟩
theorem all [Finite β] {R : β → (α → ℕ) → Prop} (hr : ∀ i, SF (R i)) : SF (fun x => ∀ i, R i x) :=
  ⟨Representation.all R (fun i => Classical.choice (hr i))⟩
theorem eq (p q : Poly α) : SF (fun x => p x=q x) := ⟨Representation.eq p q⟩
theorem ex {R : (α ⊕ β → ℕ) → Prop} [Finite β] (hr : SF R)
    (hu : ∀ x y y', R (Sum.elim x y) → R (Sum.elim x y') → y=y') :
    SF (fun x => ∃ y, R (Sum.elim x y)) := by
  obtain ⟨r⟩ := hr; exact ⟨r.ex hu⟩
end SingleFold.Compiler.SF

namespace SingleFold.RationalCompiler
open Compiler

namespace FractionPoly
variable {α : Type}
end FractionPoly

namespace Expr
variable {α : Type}
end Expr
end SingleFold.RationalCompiler

namespace SingleFold.Compiler

namespace Semi
variable {α β : Type} {R S : (α → ℕ) → Prop}
end Semi
end SingleFold.Compiler

namespace SingleFold.RationalCompiler
open Compiler

namespace Expr
variable {α β : Type}
end Expr
end SingleFold.RationalCompiler

namespace SingleFold.RationalCode
end SingleFold.RationalCode

end OAI

-- ---- from OAI.NumberTheory.SingleFold.EllipticCoordinates ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.PointCompiler

section
open Compiler RationalCompiler
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

lemma encode_toPoint (P : E.Point) : (encode P).toPoint (encode_valid P)=P := by
  cases P with
  | zero => simp [Code.toPoint,encode,←zero_def]
  | some x y h => simp [Code.toPoint,encode,RationalCode.encode_value]
lemma from_tuple (c : Code) : fromTuple (tuple c)=c := by
  simp only [fromTuple,tuple,Sum.elim_inl,Sum.elim_inr,ite_true,show (1:Fin 2)≠0 by decide,ite_false]
  change Code.mk c.flag (code (RationalCompiler.tuple c.x)) (code (RationalCompiler.tuple c.y))=c
  rw [code_tuple,code_tuple]
lemma tuple_from (z : Var → ℕ) : tuple (fromTuple z)=z := by
  funext i
  rcases i with i|⟨i,j⟩
  · rfl
  · fin_cases i <;> fin_cases j <;> rfl

lemma encode_injective : Function.Injective encode := by
  intro p q he
  have he' : (⟨encode p,encode_valid p⟩ : {c : Code // c.Valid})=⟨encode q,encode_valid q⟩ := Subtype.ext he
  have hh := congrArg (fun c : {c : Code // c.Valid} => c.1.toPoint c.2) he'
  simpa only [encode_toPoint] using hh

variable {ι : Type} [Finite ι]
end

open Compiler RationalCompiler
open WeierstrassCurve.Affine.Point

lemma fromTuple_injective : Function.Injective fromTuple := by
  intro x y h
  have hh := congrArg tuple h
  simpa only [tuple_from] using hh

variable {α : Type}
end SingleFold.PointCompiler

namespace SingleFold.Compiler.Semi
variable {α : Type}
end SingleFold.Compiler.Semi

namespace SingleFold.PointCompiler
open Compiler RationalCompiler
open WeierstrassCurve.Affine.Point

end SingleFold.PointCompiler

end OAI

-- ---- from OAI.NumberTheory.SingleFold.FunctionalCompiler ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.Compiler

namespace MapSF
variable {α β γ δ : Type}
lemma proj (i : β → α) [Finite β] : MapSF (fun z => z ∘ i) := by
  have h := SF.all (fun j : β => SF.eq (Poly.proj (Sum.inr j : α⊕β)) (Poly.proj (Sum.inl (i j))))
  refine h.congr ?_
  intro z
  change (∀ j, (z (Sum.inr j):ℤ)=z (Sum.inl (i j))) ↔ _
  simp only [Int.natCast_inj]
  exact ⟨fun h => funext h,fun h j => congrFun h j⟩
lemma reindex {f : (α → ℕ) → (β → ℕ)} (hf : MapSF f) (i : α → γ) :
    MapSF (fun z => f (z ∘ i)) := by
  exact (SF.reindex hf (Sum.map i id)).congr (by intro z; rfl)
lemma pair {f : (α → ℕ) → (β → ℕ)} {g : (α → ℕ) → (γ → ℕ)}
    (hf : MapSF f) (hg : MapSF g) : MapSF (fun z => Sum.elim (f z) (g z)) := by
  have h := (SF.reindex hf (Sum.map id Sum.inl)).and (SF.reindex hg (Sum.map id Sum.inr))
  refine h.congr ?_
  intro z
  change (z ∘ Sum.inr ∘ Sum.inl=f (z ∘ Sum.inl) ∧ z ∘ Sum.inr ∘ Sum.inr=g (z ∘ Sum.inl)) ↔ _
  constructor
  · rintro ⟨h₁,h₂⟩; funext j; cases j with
    | inl j => exact congrFun h₁ j
    | inr j => exact congrFun h₂ j
  · intro h
    exact ⟨congrArg (fun z => z ∘ Sum.inl) h,congrArg (fun z => z ∘ Sum.inr) h⟩
lemma pullback {f : (α → ℕ) → (β → ℕ)} [Finite β] (hf : MapSF f)
    {R : (β → ℕ) → Prop} (hR : SF R) : SF (fun z => R (f z)) := by
  have h := hf.and (hR.reindex Sum.inr)
  refine (h.ex (fun z x y hx hy => hx.1.trans hy.1.symm)).congr ?_
  intro z
  change (∃ x, x=f z ∧ R x) ↔ _
  simp only [exists_eq_left]
end MapSF
end SingleFold.Compiler

namespace SingleFold.PointCompiler
open Compiler RationalCompiler
namespace PointSF
variable {α β : Type} {f g : (α → ℕ) → E.Point}
lemma smul (n : ℕ) (hf : PointSF f) : PointSF (fun z => n • f z) := by
  have hframe := MapSF.pair (MapSF.reindex hf (Sum.inl : α → α⊕Var))
    (MapSF.proj (Sum.inr : Var → α⊕Var))
  refine (hframe.pullback (mulRel_sf n Sum.inl Sum.inr)).congr ?_
  intro z
  change MulRel n (fromTuple (tuple (encode (f (z ∘ Sum.inl))))) (fromTuple (z ∘ Sum.inr)) ↔ _
  rw [from_tuple]
  constructor
  · rintro ⟨P,hP,hout⟩
    have hp := encode_injective hP
    subst P
    exact fromTuple_injective (hout.trans (from_tuple _).symm)
  · intro he
    refine ⟨f (z ∘ Sum.inl),rfl,?_⟩
    have hh := congrArg fromTuple he
    simpa only [from_tuple] using hh
end PointSF
end SingleFold.PointCompiler

namespace SingleFold.Compiler
namespace ScalarSF
variable {α : Type} {f g : (α → ℕ) → ℕ}
end ScalarSF
end SingleFold.Compiler

namespace SingleFold.PointCompiler
open Compiler RationalCompiler
namespace PointSF
variable {α : Type} {f g : (α → ℕ) → E.Point}
end PointSF
end SingleFold.PointCompiler

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.PointCompiler OAI.SingleFold.PointCompiler.PointSF
open Compiler RationalCompiler


theorem solution : type_of% @_root_.OAI.SingleFold.PointCompiler.PointSF.smul := @_root_.OAI.SingleFold.PointCompiler.PointSF.smul
