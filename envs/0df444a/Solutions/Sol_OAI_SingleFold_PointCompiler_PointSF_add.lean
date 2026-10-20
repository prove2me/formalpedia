-- Prove2me | solution 1 for OAI.SingleFold.PointCompiler.PointSF.add
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:04:46.587833+00:00
-- url     : https://prove2.me/submissions/49c39bde-a482-476c-9b31-6ea90743f0b5

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/FunctionalCompiler.lean:L106-L129
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.PointCompiler.PointSF.add. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Theorems.Thm_OAI_SingleFold_PointCompiler_addEq_encode
import Theorems.Thm_OAI_SingleFold_PointCompiler_add_general_sf

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
lemma eq_encode {z : RationalCode} (hz : z.Valid) : z=encode z.value :=
  unique hz (encode_valid _) (encode_value _).symm
end SingleFold.RationalCode

end OAI

-- ---- from OAI.NumberTheory.SingleFold.EllipticCoordinates ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

namespace SingleFold.PointCompiler

section
open Compiler RationalCompiler
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

lemma Code.encode_toPoint (c : Code) (hc : c.Valid) : encode (c.toPoint hc)=c := by
  by_cases hf : c.flag=1
  · have hxy := (hc.2.2.resolve_right (by rintro ⟨h,_⟩; omega)).2
    have hx : RationalCode.encode 0=c.x := RationalCode.unique (RationalCode.encode_valid _) hc.1 ((RationalCode.encode_value _).trans hxy.1.symm)
    have hy : RationalCode.encode 0=c.y := RationalCode.unique (RationalCode.encode_valid _) hc.2.1 ((RationalCode.encode_value _).trans hxy.2.symm)
    simp only [Code.toPoint,dite_eq_left hf,encode,hx]
    cases c; simp_all
  · have hf0 := (hc.2.2.resolve_left (by tauto)).1
    simp only [Code.toPoint,dite_eq_right hf,encode,←RationalCode.eq_encode hc.1,←RationalCode.eq_encode hc.2.1]
    cases c; simp_all
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

lemma addEq_spec (a b c : Code) (ha : a.Valid) (hb : b.Valid) (hc : c.Valid) :
    AddEq a b c ↔ a.toPoint ha+b.toPoint hb=c.toPoint hc := by
  simpa only [Code.encode_toPoint] using addEq_encode (a.toPoint ha) (b.toPoint hb) (c.toPoint hc)
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
lemma add (hf : PointSF f) (hg : PointSF g) : PointSF (fun z => f z+g z) := by
  have hf' := MapSF.reindex hf (Sum.inl : α → α⊕Var)
  have hg' := MapSF.reindex hg (Sum.inl : α → α⊕Var)
  have hframe := MapSF.pair (MapSF.pair hf' hg') (MapSF.proj (Sum.inr : Var → α⊕Var))
  have h := hframe.pullback (add_general_sf (Sum.inl ∘ Sum.inl) (Sum.inl ∘ Sum.inr) Sum.inr)
  refine h.congr ?_
  intro z
  simp only [Function.comp_def,Sum.elim_inl,Sum.elim_inr,from_tuple] at h ⊢
  change ((encode (f (z ∘ Sum.inl))).Valid ∧ (encode (g (z ∘ Sum.inl))).Valid ∧
    (fromTuple (z ∘ Sum.inr)).Valid ∧ AddEq (encode (f (z ∘ Sum.inl))) (encode (g (z ∘ Sum.inl)))
      (fromTuple (z ∘ Sum.inr))) ↔ _
  constructor
  · rintro ⟨_,_,hv,he⟩
    have hh := (addEq_spec _ _ _ (encode_valid _) (encode_valid _) hv).mp he
    rw [encode_toPoint,encode_toPoint] at hh
    have hc : fromTuple (z ∘ Sum.inr)=encode (f (z ∘ Sum.inl)+g (z ∘ Sum.inl)) := by
      rw [hh,Code.encode_toPoint]
    exact fromTuple_injective (hc.trans (from_tuple _).symm)
  · intro he
    have hc := congrArg fromTuple he
    rw [from_tuple] at hc
    change fromTuple (z ∘ Sum.inr)=encode (f (z ∘ Sum.inl)+g (z ∘ Sum.inl)) at hc
    rw [hc]
    exact ⟨encode_valid _,encode_valid _,encode_valid _,(addEq_encode _ _ _).mpr rfl⟩
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


theorem solution : type_of% @_root_.OAI.SingleFold.PointCompiler.PointSF.add := @_root_.OAI.SingleFold.PointCompiler.PointSF.add
