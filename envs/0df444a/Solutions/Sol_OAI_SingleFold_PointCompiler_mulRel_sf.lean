-- Prove2me | solution 1 for OAI.SingleFold.PointCompiler.mulRel_sf
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:03:21.878995+00:00
-- url     : https://prove2.me/submissions/0f613cac-47f9-45e1-80cc-f279811324f3

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/EllipticCoordinates.lean:L371-L401
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.PointCompiler.mulRel_sf. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Theorems.Thm_OAI_SingleFold_PointCompiler_addEq_encode
import Theorems.Thm_OAI_SingleFold_PointCompiler_add_general_sf
import Theorems.Thm_OAI_SingleFold_PointCompiler_code_valid_semi

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

lemma encode_injective : Function.Injective encode := by
  intro p q he
  have he' : (⟨encode p,encode_valid p⟩ : {c : Code // c.Valid})=⟨encode q,encode_valid q⟩ := Subtype.ext he
  have hh := congrArg (fun c : {c : Code // c.Valid} => c.1.toPoint c.2) he'
  simpa only [encode_toPoint] using hh

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

lemma mulRel_unique {n a b c} (hb : MulRel n a b) (hc : MulRel n a c) : b=c := by
  obtain ⟨P,rfl,rfl⟩ := hb
  obtain ⟨Q,hq,rfl⟩ := hc
  exact congrArg (fun P => encode (n • P)) (encode_injective hq)
lemma mulRel_zero (a b : Code) : MulRel 0 a b ↔ a.Valid ∧ b=encode 0 := by
  constructor
  · rintro ⟨P,rfl,hb⟩; exact ⟨encode_valid _,by simpa using hb⟩
  · rintro ⟨ha,rfl⟩; exact ⟨a.toPoint ha,(a.encode_toPoint ha).symm,by simp⟩
lemma mulRel_succ (n : ℕ) (a b : Code) : MulRel (n+1) a b ↔
    ∃ c, MulRel n a c ∧ c.Valid ∧ a.Valid ∧ b.Valid ∧ AddEq c a b := by
  constructor
  · rintro ⟨P,rfl,rfl⟩
    refine ⟨encode (n • P),⟨P,rfl,rfl⟩,encode_valid _,encode_valid _,encode_valid _,?_⟩
    apply (addEq_encode _ _ _).mpr
    exact (add_nsmul P n 1).symm.trans (by simp)
  · rintro ⟨c,⟨P,rfl,rfl⟩,_,_,hb,he⟩
    refine ⟨P,rfl,?_⟩
    have hh := (addEq_spec _ _ _ (encode_valid _) (encode_valid _) hb).mp he
    rw [encode_toPoint,encode_toPoint] at hh
    have hh' : b.toPoint hb=(n+1) • P := by rw [←hh,add_nsmul,one_nsmul]
    exact (b.encode_toPoint hb).symm.trans (congrArg encode hh')

variable {α : Type}
lemma valid_sf (f : Var → α) : SF (fun z => (fromTuple (z ∘ f)).Valid) := code_valid_semi.1.reindex f
lemma const_sf (f : Var → α) (c : Code) : SF (fun z => fromTuple (z ∘ f)=c) := by
  have h : SF (fun z : α → ℕ => ∀ v, z (f v)=tuple c v) :=
    SF.all (fun v => (SF.eq (Poly.proj (f v)) (Poly.const (tuple c v))).congr (by intro z; change (z (f v):ℤ)=(tuple c v:ℤ) ↔ _; exact_mod_cast Iff.rfl))
  refine h.congr ?_
  intro z
  constructor
  · intro hh; have he : z ∘ f=tuple c := funext hh; rw [he,from_tuple]
  · intro hh v; simpa only [tuple_from,Function.comp_apply] using congrFun (congrArg tuple hh) v

lemma mulRel_sf (n : ℕ) : ∀ {α : Type} (f g : Var → α),
    SF (fun z => MulRel n (fromTuple (z ∘ f)) (fromTuple (z ∘ g))) := by
  induction n with
  | zero =>
    intro α f g
    exact ((valid_sf f).and (const_sf g (encode 0))).congr (fun _ => (mulRel_zero _ _).symm)
  | succ n ih =>
    intro α f g
    let f' : Var → α⊕Var := Sum.inl ∘ f
    let g' : Var → α⊕Var := Sum.inl ∘ g
    have h := (ih f' Sum.inr).and (add_general_sf Sum.inr f' g')
    have hu : ∀ x y y',
        (MulRel n (fromTuple (Sum.elim x y ∘ f')) (fromTuple (Sum.elim x y ∘ Sum.inr)) ∧
          (fromTuple (Sum.elim x y ∘ Sum.inr)).Valid ∧ (fromTuple (Sum.elim x y ∘ f')).Valid ∧
          (fromTuple (Sum.elim x y ∘ g')).Valid ∧ AddEq (fromTuple (Sum.elim x y ∘ Sum.inr))
            (fromTuple (Sum.elim x y ∘ f')) (fromTuple (Sum.elim x y ∘ g'))) →
        (MulRel n (fromTuple (Sum.elim x y' ∘ f')) (fromTuple (Sum.elim x y' ∘ Sum.inr)) ∧
          (fromTuple (Sum.elim x y' ∘ Sum.inr)).Valid ∧ (fromTuple (Sum.elim x y' ∘ f')).Valid ∧
          (fromTuple (Sum.elim x y' ∘ g')).Valid ∧ AddEq (fromTuple (Sum.elim x y' ∘ Sum.inr))
            (fromTuple (Sum.elim x y' ∘ f')) (fromTuple (Sum.elim x y' ∘ g'))) → y=y' := by
      intro x y y' hy hy'
      exact fromTuple_injective (mulRel_unique hy.1 hy'.1)
    refine (h.ex hu).congr ?_
    intro z
    change (∃ y : Var → ℕ, MulRel n (fromTuple (z ∘ f)) (fromTuple y) ∧
      (fromTuple y).Valid ∧ (fromTuple (z ∘ f)).Valid ∧ (fromTuple (z ∘ g)).Valid ∧
      AddEq (fromTuple y) (fromTuple (z ∘ f)) (fromTuple (z ∘ g))) ↔ _
    rw [mulRel_succ]
    constructor
    · rintro ⟨y,hy⟩; exact ⟨fromTuple y,hy⟩
    · rintro ⟨c,hc⟩; exact ⟨tuple c,by simpa only [from_tuple] using hc⟩
end SingleFold.PointCompiler

namespace SingleFold.Compiler.Semi
variable {α : Type}
end SingleFold.Compiler.Semi

namespace SingleFold.PointCompiler
open Compiler RationalCompiler
open WeierstrassCurve.Affine.Point

end SingleFold.PointCompiler

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.PointCompiler
open Compiler RationalCompiler
open WeierstrassCurve.Affine.Point


theorem solution : type_of% @_root_.OAI.SingleFold.PointCompiler.mulRel_sf := @_root_.OAI.SingleFold.PointCompiler.mulRel_sf
