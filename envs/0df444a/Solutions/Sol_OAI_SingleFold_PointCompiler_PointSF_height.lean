-- Prove2me | solution 1 for OAI.SingleFold.PointCompiler.PointSF.height
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:07:59.861987+00:00
-- url     : https://prove2.me/submissions/0519d5dd-ad4c-4d61-b4d1-5dee556ee2f9

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/FunctionalCompiler.lean:L146-L160
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.PointCompiler.PointSF.height. The node keeps its source
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
theorem or (hR : SF R) (hS : SF S) (hd : ∀ x, ¬(R x ∧ S x)) : SF (fun x => R x ∨ S x) := by
  obtain ⟨r⟩ := hR; obtain ⟨s⟩ := hS
  exact ⟨r.or s hd⟩
theorem reindex (hR : SF R) (f : α → β) : SF (fun x => R (x ∘ f)) := by
  obtain ⟨r⟩ := hR; exact ⟨r.reindex f⟩
theorem all [Finite β] {R : β → (α → ℕ) → Prop} (hr : ∀ i, SF (R i)) : SF (fun x => ∀ i, R i x) :=
  ⟨Representation.all R (fun i => Classical.choice (hr i))⟩
theorem eq (p q : Poly α) : SF (fun x => p x=q x) := ⟨Representation.eq p q⟩
theorem le (p q : Poly α) : SF (fun x => p x≤q x) := ⟨Representation.le p q⟩
theorem lt (p q : Poly α) : SF (fun x => p x<q x) := ⟨Representation.lt p q⟩
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
theorem congr (h : Semi R) (he : ∀ x, R x ↔ S x) : Semi S :=
  ⟨h.1.congr he,h.2.congr (fun x => not_congr (he x))⟩
theorem not (h : Semi R) : Semi (fun x => ¬R x) :=
  ⟨h.2,h.1.congr (fun _ => (not_not).symm)⟩
theorem and (hR : Semi R) (hS : Semi S) : Semi (fun x => R x ∧ S x) := by
  refine ⟨hR.1.and hS.1,?_⟩
  refine (hR.2.or (hR.1.and hS.2) (by intro x h; exact h.1 h.2.1)).congr ?_
  intro x; tauto
theorem or (hR : Semi R) (hS : Semi S) : Semi (fun x => R x ∨ S x) :=
  ((hR.not.and hS.not).not).congr (by intro x; tauto)
theorem eq (p q : Poly α) : Semi (fun x => p x=q x) := by
  refine ⟨SF.eq p q,((SF.lt p q).or (SF.lt q p) (by intro x h; exact lt_asymm h.1 h.2)).congr ?_⟩
  intro x; constructor
  · intro h; rcases h with h|h; exact h.ne; exact h.ne'
  · exact lt_or_gt_of_ne
theorem le (p q : Poly α) : Semi (fun x => p x≤q x) :=
  ⟨SF.le p q,(SF.lt q p).congr (fun _ => not_le.symm)⟩
theorem lt (p q : Poly α) : Semi (fun x => p x<q x) :=
  ⟨SF.lt p q,(SF.le q p).congr (fun _ => not_lt.symm)⟩
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

lemma mulRel_unique {n a b c} (hb : MulRel n a b) (hc : MulRel n a c) : b=c := by
  obtain ⟨P,rfl,rfl⟩ := hb
  obtain ⟨Q,hq,rfl⟩ := hc
  exact congrArg (fun P => encode (n • P)) (encode_injective hq)
variable {α : Type}
end SingleFold.PointCompiler

namespace SingleFold.Compiler.Semi
variable {α : Type}
theorem max_eq (p q r : Poly α) : Semi (fun z => max (p z) (q z)=r z) := by
  refine (((Semi.le p q).and (Semi.eq q r)).or ((Semi.lt q p).and (Semi.eq p r))).congr ?_
  intro z
  by_cases h : p z≤q z
  · simp only [h,max_eq_right h,true_and,not_lt_of_ge h,false_and,or_false]
  · have h' := lt_of_not_ge h
    simp only [h,max_eq_left h'.le,false_and,h',true_and,false_or]
end SingleFold.Compiler.Semi

namespace SingleFold.PointCompiler
open Compiler RationalCompiler
open WeierstrassCurve.Affine.Point

lemma height_semi {α : Type} (f : Var → α) (v : α) :
    Semi (fun z => (fromTuple (z ∘ f)).height=z v) := by
  let p : Poly α := Poly.proj (f (.inr (0,0)))+Poly.proj (f (.inr (0,1)))
  let q : Poly α := Poly.proj (f (.inr (0,2)))
  refine (Semi.max_eq p q (Poly.proj v)).congr ?_
  intro z
  change max ((z (f (.inr (0,0))):ℤ)+z (f (.inr (0,1)))) (z (f (.inr (0,2))):ℤ)=(z v:ℤ) ↔ _
  dsimp only [Code.height,fromTuple,RationalCompiler.code,Function.comp_apply]
  exact_mod_cast Iff.rfl

lemma wRel_semantics (m : ℕ) (a : Code) (v : ℕ) :
    WRel m a v ↔ ∃ P, a=encode P ∧ (encode (m • P)).height=v := by
  constructor
  · rintro ⟨b,⟨P,ha,rfl⟩,hv⟩; exact ⟨P,ha,hv⟩
  · rintro ⟨P,rfl,hv⟩; exact ⟨encode (m • P),⟨P,rfl,rfl⟩,hv⟩
lemma wRel_sf {α : Type} (m : ℕ) (f : Var → α) (v : α) :
    SF (fun z => WRel m (fromTuple (z ∘ f)) (z v)) := by
  let f' : Var → α⊕Var := Sum.inl ∘ f
  have h := (mulRel_sf m f' Sum.inr).and (height_semi Sum.inr (Sum.inl v)).1
  refine (h.ex (fun z x y hx hy => fromTuple_injective (mulRel_unique hx.1 hy.1))).congr ?_
  intro z
  change (∃ b : Var → ℕ, MulRel m (fromTuple (z ∘ f)) (fromTuple b) ∧ (fromTuple b).height=z v) ↔ _
  constructor
  · rintro ⟨b,hb⟩; exact ⟨fromTuple b,hb⟩
  · rintro ⟨b,hb⟩; exact ⟨tuple b,by simpa only [from_tuple] using hb⟩

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
lemma height (m : ℕ) (hf : PointSF f) :
    MapSF (fun z (_ : Unit) => (encode (m • f z)).height) := by
  have hframe := MapSF.pair (MapSF.reindex hf (Sum.inl : α → α⊕Unit))
    (MapSF.proj (Sum.inr : Unit → α⊕Unit))
  refine (hframe.pullback (wRel_sf m Sum.inl (Sum.inr ()))).congr ?_
  intro z
  change WRel m (fromTuple (tuple (encode (f (z ∘ Sum.inl))))) (z (Sum.inr ())) ↔ _
  rw [from_tuple,wRel_semantics]
  constructor
  · rintro ⟨P,hP,hv⟩
    have hp := encode_injective hP
    subst P
    funext j; cases j; exact hv.symm
  · intro he
    exact ⟨f (z ∘ Sum.inl),rfl,(congrFun he ()).symm⟩
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


theorem solution : type_of% @_root_.OAI.SingleFold.PointCompiler.PointSF.height := @_root_.OAI.SingleFold.PointCompiler.PointSF.height
