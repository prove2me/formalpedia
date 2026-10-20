-- Prove2me | solution 1 for OAI.SingleFold.PointCompiler.code_valid_semi
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T17:56:15.921985+00:00
-- url     : https://prove2.me/submissions/a48ecb79-b6b8-441f-9e28-7e938c6fcf0d

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/EllipticCoordinates.lean:L73-L98
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.PointCompiler.code_valid_semi. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Theorems.Thm_OAI_SingleFold_RationalCompiler_valid_semi

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
theorem eq (p q : Poly α) : SF (fun x => p x=q x) := ⟨Representation.eq p q⟩
theorem lt (p q : Poly α) : SF (fun x => p x<q x) := ⟨Representation.lt p q⟩
end SingleFold.Compiler.SF

namespace SingleFold.RationalCompiler
open Compiler

namespace FractionPoly
variable {α : Type}
lemma const_value (r : ℚ) (z : α → ℕ) : (const r).value z=r := by
  simpa only [value,const,Poly.const_apply,Int.cast_natCast] using r.num_div_den
lemma add_value (p q : FractionPoly α) (z : α → ℕ) (hp : 0<p.den z) (hq : 0<q.den z) :
    (p.add q).value z=p.value z+q.value z := by
  have hp' : (p.den z:ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have hq' : (q.den z:ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  simp only [value,add,Poly.add_apply,Poly.mul_apply,Int.cast_add,Int.cast_mul]
  simpa only [mul_comm] using (div_add_div (p.num z : ℚ) (q.num z : ℚ) hp' hq').symm
lemma mul_value (p q : FractionPoly α) (z : α → ℕ) :
    (p.mul q).value z=p.value z*q.value z := by
  simp only [value,mul,Poly.mul_apply,Int.cast_mul,div_mul_div_comm]
lemma neg_value (p : FractionPoly α) (z : α → ℕ) : (p.neg).value z= -p.value z := by
  simp only [value,neg,Poly.neg_apply,Int.cast_neg,neg_div]

lemma eq_iff (p q : FractionPoly α) (z : α → ℕ) (hp : 0<p.den z) (hq : 0<q.den z) :
    p.value z=q.value z ↔ (p.num*q.den) z=(q.num*p.den) z := by
  have hp' : (p.den z:ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have hq' : (q.den z:ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [value,value,div_eq_div_iff hp' hq']
  simp only [Poly.mul_apply]
  exact_mod_cast (Iff.rfl : (p.num z:ℚ)*q.den z=q.num z*p.den z ↔ (p.num z:ℚ)*q.den z=q.num z*p.den z)

end FractionPoly

lemma input_value {α : Type} (i : α) (z : α × Fin 6 → ℕ) : (input i).value z=value z i := by
  simp only [FractionPoly.value,input,Poly.sub_apply,Poly.proj_apply,Int.cast_sub,
    Int.cast_natCast,value,RationalCode.value,code]
lemma input_pos {α : Type} (i : α) (z : α × Fin 6 → ℕ) (hz : Valid z) : 0<(input i).den z := by
  change (0:ℤ) < (z (i,2):ℤ)
  have h := RationalCode.den_pos (hz i)
  change 0 < z (i,2) at h
  exact_mod_cast h

namespace Expr
variable {α : Type}
lemma compile_spec (p : Expr α) (z : α × Fin 6 → ℕ) (hz : Valid z) :
    0<p.compile.den z ∧ p.compile.value z=p.eval (value z) := by
  induction p with
  | var i => exact ⟨input_pos i z hz,input_value i z⟩
  | const q => exact ⟨by change (0:ℤ)<(q.den:ℤ); exact_mod_cast q.den_pos,FractionPoly.const_value q z⟩
  | add p q hp hq =>
    exact ⟨mul_pos hp.1 hq.1,by simpa only [compile,eval,hp.2,hq.2] using FractionPoly.add_value p.compile q.compile z hp.1 hq.1⟩
  | mul p q hp hq =>
    exact ⟨mul_pos hp.1 hq.1,by simpa only [compile,eval,hp.2,hq.2] using FractionPoly.mul_value p.compile q.compile z⟩
  | neg p hp => exact ⟨hp.1,by simpa only [compile,eval,hp.2] using FractionPoly.neg_value p.compile z⟩

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
theorem reindex (hR : Semi R) (f : α → β) : Semi (fun x => R (x ∘ f)) :=
  ⟨hR.1.reindex f,hR.2.reindex f⟩
theorem eq (p q : Poly α) : Semi (fun x => p x=q x) := by
  refine ⟨SF.eq p q,((SF.lt p q).or (SF.lt q p) (by intro x h; exact lt_asymm h.1 h.2)).congr ?_⟩
  intro x; constructor
  · intro h; rcases h with h|h; exact h.ne; exact h.ne'
  · exact lt_or_gt_of_ne
end Semi
end SingleFold.Compiler

namespace SingleFold.RationalCompiler
open Compiler

namespace Expr
variable {α β : Type}
lemma eq_under {G : (β → ℕ) → Prop} (hG : Semi G) (f : α×Fin 6 → β)
    (hv : ∀ z, G z → Valid (z ∘ f)) (p q : Expr α) :
    Semi (fun z => G z ∧ p.eval (value (z ∘ f))=q.eval (value (z ∘ f))) := by
  refine (hG.and (Semi.eq ((p.compile.num*q.compile.den).map f) ((q.compile.num*p.compile.den).map f))).congr ?_
  intro z
  apply and_congr_right
  intro hz
  have hp := p.compile_spec (z ∘ f) (hv z hz)
  have hq := q.compile_spec (z ∘ f) (hv z hz)
  change (p.compile.num*q.compile.den) (z ∘ f)=(q.compile.num*p.compile.den) (z ∘ f) ↔ _
  rw [←FractionPoly.eq_iff _ _ _ hp.1 hq.1,hp.2,hq.2]
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

lemma code_valid_semi : Semi (fun z => (fromTuple z).Valid) := by
  let f : Fin 2 × Fin 6 → Var := Sum.inr
  let G : (Var → ℕ) → Prop := fun z => Valid (z ∘ f)
  have hg : Semi G := valid_semi.reindex f
  have eqc (p q : Expr (Fin 2)) := Expr.eq_under hg f (fun _ h => h) p q
  let x : Expr (Fin 2) := .var 0
  let y : Expr (Fin 2) := .var 1
  have ho := (Semi.eq (Poly.proj (.inl () : Var)) 1).and ((eqc x 0).and (eqc y 0))
  have ha := (Semi.eq (Poly.proj (.inl () : Var)) 0).and (eqc (y^2) (x^3-25*x))
  refine (ho.or ha).congr ?_
  intro z
  have hG : G z ↔ (fromTuple z).x.Valid ∧ (fromTuple z).y.Valid := by
    change (∀ i : Fin 2, (code (fun j => z (Sum.inr (i,j)))).Valid) ↔ _
    constructor
    · intro h; exact ⟨h 0,h 1⟩
    · intro h i; fin_cases i; exact h.1; exact h.2
  simp only [Expr.eval_pow,Expr.eval_sub,Expr.eval_mul,Expr.eval_zero,
    Expr.eval_var,Poly.proj_apply,Poly.one_apply,Poly.zero_apply,x,y] at *
  change (((z (.inl ()):ℤ)=1 ∧ (G z ∧ (fromTuple z).x.value=0) ∧ G z ∧ (fromTuple z).y.value=0) ∨
    (z (.inl ()):ℤ)=0 ∧ G z ∧ (fromTuple z).y.value^2=(fromTuple z).x.value^3-25*(fromTuple z).x.value) ↔ _
  rw [hG]
  have h1 : (z (.inl ()):ℤ)=1 ↔ z (.inl ())=1 := by omega
  have h0 : (z (.inl ()):ℤ)=0 ↔ z (.inl ())=0 := by omega
  rw [h1,h0]
  dsimp only [Code.Valid,fromTuple]
  tauto

variable {ι : Type} [Finite ι]
end

open Compiler RationalCompiler
open WeierstrassCurve.Affine.Point

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

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.PointCompiler
open Compiler RationalCompiler
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point


theorem solution : type_of% @_root_.OAI.SingleFold.PointCompiler.code_valid_semi := @_root_.OAI.SingleFold.PointCompiler.code_valid_semi
