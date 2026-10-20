-- Prove2me | solution 1 for OAI.SingleFold.PointCompiler.PointSF.xle
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:09:37.772258+00:00
-- url     : https://prove2.me/submissions/10fb1556-90d0-4c07-bc6b-7522990e2c24

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/FunctionalCompiler.lean:L236-L254
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.PointCompiler.PointSF.xle. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
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

lemma le_iff (p q : FractionPoly α) (z : α → ℕ) (hp : 0<p.den z) (hq : 0<q.den z) :
    p.value z≤q.value z ↔ (p.num*q.den) z≤(q.num*p.den) z := by
  have hp' : (0:ℚ)<p.den z := by exact_mod_cast hp
  have hq' : (0:ℚ)<q.den z := by exact_mod_cast hq
  rw [value,value,div_le_div_iff₀ hp' hq']
  simp only [Poly.mul_apply]
  exact_mod_cast (Iff.rfl : (p.num z:ℚ)*q.den z≤q.num z*p.den z ↔ (p.num z:ℚ)*q.den z≤q.num z*p.den z)

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
theorem and (hR : Semi R) (hS : Semi S) : Semi (fun x => R x ∧ S x) := by
  refine ⟨hR.1.and hS.1,?_⟩
  refine (hR.2.or (hR.1.and hS.2) (by intro x h; exact h.1 h.2.1)).congr ?_
  intro x; tauto
theorem reindex (hR : Semi R) (f : α → β) : Semi (fun x => R (x ∘ f)) :=
  ⟨hR.1.reindex f,hR.2.reindex f⟩
theorem eq (p q : Poly α) : Semi (fun x => p x=q x) := by
  refine ⟨SF.eq p q,((SF.lt p q).or (SF.lt q p) (by intro x h; exact lt_asymm h.1 h.2)).congr ?_⟩
  intro x; constructor
  · intro h; rcases h with h|h; exact h.ne; exact h.ne'
  · exact lt_or_gt_of_ne
theorem le (p q : Poly α) : Semi (fun x => p x≤q x) :=
  ⟨SF.le p q,(SF.lt q p).congr (fun _ => not_le.symm)⟩
theorem all [Finite β] {P : β → (α → ℕ) → Prop} (hp : ∀ i, Semi (P i)) :
    Semi (fun x => ∀ i, P i x) := by
  classical
  let := Fintype.ofFinite β
  suffices ∀ s : Finset β, Semi (fun x => ∀ i∈s, P i x) by
    exact (this Finset.univ).congr (by simp)
  intro s
  induction s using Finset.induction_on with
  | empty => exact (Semi.eq (0:Poly α) 0).congr (by simp)
  | @insert i s hi hs => exact ((hp i).and hs).congr (by simp)
end Semi
end SingleFold.Compiler

namespace SingleFold.RationalCompiler
open Compiler

namespace Expr
variable {α β : Type}
lemma le_under {G : (β → ℕ) → Prop} (hG : Semi G) (f : α×Fin 6 → β)
    (hv : ∀ z, G z → Valid (z ∘ f)) (p q : Expr α) :
    Semi (fun z => G z ∧ p.eval (value (z ∘ f))≤q.eval (value (z ∘ f))) := by
  refine (hG.and (Semi.le ((p.compile.num*q.compile.den).map f) ((q.compile.num*p.compile.den).map f))).congr ?_
  intro z
  apply and_congr_right
  intro hz
  have hp := p.compile_spec (z ∘ f) (hv z hz)
  have hq := q.compile_spec (z ∘ f) (hv z hz)
  change (p.compile.num*q.compile.den) (z ∘ f)≤(q.compile.num*p.compile.den) (z ∘ f) ↔ _
  rw [←FractionPoly.le_iff _ _ _ hp.1 hq.1,hp.2,hq.2]
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

lemma from_tuple (c : Code) : fromTuple (tuple c)=c := by
  simp only [fromTuple,tuple,Sum.elim_inl,Sum.elim_inr,ite_true,show (1:Fin 2)≠0 by decide,ite_false]
  change Code.mk c.flag (code (RationalCompiler.tuple c.x)) (code (RationalCompiler.tuple c.y))=c
  rw [code_tuple,code_tuple]
variable {ι : Type} [Finite ι]
lemma allValid_semi : Semi (@AllValid ι) :=
  Semi.all (fun i => code_valid_semi.reindex (fun k => (i,k)))
omit [Finite ι] in
lemma allValid_rational (z) (hz : AllValid z) : Valid (z ∘ @ratMap ι) := by
  intro ⟨i,v⟩
  fin_cases v
  · exact (hz i).1
  · exact (hz i).2.1
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

-- ---- from OAI.NumberTheory.SingleFold.FunctionalCompiler ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.Compiler

namespace MapSF
variable {α β γ δ : Type}
lemma all [Finite δ] {f : δ → (α → ℕ) → (β → ℕ)} (hf : ∀ d, MapSF (f d)) :
    MapSF (fun z (v : δ×β) => f v.1 z v.2) := by
  have h := SF.all (fun d => SF.reindex (hf d) (Sum.map id (fun j => (d,j))))
  refine h.congr ?_
  intro z
  constructor
  · intro hh; funext ⟨d,j⟩; exact congrFun (hh d) j
  · intro hh d; funext j; exact congrFun hh (d,j)
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
end PointSF
end SingleFold.PointCompiler

namespace SingleFold.Compiler
namespace ScalarSF
variable {α : Type} {f g : (α → ℕ) → ℕ}
end ScalarSF
end SingleFold.Compiler

namespace SingleFold.PointCompiler
open Compiler RationalCompiler
lemma exprLe_semi {ι : Type} [Finite ι] (p q : Expr (ι×Fin 2)) :
    Semi (fun z => AllValid z ∧ p.eval (values z)≤q.eval (values z)) :=
  Expr.le_under allValid_semi ratMap allValid_rational p q
namespace PointSF
variable {α : Type} {f g : (α → ℕ) → E.Point}
lemma xle (hf : PointSF f) (hg : PointSF g) :
    SF (fun z => (encode (f z)).x.value≤(encode (g z)).x.value) := by
  have hh := MapSF.all (f:=fun i : Fin 2 => if i=0 then (fun z => tuple (encode (f z))) else (fun z => tuple (encode (g z))))
    (fun i => by fin_cases i; exact hf; exact hg)
  have he := (exprLe_semi (xe (0:Fin 2)) (xe 1)).1
  refine (hh.pullback he).congr ?_
  intro z
  let frame : Fin 2×Var → ℕ := fun v => (if v.1=0 then (fun z => tuple (encode (f z))) else (fun z => tuple (encode (g z)))) z v.2
  change (AllValid frame ∧ (At frame 0).x.value≤(At frame 1).x.value) ↔ _
  have h₀ : At frame 0=encode (f z) := from_tuple _
  have h₁ : At frame 1=encode (g z) := from_tuple _
  have hv : AllValid frame := by
    intro i; fin_cases i
    · change (At frame 0).Valid
      rw [h₀]; exact encode_valid _
    · change (At frame 1).Valid
      rw [h₁]; exact encode_valid _
  rw [h₀,h₁]
  simp only [hv,true_and]
end PointSF
end SingleFold.PointCompiler

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.PointCompiler OAI.SingleFold.PointCompiler.PointSF
open Compiler RationalCompiler


theorem solution : type_of% @_root_.OAI.SingleFold.PointCompiler.PointSF.xle := @_root_.OAI.SingleFold.PointCompiler.PointSF.xle
