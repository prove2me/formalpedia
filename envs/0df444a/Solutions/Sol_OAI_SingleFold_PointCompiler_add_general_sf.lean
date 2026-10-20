-- Prove2me | solution 1 for OAI.SingleFold.PointCompiler.add_general_sf
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:01:08.010999+00:00
-- url     : https://prove2.me/submissions/511e4719-e282-45b6-9aad-f582656d7dea

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/EllipticCoordinates.lean:L353-L369
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.PointCompiler.add_general_sf. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
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

lemma tuple_from (z : Var → ℕ) : tuple (fromTuple z)=z := by
  funext i
  rcases i with i|⟨i,j⟩
  · rfl
  · fin_cases i <;> fin_cases j <;> rfl

variable {ι : Type} [Finite ι]
lemma allValid_semi : Semi (@AllValid ι) :=
  Semi.all (fun i => code_valid_semi.reindex (fun k => (i,k)))
omit [Finite ι] in
lemma flag_semi (i : ι) (n : ℕ) : Semi (fun z => (At z i).flag=n) :=
  (Semi.eq (Poly.proj (i,Sum.inl ())) (Poly.const n)).congr (by intro z; change (z (i,Sum.inl ()):ℤ)=(n:ℤ) ↔ _; exact_mod_cast Iff.rfl)
omit [Finite ι] in
lemma codeEq_semi (i j : ι) : Semi (fun z => At z i=At z j) := by
  have h : Semi (fun z : ι×Var → ℕ => ∀ k, z (i,k)=z (j,k)) :=
    Semi.all (fun k => (Semi.eq (Poly.proj (i,k)) (Poly.proj (j,k))).congr (by intro z; change (z (i,k):ℤ)=(z (j,k):ℤ) ↔ _; exact_mod_cast Iff.rfl))
  refine h.congr ?_
  intro z
  constructor
  · intro he; exact congrArg fromTuple (funext he)
  · intro he k
    have hh := congrArg tuple he
    simp only [At,tuple_from] at hh
    exact congrFun hh k

omit [Finite ι] in
lemma allValid_rational (z) (hz : AllValid z) : Valid (z ∘ @ratMap ι) := by
  intro ⟨i,v⟩
  fin_cases v
  · exact (hz i).1
  · exact (hz i).2.1
lemma exprEq_semi (p q : Expr (ι×Fin 2)) : Semi (fun z => AllValid z ∧ p.eval (values z)=q.eval (values z)) :=
  Expr.eq_under allValid_semi ratMap allValid_rational p q
lemma exprNe_semi (p q : Expr (ι×Fin 2)) : Semi (fun z => AllValid z ∧ p.eval (values z)≠q.eval (values z)) :=
  (allValid_semi.and (exprEq_semi p q).not).congr (by intro z; tauto)
lemma line_semi (d n x₁ x₂ y₁ x₃ y₃ : Expr (ι×Fin 2)) :
    Semi (fun z => AllValid z ∧ Line (d.eval (values z)) (n.eval (values z))
      (x₁.eval (values z)) (x₂.eval (values z)) (y₁.eval (values z)) (x₃.eval (values z)) (y₃.eval (values z))) := by
  refine ((exprEq_semi (d^2*(x₃+x₁+x₂)) (n^2)).and (exprEq_semi (d*(y₃+y₁)) (n*(x₁-x₃)))).congr ?_
  intro z
  simp only [Expr.eval_pow,Expr.eval_mul,Expr.eval_add,Expr.eval_sub,Line]
  tauto

lemma chord_semi (i j k : ι) : Semi (fun z => AllValid z ∧
    Line ((At z i).x.value-(At z j).x.value) ((At z i).y.value-(At z j).y.value)
      (At z i).x.value (At z j).x.value (At z i).y.value (At z k).x.value (At z k).y.value) := by
  refine (line_semi (xe i-xe j) (ye i-ye j) (xe i) (xe j) (ye i) (xe k) (ye k)).congr ?_
  intro z
  simp only [Expr.eval_sub,xe,ye,Expr.eval_var]
  rfl
lemma tangent_semi (i k : ι) : Semi (fun z => AllValid z ∧
    Line (2*(At z i).y.value) (3*(At z i).x.value^2-25)
      (At z i).x.value (At z i).x.value (At z i).y.value (At z k).x.value (At z k).y.value) := by
  refine (line_semi (2*ye i) (3*(xe i)^2-25) (xe i) (xe i) (ye i) (xe k) (ye k)).congr ?_
  intro z
  simp only [Expr.eval_pow,Expr.eval_sub,Expr.eval_mul,xe,ye,Expr.eval_var]
  rfl
lemma xeq_semi (i j : ι) : Semi (fun z => AllValid z ∧ (At z i).x.value=(At z j).x.value) := exprEq_semi (xe i) (xe j)
lemma xne_semi (i j : ι) : Semi (fun z => AllValid z ∧ (At z i).x.value≠(At z j).x.value) := exprNe_semi (xe i) (xe j)
lemma yneg_semi (i j : ι) : Semi (fun z => AllValid z ∧ (At z i).y.value+(At z j).y.value=0) := exprEq_semi (ye i+ye j) 0
lemma ynneg_semi (i j : ι) : Semi (fun z => AllValid z ∧ (At z i).y.value+(At z j).y.value≠0) := exprNe_semi (ye i+ye j) 0

omit [Finite ι] in
lemma add1_semi (i j k : ι) : Semi (fun z => (At z i).flag=1 ∧ At z k=At z j) :=
  (flag_semi i 1).and (codeEq_semi k j)
omit [Finite ι] in
lemma add2_semi (i j k : ι) : Semi (fun z => (At z i).flag=0 ∧ (At z j).flag=1 ∧ At z k=At z i) :=
  (flag_semi i 0).and ((flag_semi j 1).and (codeEq_semi k i))
lemma add3_semi (i j k : ι) : Semi (fun z => AllValid z ∧ (At z i).flag=0 ∧ (At z j).flag=0 ∧
    (At z i).x.value=(At z j).x.value ∧ (At z i).y.value+(At z j).y.value=0 ∧ (At z k).flag=1) := by
  refine ((flag_semi i 0).and ((flag_semi j 0).and ((xeq_semi i j).and ((yneg_semi i j).and (flag_semi k 1))))).congr ?_
  intro z; tauto
lemma add4_semi (i j k : ι) : Semi (fun z => AllValid z ∧ (At z i).flag=0 ∧ (At z j).flag=0 ∧
    (At z i).x.value≠(At z j).x.value ∧ (At z k).flag=0 ∧
    Line ((At z i).x.value-(At z j).x.value) ((At z i).y.value-(At z j).y.value)
      (At z i).x.value (At z j).x.value (At z i).y.value (At z k).x.value (At z k).y.value) := by
  refine ((flag_semi i 0).and ((flag_semi j 0).and ((xne_semi i j).and ((flag_semi k 0).and (chord_semi i j k))))).congr ?_
  intro z; tauto
lemma add5_semi (i j k : ι) : Semi (fun z => AllValid z ∧ (At z i).flag=0 ∧ (At z j).flag=0 ∧
    (At z i).x.value=(At z j).x.value ∧ (At z i).y.value+(At z j).y.value≠0 ∧ (At z k).flag=0 ∧
    Line (2*(At z i).y.value) (3*(At z i).x.value^2-25)
      (At z i).x.value (At z i).x.value (At z i).y.value (At z k).x.value (At z k).y.value) := by
  refine ((flag_semi i 0).and ((flag_semi j 0).and ((xeq_semi i j).and ((ynneg_semi i j).and ((flag_semi k 0).and (tangent_semi i k)))))).congr ?_
  intro z; tauto
lemma addEq_semi (i j k : ι) : Semi (fun z => AllValid z ∧ AddEq (At z i) (At z j) (At z k)) := by
  refine (allValid_semi.and ((add1_semi i j k).or ((add2_semi i j k).or ((add3_semi i j k).or ((add4_semi i j k).or (add5_semi i j k)))))).congr ?_
  intro z
  unfold AddEq
  tauto
end

open Compiler RationalCompiler
open WeierstrassCurve.Affine.Point

variable {α : Type}
lemma add_general_sf (f g h : Var → α) : SF (fun z =>
    (fromTuple (z ∘ f)).Valid ∧ (fromTuple (z ∘ g)).Valid ∧ (fromTuple (z ∘ h)).Valid ∧
    AddEq (fromTuple (z ∘ f)) (fromTuple (z ∘ g)) (fromTuple (z ∘ h))) := by
  refine ((addEq_semi (ι:=Fin 3) 0 1 2).1.reindex (tripleMap f g h)).congr ?_
  intro z
  have hh : AllValid (z ∘ tripleMap f g h) ↔
      (fromTuple (z ∘ f)).Valid ∧ (fromTuple (z ∘ g)).Valid ∧ (fromTuple (z ∘ h)).Valid := by
    constructor
    · intro hh; exact ⟨hh 0,hh 1,hh 2⟩
    · rintro ⟨h₀,h₁,h₂⟩ i
      fin_cases i
      exact h₀
      exact h₁
      exact h₂
  change (AllValid (z ∘ tripleMap f g h) ∧ _) ↔ _
  rw [hh]
  tauto

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


theorem solution : type_of% @_root_.OAI.SingleFold.PointCompiler.add_general_sf := @_root_.OAI.SingleFold.PointCompiler.add_general_sf
