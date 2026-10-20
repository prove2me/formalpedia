-- Prove2me | solution 1 for OAI.SingleFold.GrowthCompilation.graph_sf
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:31:06.844976+00:00
-- url     : https://prove2.me/submissions/01f87f41-9cf9-4b13-a521-b9562b20ea66

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/EllipticGrowth.lean:L443-L487
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.GrowthCompilation.graph_sf. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Theorems.Thm_OAI_SingleFold_PointCompiler_PointSF_add
import Theorems.Thm_OAI_SingleFold_PointCompiler_PointSF_height
import Theorems.Thm_OAI_SingleFold_PointCompiler_PointSF_smul
import Theorems.Thm_OAI_SingleFold_PointCompiler_PointSF_xle
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
theorem le (p q : Poly α) : Semi (fun x => p x≤q x) :=
  ⟨SF.le p q,(SF.lt q p).congr (fun _ => not_le.symm)⟩
theorem lt (p q : Poly α) : Semi (fun x => p x<q x) :=
  ⟨SF.lt p q,(SF.le q p).congr (fun _ => not_lt.symm)⟩
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
lemma Code.unique {c d : Code} (hc : c.Valid) (hd : d.Valid) (he : c.toPoint hc=d.toPoint hd) : c=d := by
  rw [←c.encode_toPoint hc,←d.encode_toPoint hd,he]

lemma from_tuple (c : Code) : fromTuple (tuple c)=c := by
  simp only [fromTuple,tuple,Sum.elim_inl,Sum.elim_inr,ite_true,show (1:Fin 2)≠0 by decide,ite_false]
  change Code.mk c.flag (code (RationalCompiler.tuple c.x)) (code (RationalCompiler.tuple c.y))=c
  rw [code_tuple,code_tuple]
lemma tuple_from (z : Var → ℕ) : tuple (fromTuple z)=z := by
  funext i
  rcases i with i|⟨i,j⟩
  · rfl
  · fin_cases i <;> fin_cases j <;> rfl

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

lemma fromTuple_injective : Function.Injective fromTuple := by
  intro x y h
  have hh := congrArg tuple h
  simpa only [tuple_from] using hh

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

lemma rational_height (r : ℚ) :
    max ((RationalCode.encode r).p+(RationalCode.encode r).n) (RationalCode.encode r).d=
      max r.num.natAbs r.den := by
  have hv := RationalCode.encode_valid r
  have hc := RationalCode.canonical hv
  have hp := RationalCode.positive_num hv
  have hn := RationalCode.negative_num hv
  rw [RationalCode.encode_value] at hc hp hn
  rw [←hp,←hn,hc.2,Int.toNat_add_toNat_neg_eq_natAbs]
end SingleFold.PointCompiler

end OAI

-- ---- from OAI.NumberTheory.SingleFold.FunctionalCompiler ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.Compiler

namespace MapSF
variable {α β γ δ : Type}
lemma congr {f g : (α → ℕ) → (β → ℕ)} (hf : MapSF f) (hfg : ∀ z, f z=g z) : MapSF g :=
  SF.congr hf (by intro z; rw [hfg])
lemma proj (i : β → α) [Finite β] : MapSF (fun z => z ∘ i) := by
  have h := SF.all (fun j : β => SF.eq (Poly.proj (Sum.inr j : α⊕β)) (Poly.proj (Sum.inl (i j))))
  refine h.congr ?_
  intro z
  change (∀ j, (z (Sum.inr j):ℤ)=z (Sum.inl (i j))) ↔ _
  simp only [Int.natCast_inj]
  exact ⟨fun h => funext h,fun h j => congrFun h j⟩
lemma const (b : β → ℕ) [Finite β] : MapSF (fun _ : α → ℕ => b) := by
  have h := SF.all (fun j : β => SF.eq (Poly.proj (Sum.inr j : α⊕β)) (Poly.const (b j)))
  refine h.congr ?_
  intro z
  change (∀ j, (z (Sum.inr j):ℤ)=(b j:ℤ)) ↔ _
  simp only [Int.natCast_inj]
  exact ⟨fun h => funext h,fun h j => congrFun h j⟩
lemma reindex {f : (α → ℕ) → (β → ℕ)} (hf : MapSF f) (i : α → γ) :
    MapSF (fun z => f (z ∘ i)) := by
  exact (SF.reindex hf (Sum.map i id)).congr (by intro z; rfl)
lemma comp {f : (α → ℕ) → (β → ℕ)} {g : (β → ℕ) → (γ → ℕ)} [Finite β]
    (hg : MapSF g) (hf : MapSF f) : MapSF (fun z => g (f z)) := by
  have h := (SF.reindex hf (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr)).and
    (SF.reindex hg (Sum.elim Sum.inr (Sum.inl ∘ Sum.inr)))
  have hu : ∀ (z : α⊕γ → ℕ) (x y : β → ℕ),
      (x=f (z ∘ Sum.inl) ∧ z ∘ Sum.inr=g x) →
      (y=f (z ∘ Sum.inl) ∧ z ∘ Sum.inr=g y) → x=y := by
    intro z x y hx hy; exact hx.1.trans hy.1.symm
  refine (h.ex hu).congr ?_
  intro z
  change (∃ x, x=f (z ∘ Sum.inl) ∧ z ∘ Sum.inr=g x) ↔ _
  simp only [exists_eq_left]
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
lemma decode_encode (P : E.Point) : (encode P).decode=P := by
  rw [Code.decode,dite_eq_left (encode_valid P),encode_toPoint]
lemma normalized_graph : MapSF (fun z : Var → ℕ => tuple (encode (fromTuple z).decode)) := by
  let v := code_valid_semi.reindex (Sum.inl : Var → Var⊕Var)
  have ht : SF (fun z : Var⊕Var → ℕ => z ∘ Sum.inr=z ∘ Sum.inl) := MapSF.proj id
  have hz : SF (fun z : Var⊕Var → ℕ => z ∘ Sum.inr=tuple (encode 0)) := MapSF.const _
  have h := (v.1.and ht).or (v.2.and hz) (by intro z; tauto)
  refine h.congr ?_
  intro z
  change (((fromTuple (z ∘ Sum.inl)).Valid ∧ z ∘ Sum.inr=z ∘ Sum.inl) ∨
    ¬(fromTuple (z ∘ Sum.inl)).Valid ∧ z ∘ Sum.inr=tuple (encode 0)) ↔ _
  by_cases hv : (fromTuple (z ∘ Sum.inl)).Valid
  · simp only [hv,true_and,not_true,false_and,or_false]
    rw [Code.decode,dite_eq_left hv,Code.encode_toPoint,tuple_from]
  · simp only [hv,false_and,not_false_eq_true,true_and,false_or]
    rw [Code.decode,dite_eq_right hv]

namespace PointSF
variable {α β : Type} {f g : (α → ℕ) → E.Point}
lemma const (P : E.Point) : PointSF (fun _ : α → ℕ => P) := MapSF.const _
lemma var (i : Var → α) : PointSF (fun z => (fromTuple (z ∘ i)).decode) :=
  MapSF.reindex normalized_graph i
end PointSF
end SingleFold.PointCompiler

namespace SingleFold.Compiler
namespace ScalarSF
variable {α : Type} {f g : (α → ℕ) → ℕ}
lemma const (n : ℕ) : ScalarSF (fun _ : α → ℕ => n) := MapSF.const _
lemma proj (i : α) : ScalarSF (fun z => z i) := MapSF.proj (fun _ => i)
lemma poly {f : (α → ℕ) → ℕ} (p : Poly α) (hp : ∀ z, p z=(f z:ℤ)) : ScalarSF f := by
  have h := SF.eq (Poly.proj (Sum.inr () : α⊕Unit)) (p.map Sum.inl)
  refine h.congr ?_
  intro z
  change (z (Sum.inr ()):ℤ)=p (z ∘ Sum.inl) ↔ _
  rw [hp,Int.natCast_inj]
  exact ⟨fun hh => funext (fun j => by cases j; exact hh),fun hh => congrFun hh ()⟩
lemma add (hf : ScalarSF f) (hg : ScalarSF g) : ScalarSF (fun z => f z+g z) := by
  have h : ScalarSF (fun z : Unit⊕Unit → ℕ => z (.inl ())+z (.inr ())) :=
    poly (Poly.proj (.inl ())+Poly.proj (.inr ())) (by intro z; simp)
  exact MapSF.comp h (MapSF.pair hf hg)
lemma mul (hf : ScalarSF f) (hg : ScalarSF g) : ScalarSF (fun z => f z*g z) := by
  have h : ScalarSF (fun z : Unit⊕Unit → ℕ => z (.inl ())*z (.inr ())) :=
    poly (Poly.proj (.inl ())*Poly.proj (.inr ())) (by intro z; simp)
  exact MapSF.comp h (MapSF.pair hf hg)
lemma pow (hf : ScalarSF f) (n : ℕ) : ScalarSF (fun z => f z^n) := by
  have h : ScalarSF (fun z : Unit → ℕ => z ()^n) :=
    poly (Poly.proj ()^n) (by
      intro z
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ,Poly.mul_apply,ih,Poly.proj_apply,Nat.cast_pow,←pow_succ,Nat.cast_pow])
  exact MapSF.comp h hf
lemma max (hf : ScalarSF f) (hg : ScalarSF g) : ScalarSF (fun z => max (f z) (g z)) := by
  have h : ScalarSF (fun z : Unit⊕Unit → ℕ => Max.max (z (.inl ())) (z (.inr ()))) := by
    refine (Semi.max_eq (Poly.proj (.inl (.inl ()))) (Poly.proj (.inl (.inr ())))
      (Poly.proj (.inr ()))).1.congr ?_
    intro z
    change Max.max (z (.inl (.inl ())):ℤ) (z (.inl (.inr ())) : ℤ)=(z (.inr ()):ℤ) ↔ _
    rw [←Nat.cast_max,Int.natCast_inj]
    exact ⟨fun hh => funext (fun j => by cases j; exact hh.symm),fun hh => (congrFun hh ()).symm⟩
  exact MapSF.comp h (MapSF.pair hf hg)
lemma le (hf : ScalarSF f) (hg : ScalarSF g) : SF (fun z => f z≤g z) := by
  have h := (MapSF.pair hf hg).pullback (SF.le (Poly.proj (.inl ())) (Poly.proj (.inr ())))
  refine h.congr ?_
  intro z
  change (f z:ℤ)≤(g z:ℤ) ↔ _
  exact_mod_cast Iff.rfl
lemma lt (hf : ScalarSF f) (hg : ScalarSF g) : SF (fun z => f z<g z) := by
  have h := (MapSF.pair hf hg).pullback (SF.lt (Poly.proj (.inl ())) (Poly.proj (.inr ())))
  refine h.congr ?_
  intro z
  change (f z:ℤ)<(g z:ℤ) ↔ _
  exact_mod_cast Iff.rfl
lemma eq (hf : ScalarSF f) (hg : ScalarSF g) : SF (fun z => f z=g z) := by
  have h := (MapSF.pair hf hg).pullback (SF.eq (Poly.proj (.inl ())) (Poly.proj (.inr ())))
  refine h.congr ?_
  intro z
  change (f z:ℤ)=(g z:ℤ) ↔ _
  exact_mod_cast Iff.rfl
end ScalarSF
end SingleFold.Compiler

namespace SingleFold.PointCompiler
open Compiler RationalCompiler
lemma exprLe_semi {ι : Type} [Finite ι] (p q : Expr (ι×Fin 2)) :
    Semi (fun z => AllValid z ∧ p.eval (values z)≤q.eval (values z)) :=
  Expr.le_under allValid_semi ratMap allValid_rational p q
namespace PointSF
variable {α : Type} {f g : (α → ℕ) → E.Point}
lemma nonzero (hf : PointSF f) : SF (fun z => f z≠0) := by
  have h := hf.pullback ((Semi.eq (Poly.proj (Sum.inl () : Var)) 0).1)
  refine h.congr ?_
  intro z
  change ((encode (f z)).flag:ℤ)=0 ↔ _
  cases f z <;> simp [encode,←WeierstrassCurve.Affine.Point.zero_def]
lemma ynonneg (hf : PointSF f) : SF (fun z => 0≤(encode (f z)).y.value) := by
  have hh := MapSF.all (fun _ : Unit => hf)
  refine (hh.pullback (exprLe_semi (ι:=Unit) 0 (ye ()) ).1).congr ?_
  intro z
  change (AllValid (fun v : Unit×Var => tuple (encode (f z)) v.2) ∧ 0≤(encode (f z)).y.value) ↔ _
  have hv : AllValid (fun v : Unit×Var => tuple (encode (f z)) v.2) := by
    intro i; exact (by simpa only [At,from_tuple] using encode_valid (f z))
  simp only [hv,true_and]
end PointSF
end SingleFold.PointCompiler

end OAI

-- ---- from OAI.NumberTheory.SingleFold.EllipticGrowth ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.EllipticModel
open WeierstrassCurve.Affine.Point
variable {T : Type} [AddCommGroup T]
variable (f : E.Point ≃+ (Fin 1 → ℤ)×T)
end SingleFold.EllipticModel

namespace SingleFold.GrowthCompilation
open Compiler PointCompiler
lemma encoded_height (Q : E.Point) : (encode Q).height=EllipticModel.Hx Q := by
  cases Q with
  | zero => change max ((RationalCode.encode 0).p+(RationalCode.encode 0).n) (RationalCode.encode 0).d=1
            rw [rational_height]; norm_num
  | some x y h => exact rational_height x
lemma encoded_x (Q : E.Point) : (encode Q).x.value=EllipticModel.xcoord Q := by
  cases Q <;> exact RationalCode.encode_value _
lemma encoded_y (Q : E.Point) : (encode Q).y.value=EllipticModel.ycoord Q := by
  cases Q <;> exact RationalCode.encode_value _
lemma height_sf {α : Type} {Q : (α → ℕ) → E.Point} (hQ : PointSF Q) (m : ℕ) :
    ScalarSF (fun z => EllipticModel.W m (Q z)) := by
  refine MapSF.congr (PointSF.height m hQ) ?_
  intro z; funext j; exact encoded_height _

section
variable {T α : Type} [AddCommGroup T] [Finite T]
variable (f : E.Point ≃+ (Fin 1 → ℤ)×T)
variable {Q R : (α → ℕ) → E.Point}
lemma representative_sf (m : ℕ) (hQ : PointSF Q) :
    SF (fun z => EllipticModel.Representative f m (Q z)) := by
  have hy := hQ.ynonneg.congr (fun z => by rw [encoded_y])
  have hw := (ScalarSF.const 1).lt (height_sf hQ m)
  have ht := SF.all (fun t : T =>
    let hadd := hQ.add (PointSF.const (EllipticModel.point f 0 t))
    hadd.nonzero.and (hadd.xle hQ))
  refine (hQ.nonzero.and (hy.and (hw.and ht))).congr ?_
  intro z
  change (Q z ≠ 0 ∧ 0 ≤ EllipticModel.ycoord (Q z) ∧ 1 < EllipticModel.W m (Q z) ∧
    ∀ t : T, Q z + EllipticModel.point f 0 t ≠ 0 ∧
      (encode (Q z + EllipticModel.point f 0 t)).x.value ≤ (encode (Q z)).x.value) ↔ _
  simp only [EllipticModel.Representative, encoded_x]
omit [Finite T] in
lemma bracket_sf (m : ℕ) {u : (α → ℕ) → ℕ} (hu : ScalarSF u) (hQ : PointSF Q) :
    SF (fun z => EllipticModel.Bracket f m (u z) (Q z)) := by
  have hw := height_sf hQ m
  have hplus := height_sf (hQ.add (PointSF.const (EllipticModel.P f))) m
  have hminus := height_sf (hQ.add (PointSF.const (-EllipticModel.P f))) m
  have hb := hu.add (ScalarSF.const (EllipticModel.W m (EllipticModel.P f)))
  have hn := hplus.max hminus
  refine ((hw.le hb).and (hb.lt hn)).congr ?_
  intro z
  simp only [sub_eq_add_neg,EllipticModel.Bracket]
  rfl
omit [Finite T] in
lemma window_sf (m κ : ℕ) (hQ : PointSF Q) (hR : PointSF R) :
    SF (fun z => EllipticModel.Window f m κ (Q z) (R z)) := by
  have hL := ((height_sf (hQ.smul 2) m).mul (height_sf hR m)).mul
    (ScalarSF.const (EllipticModel.W m (EllipticModel.P f)))
  have hmax := (height_sf (hR.add (PointSF.const (EllipticModel.P f))) m).max
    (height_sf (hR.add (PointSF.const (-EllipticModel.P f))) m)
  have hD := ((height_sf hQ m).pow 2).mul hmax
  refine ((hL.le ((ScalarSF.const κ).mul hD)).and (hD.le ((ScalarSF.const κ).mul hL))).congr ?_
  intro z
  simp only [sub_eq_add_neg,EllipticModel.Window]
  rfl
lemma pair_sf (m κ : ℕ) {u : (α → ℕ) → ℕ} (hu : ScalarSF u) (hQ : PointSF Q) (hR : PointSF R) :
    SF (fun z => EllipticModel.GrowthPair f m κ (u z) (Q z,R z)) :=
  (representative_sf f m hQ).and ((bracket_sf f m hu hQ).and
    ((representative_sf f m hR).and (window_sf f m κ hQ hR)))
end

lemma decode_injective_valid {a b : Code} (ha : a.Valid) (hb : b.Valid)
    (he : a.decode=b.decode) : a=b := by
  apply Code.unique ha hb
  simpa only [Code.decode,dite_eq_left ha,dite_eq_left hb] using he

section
variable {T : Type} [AddCommGroup T] [Finite T]
variable (f : E.Point ≃+ (Fin 1 → ℤ)×T)
lemma graph_sf (m κ : ℕ) (hunique : ∀ u, ∃! A, EllipticModel.GrowthPair f m κ u A) :
    SF (fun z : Fin 2 → ℕ => ∃ A, EllipticModel.GrowthPair f m κ (z 0) A ∧ EllipticModel.W m A.2=z 1) := by
  let α := Fin 2⊕(Fin 2×Var)
  let q : Var → α := fun k => .inr (0,k)
  let r : Var → α := fun k => .inr (1,k)
  let Q (z : α → ℕ) := (fromTuple (z ∘ q)).decode
  let R (z : α → ℕ) := (fromTuple (z ∘ r)).decode
  have hQ : PointSF Q := PointSF.var q
  have hR : PointSF R := PointSF.var r
  have hv := allValid_semi.reindex (Sum.inr : Fin 2×Var → α)
  have hp := pair_sf f m κ (ScalarSF.proj (.inl 0)) hQ hR
  have hw := (height_sf hR m).eq (ScalarSF.proj (.inl 1))
  have h := hv.1.and (hp.and hw)
  have hdec (z : Fin 2 → ℕ) (w : Fin 2×Var → ℕ) :
      (Q (Sum.elim z w),R (Sum.elim z w))=((At w 0).decode,(At w 1).decode) := rfl
  have hu : ∀ (z : Fin 2 → ℕ) (w w' : Fin 2×Var → ℕ),
      (AllValid w ∧ EllipticModel.GrowthPair f m κ (z 0) ((At w 0).decode,(At w 1).decode) ∧
        EllipticModel.W m (At w 1).decode=z 1) →
      (AllValid w' ∧ EllipticModel.GrowthPair f m κ (z 0) ((At w' 0).decode,(At w' 1).decode) ∧
        EllipticModel.W m (At w' 1).decode=z 1) → w=w' := by
    intro z w w' hw hw'
    have he := (hunique (z 0)).unique hw.2.1 hw'.2.1
    have hcode (i : Fin 2) : At w i=At w' i := by
      apply decode_injective_valid (hw.1 i) (hw'.1 i)
      fin_cases i
      · exact congrArg Prod.fst he
      · exact congrArg Prod.snd he
    funext ⟨i,j⟩
    exact congrFun (fromTuple_injective (hcode i)) j
  refine (h.ex hu).congr ?_
  intro z
  change (∃ w : Fin 2×Var → ℕ, AllValid w ∧
    EllipticModel.GrowthPair f m κ (z 0) ((At w 0).decode,(At w 1).decode) ∧
    EllipticModel.W m (At w 1).decode=z 1) ↔ _
  constructor
  · rintro ⟨w,_,hp,hw⟩; exact ⟨_,hp,hw⟩
  · rintro ⟨⟨P,S⟩,hp,hw⟩
    let w : Fin 2×Var → ℕ := fun v => tuple (encode (if v.1=0 then P else S)) v.2
    have hc (i : Fin 2) : At w i=encode (if i=0 then P else S) := from_tuple _
    have hd0 : (At w 0).decode=P := by rw [hc]; exact decode_encode P
    have hd1 : (At w 1).decode=S := by rw [hc]; exact decode_encode S
    refine ⟨w,?_,?_,?_⟩
    · intro i; rw [hc]; exact encode_valid _
    · simpa only [hd0,hd1] using hp
    · simpa only [hd1] using hw
end

end SingleFold.GrowthCompilation

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.GrowthCompilation
open Compiler PointCompiler


theorem solution : type_of% @_root_.OAI.SingleFold.GrowthCompilation.graph_sf := @_root_.OAI.SingleFold.GrowthCompilation.graph_sf
