-- Prove2me | solution 1 for OAI.SingleFold.RationalCompiler.valid_semi
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T17:52:52.694978+00:00
-- url     : https://prove2.me/submissions/74ea244f-c515-4d3f-a234-6b327f820b1f

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/RationalCodes.lean:L343-L357
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.RationalCompiler.valid_semi. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes

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
theorem eq (p q : Poly α) : SF (fun x => p x=q x) := ⟨Representation.eq p q⟩
theorem lt (p q : Poly α) : SF (fun x => p x<q x) := ⟨Representation.lt p q⟩
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
theorem and (hR : Semi R) (hS : Semi S) : Semi (fun x => R x ∧ S x) := by
  refine ⟨hR.1.and hS.1,?_⟩
  refine (hR.2.or (hR.1.and hS.2) (by intro x h; exact h.1 h.2.1)).congr ?_
  intro x; tauto
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

lemma valid_semi {α : Type} [Finite α] : Semi (@Valid α) := by
  apply Semi.all
  intro i
  let p : Poly (α × Fin 6) := Poly.proj (i,0)
  let n : Poly (α × Fin 6) := Poly.proj (i,1)
  let d : Poly (α × Fin 6) := Poly.proj (i,2)
  let t : Poly (α × Fin 6) := Poly.proj (i,3)
  let s : Poly (α × Fin 6) := Poly.proj (i,4)
  let q : Poly (α × Fin 6) := Poly.proj (i,5)
  refine ((Semi.eq (p*n) 0).and ((Semi.eq d (1+t+s)).and (Semi.eq ((p+n)*t+d) (1+q*d)))).congr ?_
  intro z
  simp only [p,n,d,t,s,q,Poly.proj_apply,Poly.mul_apply,Poly.add_apply,Poly.zero_apply,Poly.one_apply,code,RationalCode.Valid]
  constructor
  · rintro ⟨h₁,h₂,h₃⟩; exact ⟨by exact_mod_cast h₁,by exact_mod_cast h₂,by exact_mod_cast h₃⟩
  · rintro ⟨h₁,h₂,h₃⟩; exact ⟨by exact_mod_cast h₁,by exact_mod_cast h₂,by exact_mod_cast h₃⟩
namespace Expr
variable {α β : Type}
end Expr
end SingleFold.RationalCompiler

namespace SingleFold.RationalCode
end SingleFold.RationalCode

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.RationalCompiler
open Compiler


theorem solution : type_of% @_root_.OAI.SingleFold.RationalCompiler.valid_semi := @_root_.OAI.SingleFold.RationalCompiler.valid_semi
