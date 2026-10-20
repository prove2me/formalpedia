-- Prove2me | solution 2 for OAI.SingleFold.Compiler.ScalarSF.sub
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:50:08.148402+00:00
-- url     : https://prove2.me/submissions/9c199304-a806-4f6e-a4aa-f25c848fdae6

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/Power.lean:L233-L247
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.Compiler.ScalarSF.sub. The node keeps its source
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
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell
import Definitions.Def_OAI_NumberTheory_SingleFold_Power

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

variable {ι : Type} [Finite ι]
end

open Compiler RationalCompiler
open WeierstrassCurve.Affine.Point

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
lemma max (hf : ScalarSF f) (hg : ScalarSF g) : ScalarSF (fun z => max (f z) (g z)) := by
  have h : ScalarSF (fun z : Unit⊕Unit → ℕ => Max.max (z (.inl ())) (z (.inr ()))) := by
    refine (Semi.max_eq (Poly.proj (.inl (.inl ()))) (Poly.proj (.inl (.inr ())))
      (Poly.proj (.inr ()))).1.congr ?_
    intro z
    change Max.max (z (.inl (.inl ())):ℤ) (z (.inl (.inr ())) : ℤ)=(z (.inr ()):ℤ) ↔ _
    rw [←Nat.cast_max,Int.natCast_inj]
    exact ⟨fun hh => funext (fun j => by cases j; exact hh.symm),fun hh => (congrFun hh ()).symm⟩
  exact MapSF.comp h (MapSF.pair hf hg)
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
namespace PointSF
variable {α : Type} {f g : (α → ℕ) → E.Point}
end PointSF
end SingleFold.PointCompiler

end OAI

-- ---- from OAI.NumberTheory.SingleFold.Power ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.PowerEstimate
end SingleFold.PowerEstimate

namespace SingleFold.PowerSystem
open PowerEstimate

variable {g : ℕ → ℕ} {δ : ℝ} {ell u₀ : ℕ}
variable (hδ : 0<δ) (hell : 1≤ell) (h₀ : 4≤u₀)
variable (hg : ∀ u, u₀≤u → δ*(Real.log (u:ℝ))^2<Real.log (g u:ℝ) ∧ Real.log (g u:ℝ)<(u:ℝ)*Real.log (u:ℝ))
include hδ hell h₀ hg
end SingleFold.PowerSystem

namespace SingleFold.Compiler.ScalarSF
variable {α : Type} {f g : (α → ℕ) → ℕ}
lemma reindex (hf : ScalarSF f) {β : Type} (i : α → β) : ScalarSF (fun z => f (z ∘ i)) :=
  MapSF.reindex hf i
lemma sub (hf : ScalarSF f) (hg : ScalarSF g) : ScalarSF (fun z => f z-g z) := by
  have h := ((proj (Sum.inr ())).add (hg.reindex Sum.inl)).eq
    ((hf.reindex Sum.inl).max (hg.reindex Sum.inl))
  refine SF.congr h ?_
  intro z

  constructor
  · intro hh
    funext j; cases j
    change z (.inr ())=f (z ∘ Sum.inl)-g (z ∘ Sum.inl)
    omega
  · intro hh
    have he := congrFun hh ()
    change z (.inr ())=f (z ∘ Sum.inl)-g (z ∘ Sum.inl) at he
    omega
end SingleFold.Compiler.ScalarSF

namespace SingleFold.PowerCompilation
open Compiler
end SingleFold.PowerCompilation

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.Compiler OAI.SingleFold.Compiler.ScalarSF


theorem solution : type_of% @_root_.OAI.SingleFold.Compiler.ScalarSF.sub := @_root_.OAI.SingleFold.Compiler.ScalarSF.sub
