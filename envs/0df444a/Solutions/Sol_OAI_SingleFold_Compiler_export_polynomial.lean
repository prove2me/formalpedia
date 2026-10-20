-- Prove2me | solution 1 for OAI.SingleFold.Compiler.export_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T17:51:11.508645+00:00
-- url     : https://prove2.me/submissions/6d5d68ac-ca90-4e2e-b88c-7906856448ed

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/PolynomialCompiler.lean:L254-L300
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.Compiler.export_polynomial. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler

-- ---- from OAI.NumberTheory.SingleFold.PolynomialCompiler ----
namespace OAI

namespace SingleFold.Compiler

attribute [instance] Representation.finite

namespace Representation
variable {α β γ : Type} {R S : (α → ℕ) → Prop}

end Representation

theorem poly_to_mv {α : Type} (p : Poly α) :
    ∃ q : MvPolynomial α ℤ, ∀ x, q.eval (fun i => (x i : ℤ)) = p x := by
  induction p using Poly.induction with
  | H1 i => exact ⟨MvPolynomial.X i,by simp⟩
  | H2 n => exact ⟨MvPolynomial.C n,by simp⟩
  | H3 f g hf hg =>
    obtain ⟨p,hp⟩ := hf
    obtain ⟨q,hq⟩ := hg
    exact ⟨p-q,by intro x; simp [hp,hq]⟩
  | H4 f g hf hg =>
    obtain ⟨p,hp⟩ := hf
    obtain ⟨q,hq⟩ := hg
    exact ⟨p*q,by intro x; simp [hp,hq]⟩

theorem export_polynomial {α : Type} {R : (α → ℕ) → Prop} (r : Representation R) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ p : MvPolynomial (α ⊕ Fin m) ℤ,
      (∀ x, R x ↔ ∃ w : Fin m → ℕ, p.eval (Sum.elim (fun i => (x i:ℤ)) (fun j => (w j:ℤ)))=0) ∧
      (∀ (x : α → ℕ) (w w' : Fin m → ℕ), p.eval (Sum.elim (fun i => (x i:ℤ)) (fun j => (w j:ℤ)))=0 →
        p.eval (Sum.elim (fun i => (x i:ℤ)) (fun j => (w' j:ℤ)))=0 → w=w') := by
  classical
  let p : Poly (α ⊕ (r.vars ⊕ Unit)) := r.poly.map (Sum.map id Sum.inl)
  let q : Poly (α ⊕ (r.vars ⊕ Unit)) := Poly.proj (Sum.inr (Sum.inr ()))
  let := Fintype.ofFinite (r.vars ⊕ Unit)
  let e := Fintype.equivFin (r.vars ⊕ Unit)
  let f := (p*p+q*q).map (Sum.map id e)
  obtain ⟨P,hP⟩ := poly_to_mv f
  have ev (x : α → ℕ) (w : Fin (Fintype.card (r.vars ⊕ Unit)) → ℕ) :
      P.eval (Sum.elim (fun i => (x i:ℤ)) (fun j => (w j:ℤ)))=0 ↔
        r.poly (Sum.elim x (fun i => w (e (Sum.inl i))))=0 ∧ w (e (Sum.inr ()))=0 := by
    have he := hP (Sum.elim x w)
    have hc : (fun i : α ⊕ Fin (Fintype.card (r.vars ⊕ Unit)) => ((Sum.elim x w) i:ℤ)) =
        Sum.elim (fun i => (x i:ℤ)) (fun j => (w j:ℤ)) := by funext i; cases i <;> rfl
    rw [hc] at he
    rw [he]
    simp only [f,p,q,Poly.map_apply,Poly.add_apply,Poly.mul_apply,Poly.proj_apply,elim_comp_map,Function.comp_id]
    change r.poly (Sum.elim x (fun i => w (e (Sum.inl i)))) *
      r.poly (Sum.elim x (fun i => w (e (Sum.inl i)))) +
      (w (e (Sum.inr ())):ℤ) * (w (e (Sum.inr ())):ℤ)=0 ↔ _
    constructor
    · intro h
      have h₁ : r.poly (Sum.elim x (fun i => w (e (Sum.inl i))))=0 := by nlinarith [sq_nonneg (w (e (Sum.inr ())):ℤ)]
      exact ⟨h₁,by rw [h₁] at h; norm_num at h; exact h⟩
    · rintro ⟨h₁,h₂⟩; simp [h₁,h₂]
  refine ⟨Fintype.card (r.vars ⊕ Unit),by exact Fintype.card_pos, P,?_,?_⟩
  · intro x
    constructor
    · intro hx
      obtain ⟨w,hw⟩ := r.complete x hx
      refine ⟨Sum.elim w (fun _ => 0) ∘ e.symm,(ev _ _).mpr ?_⟩
      simpa using And.intro hw (show (0:ℕ)=0 from rfl)
    · rintro ⟨w,hw⟩
      exact r.sound _ _ ((ev _ _).mp hw).1
  · intro x w w' hw hw'
    obtain ⟨hr,hz⟩ := (ev _ _).mp hw
    obtain ⟨hr',hz'⟩ := (ev _ _).mp hw'
    have hh := r.unique _ _ _ hr hr'
    funext i
    obtain ⟨j,rfl⟩ := e.surjective i
    rcases j with j|⟨⟩
    · exact congrFun hh j
    · exact hz.trans hz'.symm

end SingleFold.Compiler

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.Compiler


theorem solution : type_of% @_root_.OAI.SingleFold.Compiler.export_polynomial := @_root_.OAI.SingleFold.Compiler.export_polynomial
