-- Prove2me | solution 1 for OAI.SingleFold.Compiler.ScalarSF.sub
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:12:53.16156+00:00
-- url     : https://prove2.me/submissions/403b7e67-f7c4-4bba-886d-8c6eda9fbd26

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

open OAI OAI.SingleFold OAI.SingleFold.Compiler
variable {α : Type} {f g : (α → ℕ) → ℕ}


theorem solution (hf : ScalarSF f) (hg : ScalarSF g) : ScalarSF (fun z => f z-g z) := by
  classical
  obtain ⟨rf⟩ := hf
  obtain ⟨rg⟩ := hg
  -- variables: γ = (α ⊕ Unit) ⊕ (Unit ⊕ Unit)
  let A : (α ⊕ Unit) ⊕ (Unit ⊕ Unit) := Sum.inr (Sum.inl ())
  let Bv : (α ⊕ Unit) ⊕ (Unit ⊕ Unit) := Sum.inr (Sum.inr ())
  let Y : (α ⊕ Unit) ⊕ (Unit ⊕ Unit) := Sum.inl (Sum.inr ())
  let φ : α ⊕ Unit → (α ⊕ Unit) ⊕ (Unit ⊕ Unit) := Sum.elim (Sum.inl ∘ Sum.inl) (fun _ => A)
  let ψ : α ⊕ Unit → (α ⊕ Unit) ⊕ (Unit ⊕ Unit) := Sum.elim (Sum.inl ∘ Sum.inl) (fun _ => Bv)
  let pa : Poly ((α ⊕ Unit) ⊕ (Unit ⊕ Unit)) := Poly.proj A
  let pb : Poly ((α ⊕ Unit) ⊕ (Unit ⊕ Unit)) := Poly.proj Bv
  let py : Poly ((α ⊕ Unit) ⊕ (Unit ⊕ Unit)) := Poly.proj Y
  let r1 := (Compiler.Representation.le pb pa).and (Compiler.Representation.eq (py + pb) pa)
  let r2 := (Compiler.Representation.lt pa pb).and (Compiler.Representation.eq py 0)
  let r3 := r1.or r2 (by
    intro x ⟨⟨h1, _⟩, h2, _⟩; exact absurd h1 (not_le.mpr h2))
  let r4 := ((rf.reindex φ).and (rg.reindex ψ)).and r3
  have key : ∀ (z : α ⊕ Unit → ℕ) (y : Unit ⊕ Unit → ℕ),
      ((Sum.elim z y ∘ φ) ∘ Sum.inr = (fun _ => f ((Sum.elim z y ∘ φ) ∘ Sum.inl)) ∧
        (Sum.elim z y ∘ ψ) ∘ Sum.inr = (fun _ => g ((Sum.elim z y ∘ ψ) ∘ Sum.inl))) ↔
      (y (Sum.inl ()) = f (z ∘ Sum.inl) ∧ y (Sum.inr ()) = g (z ∘ Sum.inl)) := by
    intro z y
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨congrFun h1 (), congrFun h2 ()⟩
    · rintro ⟨h1, h2⟩
      exact ⟨funext fun _ => h1, funext fun _ => h2⟩
  let r5 := r4.ex (by
    intro x y y' h h'
    have k := (key x y).mp h.1
    have k' := (key x y').mp h'.1
    funext i
    rcases i with ⟨⟩ | ⟨⟩
    · exact k.1.trans k'.1.symm
    · exact k.2.trans k'.2.symm)
  refine ⟨r5.congr ?_⟩
  intro z
  constructor
  · rintro ⟨y, h1, h3⟩
    have k := (key z y).mp h1
    funext u
    rcases u
    simp only [Function.comp_apply]
    simp only [pa, pb, py, A, Bv, Y, Poly.proj_apply, Poly.add_apply, Poly.zero_apply,
      Sum.elim_inl, Sum.elim_inr] at h3
    have k1 := k.1
    have k2 := k.2
    rw [k1, k2] at h3
    change z (Sum.inr ()) = _
    rcases h3 with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
  · intro hz
    have hz' : z (Sum.inr ()) = f (z ∘ Sum.inl) - g (z ∘ Sum.inl) := congrFun hz ()
    refine ⟨Sum.elim (fun _ => f (z ∘ Sum.inl)) (fun _ => g (z ∘ Sum.inl)),
      (key z _).mpr ⟨rfl, rfl⟩, ?_⟩
    simp only [pa, pb, py, A, Bv, Y, Poly.proj_apply, Poly.add_apply, Poly.zero_apply,
      Sum.elim_inl, Sum.elim_inr]
    rw [hz']
    by_cases hc : g (z ∘ Sum.inl) ≤ f (z ∘ Sum.inl)
    · left; omega
    · right; omega

