-- Prove2me | solution 1 for KrohnRhodes.mem_reset_submonoid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:03:29.266824+00:00
-- url     : https://prove2.me/submissions/9bc71a52-8c51-441c-9b65-ff1ab78e498d

module
public import Definitions.Def_KrohnRhodes_Defs
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Definitions.Def_KrohnRhodes_Foundations_LocalDivisor
public import Definitions.Def_KrohnRhodes_Foundations_ConstantMaps
public import Definitions.Def_KrohnRhodes_Foundations_Division
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Definitions.Def_KrohnRhodes_FactorTower
public import Definitions.Def_KrohnRhodes_PrimeDecomposition
public import Theorems.Thm_KrohnRhodes_constEnd_mul
public import Theorems.Thm_KrohnRhodes_isConstEnd_constEnd
attribute [local simp] KrohnRhodes.constEnd_mul



set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedFintypeInType false
open KrohnRhodes
open Green
namespace KrohnRhodes
theorem _root_.solution (Q : Type) (t : Function.End Q) :
    t ∈ resetSubmonoid Q ↔ t = 1 ∨ IsConstEnd t := by
  constructor
  · intro ht
    induction ht using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨q, rfl⟩ := hx
      exact Or.inr (isConstEnd_constEnd q)
    | one => exact Or.inl rfl
    | mul x y _ _ ihx ihy =>
      rcases ihx with rfl | ⟨p, rfl⟩
      · rw [one_mul]; exact ihy
      · exact Or.inr ⟨p, constEnd_mul p y⟩
  · rintro (rfl | ⟨q, rfl⟩)
    · exact one_mem _
    · exact Submonoid.subset_closure ⟨q, rfl⟩
end KrohnRhodes
