-- Prove2me | solution 1 for KrohnRhodes.covers_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:04:20.996283+00:00
-- url     : https://prove2.me/submissions/a6f23259-f85a-46ec-82d3-cc6f8109c4cb

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
public import Theorems.Thm_KrohnRhodes_MonoidDivides_trans


set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedFintypeInType false
open KrohnRhodes
open Green
namespace KrohnRhodes
theorem _root_.solution {A B P X R : Type} [Monoid A] [Monoid B] [MulAction A P] [MulAction B X]
    {φ : P × X → R} (hφ : Function.Surjective φ) {w : WreathProduct A B X}
    {t₁ t₂ : Function.End R} (h₁ : Covers φ w t₁) (h₂ : Covers φ w t₂) :
    t₁ = t₂ := by
  funext r
  obtain ⟨⟨p, y⟩, rfl⟩ := hφ r
  exact (h₁ p y).symm.trans (h₂ p y)
end KrohnRhodes
