-- Prove2me | solution 1 for KrohnRhodes.covers_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:04:16.799712+00:00
-- url     : https://prove2.me/submissions/becd6ce9-4162-49d4-a361-56e86dad87ec

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

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedFintypeInType false
open KrohnRhodes
open Green
namespace KrohnRhodes
theorem _root_.solution {A B P X R : Type} [Monoid A] [Monoid B] [MulAction A P] [MulAction B X]
    (φ : P × X → R) {w₁ w₂ : WreathProduct A B X} {t₁ t₂ : Function.End R}
    (h₁ : Covers φ w₁ t₁) (h₂ : Covers φ w₂ t₂) :
    Covers φ (w₁ * w₂) (t₁ * t₂) := by
  intro p y
  calc φ ((w₁ * w₂).func y • p, (w₁ * w₂).base • y)
      = φ (w₁.func (w₂.base • y) • (w₂.func y • p), w₁.base • (w₂.base • y)) := by
        rw [WreathProduct.mul_func, WreathProduct.mul_base, mul_smul, mul_smul]
    _ = t₁ (φ (w₂.func y • p, w₂.base • y)) := h₁ (w₂.func y • p) (w₂.base • y)
    _ = t₁ (t₂ (φ (p, y))) := congrArg t₁ (h₂ p y)
    _ = (t₁ * t₂) (φ (p, y)) := rfl
end KrohnRhodes
