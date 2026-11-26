-- Prove2me | solution 1 for KrohnRhodes.covers_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:04:14.970973+00:00
-- url     : https://prove2.me/submissions/dcbeb9d6-8558-47dc-b129-f8491141add4

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
public import Theorems.Thm_KrohnRhodes_krasnerKaloujnine_hom_left
attribute [local simp] KrohnRhodes.constEnd_mul
attribute [local simp] KrohnRhodes.krasnerKaloujnine_hom_left



set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedFintypeInType false
open KrohnRhodes
open Green
namespace KrohnRhodes
theorem _root_.solution {A B P X R : Type} [Monoid A] [Monoid B] [MulAction A P] [MulAction B X]
    (φ : P × X → R) :
    Covers φ (1 : WreathProduct A B X) (1 : Function.End R) := by
  intro p y
  simp only [WreathProduct.one_func, WreathProduct.one_base, one_smul]
  rfl
end KrohnRhodes
