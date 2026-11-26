-- Prove2me | solution 1 for KrohnRhodes.ext_act_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:05:24.846809+00:00
-- url     : https://prove2.me/submissions/fed7d230-608d-4f05-8d3f-ac8c297d5acf

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
theorem _root_.solution {M Q : Type} [Monoid M] (act : M →* Function.End Q)
    (N : Submonoid M) : Function.Injective (extAct act N) := by
  intro n₁ n₂ h
  have h2 : (Sum.inr (n₁ * 1) : Q ⊕ ↥N) = Sum.inr (n₂ * 1) :=
    congrFun h (Sum.inr (1 : ↥N))
  rw [mul_one, mul_one] at h2
  exact Sum.inr_injective h2
end KrohnRhodes
