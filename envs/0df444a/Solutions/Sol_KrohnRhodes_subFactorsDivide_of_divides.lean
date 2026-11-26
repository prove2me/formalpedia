-- Prove2me | solution 1 for KrohnRhodes.subFactorsDivide_of_divides
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:03:03.085122+00:00
-- url     : https://prove2.me/submissions/df375f59-90a4-43d4-8bd3-e41e89f0b8a5

module
public import Definitions.Def_KrohnRhodes_Defs
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Definitions.Def_KrohnRhodes_Foundations_LocalDivisor
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Definitions.Def_KrohnRhodes_Foundations_Division
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Definitions.Def_KrohnRhodes_Foundations_Cayley
public import Definitions.Def_KrohnRhodes_Foundations_ConstantMaps
public import Definitions.Def_KrohnRhodes_FactorTower
public import Theorems.Thm_KrohnRhodes_MonoidDivides_trans


set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.style.show false
set_option linter.unusedSectionVars false
universe u
open Green
open KrohnRhodes
open Green
namespace KrohnRhodes
theorem _root_.solution {A M : Type u} [Monoid A] [Monoid M]
    (hAM : KrohnRhodes.MonoidDivides A M)
    {factors : List KRFactor.{u}} (h : SubFactorsDivide A factors) :
    SubFactorsDivide M factors :=
  fun F hF => (h F hF).trans hAM
end KrohnRhodes
