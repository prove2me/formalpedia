-- Prove2me | solution 1 for KrohnRhodes.subFactorsDivide_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:03:07.346942+00:00
-- url     : https://prove2.me/submissions/1a37eacd-dc54-4132-88d9-cdd245fc7e38

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
theorem _root_.solution {M : Type u} [Monoid M]
    {towA towB : List KRFactor.{u}}
    (hA : SubFactorsDivide M towA) (hB : SubFactorsDivide M towB) :
    SubFactorsDivide M (towA ++ towB) := by
  intro F hF
  rcases List.mem_append.mp hF with h | h
  · exact hA F h
  · exact hB F h
end KrohnRhodes
