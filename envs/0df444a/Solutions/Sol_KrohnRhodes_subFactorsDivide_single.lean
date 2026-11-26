-- Prove2me | solution 1 for KrohnRhodes.subFactorsDivide_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:02:57.960879+00:00
-- url     : https://prove2.me/submissions/2cd401c0-2327-4901-bb11-11ae7520e553

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
theorem _root_.solution {M : Type u} [Monoid M] (F : KRFactor.{u})
    (h : KrohnRhodes.MonoidDivides F.carrier M) :
    SubFactorsDivide M [F] := by
  intro G hG; rw [List.mem_singleton] at hG; subst hG; exact h
end KrohnRhodes
