-- Prove2me | solution 1 for KrohnRhodes.monoidDivides_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:02:38.186798+00:00
-- url     : https://prove2.me/submissions/3b5fac29-edec-4ed9-b8ae-dcf992295ee3

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
theorem _root_.solution {G : Type u} [Group G] (N : Subgroup G) :
    KrohnRhodes.MonoidDivides (N : Type u) G :=
  ⟨N.toSubmonoid, MonoidHom.id _, fun x => ⟨x, rfl⟩⟩
end KrohnRhodes
