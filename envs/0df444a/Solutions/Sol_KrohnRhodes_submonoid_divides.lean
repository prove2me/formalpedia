-- Prove2me | solution 1 for KrohnRhodes.submonoid_divides
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:15.528681+00:00
-- url     : https://prove2.me/submissions/15482ba8-0886-43e7-b474-6cb3c80981f4

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
theorem _root_.solution {M : Type} [Monoid M] (N : Submonoid M) :
    KrohnRhodes.MonoidDivides ↥N M := by
  exact ⟨N, MonoidHom.id ↥N, Function.surjective_id⟩
end KrohnRhodes
