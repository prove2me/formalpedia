-- Prove2me | solution 1 for KrohnRhodes.quotientGroup_divides
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:02:44.498536+00:00
-- url     : https://prove2.me/submissions/bbc58d67-6182-4a62-b622-5da7cf3558ac

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
public import Theorems.Thm_KrohnRhodes_monoidDivides_of_surjective

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
theorem _root_.solution {G : Type u} [Group G] (N : Subgroup G) [N.Normal] :
    KrohnRhodes.MonoidDivides (G ⧸ N) G :=
  monoidDivides_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
end KrohnRhodes
