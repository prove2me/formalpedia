-- Prove2me | solution 1 for KrohnRhodes.reset_submonoid_aperiodic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:05:18.811872+00:00
-- url     : https://prove2.me/submissions/d1b6baa0-324a-49ee-b97f-596dd4f7ed27

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
public import Theorems.Thm_KrohnRhodes_mem_reset_submonoid
public import Theorems.Thm_KrohnRhodes_isAperiodicElem_of_id_or_const


set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedFintypeInType false
open KrohnRhodes
open Green
namespace KrohnRhodes
theorem _root_.solution (Q : Type) :
    ∀ a : ↥(resetSubmonoid Q), IsAperiodicElem a := by
  intro a b hab
  exact isAperiodicElem_of_id_or_const (resetSubmonoid Q)
    (fun t ht => (mem_reset_submonoid Q t).mp ht) a b ⟨hab.1, hab.2⟩
end KrohnRhodes
