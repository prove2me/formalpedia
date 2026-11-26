-- Prove2me | solution 1 for KrohnRhodes.closure_monoid_gen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:04:00.384581+00:00
-- url     : https://prove2.me/submissions/063d7922-b3d6-42e6-8df4-b86074f58446

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
    (A : Set M) (hA : Submonoid.closure A = ⊤) :
    Submonoid.closure ((⇑act) '' A ∪ Set.range (constEnd : Q → Function.End Q)) =
      closureMonoid act := by
  have h1 : Submonoid.closure ((⇑act) '' A) = MonoidHom.mrange act := by
    rw [← MonoidHom.map_mclosure, hA, ← MonoidHom.mrange_eq_map]
  have h2 : Submonoid.closure (Set.range ⇑act) = MonoidHom.mrange act := by
    rw [← MonoidHom.coe_mrange, Submonoid.closure_eq]
  rw [closureMonoid, Submonoid.closure_union, Submonoid.closure_union, h1, h2]
end KrohnRhodes
