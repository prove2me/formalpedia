-- Prove2me | solution 1 for KrohnRhodes.dks_proj_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:05:25.367612+00:00
-- url     : https://prove2.me/submissions/3c6b2381-46ea-4275-92d4-99432774b151

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
theorem _root_.solution {M Q : Type} [Monoid M] [Nonempty Q]
    (act : M →* Function.End Q) (c : M) (N : Submonoid M) :
    Function.Surjective (dksProj act c N) := by
  intro q
  obtain ⟨q₀⟩ := ‹Nonempty Q›
  exact ⟨(⟨act c q₀, q₀, rfl⟩, Sum.inl q), rfl⟩
end KrohnRhodes
