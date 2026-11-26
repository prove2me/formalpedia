-- Prove2me | solution 1 for KrohnRhodes.monoidDivides_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:59:10.957567+00:00
-- url     : https://prove2.me/submissions/628bcd5b-6535-422f-ab15-a5eff90a8bc7

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
theorem _root_.solution {M N : Type u} [Monoid M] [Monoid N]
    (φ : M →* N) (hφ : Function.Surjective φ) :
    KrohnRhodes.MonoidDivides N M :=
  ⟨⊤, φ.comp (⊤ : Submonoid M).subtype, fun n => by
    obtain ⟨m, rfl⟩ := hφ n; exact ⟨⟨m, Submonoid.mem_top m⟩, rfl⟩⟩
end KrohnRhodes
