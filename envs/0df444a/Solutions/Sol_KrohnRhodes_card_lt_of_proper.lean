-- Prove2me | solution 1 for KrohnRhodes.card_lt_of_proper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:35.908673+00:00
-- url     : https://prove2.me/submissions/b4573430-8c7a-4d5c-9af0-3234acd7ff4d

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
public import Theorems.Thm_KrohnRhodes_MonoidDivides_trans


set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedFintypeInType false
open KrohnRhodes
open Green
namespace KrohnRhodes
theorem _root_.solution {M : Type} [Monoid M] [Finite M] {N : Submonoid M}
    (hN : N ≠ ⊤) : Nat.card ↥N < Nat.card M := by
  have hssub : (N : Set M) ⊂ Set.univ :=
    Set.ssubset_univ_iff.mpr fun h =>
      hN (SetLike.coe_set_eq.mp (h.trans Submonoid.coe_top.symm))
  have hlt := Set.Finite.card_lt_card Set.finite_univ hssub
  rwa [Nat.card_univ] at hlt
end KrohnRhodes
