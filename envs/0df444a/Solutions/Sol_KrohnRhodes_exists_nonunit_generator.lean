-- Prove2me | solution 1 for KrohnRhodes.exists_nonunit_generator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:32.82183+00:00
-- url     : https://prove2.me/submissions/8ce9cb50-8aae-4c8b-9835-8eafca8168c9

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
theorem _root_.solution {M : Type} [Monoid M] {A : Finset M}
    (hA : Submonoid.closure (A : Set M) = ⊤) (hM : ∃ m : M, ¬ IsUnit m) :
    ∃ c ∈ A, ¬ IsUnit c := by
  by_contra h
  push Not at h
  obtain ⟨m, hm⟩ := hM
  refine hm ?_
  clear hm
  have hmem : m ∈ Submonoid.closure (A : Set M) := by
    rw [hA]; exact Submonoid.mem_top m
  induction hmem using Submonoid.closure_induction with
  | mem x hx => exact h x hx
  | one => exact isUnit_one
  | mul x y hx hy ihx ihy => exact ihx.mul ihy
end KrohnRhodes
