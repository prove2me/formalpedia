-- Prove2me | solution 1 for KrohnRhodes.exists_minimal_generating
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:32.278254+00:00
-- url     : https://prove2.me/submissions/fcc346ae-c437-4ad4-a7a2-f46071dddcab

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
theorem _root_.solution (M : Type) [Monoid M] [Finite M] [DecidableEq M] :
    ∃ A : Finset M, Submonoid.closure (A : Set M) = ⊤ ∧
      ∀ a ∈ A, Submonoid.closure ((A.erase a : Finset M) : Set M) ≠ ⊤ := by
  classical
  cases nonempty_fintype M
  have hex : ∃ n : ℕ, ∃ A : Finset M, A.card = n ∧ Submonoid.closure (A : Set M) = ⊤ :=
    ⟨(Finset.univ : Finset M).card, Finset.univ, rfl, by
      rw [Finset.coe_univ, Submonoid.closure_univ]⟩
  obtain ⟨A, hcard, hA⟩ := Nat.find_spec hex
  refine ⟨A, hA, fun a ha hcl => ?_⟩
  have hlt : (A.erase a).card < Nat.find hex := by
    rw [← hcard]; exact Finset.card_erase_lt_of_mem ha
  exact Nat.find_min hex hlt ⟨A.erase a, rfl, hcl⟩
end KrohnRhodes
