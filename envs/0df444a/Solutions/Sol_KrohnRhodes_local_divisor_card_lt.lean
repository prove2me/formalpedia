-- Prove2me | solution 1 for KrohnRhodes.local_divisor_card_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:04:28.300819+00:00
-- url     : https://prove2.me/submissions/3114a9e2-33b2-48cf-a951-2c2f163cc6f9

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
theorem _root_.solution {M : Type} [Monoid M] [Finite M] {c : M} (hc : ¬ IsUnit c) :
    Nat.card (LocalDivisor M c) < Nat.card M := by
  have hone : ∀ x : LocalDivisor M c, x.val ≠ 1 := by
    intro x hx
    obtain ⟨a, ha⟩ := x.mem_left
    obtain ⟨b, hb⟩ := x.mem_right
    have h1 : c * a = 1 := by rw [← ha]; exact hx
    have h2 : b * c = 1 := by rw [← hb]; exact hx
    have h3 : a * c = 1 := by
      have hba : b = a := by
        calc b = b * (c * a) := by rw [h1, mul_one]
          _ = b * c * a := by rw [mul_assoc]
          _ = a := by rw [h2, one_mul]
      rw [← hba]; exact h2
    exact hc ⟨⟨c, a, h1, h3⟩, rfl⟩
  have : Fintype M := Fintype.ofFinite M
  have : Fintype (LocalDivisor M c) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  refine Fintype.card_lt_of_injective_of_notMem (LocalDivisor.val (c := c))
    (fun _ _ h => LocalDivisor.ext h) (b := 1) ?_
  rintro ⟨x, hx⟩
  exact hone x hx
end KrohnRhodes
