-- Prove2me | solution 1 for GlobalTheory.UnitLemma.CayleyCase.val_res_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:06:11.357148+00:00
-- url     : https://prove2.me/submissions/c1ff4821-1292-4c0b-b74c-88c212cba754

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyMulLeftSeparableOfAdjoinEqTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley
import Theorems.Thm_GlobalTheory_T_card_stable_lattices_alt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.CayleyCase
namespace GlobalTheory.UnitLemma.CayleyCase
theorem _root_.solution {O E A₁ A₂ : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A₁]
    [CommRing A₂] [Algebra E A₁] [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁]
    [IsScalarTower O E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ Y₁ : A₁) (g₂ Y₂ : A₂)
    (hr : resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly ≠ 0)
    (hr' : resultant (LinearMap.mulLeft E Y₁).charpoly (LinearMap.mulLeft E Y₂).charpoly ≠ 0)
    (h₁ : ∀ L : Submodule O A₁, (∀ y ∈ L, g₁ * y ∈ L) ↔ (∀ y ∈ L, Y₁ * y ∈ L))
    (h₂ : ∀ L : Submodule O A₂, (∀ y ∈ L, g₂ * y ∈ L) ↔ (∀ y ∈ L, Y₂ * y ∈ L))
    (h : ∀ L : Submodule O (A₁ × A₂), (∀ y ∈ L, (g₁, g₂) * y ∈ L) ↔ (∀ y ∈ L, (Y₁, Y₂) * y ∈ L))
    (M₁ : Submodule O A₁) (M₂ : Submodule O A₂) (l₁ : IsLat O E M₁) (l₂ : IsLat O E M₂)
    (s₁ : ∀ y ∈ M₁, g₁ * y ∈ M₁) (s₂ : ∀ y ∈ M₂, g₂ * y ∈ M₂) :
    val O (resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly) =
      val O (resultant (LinearMap.mulLeft E Y₁).charpoly (LinearMap.mulLeft E Y₂).charpoly) := by
  have c1 := GlobalTheory.T.card_stable_lattices_alt O E A₁ A₂ g₁ g₂ hr M₁ M₂ l₁ l₂ s₁ s₂
  have c2 := GlobalTheory.T.card_stable_lattices_alt O E A₁ A₂ Y₁ Y₂ hr' M₁ M₂ l₁ l₂ ((h₁ M₁).1 s₁) ((h₂ M₂).1 s₂)
  have hc : Nat.card {M : Submodule O (A₁ × A₂) // (∀ y ∈ M, (g₁, g₂) * y ∈ M) ∧
      M.comap (LinearMap.inl O A₁ A₂) = M₁ ∧ M.map (LinearMap.snd O A₁ A₂) = M₂} =
      Nat.card {M : Submodule O (A₁ × A₂) // (∀ y ∈ M, (Y₁, Y₂) * y ∈ M) ∧
      M.comap (LinearMap.inl O A₁ A₂) = M₁ ∧ M.map (LinearMap.snd O A₁ A₂) = M₂} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun M => by rw [h M])
  rw [hc, c2] at c1
  have hq : (1 : ℚ) < Nat.card (IsLocalRing.ResidueField O) := by
    exact_mod_cast (Finite.one_lt_card (α := IsLocalRing.ResidueField O))
  exact (zpow_right_injective₀ (by linarith) hq.ne' c1).symm
end GlobalTheory.UnitLemma.CayleyCase
