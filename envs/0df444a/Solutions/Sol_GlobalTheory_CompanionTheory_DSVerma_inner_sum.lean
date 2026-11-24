-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSVerma.inner_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:45:14.291309+00:00
-- url     : https://prove2.me/submissions/87549139-d626-4b0f-a6a0-5f5b7c009fea

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_KummerLiftedCocycleImageEqPicardClass
import Theorems.Thm_GlobalTheory_CompanionTheory_DSVerma_sum_nc
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSVerma
open CompanionTheory.D.DSIC Formalism.REAL
variable {n : ℕ} {ε : Fin n → Bool}
variable {R : Type} [Ring R] (Y : NC ε → R) (u v : Fin n → Fin n → R)
namespace GlobalTheory.CompanionTheory.DSVerma
theorem _root_.solution
    (huY : ∀ a c j, u a c * Y j - Y j * u a c = -(if a = j.1.1 ∧ c = j.1.2 then 1 else 0))
    (hvY : ∀ a c j, v a c * Y j - Y j * v a c = if a = j.1.1 ∧ c = j.1.2 then 1 else 0)
    (i : NC ε) (c d e f : Fin n) :
    (∑ j : NC ε, ((u i.1.1 c * v d i.1.2) * Y j - Y j * (u i.1.1 c * v d i.1.2)) * (u j.1.1 e * v f j.1.2)) =
      u i.1.1 c * (if ε d = true then u d e else 0) * v f i.1.2 -
        v d i.1.2 * u i.1.1 e * (if ε c = false then v f c else 0) := by
  have h1 : ∀ j : NC ε, ((u i.1.1 c * v d i.1.2) * Y j - Y j * (u i.1.1 c * v d i.1.2)) * (u j.1.1 e * v f j.1.2) =
      (if d = j.1.1 ∧ i.1.2 = j.1.2 then u i.1.1 c * u j.1.1 e * v f j.1.2 else 0) -
        (if i.1.1 = j.1.1 ∧ c = j.1.2 then v d i.1.2 * u j.1.1 e * v f j.1.2 else 0) := by
    intro j
    have : (u i.1.1 c * v d i.1.2) * Y j - Y j * (u i.1.1 c * v d i.1.2) =
        u i.1.1 c * (v d i.1.2 * Y j - Y j * v d i.1.2) + (u i.1.1 c * Y j - Y j * u i.1.1 c) * v d i.1.2 := by
      noncomm_ring
    rw [this, huY, hvY]
    split_ifs <;> noncomm_ring
  simp only [h1, Finset.sum_sub_distrib]
  rw [sum_nc d i.1.2 (fun a b => u i.1.1 c * u a e * v f b),
    sum_nc i.1.1 c (fun a b => v d i.1.2 * u a e * v f b)]
  simp only [i.2.1, i.2.2, and_true, true_and]
  split_ifs <;> simp
end GlobalTheory.CompanionTheory.DSVerma
