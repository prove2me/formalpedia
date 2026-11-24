-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSVerma.glRel_abstract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:05:07.658379+00:00
-- url     : https://prove2.me/submissions/d786d847-2fb8-4103-8252-be6b881b38a4

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_KummerLiftedCocycleImageEqPicardClass
import Theorems.Thm_GlobalTheory_CompanionTheory_DSVerma_inner_sum
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
theorem _root_.solution (hYY : ∀ i j, Commute (Y i) (Y j))
    (huu : ∀ a b c d, Commute (u a b) (u c d)) (huv : ∀ a b c d, Commute (u a b) (v c d))
    (hvv : ∀ a b c d, Commute (v a b) (v c d))
    (huY : ∀ a c j, u a c * Y j - Y j * u a c = -(if a = j.1.1 ∧ c = j.1.2 then 1 else 0))
    (hvY : ∀ a c j, v a c * Y j - Y j * v a c = if a = j.1.1 ∧ c = j.1.2 then 1 else 0)
    (hs : ∀ d e, (if ε d = true then u d e else 0) + (if ε e = false then v d e else 0) =
      if d = e then 1 else 0) (c d e f : Fin n) :
    (∑ i : NC ε, Y i * (u i.1.1 c * v d i.1.2)) * (∑ i : NC ε, Y i * (u i.1.1 e * v f i.1.2)) -
      (∑ i : NC ε, Y i * (u i.1.1 e * v f i.1.2)) * (∑ i : NC ε, Y i * (u i.1.1 c * v d i.1.2)) =
      (if d = e then ∑ i : NC ε, Y i * (u i.1.1 c * v f i.1.2) else 0) -
        (if f = c then ∑ i : NC ε, Y i * (u i.1.1 e * v d i.1.2) else 0) := by
  have hprod : ∀ p q : NC ε → R, (∑ i, Y i * p i) * (∑ j, Y j * q j) =
      ∑ i, ∑ j, Y i * Y j * (p i * q j) + ∑ i, Y i * ∑ j, (p i * Y j - Y j * p i) * q j := by
    intro p q
    rw [Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    noncomm_ring
  rw [hprod, hprod]
  have hsym : (∑ i : NC ε, ∑ j : NC ε, Y i * Y j * (u i.1.1 c * v d i.1.2 * (u j.1.1 e * v f j.1.2))) =
      ∑ i : NC ε, ∑ j : NC ε, Y i * Y j * (u i.1.1 e * v f i.1.2 * (u j.1.1 c * v d j.1.2)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [(hYY j i).eq, (((huu _ _ _ _).mul_right (huv _ _ _ _)).mul_left
      ((huv _ _ _ _).symm.mul_right (hvv _ _ _ _))).eq]
  rw [hsym, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  have key : ∀ i : NC ε,
      Y i * (∑ j : NC ε, ((u i.1.1 c * v d i.1.2) * Y j - Y j * (u i.1.1 c * v d i.1.2)) * (u j.1.1 e * v f j.1.2)) -
      Y i * (∑ j : NC ε, ((u i.1.1 e * v f i.1.2) * Y j - Y j * (u i.1.1 e * v f i.1.2)) * (u j.1.1 c * v d j.1.2)) =
      (if d = e then Y i * (u i.1.1 c * v f i.1.2) else 0) -
        (if f = c then Y i * (u i.1.1 e * v d i.1.2) else 0) := by
    intro i
    rw [inner_sum Y u v huY hvY, inner_sum Y u v huY hvY]
    have e1 : ∀ c d e f : Fin n, v d i.1.2 * u i.1.1 e * (if ε c = false then v f c else 0) =
        u i.1.1 e * (if ε c = false then v f c else 0) * v d i.1.2 := by
      intro c d e f
      split_ifs
      · rw [mul_assoc]
        exact ((huv _ _ _ _).symm.mul_right (hvv _ _ _ _)).eq
      · simp
    rw [e1, e1]
    have h1 := hs d e
    have h2 := hs f c
    generalize (if ε d = true then u d e else 0) = A at *
    generalize (if ε e = false then v d e else 0) = B at *
    generalize (if ε f = true then u f c else 0) = C at *
    generalize (if ε c = false then v f c else 0) = D at *
    calc _ = Y i * (u i.1.1 c * (A + B) * v f i.1.2) - Y i * (u i.1.1 e * (C + D) * v d i.1.2) := by noncomm_ring
      _ = _ := by rw [h1, h2]; split_ifs <;> simp
  simp only [key, Finset.sum_sub_distrib]
  split_ifs <;> simp
end GlobalTheory.CompanionTheory.DSVerma
