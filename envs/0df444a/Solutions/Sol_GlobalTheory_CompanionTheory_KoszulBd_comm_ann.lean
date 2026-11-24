-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KoszulBd.comm_ann
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:48:23.41316+00:00
-- url     : https://prove2.me/submissions/9dd60f11-7e7b-40d3-bf2f-2614bafc8480

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CommuteOfUnitaryConjugate
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KoszulBd
open CompanionTheory.D.DSIC
open Formalism.REAL (GlRel)
variable {n : ℕ} {ε : Fin n → Bool}
variable {ι R : Type} [Fintype ι] [DecidableEq ι] [Ring R] [Algebra ℂ R]
namespace GlobalTheory.CompanionTheory.KoszulBd
theorem _root_.solution (A C : ι → R) (q : ι → ι → ℂ) (hAA : ∀ i j, A i * A j + A j * A i = 0)
    (hAC : ∀ i j, A i * C j + C j * A i = if i = j then 1 else 0) (k : ι) :
    (∑ i, ∑ j, q i j • (C i * A j)) * A k - A k * (∑ i, ∑ j, q i j • (C i * A j)) = -∑ j, q k j • A j := by
  have hterm : ∀ i j, (q i j • (C i * A j)) * A k - A k * (q i j • (C i * A j))
      = -(if k = i then q i j • A j else 0) := by
    intro i j
    have h1 : A j * A k = -(A k * A j) := eq_neg_of_add_eq_zero_left (hAA j k)
    have h2 : A k * C i = (if k = i then 1 else 0) - C i * A k := eq_sub_of_add_eq (hAC k i)
    have h3 : C i * A j * A k - A k * (C i * A j) = -(if k = i then A j else 0) := by
      rw [mul_assoc, h1, ← mul_assoc (A k), h2]
      split_ifs <;> noncomm_ring
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, h3]
    split_ifs <;> simp
  have hrow : ∀ i, (∑ j, q i j • (C i * A j)) * A k - A k * (∑ j, q i j • (C i * A j))
      = ∑ j, -(if k = i then q i j • A j else 0) := by
    intro i
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => hterm i j
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_congr rfl fun i _ => hrow i]
  rw [Finset.sum_eq_single k]
  · simp [Finset.sum_neg_distrib]
  · intro i _ hik
    simp [Ne.symm hik]
  · intro h
    exact absurd (Finset.mem_univ k) h
end GlobalTheory.CompanionTheory.KoszulBd
