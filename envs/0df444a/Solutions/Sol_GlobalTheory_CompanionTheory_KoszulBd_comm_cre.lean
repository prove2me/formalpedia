-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KoszulBd.comm_cre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:48:24.683159+00:00
-- url     : https://prove2.me/submissions/ce66c645-78d9-4880-b314-451c89dba3e3

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
theorem _root_.solution (A C : ι → R) (q : ι → ι → ℂ) (hCC : ∀ i j, C i * C j + C j * C i = 0)
    (hAC : ∀ i j, A i * C j + C j * A i = if i = j then 1 else 0) (k : ι) :
    (∑ i, ∑ j, q i j • (C i * A j)) * C k - C k * (∑ i, ∑ j, q i j • (C i * A j)) = ∑ i, q i k • C i := by
  have hterm : ∀ i j, (q i j • (C i * A j)) * C k - C k * (q i j • (C i * A j))
      = if j = k then q i j • C i else 0 := by
    intro i j
    have h1 : C k * C i = -(C i * C k) := eq_neg_of_add_eq_zero_left (hCC k i)
    have h2 : A j * C k = (if j = k then 1 else 0) - C k * A j := eq_sub_of_add_eq (hAC j k)
    have h3 : C i * A j * C k - C k * (C i * A j) = if j = k then C i else 0 := by
      rw [mul_assoc, h2, ← mul_assoc (C k), h1]
      split_ifs <;> noncomm_ring
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, h3]
    split_ifs <;> simp
  have hrow : ∀ i, (∑ j, q i j • (C i * A j)) * C k - C k * (∑ j, q i j • (C i * A j)) = q i k • C i := by
    intro i
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_congr rfl fun j _ => hterm i j]
    simp
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => hrow i
end GlobalTheory.CompanionTheory.KoszulBd
