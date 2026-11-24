-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSICFRel.bil_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:43:49.765002+00:00
-- url     : https://prove2.me/submissions/a254571c-9cb7-457a-a341-36502d2e3c25

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CarImpFrel
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICFRel_pair_comm
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
open Finset CompanionTheory.D.DSIC
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSICFRel
namespace GlobalTheory.CompanionTheory.DSICFRel
theorem _root_.solution {ι A : Type} [Fintype ι] [DecidableEq ι] [Ring A] [Algebra ℂ A] (c a : ι → A)
    (haa : ∀ i j, a i * a j + a j * a i = 0) (hcc : ∀ i j, c i * c j + c j * c i = 0)
    (hac : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (m m' : ι → ι → ℂ) :
    bil c a m * bil c a m' - bil c a m' * bil c a m =
      bil c a (fun i l => ∑ k, m i k * m' k l - ∑ k, m' i k * m k l) := by
  have e1 : bil c a m * bil c a m' =
      ∑ i, ∑ j, ∑ k, ∑ l, (m i j * m' k l) • ((c i * a j) * (c k * a l)) := by
    unfold bil
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_smul_comm]
  have e2 : bil c a m' * bil c a m =
      ∑ i, ∑ j, ∑ k, ∑ l, (m i j * m' k l) • ((c k * a l) * (c i * a j)) := by
    unfold bil
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_smul_comm, mul_comm (m' k l)]
  have e3 : ∑ i, ∑ j, ∑ k, ∑ l, (m i j * m' k l) • (if j = k then c i * a l else 0) =
      ∑ i, ∑ l, (∑ k, m i k * m' k l) • (c i * a l) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.sum_smul]
    rw [Finset.sum_comm (f := fun l k => (m i k * m' k l) • (c i * a l))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    simp
  have e4 : ∑ i, ∑ j, ∑ k, ∑ l, (m i j * m' k l) • (if l = i then c k * a j else 0) =
      ∑ i, ∑ l, (∑ k, m' i k * m k l) • (c i * a l) := by
    have : ∀ i j k, ∑ l, (m i j * m' k l) • (if l = i then c k * a j else 0) =
        (m' k i * m i j) • (c k * a j) := by
      intro i j k
      simp [mul_comm]
    simp only [this, Finset.sum_smul]
    calc ∑ i, ∑ j, ∑ k, (m' k i * m i j) • (c k * a j)
        = ∑ j, ∑ i, ∑ k, (m' k i * m i j) • (c k * a j) := Finset.sum_comm
      _ = ∑ j, ∑ k, ∑ i, (m' k i * m i j) • (c k * a j) :=
          Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [e1, e2]
  simp only [← Finset.sum_sub_distrib, ← smul_sub, pair_comm c a haa hcc hac]
  simp only [smul_sub, Finset.sum_sub_distrib, e3, e4, bil, sub_smul]
end GlobalTheory.CompanionTheory.DSICFRel
