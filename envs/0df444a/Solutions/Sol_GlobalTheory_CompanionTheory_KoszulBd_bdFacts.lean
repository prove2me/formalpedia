-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KoszulBd.bdFacts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:05:09.382279+00:00
-- url     : https://prove2.me/submissions/f8e592b1-deee-41f5-9177-54884d146a25

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CommuteOfUnitaryConjugate
import Theorems.Thm_GlobalTheory_CompanionTheory_KoszulBd_sum_pick
import Theorems.Thm_GlobalTheory_CompanionTheory_KoszulBd_sq_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_KoszulBd_commute_of_unitary_conjugate
import Theorems.Thm_GlobalTheory_CompanionTheory_KoszulBd_comm_ann
import Theorems.Thm_GlobalTheory_CompanionTheory_KoszulBd_comm_cre
import Theorems.Thm_GlobalTheory_CompanionTheory_KoszulBd_lift_ann
import Theorems.Thm_GlobalTheory_CompanionTheory_KoszulBd_lift_cre
import Theorems.Thm_GlobalTheory_CompanionTheory_KoszulBd_lift_Gop
import Theorems.Thm_GlobalTheory_CompanionTheory_KoszulBd_glRel_lift
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
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.KoszulBd
theorem _root_.solution : CAR → BdFacts := by
  intro hCAR n ε V _ _ E hE
  have hAA : ∀ i j : NC ε, ann i * ann j + ann j * ann i = (0 : Module.End ℂ (Ch ε V)) :=
    fun i j => (hCAR n ε V i j).1
  have hCC : ∀ i j : NC ε, cre i * cre j + cre j * cre i = (0 : Module.End ℂ (Ch ε V)) :=
    fun i j => (hCAR n ε V i j).2.1
  have hAC : ∀ i j : NC ε, ann i * cre j + cre j * ann i = (if i = j then 1 else 0 : Module.End ℂ (Ch ε V)) :=
    fun i j => (hCAR n ε V i j).2.2
  have hGl := glRel_lift (ε := ε) E hE
  have hLL : ∀ i j : NC ε,
      Commute (lift ε (E i.1.1 i.1.2) : Module.End ℂ (Ch ε V)) (lift ε (E j.1.1 j.1.2)) := by
    intro i j
    have h1 : i.1.2 ≠ j.1.1 := by
      intro h'
      have a := i.2.2
      rw [h', j.2.1] at a
      exact absurd a (by decide)
    have h2 : j.1.2 ≠ i.1.1 := by
      intro h'
      have a := j.2.2
      rw [h', i.2.1] at a
      exact absurd a (by decide)
    have h := hGl i.1.1 i.1.2 j.1.1 j.1.2
    rw [if_neg h1, if_neg h2, sub_zero, sub_eq_zero] at h
    exact h
  refine ⟨sq_zero (fun i : NC ε => (lift ε (E i.1.1 i.1.2) : Module.End ℂ (Ch ε V))) ann hLL
    (fun i j => lift_ann _ j) hAA, ?_⟩
  intro c d hcd
  let qG : NC ε → NC ε → ℂ := fun i j =>
    (if i.1.1 = c ∧ j.1.1 = d ∧ i.1.2 = j.1.2 then 1 else 0) -
      (if i.1.2 = d ∧ j.1.2 = c ∧ i.1.1 = j.1.1 then 1 else 0)
  have hGop : Gop ε c d = ∑ i, ∑ j, qG i j • (cre i * ann j : Module.End ℂ (Ch ε V)) := rfl
  have hdiff : ∀ X Y : Module.End ℂ (Ch ε V), X - Y + (Y - X) = 0 := fun X Y => by abel
  constructor
  · show Commute (lift ε (E c d) + Gop ε c d) (∑ i, lift ε (E i.1.1 i.1.2) * ann i)
    refine commute_of_unitary_conjugate (lift ε (E c d)) (Gop ε c d)
      (fun k : NC ε => (lift ε (E k.1.1 k.1.2) : Module.End ℂ (Ch ε V))) ann
      (fun k => lift_ann _ k) (fun k => lift_Gop _ c d) ?_
    beta_reduce
    have hrow : ∀ k : NC ε, (lift ε (E c d) : Module.End ℂ (Ch ε V)) * lift ε (E k.1.1 k.1.2)
        - lift ε (E k.1.1 k.1.2) * lift ε (E c d)
        = (if d = k.1.1 then lift ε (E c k.1.2) else 0) - (if k.1.2 = c then lift ε (E k.1.1 d) else 0) :=
      fun k => hGl c d k.1.1 k.1.2
    have hcomm : ∀ k : NC ε, (Gop ε c d : Module.End ℂ (Ch ε V)) * ann k - ann k * Gop ε c d = -∑ j, qG k j • ann j := by
      intro k
      rw [hGop]
      exact comm_ann ann cre qG hAA hAC k
    have hsecond : ∑ k : NC ε, (lift ε (E k.1.1 k.1.2) : Module.End ℂ (Ch ε V)) * -∑ j : NC ε, qG k j • ann j
        = -∑ j : NC ε, (∑ k : NC ε, qG k j • (lift ε (E k.1.1 k.1.2) : Module.End ℂ (Ch ε V))) * ann j := by
      simp_rw [mul_neg, Finset.mul_sum, Finset.sum_neg_distrib, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
      rw [Finset.sum_comm]
    have hpick : ∀ j : NC ε, ∑ k : NC ε, qG k j • (lift ε (E k.1.1 k.1.2) : Module.End ℂ (Ch ε V))
        = (if d = j.1.1 then lift ε (E c j.1.2) else 0) - (if j.1.2 = c then lift ε (E j.1.1 d) else 0) := by
      intro j
      simp only [qG, sub_smul, Finset.sum_sub_distrib]
      congr 1
      · exact sum_pick (fun x y => (lift ε (E x y) : Module.End ℂ (Ch ε V))) c j.1.2 (d = j.1.1)
          (fun h => ⟨hcd.trans (h ▸ j.2.1), j.2.2⟩) _
          (fun k => ⟨fun h => ⟨h.2.1.symm, h.1, h.2.2⟩, fun h => ⟨h.2.1, h.1.symm, h.2.2⟩⟩)
      · exact sum_pick (fun x y => (lift ε (E x y) : Module.End ℂ (Ch ε V))) j.1.1 d (j.1.2 = c)
          (fun h => ⟨j.2.1, hcd.symm.trans (h ▸ j.2.2)⟩) _
          (fun k => ⟨fun h => ⟨h.2.1, h.2.2, h.1⟩, fun h => ⟨h.2.2, h.1, h.2.1⟩⟩)
    simp_rw [hrow, hcomm]
    rw [hsecond]
    simp_rw [hpick]
    exact add_neg_cancel _
  · show Commute (lift ε (E c d) + Gop ε c d) (∑ i, lift ε (E i.1.2 i.1.1) * cre i)
    refine commute_of_unitary_conjugate (lift ε (E c d)) (Gop ε c d)
      (fun k : NC ε => (lift ε (E k.1.2 k.1.1) : Module.End ℂ (Ch ε V))) cre
      (fun k => lift_cre _ k) (fun k => lift_Gop _ c d) ?_
    beta_reduce
    have hrow : ∀ k : NC ε, (lift ε (E c d) : Module.End ℂ (Ch ε V)) * lift ε (E k.1.2 k.1.1)
        - lift ε (E k.1.2 k.1.1) * lift ε (E c d)
        = (if d = k.1.2 then lift ε (E c k.1.1) else 0) - (if k.1.1 = c then lift ε (E k.1.2 d) else 0) :=
      fun k => hGl c d k.1.2 k.1.1
    have hcomm : ∀ k : NC ε, (Gop ε c d : Module.End ℂ (Ch ε V)) * cre k - cre k * Gop ε c d = ∑ i, qG i k • cre i := by
      intro k
      rw [hGop]
      exact comm_cre ann cre qG hCC hAC k
    have hsecond : ∑ k : NC ε, (lift ε (E k.1.2 k.1.1) : Module.End ℂ (Ch ε V)) * ∑ i : NC ε, qG i k • cre i
        = ∑ i : NC ε, (∑ k : NC ε, qG i k • (lift ε (E k.1.2 k.1.1) : Module.End ℂ (Ch ε V))) * cre i := by
      simp_rw [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
      rw [Finset.sum_comm]
    have hpick : ∀ i : NC ε, ∑ k : NC ε, qG i k • (lift ε (E k.1.2 k.1.1) : Module.End ℂ (Ch ε V))
        = (if i.1.1 = c then lift ε (E i.1.2 d) else 0) - (if d = i.1.2 then lift ε (E c i.1.1) else 0) := by
      intro i
      simp only [qG, sub_smul, Finset.sum_sub_distrib]
      congr 1
      · exact sum_pick (fun x y => (lift ε (E y x) : Module.End ℂ (Ch ε V))) d i.1.2 (i.1.1 = c)
          (fun h => ⟨hcd.symm.trans (h ▸ i.2.1), i.2.2⟩) _
          (fun k => ⟨fun h => ⟨h.1, h.2.1, h.2.2.symm⟩, fun h => ⟨h.1, h.2.1, h.2.2.symm⟩⟩)
      · exact sum_pick (fun x y => (lift ε (E y x) : Module.End ℂ (Ch ε V))) i.1.1 c (d = i.1.2)
          (fun h => ⟨i.2.1, hcd.trans (h ▸ i.2.2)⟩) _
          (fun k => ⟨fun h => ⟨h.1.symm, h.2.2.symm, h.2.1⟩, fun h => ⟨h.1.symm, h.2.2, h.2.1.symm⟩⟩)
    simp_rw [hrow, hcomm]
    rw [hsecond]
    simp_rw [hpick]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← add_mul, hdiff, zero_mul]
end GlobalTheory.CompanionTheory.KoszulBd
