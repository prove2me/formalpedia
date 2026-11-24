-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSICKoszul.koszul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:07:01.808878+00:00
-- url     : https://prove2.me/submissions/78fdb8f6-61fc-43a8-abb7-8c2afa1b3f10

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MemFiltOfWords
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICKoszul_homotopy_ring
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICKoszul_sq_ring
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICKoszul_filt_mono
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICKoszul_mem_filt_of_words
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICKoszul_euler_filt
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICKoszul_lift_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICKoszul_ann_lift
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICKoszul_cre_lift
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICKoszul_number_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICKoszul_deg_h
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSICKoszul
open CompanionTheory.D.DSIC
variable {n : ℕ} {ε : Fin n → Bool} {Z : Type} [AddCommGroup Z] [Module ℂ Z]
namespace GlobalTheory.CompanionTheory.DSICKoszul
theorem _root_.solution : CAR → Koszul := by
  intro hC n ε Z _ _ a d ha hd hda hnil j x hx hcyc
  set H : Module.End ℂ (Ch ε Z) := ∑ i : NC ε, (lift ε (d i) : Module.End ℂ (Ch ε Z)) * cre i with hH
  have hom : bdA a * H + H * bdA a =
      ∑ i, (lift ε (a i) : Module.End ℂ (Ch ε Z)) * lift ε (d i) + ∑ i, cre i * ann i := by
    refine homotopy_ring (fun i => (lift ε (a i) : Module.End ℂ (Ch ε Z))) (fun i => lift ε (d i)) ann cre
      (fun i j => ann_lift _ _) (fun i j => cre_lift _ _) (fun i j => ?_) (fun i j => (hC n ε Z i j).2.2)
    refine LinearMap.ext fun y => funext fun A => ?_
    have e := congrArg (fun T : Module.End ℂ Z => T (y A)) (hda i j)
    by_cases h : i = j
    · simpa [h] using e
    · simpa [h] using e
  have hsq : ∀ y : Ch ε Z, bdA a (bdA a y) = 0 := by
    intro y
    have e : bdA a * bdA a + bdA a * bdA a = 0 :=
      sq_ring (fun i => (lift ε (a i) : Module.End ℂ (Ch ε Z))) ann (fun i j => ann_lift _ _)
        (fun i j => by
          show lift ε (a i) * lift ε (a j) = lift ε (a j) * lift ε (a i)
          rw [← lift_mul, ← lift_mul, (ha i j).eq]) (fun i j => (hC n ε Z i j).1)
    have e2 := congrArg (fun T : Module.End ℂ (Ch ε Z) => T y) e
    simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply] at e2
    rw [← two_smul ℂ] at e2
    exact (smul_eq_zero.mp e2).resolve_left two_ne_zero
  have main : ∀ (m : ℕ) (y : Ch ε Z), (∀ A, y A ∈ filt d m) → Deg (j + 1) y → bdA a y = 0 →
      ∃ t : Ch ε Z, Deg (j + 2) t ∧ bdA a t = y := by
    intro m
    induction m with
    | zero =>
      intro y hy _ _
      refine ⟨0, fun _ _ => rfl, ?_⟩
      rw [map_zero]
      funext A
      simpa [filt, eq_comm] using hy A
    | succ m ih =>
      intro y hy hdeg hc
      have hne : ((m : ℂ) + (j + 1 : ℕ)) ≠ 0 := by
        exact_mod_cast (by omega : m + (j + 1) ≠ 0)
      have hw : ∀ A, (bdA a (H y) - ((m : ℂ) + (j + 1 : ℕ)) • y) A =
          (∑ i, a i * d i) (y A) - (m : ℂ) • y A := by
        intro A
        have e := congrArg (fun T : Module.End ℂ (Ch ε Z) => T y A) hom
        simp only [LinearMap.add_apply, Module.End.mul_apply, hc, map_zero, Pi.add_apply, Pi.zero_apply, add_zero,
          number_apply] at e
        have e2 : (A.card : ℂ) • y A = ((j + 1 : ℕ) : ℂ) • y A := by
          by_cases h : A.card = j + 1
          · rw [h]
          · rw [hdeg A h, smul_zero, smul_zero]
        have e3 : ((∑ i, (lift ε (a i) : Module.End ℂ (Ch ε Z)) * lift ε (d i)) y) A =
            (∑ i, a i * d i) (y A) := by
          rw [LinearMap.sum_apply, Finset.sum_apply, LinearMap.sum_apply]
          rfl
        rw [Pi.sub_apply, e, e2, e3, Pi.smul_apply, add_smul]
        abel
      obtain ⟨t, ht, hbt⟩ := ih (bdA a (H y) - ((m : ℂ) + (j + 1 : ℕ)) • y)
        (fun A => by rw [hw]; exact euler_filt a d hd hda m _ (hy A))
        (fun A hA => by rw [hw, hdeg A hA]; simp)
        (by rw [map_sub, hsq, map_smul, hc]; simp)
      refine ⟨((m : ℂ) + (j + 1 : ℕ))⁻¹ • (H y - t), fun A hA => ?_, ?_⟩
      · have := deg_h d (j + 1) y hdeg A hA
        rw [Pi.smul_apply, Pi.sub_apply, ht A hA, this]
        simp
      · rw [map_smul, map_sub, hbt, sub_sub_cancel, smul_smul, inv_mul_cancel₀ hne, one_smul]
  choose f hf using hnil
  refine main (univ.sup fun A => f (x A)) x (fun A => ?_) hx hcyc
  exact filt_mono d (Finset.le_sup (f := fun A => f (x A)) (mem_univ A)) (mem_filt_of_words d _ _ (hf _))
end GlobalTheory.CompanionTheory.DSICKoszul
