-- Prove2me | solution 1 for GlobalTheory.SupNormExample.exists_fnorm_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:00:03.845109+00:00
-- url     : https://prove2.me/submissions/7fef0362-0ceb-4cef-9fac-f893b5efeb3c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ChosenEqOfAllRules

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SupNormExample
open Formalism.L2.Pj
variable {K : Type} [Field K] {ι : Type} [Fintype ι]
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
namespace GlobalTheory.SupNormExample
theorem _root_.solution (σ : K →+* ℂ) (e : ι → ℕ) (i : ι) (hi : e i ≠ 0) (f : Rules pts) :
    ∃ fnorm : pts (CAt σ) → ι → ℝ, (∀ y j, 0 < fnorm y j) ∧ BddAt pts mapR σ fnorm e f ∧
      supAt pts mapR σ fnorm e f ≤ 1 := by
  classical
  let c : pts (CAt σ) → ℝ := fun y => cabs (evalAt pts mapR f y)
  have hc : ∀ y, 0 ≤ c y := fun y => norm_nonneg _
  have h : ∀ y, ptNorm pts mapR σ (fun y _ => 1 + c y) e f y ≤ 1 := fun y => by
    have hp : 0 < 1 + c y := by linarith [hc y]
    have h1 : (1 + c y)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [hc y])
    have h0 : 0 ≤ (1 + c y)⁻¹ := inv_nonneg.2 hp.le
    show c y * ∏ j, |1 + c y|⁻¹ ^ e j ≤ 1
    rw [abs_of_pos hp, Finset.prod_pow_eq_pow_sum]
    have hs : 1 ≤ ∑ j, e j :=
      (Nat.one_le_iff_ne_zero.2 hi).trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
    have h2 : (1 + c y)⁻¹ ^ ∑ j, e j ≤ (1 + c y)⁻¹ := by
      simpa using pow_le_pow_of_le_one h0 h1 hs
    refine (mul_le_mul_of_nonneg_left h2 (hc y)).trans ?_
    rw [← div_eq_mul_inv, div_le_one hp]; linarith
  refine ⟨fun y _ => 1 + c y, fun y _ => by linarith [hc y], ⟨1, ?_⟩, Real.iSup_le h zero_le_one⟩
  rintro _ ⟨y, rfl⟩; exact h y
end GlobalTheory.SupNormExample
