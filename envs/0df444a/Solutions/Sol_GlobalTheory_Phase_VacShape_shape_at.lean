-- Prove2me | solution 1 for GlobalTheory.Phase.VacShape.shape_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:20:25.075007+00:00
-- url     : https://prove2.me/submissions/05fa79b3-2edd-4d8b-8250-6b252a00eb4f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsExOfPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SelfDualVacuumGaussianShapeRootOfUnityPhases
import Theorems.Thm_GlobalTheory_Phase_VacShape_isMu_mul
import Theorems.Thm_GlobalTheory_Phase_VacShape_isMu_ex
import Theorems.Thm_P2M_GlobalTheory_Phase_VacShape_semi__f1f6dd4150d6
import Theorems.Thm_GlobalTheory_Phase_VacShape_isMu_eps
import Theorems.Thm_GlobalTheory_SW_Vac_ex_add
import Theorems.Thm_GlobalTheory_SW_Vac_ex_two_eq_one
import Theorems.Thm_GlobalTheory_SW_Vac_exists_lift
import Theorems.Thm_GlobalTheory_SW_Vac_fac_add
import Theorems.Thm_GlobalTheory_SW_Vac_fixed_iff
import Theorems.Thm_GlobalTheory_SW_Vac_om_eq
import Theorems.Thm_GlobalTheory_SW_Vac_pr_add_left
import Theorems.Thm_GlobalTheory_SW_Vac_pr_add_right
import Theorems.Thm_GlobalTheory_SW_Vac_pr_sub_left
import Theorems.Thm_GlobalTheory_SW_Vac_pr_zero_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.VacShape
open GlobalTheory.SW.Vac
variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
  {A : AddSubgroup (Matrix κ ι ℚ × Matrix κ ι ℚ)} {ε : Matrix κ ι ℚ × Matrix κ ι ℚ → ℂ}
  {φ : Matrix κ ι ℚ → ℂ}
namespace GlobalTheory.Phase.VacShape
theorem _root_.solution (h : VacS A ε φ) (a : Matrix κ ι ℚ) (ha : φ a ≠ 0) :
    ∃ (S : AddSubgroup (Matrix κ ι ℚ)) (f : Matrix κ ι ℚ → ℂ), Quad S f ∧
      ∀ x, (x - a ∈ S → φ x = φ a * f (x - a)) ∧ (x - a ∉ S → φ x = 0) := by
  have hfix : ∀ y ∈ A, ∀ x, fac ε y x * φ (x - y.2) = φ x := fun y hy =>
    (fixed_iff ε y φ).1 (h.fix y hy)
  let f : Matrix κ ι ℚ → ℂ := fun b => φ (a + b) / φ a
  have hf : ∀ y ∈ A, f y.2 = fac ε y (a + y.2) := by
    intro y hy
    simp only [f]
    rw [← hfix y hy (a + y.2), add_sub_cancel_right, mul_div_cancel_right₀ _ ha]
  have hadd : ∀ y ∈ A, ∀ y' ∈ A, f (y.2 + y'.2) = f y.2 * f y'.2 * ex (2 * pr y'.2 y.1) := by
    intro y hy y' hy'
    have := hf _ (A.add_mem hy hy')
    rw [Prod.snd_add, fac_add (semi' h y hy y' hy')] at this
    rw [this, hf y hy, hf y' hy', show a + (y.2 + y'.2) - y.2 = a + y'.2 by abel, mul_right_comm]
    congr 1
    unfold fac
    rw [mul_assoc, ← ex_add]
    congr 2
    simp only [pr_add_left]; ring
  refine ⟨A.map (AddMonoidHom.snd _ _), f, ⟨?_, ?_⟩, fun x => ⟨fun _ => ?_, fun hx => ?_⟩⟩
  · rintro _ ⟨y, hy, rfl⟩
    change IsMu (f y.2)
    rw [hf y hy]
    exact isMu_mul (isMu_eps h hy) (isMu_ex _)
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    change f (x.2 + y.2 + z.2) * f x.2 * f y.2 * f z.2 =
      f (x.2 + y.2) * f (y.2 + z.2) * f (x.2 + z.2) * f 0
    have h0 : f 0 = 1 := by simp [f, ha]
    have h1 := hadd _ (A.add_mem hx hy) z hz
    rw [Prod.snd_add, Prod.fst_add, pr_add_right, mul_add, ex_add] at h1
    rw [h1, hadd y hy z hz, hadd x hx z hz, h0]
    ring
  · simp only [f]
    rw [add_sub_cancel, mul_div_cancel₀ _ ha]
  · by_contra hne
    apply hx
    have hd : ∀ y, y ∈ A ↔ ∀ y' ∈ A, ∃ m : ℤ, pr y.1 y'.2 - pr y'.1 y.2 = m := by
      intro y
      simpa only [om, om_eq] using h.dual y
    have key : ∀ b, (b, 0) ∈ A → ∀ w, φ w ≠ 0 → ε (b, 0) * ex (2 * pr w b) = 1 := by
      intro b hb w hw
      have h1 := hfix _ hb w
      simp only [sub_zero, fac, pr_zero_right] at h1
      apply mul_right_cancel₀ hw; rw [h1, one_mul]
    obtain ⟨b, hb⟩ := exists_lift A h.fg hd (x - a) fun b hb => by
      have h2 := key b hb x hne
      have h3 := key b hb a ha
      apply ex_two_eq_one
      calc _ = ε (b, 0) * ex (2 * pr a b) * ex (2 * pr (x - a) b) := by rw [h3, one_mul]
        _ = ε (b, 0) * ex (2 * pr x b) := by
          rw [mul_assoc, ← ex_add, pr_sub_left]; congr 2; ring
        _ = 1 := h2
    exact ⟨_, hb, rfl⟩
end GlobalTheory.Phase.VacShape
