-- Prove2me | solution 1 for GlobalTheory.ZetaWide.scaled
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:28:47.657793+00:00
-- url     : https://prove2.me/submissions/beff8de7-a065-4a23-93cf-d20209fd0ed8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormSubOneMulRiemannZetaLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TsumOneDivRpowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormOneSubConjMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ImportsMore
import Theorems.Thm_GlobalTheory_LogDerivZeros_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.ZetaWide
namespace GlobalTheory.ZetaWide
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ (F : ℂ → ℂ) (c : ℂ) (M : ℝ), Differentiable ℂ F → F c ≠ 0 →
    (∀ w, ‖w - c‖ ≤ 15/4 → ‖F w‖ ≤ M) →
    ({w : ℂ | ‖w - c‖ ≤ 7/2 ∧ F w = 0}.Finite ∧
      (∑ᶠ w ∈ {w : ℂ | ‖w - c‖ ≤ 7/2 ∧ F w = 0}, (analyticOrderNatAt F w : ℝ))
        ≤ C * (1 + Real.log (M / ‖F c‖))) ∧
    ∀ s : ℂ, ‖s - c‖ ≤ 3 → F s ≠ 0 →
      ‖deriv F s / F s - ∑ᶠ w ∈ {w : ℂ | ‖w - c‖ ≤ 7/2 ∧ F w = 0},
        (analyticOrderNatAt F w : ℂ) / (s - w)‖ ≤ C * (1 + Real.log (M / ‖F c‖)) := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.LogDerivZeros.main (4/5) (14/15) (by norm_num) (by norm_num)
    (by norm_num)
  refine ⟨C, hC, fun F c M hF hc hM => ?_⟩
  set g : ℂ → ℂ := fun z => c + 15/4 * z with hg
  have hgn : ∀ z, ‖g z - c‖ = 15/4 * ‖z‖ := fun z => by simp [hg]
  have hgd : ∀ z, HasDerivAt g (15/4) z := fun z => by
    have := ((hasDerivAt_id z).const_mul (15/4 : ℂ)).const_add c
    rw [mul_one] at this
    exact this
  have hgD : Differentiable ℂ g := fun z => (hgd z).differentiableAt
  have hfD : Differentiable ℂ (F ∘ g) := hF.comp hgD
  have hg0 : g 0 = c := by simp [hg]
  have hf0 : (F ∘ g) 0 = F c := by simp [hg0]
  obtain ⟨⟨h1, h2⟩, h3⟩ := H (F ∘ g) M (fun z _ => hfD.analyticAt z) (by rwa [hf0])
    (fun z hz => hM _ (by
      have : ‖z‖ ≤ 1 := by simpa using hz
      rw [hgn]; linarith))
  rw [hf0] at h2 h3
  have hinj : Function.Injective g := fun a b h => by simpa [hg] using h
  have hsur : ∀ w, g ((w - c) * (4/15)) = w := fun w => by simp only [hg]; ring
  have hset : {w : ℂ | ‖w - c‖ ≤ 7/2 ∧ F w = 0} = g '' {w : ℂ | ‖w‖ ≤ 14/15 ∧ (F ∘ g) w = 0} := by
    ext w
    constructor
    · rintro ⟨ha, hb⟩
      refine ⟨(w - c) * (4/15), ⟨?_, by simp only [Function.comp, hsur, hb]⟩, hsur w⟩
      have := hgn ((w - c) * (4/15))
      rw [hsur] at this
      linarith
    · rintro ⟨z, ⟨ha, hb⟩, rfl⟩
      exact ⟨by rw [hgn]; linarith, hb⟩
  have hord : ∀ z, analyticOrderNatAt (F ∘ g) z = analyticOrderNatAt F (g z) := fun z => by
    unfold analyticOrderNatAt
    rw [analyticOrderAt_comp_of_deriv_ne_zero (hgD.analyticAt z) (by rw [(hgd z).deriv]; norm_num)]
  simp only [hord] at h2 h3
  rw [hset]
  refine ⟨⟨h1.image g, by rwa [finsum_mem_image hinj.injOn]⟩, fun s hs hFs => ?_⟩
  obtain ⟨z, rfl⟩ : ∃ z, s = g z := ⟨_, (hsur s).symm⟩
  rw [hgn] at hs
  have h4 := h3 z (by linarith) hFs
  have hL : 0 ≤ C * (1 + Real.log (M / ‖F c‖)) := (norm_nonneg _).trans h4
  rw [finsum_mem_image hinj.injOn]
  rw [finsum_mem_eq_finite_toFinset_sum _ h1] at h4 ⊢
  have hd : deriv (F ∘ g) z = deriv F (g z) * (15/4) :=
    ((hF (g z)).hasDerivAt.comp z (hgd z)).deriv
  have e : deriv F (g z) / F (g z) - ∑ w ∈ h1.toFinset, (analyticOrderNatAt F (g w) : ℂ) / (g z - g w)
      = (4/15) * (deriv (F ∘ g) z / (F ∘ g) z -
        ∑ w ∈ h1.toFinset, (analyticOrderNatAt F (g w) : ℂ) / (z - w)) := by
    rw [hd, mul_sub, Finset.mul_sum]
    congr 1
    · simp only [Function.comp]; ring
    · refine Finset.sum_congr rfl fun w _ => ?_
      have : g z - g w = 15/4 * (z - w) := by simp only [hg]; ring
      rw [this, div_eq_mul_inv, mul_inv]
      ring
  rw [e, norm_mul]
  have : ‖(4/15 : ℂ)‖ = 4/15 := by simp
  rw [this]
  linarith
end GlobalTheory.ZetaWide
