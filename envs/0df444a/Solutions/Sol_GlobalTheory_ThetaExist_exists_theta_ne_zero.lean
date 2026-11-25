-- Prove2me | solution 1 for GlobalTheory.ThetaExist.exists_theta_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:52:28.64689+00:00
-- url     : https://prove2.me/submissions/b9283764-ac4e-4f18-aed7-b7c2aa4e7400

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_HfNegRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_CoeffEqZeroOfOrthonormal
import Theorems.Thm_GlobalTheory_ThetaExist_exists_sec_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
noncomputable section
open GlobalTheory GlobalTheory.ThetaExist
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.ThetaExist
theorem _root_.solution (E : Type) [Field E] [NumberField E] (X : PT E) :
    ∃ s ∈ X.Sec 1 1, s ≠ 0 := by
  let Y : GT (Idx X.dim) :=
    { b := X.b
      integral := X.integral
      perfect := X.perfect
      ka := fun γ => (X.eps γ : ℂ)
      ka_abs := fun x hx => by rcases X.eps_pm x hx with h | h <;> simp [h] }
  have hC : Coc Y 1 := by
    intro γ hγ δ hδ
    obtain ⟨k, hk⟩ := X.integral γ δ hγ hδ
    have h := congrArg (fun r : ℝ => (r : ℂ)) (X.eps_add γ hγ δ hδ)
    change ((X.eps (γ + δ) : ℤ) : ℂ) = (X.eps γ : ℂ) * (X.eps δ : ℂ) * _
    rw [hk] at h ⊢
    have hs : Complex.sin (-(Real.pi * (1 : ℕ) * ((k : ℝ) : ℂ))) = 0 := by
      rw [Complex.sin_neg]
      simpa [mul_comm] using Complex.sin_int_mul_pi k
    rw [Complex.exp_mul_I, hs, Complex.cos_neg]
    simpa using h
  obtain ⟨s, ⟨hd, hs⟩, hne⟩ := exists_sec_ne_zero Y hC
  refine ⟨fun v => s (v 0), ⟨hd.comp (differentiable_apply 0), fun γ hγ v => ?_⟩, fun h => hne ?_⟩
  · have := hs (γ 0) (hγ 0) (v 0)
    simpa [HC, Y] using this
  · funext z
    exact congrFun h fun _ => z
end GlobalTheory.ThetaExist
