-- Prove2me | solution 1 for GlobalTheory.SharpObj.form_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:47:04.563917+00:00
-- url     : https://prove2.me/submissions/e8524134-22c4-431d-a0ed-af8e53cd9f9e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ImInvIsHermitian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SharpObj
variable {h : ℕ}
variable {τ : Matrix (Fin h) (Fin h) ℂ}
namespace GlobalTheory.SharpObj
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] (s : Set V) (hs : Submodule.span ℝ s = ⊤)
    (B : V → V → ℂ) (h1 : ∀ z z' w, B (z + z') w = B z w + B z' w) (h2 : ∀ z w w', B z (w + w') = B z w + B z w')
    (h3 : ∀ (c : ℂ) z w, B (c • z) w = c * B z w) (h4 : ∀ (c : ℝ) z w, B z ((c : ℂ) • w) = c * B z w)
    (h0 : ∀ z ∈ s, ∀ w ∈ s, (B z w).im = 0) (z w : V) : B z w = 0 := by
  have hB0r : ∀ z, B z 0 = 0 := fun z => by
    have := h2 z 0 0
    simpa using this
  have hB0l : ∀ w, B 0 w = 0 := fun w => by
    have := h1 0 0 w
    simpa using this
  have step1 : ∀ z ∈ s, ∀ w, (B z w).im = 0 := by
    intro z hz w
    have hw : w ∈ Submodule.span ℝ s := by rw [hs]; exact Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem w hw => exact h0 z hz w hw
    | zero => simp [hB0r]
    | add w w' _ _ ihw ihw' => rw [h2, Complex.add_im, ihw, ihw', add_zero]
    | smul c w _ ihw => rw [← Complex.coe_smul, h4, Complex.im_ofReal_mul, ihw, mul_zero]
  have step2 : ∀ z w, (B z w).im = 0 := by
    intro z w
    have hz : z ∈ Submodule.span ℝ s := by rw [hs]; exact Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz => exact step1 z hz w
    | zero => simp [hB0l]
    | add z z' _ _ ihz ihz' => rw [h1, Complex.add_im, ihz, ihz', add_zero]
    | smul c z _ ihz => rw [← Complex.coe_smul, h3, Complex.im_ofReal_mul, ihz, mul_zero]
  apply Complex.ext
  · have := step2 (Complex.I • z) w
    rw [h3] at this
    simpa using this
  · simpa using step2 z w
end GlobalTheory.SharpObj
