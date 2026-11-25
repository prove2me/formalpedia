-- Prove2me | solution 1 for GlobalTheory.IsogenySum.mem_lattice_of_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:28:07.434846+00:00
-- url     : https://prove2.me/submissions/715b3846-bb47-4b00-b137-3f46ab93c4c3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FockTranslationLaws
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ContinuousThetaSectionPointwiseNormSq
import Theorems.Thm_GlobalTheory_IsogenySum_eq_zero_of_im_lattice
import Theorems.Thm_GlobalTheory_FockTranslation_herm_add_left
import Theorems.Thm_GlobalTheory_FockTranslation_herm_add_right
import Theorems.Thm_GlobalTheory_FockTranslation_herm_im_swap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Complex ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory
open GlobalTheory.IsogenySum
open FockTranslation
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.IsogenySum
theorem _root_.solution (Y : GT ι) {a : EuclideanSpace ℂ ι}
    (h : ∀ y ∈ lat Y.b, ∃ k : ℤ, (Hf y a).im = k) : a ∈ lat Y.b := by
  have hfl : ∀ y ∈ lat Y.b, ((⌊(Hf y a).im⌋ : ℤ) : ℝ) = (Hf y a).im := by
    intro y hy
    obtain ⟨k, hk⟩ := h y hy
    rw [hk, Int.floor_intCast]
  let φ : lat Y.b →+ ℤ :=
    { toFun := fun y => ⌊(Hf (y : EuclideanSpace ℂ ι) a).im⌋
      map_zero' := by simp [Hf]
      map_add' := by
        intro y y'
        apply Int.cast_injective (α := ℝ)
        push_cast
        rw [hfl _ ((lat Y.b).add_mem y.2 y'.2), hfl _ y.2, hfl _ y'.2, herm_add_left,
          Complex.add_im] }
  obtain ⟨x0, hx0, hφ⟩ := Y.perfect φ
  have h0 : a + x0 = 0 := by
    apply eq_zero_of_im_lattice Y
    intro y hy
    have := hφ ⟨y, hy⟩
    simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
    rw [hfl y hy] at this
    rw [herm_add_right, Complex.add_im, this, herm_im_swap x0 y]
    ring
  have : a = -x0 := eq_neg_of_add_eq_zero_left h0
  rw [this]
  exact (lat Y.b).neg_mem hx0
end GlobalTheory.IsogenySum
