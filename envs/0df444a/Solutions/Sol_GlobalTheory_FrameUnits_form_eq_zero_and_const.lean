-- Prove2me | solution 1 for GlobalTheory.FrameUnits.form_eq_zero_and_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:48:27.304549+00:00
-- url     : https://prove2.me/submissions/e7ba90eb-ce88-425d-b85c-40754b6e2b6c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertDataOfIsoCube
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TripleProductTorusPeriodicBounded
import Theorems.Thm_GlobalTheory_FrameUnits_exists_le_of_periodic
import Theorems.Thm_GlobalTheory_FrameUnits_weight_nonneg_of_periodic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open GlobalTheory.JetSer (IsNormRos primφ primε)
open GlobalTheory.CubeValues GlobalTheory.AppellHumbertTrivial
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.FrameUnits
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
namespace GlobalTheory.FrameUnits
theorem _root_.solution {S : Set E} {R : ℝ} (hS : ∀ z, ∃ l ∈ S, ‖z + l‖ ≤ R)
    (ψ : E → ℂ) (hψ : Differentiable ℂ ψ) (h0 : ∀ z, ψ z ≠ 0)
    (D : E → E → ℂ) (hc : Continuous fun z => D z z)
    (hadd : ∀ z z' w, D (z + z') w = D z w + D z' w)
    (hsm : ∀ (t : ℂ) z w, D (t • z) w = t * D z w)
    (hst : ∀ z w, D w z = star (D z w))
    (hper : ∀ l ∈ S, ∃ ρ : ℂ, ‖ρ‖ = 1 ∧ ∀ z, ψ (z + l) = ρ * cexp (π * D z l + π / 2 * D l l) * ψ z) :
    (∀ z w, D z w = 0) ∧ ∀ z, ψ z = ψ 0 := by
  have hre : ∀ z w, (D w z).re = (D z w).re := fun z w => by rw [hst z w]; simp
  have hsq : ∀ z l, (D (z + l) (z + l)).re = (D z z).re + 2 * (D z l).re + (D l l).re := by
    intro z l
    rw [hadd, Complex.add_re, hre (z + l) z, hre (z + l) l, hadd, hadd, Complex.add_re,
      Complex.add_re, hre z l]
    ring
  let q : E → ℝ := fun z => π / 2 * (D z z).re
  have hq : Continuous q := continuous_const.mul (Complex.continuous_re.comp hc)
  have hs : ∀ (t : ℂ) w, q (t • w) = ‖t‖ ^ 2 * q w := fun t w => by
    have : D (t • w) (t • w) = ((‖t‖ ^ 2 : ℝ) : ℂ) * D w w := by
      rw [hsm, hst (t • w) w, hsm, star_mul', ← hst w w, ← _root_.mul_assoc, Complex.star_def,
        Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [q]
    rw [this, Complex.re_ofReal_mul]
    ring
  have hn : ∀ l ∈ S, ∀ z, ‖ψ (z + l)‖ = Real.exp (q (z + l) - q z) * ‖ψ z‖ := fun l hl z => by
    obtain ⟨ρ, hρ, h⟩ := hper l hl
    rw [h, norm_mul, norm_mul, hρ, _root_.one_mul, Complex.norm_exp]
    congr 2
    simp only [q, hsq]
    have e : (π : ℂ) / 2 = ((π / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    ring
  have h1 := weight_nonneg_of_periodic hS ψ hψ (h0 0) q hq hs (fun l hl z => by
    rw [hn l hl z, mul_right_comm, ← Real.exp_add, mul_comm]
    congr 2
    ring)
  have h2 := weight_nonneg_of_periodic hS (fun z => (ψ z)⁻¹) (hψ.inv h0) (inv_ne_zero (h0 0))
    (fun z => -q z) hq.neg (fun t w => by rw [hs]; ring) (fun l hl z => by
    rw [norm_inv, norm_inv, hn l hl z, mul_inv, mul_right_comm, ← Real.exp_neg, ← Real.exp_add,
      mul_comm]
    congr 2
    ring)
  have h3 : ∀ z, (D z z).re = 0 := fun z => by
    have : q z = 0 := le_antisymm (by linarith [h2 z]) (h1 z)
    simpa [q, Real.pi_ne_zero] using this
  have h4 : ∀ z w, (D z w).re = 0 := fun z w => by
    have := hsq z w
    rw [h3, h3, h3] at this
    linarith
  refine ⟨fun z w => ?_, fun z => ?_⟩
  · refine Complex.ext (h4 z w) ?_
    have := h4 (I • z) w
    rw [hsm] at this
    simpa using this
  · obtain ⟨C, hC⟩ := exists_le_of_periodic hS (fun z => ‖ψ z‖) hψ.continuous.norm
      (fun l hl z => by simp [hn l hl z, q, h3])
    refine hψ.apply_eq_apply_of_bounded (isBounded_iff_forall_norm_le.2 ⟨C, ?_⟩) z 0
    rintro _ ⟨z, rfl⟩
    exact hC z
end GlobalTheory.FrameUnits
