-- Prove2me | solution 1 for GlobalTheory.PolarisedLattice.exists_posDef_smul_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:27:03.019514+00:00
-- url     : https://prove2.me/submissions/36b1235d-7d18-43a9-9540-80587607415c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open Matrix
open GlobalTheory.PolarisedLattice
namespace GlobalTheory.PolarisedLattice
theorem _root_.solution {ι : Type} [Fintype ι] {N C : Matrix ι ι ℝ} (hN : N.PosDef) (hC : C.IsHermitian) :
    ∃ T₀ : ℝ, ∀ t, T₀ < t → (t • N + C).PosDef := by
  have hp : ∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ N *ᵥ x := fun x hx => by
    simpa using (posDef_iff_dotProduct_mulVec.1 hN).2 hx
  have hc : ContinuousOn (fun x : ι → ℝ => -(x ⬝ᵥ C *ᵥ x) / (x ⬝ᵥ N *ᵥ x)) (Metric.sphere 0 1) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => (hp x ?_).ne'
    rintro rfl; simp at hx
  obtain ⟨T₀, hT⟩ := ((isCompact_sphere (0 : ι → ℝ) 1).image_of_continuousOn hc).bddAbove
  refine ⟨T₀, fun t ht => posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx => ?_⟩⟩
  · refine IsHermitian.add ?_ hC
    rw [IsHermitian, conjTranspose_smul, hN.1]; simp
  · have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
    have h1 := hT ⟨‖x‖⁻¹ • x, by simp [norm_smul, hn.ne'], rfl⟩
    have h2 := hp x hx
    simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at h1
    have h3 : -(‖x‖⁻¹ * (‖x‖⁻¹ * x ⬝ᵥ C *ᵥ x)) / (‖x‖⁻¹ * (‖x‖⁻¹ * x ⬝ᵥ N *ᵥ x)) =
        -(x ⬝ᵥ C *ᵥ x) / (x ⬝ᵥ N *ᵥ x) := by field_simp
    rw [h3, div_le_iff₀ h2] at h1
    simp only [star_trivial, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
    nlinarith
end GlobalTheory.PolarisedLattice
