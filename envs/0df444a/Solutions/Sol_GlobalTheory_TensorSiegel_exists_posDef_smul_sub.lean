-- Prove2me | solution 1 for GlobalTheory.TensorSiegel.exists_posDef_smul_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:27:34.547004+00:00
-- url     : https://prove2.me/submissions/70037bb5-f0e6-4a4f-b045-84c458b18988

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_BijectiveTensorOmegaStd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.PTheta Matrix
open scoped Kronecker
noncomputable section
open GlobalTheory GlobalTheory.TensorSiegel
variable {ι : Type*} [Fintype ι]
namespace GlobalTheory.TensorSiegel
theorem _root_.solution {G B : Matrix ι ι ℝ} (hG : G.PosDef) (hB : B.IsHermitian) :
    ∃ κ₀ : ℕ, ∀ κ : ℕ, κ₀ ≤ κ → ((κ : ℝ) • G - B).PosDef := by
  have hp : ∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ G *ᵥ x := fun x hx => by
    simpa using hG.dotProduct_mulVec_pos hx
  have hne : ∀ x ∈ Metric.sphere (0 : ι → ℝ) 1, x ≠ 0 := by
    rintro x hx rfl
    simp at hx
  have hc : ContinuousOn (fun x : ι → ℝ => (x ⬝ᵥ B *ᵥ x) / (x ⬝ᵥ G *ᵥ x)) (Metric.sphere 0 1) := by
    refine ContinuousOn.div (Continuous.continuousOn ?_) (Continuous.continuousOn ?_)
      fun x hx => (hp x (hne x hx)).ne'
    · exact continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
    · exact continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
  obtain ⟨C, hC⟩ := ((isCompact_sphere (0 : ι → ℝ) 1).image_of_continuousOn hc).bddAbove
  obtain ⟨κ₀, hκ₀⟩ := exists_nat_gt C
  refine ⟨κ₀, fun κ hκ => ?_⟩
  have hκ' : C < κ := hκ₀.trans_le (by exact_mod_cast hκ)
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · refine IsHermitian.sub ?_ hB
    rw [IsHermitian, conjTranspose_smul, hG.isHermitian.eq, star_trivial]
  · have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hs : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : ι → ℝ) 1 := by
      simp [norm_smul, hn.ne']
    have h1 := hC ⟨_, hs, rfl⟩
    simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h1
    rw [mul_div_mul_left _ _ (inv_pos.2 hn).ne', mul_div_mul_left _ _ (inv_pos.2 hn).ne',
      div_le_iff₀ (hp x hx)] at h1
    have h2 := mul_lt_mul_of_pos_right hκ' (hp x hx)
    rw [star_trivial, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    linarith
end GlobalTheory.TensorSiegel
