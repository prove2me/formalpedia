-- Prove2me | solution 1 for GlobalTheory.isOpen_posDef_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:04:49.205799+00:00
-- url     : https://prove2.me/submissions/50cd1d67-98b0-4c4f-b246-b0b9487b71cb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsOpenPosDefOfContinuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X n : Type} [TopologicalSpace X] [Fintype n]
    (M : X → Matrix n n ℝ) (hc : Continuous M) (hs : ∀ x, (M x).IsHermitian) :
    IsOpen {x | (M x).PosDef} := by
  rw [isOpen_iff_mem_nhds]
  intro x₀ hx₀
  have hK : IsCompact (Metric.sphere (0 : n → ℝ) 1) := isCompact_sphere _ _
  have hcont : Continuous (fun p : X × (n → ℝ) => dotProduct (star p.2) ((M p.1).mulVec p.2)) :=
    (continuous_snd.star).dotProduct ((hc.comp continuous_fst).matrix_mulVec continuous_snd)
  have hev : ∀ᶠ x in nhds x₀, ∀ v ∈ Metric.sphere (0 : n → ℝ) 1,
      0 < dotProduct (star v) ((M x).mulVec v) := by
    apply hK.eventually_forall_of_forall_eventually
    intro v hv
    have hv0 : v ≠ 0 := by
      rintro rfl
      simp at hv
    have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hx₀).2 hv0
    exact (isOpen_lt continuous_const hcont).mem_nhds hpos
  filter_upwards [hev] with x hx
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hs x, fun v hv => ?_⟩
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h1 := hx (‖v‖⁻¹ • v) (by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne'])
  simp only [star_trivial, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h1 ⊢
  have hi : 0 < ‖v‖⁻¹ := inv_pos.mpr hn
  exact (mul_pos_iff_of_pos_left hi).mp ((mul_pos_iff_of_pos_left hi).mp h1)
end GlobalTheory
