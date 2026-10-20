-- Prove2me | solution 2 for OAI.Cotype.exists_geometric_levels
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:50:55.430539+00:00
-- url     : https://prove2.me/submissions/a7c760a0-250b-4699-a591-daca455e72dc

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/GeometricTypeLevels.lean:L19-L47
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.exists_geometric_levels. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Definitions.Def_OAI_Analysis_Cotype_SectorResolvent
import Definitions.Def_OAI_Analysis_Cotype_FiniteContour
import Definitions.Def_OAI_Analysis_Cotype_NoiseHypercontractivity
import Definitions.Def_OAI_Analysis_Cotype_QuadraticTypeTensor
import Definitions.Def_OAI_Analysis_Cotype_WalshAmplification
import Definitions.Def_OAI_Analysis_Cotype_FiniteL2Dual
import Definitions.Def_OAI_Analysis_Cotype_DualMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteSupDual
import Definitions.Def_OAI_Analysis_Cotype_PrimalMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_CotypeAmplification
import Definitions.Def_OAI_Analysis_Cotype_TypeCotypeDuality

-- ---- from OAI.Analysis.Cotype.GeometricTypeLevels ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

omit [NormedSpace ℝ X] in

theorem exists_geometric_levels {N : ℕ} {r : ℝ} (hr : 1 < r)
    (x : Fin N → X) (hx : ∀ i, ‖x i‖ ≤ 1) :
    ∃ l : Fin N → ℕ, ∀ i, ‖x i‖ ≤ (r⁻¹)^(l i) ∧
      (x i ≠ 0 → (r⁻¹)^(l i+1) < ‖x i‖) := by
  classical
  have hr0 : 0 < r := by linarith
  have hq : r⁻¹ < 1 := (inv_lt_one₀ hr0).mpr hr
  have hq0 : 0 < r⁻¹ := inv_pos.mpr hr0
  have heach i : ∃ k : ℕ, ‖x i‖ ≤ (r⁻¹)^k ∧ (x i ≠ 0 → (r⁻¹)^(k+1) < ‖x i‖) := by
    by_cases hz : x i = 0
    · exact ⟨0,by simpa using hx i,fun hh => (hh hz).elim⟩
    have hex : ∃ k : ℕ, (r⁻¹)^(k+1) < ‖x i‖ := by
      obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.mpr hz) hq
      exact ⟨k,(by calc
        (r⁻¹)^(k+1) = (r⁻¹)^k*r⁻¹ := pow_succ _ _
        _ ≤ (r⁻¹)^k := mul_le_of_le_one_right (pow_nonneg hq0.le _) hq.le
        _ < _ := hk)⟩
    let k := Nat.find hex
    refine ⟨k,?_,fun _ => Nat.find_spec hex⟩
    by_cases hk : k = 0
    · simpa only [hk,pow_zero] using hx i
    have hmin : ¬ (r⁻¹)^((k-1)+1) < ‖x i‖ :=
      Nat.find_min hex (show k-1 < k by omega)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at hmin
    exact le_of_not_gt hmin
  choose l hl using heach
  exact ⟨l,hl⟩

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.exists_geometric_levels := @_root_.OAI.Cotype.exists_geometric_levels
