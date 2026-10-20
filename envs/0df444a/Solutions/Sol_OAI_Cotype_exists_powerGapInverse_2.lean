-- Prove2me | solution 2 for OAI.Cotype.exists_powerGapInverse
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:57:36.84737+00:00
-- url     : https://prove2.me/submissions/2ef36d4f-2f17-4647-a652-7766284ecd3b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/PowerGapInverse.lean:L17-L58
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.exists_powerGapInverse. The node keeps its source
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

-- ---- from OAI.Analysis.Cotype.PowerGapInverse ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype

theorem exists_powerGapInverse {N : ℕ} {b q : ℝ}
    (hb : 0 ≤ b) (hq : q < 1)
    {R : Type*} [NormedRing R] [NormOneClass R] [CompleteSpace R]
    (H : R) (hH : ‖H‖ ≤ b) (hHN : ‖H^N‖ ≤ q) :
    ∃ U : Rˣ, (U : R) = 1-H ∧ ‖(↑U⁻¹ : R)‖ ≤ powerGapInverseBound N b q := by
  let S : R := ∑ k ∈ Finset.range N, H^k
  let V := Units.oneSub (H^N) (hHN.trans_lt hq)
  have hSV : S*(1-H) = (V : R) := by
    change (∑ k ∈ Finset.range N, H^k)*(1-H) = 1-H^N
    simpa using geom_sum_mul_neg H N
  have hVS : (1-H)*S = (V : R) := by
    change (1-H)*(∑ k ∈ Finset.range N, H^k) = 1-H^N
    simpa using mul_neg_geom_sum H N
  have hl : ((↑V⁻¹ : R)*S)*(1-H) = 1 := by
    rw [mul_assoc, hSV]
    exact V.inv_val
  have hr : (1-H)*(S*(↑V⁻¹ : R)) = 1 := by
    rw [← mul_assoc, hVS]
    exact V.val_inv
  have he : (↑V⁻¹ : R)*S = S*(↑V⁻¹ : R) := by
    calc
      _ = ((↑V⁻¹ : R)*S)*((1-H)*(S*(↑V⁻¹ : R))) := by rw [hr, mul_one]
      _ = (((↑V⁻¹ : R)*S)*(1-H))*(S*(↑V⁻¹ : R)) := (mul_assoc _ _ _).symm
      _ = _ := by rw [hl, one_mul]
  let U : Rˣ := ⟨1-H, S*(↑V⁻¹ : R), hr, by rw [← he]; exact hl⟩
  refine ⟨U, rfl, ?_⟩
  have hS : ‖S‖ ≤ ∑ k ∈ Finset.range N, b^k := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro k _
    exact (norm_pow_le H k).trans (pow_le_pow_left₀ (norm_nonneg H) hH k)
  have hV : ‖(↑V⁻¹ : R)‖ ≤ (1-q)⁻¹ := by
    change ‖∑' j : ℕ, (H^N)^j‖ ≤ (1-q)⁻¹
    have h := tsum_geometric_le_of_norm_lt_one (H^N) (hHN.trans_lt hq)
    simp only [norm_one, sub_self, zero_add] at h
    exact h.trans (inv_anti₀ (sub_pos.mpr hq) (sub_le_sub_left hHN 1))
  change ‖S*(↑V⁻¹ : R)‖ ≤ _
  calc
    _ ≤ ‖S‖*‖(↑V⁻¹ : R)‖ := norm_mul_le _ _
    _ ≤ (∑ k ∈ Finset.range N, b^k)*(1-q)⁻¹ :=
      mul_le_mul hS hV (norm_nonneg _) (Finset.sum_nonneg (fun k _ => pow_nonneg hb k))
    _ = _ := by rw [powerGapInverseBound, div_eq_mul_inv]

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.exists_powerGapInverse := @_root_.OAI.Cotype.exists_powerGapInverse
