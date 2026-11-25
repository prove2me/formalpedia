-- Prove2me | solution 1 for GlobalTheory.succMin_mul_minNorm_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:44:53.080633+00:00
-- url     : https://prove2.me/submissions/dcbed8ba-2717-4416-851c-47582ae6ec93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsLinearIndependentSqrtEqSuccMinQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DiscreteTopologySpanOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Theorems.Thm_GlobalTheory_prod_succMin_le_rpow_mul_covolume
import Theorems.Thm_GlobalTheory_spanCovol_bot
import Theorems.Thm_GlobalTheory_succMin_mono_of_isZLattice
import Theorems.Thm_GlobalTheory_succMin_nonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
noncomputable section
open Module Submodule MeasureTheory
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
namespace GlobalTheory
theorem _root_.solution {k : ℕ} (h1 : 1 ≤ k) (hk : k ≤ finrank ℝ E) :
    succMin L k * minNorm L ^ (finrank ℝ E - 1) ≤
      (finrank ℝ E : ℝ) ^ ((finrank ℝ E : ℝ) / 2) * ZLattice.covolume L := by
  refine le_trans ?_ (prod_succMin_le_rpow_mul_covolume L)
  let j : Fin (finrank ℝ E) := ⟨k - 1, by omega⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), show (j : ℕ) + 1 = k by simp [j]; omega]
  refine mul_le_mul_of_nonneg_left ?_ (succMin_nonneg L k)
  calc minNorm L ^ (finrank ℝ E - 1) = ∏ _i ∈ Finset.univ.erase j, minNorm L := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ ↦ succMin_nonneg L 1) fun i _ ↦
        succMin_mono_of_isZLattice (by omega) i.2
end GlobalTheory
