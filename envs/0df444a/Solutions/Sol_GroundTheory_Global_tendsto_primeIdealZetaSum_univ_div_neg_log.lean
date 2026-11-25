-- Prove2me | solution 1 for GroundTheory.Global.tendsto_primeIdealZetaSum_univ_div_neg_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:49:18.279418+00:00
-- url     : https://prove2.me/submissions/032f7d44-5c61-4600-9a71-c296f47792b9

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOneDensity
import Theorems.Thm_GroundTheory_Global_tendsto_neg_log_sub_one_atTop
import Theorems.Thm_GroundTheory_Global_SemiLocal_tensorHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_exists_abs_primeIdealZetaSum_add_log_le
import Theorems.Thm_P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.SemiLocal.tensorHomeomorph_apply
attribute [local simp] P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Filter Topology Set Ideal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution :
    Tendsto (fun s : ℝ => (univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s /
      -Real.log (s - 1)) (𝓝[>] 1) (𝓝 1) := by
  obtain ⟨C, hC⟩ := exists_abs_primeIdealZetaSum_add_log_le K
  have hu := tendsto_neg_log_sub_one_atTop
  have hupos := hu.eventually_gt_atTop 0
  set P := fun s : ℝ => (univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s
  have h0 : Tendsto (fun s : ℝ => (P s + Real.log (s - 1)) / -Real.log (s - 1)) (𝓝[>] 1)
      (𝓝 0) := by
    have hlo : Tendsto (fun s : ℝ => -C / -Real.log (s - 1)) (𝓝[>] 1) (𝓝 0) :=
      Tendsto.div_atTop (tendsto_const_nhds (x := -C)) hu
    have hhi : Tendsto (fun s : ℝ => C / -Real.log (s - 1)) (𝓝[>] 1) (𝓝 0) :=
      Tendsto.div_atTop (tendsto_const_nhds (x := C)) hu
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
    · filter_upwards [hC, hupos] with s h1 h2
      exact div_le_div_of_nonneg_right (abs_le.mp h1).1 h2.le
    · filter_upwards [hC, hupos] with s h1 h2
      exact div_le_div_of_nonneg_right (abs_le.mp h1).2 h2.le
  have := h0.const_add 1
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [hupos] with s hs
  have hne : -Real.log (s - 1) ≠ 0 := hs.ne'
  simp only [P]
  rw [eq_div_iff hne, add_mul, div_mul_cancel₀ _ hne]
  ring
end GroundTheory.Global
