-- Prove2me | solution 1 for GroundTheory.Global.le_iff_forall_count_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:35:39.048281+00:00
-- url     : https://prove2.me/submissions/c72f0f66-06d2-4397-b35f-e21f8e16f07d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_IdeleAction
import Theorems.Thm_GroundTheory_Global_le_one_of_forall_count_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution {I J : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) :
    I ≤ J ↔ ∀ v : HeightOneSpectrum (𝓞 K), count K v J ≤ count K v I := by
  refine ⟨fun h v ↦ count_mono K v hI h, fun h ↦ ?_⟩
  have hJ' : J⁻¹ ≠ 0 := inv_ne_zero hJ
  have hle : I * J⁻¹ ≤ 1 := le_one_of_forall_count_nonneg (mul_ne_zero hI hJ') fun v ↦ by
    rw [count_mul K v hI hJ', count_inv]
    linarith [h v]
  calc I = I * J⁻¹ * J := by rw [mul_assoc, inv_mul_cancel₀ hJ, mul_one]
    _ ≤ 1 * J := mul_le_mul_left hle J
    _ = J := one_mul J
end GroundTheory.Global
