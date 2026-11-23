-- Prove2me | solution 1 for GlobalTheory.setLIntegral_le_of_isFundamentalDomain_of_ae_covers
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:32.983811+00:00
-- url     : https://prove2.me/submissions/bcd0b4b4-16e6-4c85-85ce-9f3e422f854a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EncardSmulMemLeEncardSmulInterNonempty
import Theorems.Thm_GlobalTheory_encard_smul_mem_le_encard_smul_inter_nonempty
import Theorems.Thm_GlobalTheory_tsum_indicator_smul_eq_encard
import Theorems.Thm_GlobalTheory_sum_restrict_preimage_smul_le
import Theorems.Thm_GlobalTheory_setLIntegral_le_mul_of_ae_covers
import Theorems.Thm_GlobalTheory_setIntegral_le_mul_of_ae_covers
import Theorems.Thm_GlobalTheory_setLIntegral_le_mul_of_isFundamentalDomain
import Theorems.Thm_GlobalTheory_setLIntegral_le_encard_mul_of_ae_covers
import Theorems.Thm_GlobalTheory_ae_encard_smul_mem_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal Pointwise
open GlobalTheory
variable {G X : Type*} [Group G] [MulAction G X]
variable [MeasurableSpace X] {μ : Measure X} [MeasurableConstSMul G X]
  [SMulInvariantMeasure G X μ] [Countable G] {B D : Set X}
namespace GlobalTheory
theorem _root_.solution {D' : Set X}
    (hD : IsFundamentalDomain G D μ) (hD' : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ D')
    {u : X → ℝ≥0∞} (hu : ∀ (g : G) (x : X), u (g • x) = u x) :
    ∫⁻ x in D, u x ∂μ ≤ ∫⁻ x in D', u x ∂μ := by
  have := setLIntegral_le_mul_of_ae_covers hD' hD.nullMeasurableSet hu (m := 1) (by
    filter_upwards [ae_restrict_of_ae (ae_encard_smul_mem_le_one hD)] with x hx
    exact_mod_cast ENat.toENNReal_le.2 hx)
  simpa using this
end GlobalTheory
