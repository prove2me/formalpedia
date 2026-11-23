-- Prove2me | solution 1 for GlobalTheory.setLIntegral_le_encard_mul_of_ae_covers
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:14:04.332801+00:00
-- url     : https://prove2.me/submissions/a4b779d7-6f65-4af3-ab11-68d6569103c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EncardSmulMemLeEncardSmulInterNonempty
import Theorems.Thm_GlobalTheory_encard_smul_mem_le_encard_smul_inter_nonempty
import Theorems.Thm_GlobalTheory_setLIntegral_le_mul_of_ae_covers

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
theorem _root_.solution (hD : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ D)
    (hB : NullMeasurableSet B μ) {u : X → ℝ≥0∞} (hu : ∀ (g : G) (x : X), u (g • x) = u x) :
    ∫⁻ x in B, u x ∂μ
      ≤ ({g : G | (g • B ∩ B).Nonempty}.encard : ℝ≥0∞) * ∫⁻ x in D, u x ∂μ :=
  setLIntegral_le_mul_of_ae_covers hD hB hu (.of_forall fun x =>
    ENat.toENNReal_le.2 (encard_smul_mem_le_encard_smul_inter_nonempty B x))
end GlobalTheory
