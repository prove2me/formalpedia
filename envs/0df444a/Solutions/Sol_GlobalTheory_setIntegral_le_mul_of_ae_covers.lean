-- Prove2me | solution 1 for GlobalTheory.setIntegral_le_mul_of_ae_covers
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:14:04.62626+00:00
-- url     : https://prove2.me/submissions/7be64a99-98b6-4a70-9a36-d7fe6784c44d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EncardSmulMemLeEncardSmulInterNonempty
import Theorems.Thm_GlobalTheory_encard_smul_mem_le_encard_smul_inter_nonempty
import Theorems.Thm_GlobalTheory_tsum_indicator_smul_eq_encard
import Theorems.Thm_GlobalTheory_sum_restrict_preimage_smul_le
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
    (hB : NullMeasurableSet B μ) {u : X → ℝ} (hu : ∀ (g : G) (x : X), u (g • x) = u x)
    (hu0 : ∀ x, 0 ≤ u x) (huB : AEStronglyMeasurable u (μ.restrict B))
    (huD : IntegrableOn u D μ) {m : ℕ}
    (hm : ∀ᵐ x ∂μ.restrict D, {g : G | g • x ∈ B}.encard ≤ m) :
    IntegrableOn u B μ ∧ ∫ x in B, u x ∂μ ≤ m * ∫ x in D, u x ∂μ := by
  have key : ∫⁻ x in B, ENNReal.ofReal (u x) ∂μ ≤ m * ∫⁻ x in D, ENNReal.ofReal (u x) ∂μ := by
    refine setLIntegral_le_mul_of_ae_covers hD hB (fun g x => by rw [hu]) ?_
    filter_upwards [hm] with x hx
    exact_mod_cast ENat.toENNReal_le.2 hx
  have hfin : ∫⁻ x in D, ENNReal.ofReal (u x) ∂μ ≠ ⊤ :=
    ((hasFiniteIntegral_iff_ofReal (.of_forall hu0)).1 huD.2).ne
  have hfin' : (m : ℝ≥0∞) * ∫⁻ x in D, ENNReal.ofReal (u x) ∂μ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top m) hfin
  refine ⟨⟨huB, (hasFiniteIntegral_iff_ofReal (.of_forall hu0)).2 (key.trans_lt hfin'.lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (.of_forall hu0) huB,
    integral_eq_lintegral_of_nonneg_ae (.of_forall hu0) huD.1]
  simpa [ENNReal.toReal_mul] using ENNReal.toReal_mono hfin' key
end GlobalTheory
