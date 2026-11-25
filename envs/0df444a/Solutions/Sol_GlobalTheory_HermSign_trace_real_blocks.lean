-- Prove2me | solution 1 for GlobalTheory.HermSign.trace_real_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:41:12.024784+00:00
-- url     : https://prove2.me/submissions/38284655-7f6a-49d1-8c58-29d96f0383f5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_MemIffConjugateNotMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SignatureHermitianModelOfDatum
import Theorems.Thm_P2M_GlobalTheory_HermSign_trace_real_toLin__d42d376d233c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors TensorProduct ComplexConjugate ComplexOrder MatrixOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HermSign
namespace GlobalTheory.HermSign
theorem _root_.solution {ι : Type} [Fintype ι] {r : ℕ} (N : ι → Matrix (Fin r) (Fin r) ℂ)
    (f : (ι → Fin r → ℂ) →ₗ[ℝ] (ι → Fin r → ℂ)) (hf : ∀ u τ, f u τ = N τ *ᵥ u τ) :
    LinearMap.trace ℝ _ f = ∑ τ, 2 * (N τ).trace.re := by
  classical
  have : f = ∑ τ, LinearMap.single ℝ (fun _ : ι => Fin r → ℂ) τ ∘ₗ
      (((toLin' (N τ)).restrictScalars ℝ) ∘ₗ LinearMap.proj τ) := by
    refine LinearMap.ext fun u => funext fun τ => ?_
    simp [hf, Finset.sum_apply, Pi.single_apply]
  rw [this, map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc, LinearMap.proj_comp_single_same,
    LinearMap.comp_id, trace_real_toLin']
end GlobalTheory.HermSign
