-- Prove2me | solution 1 for GlobalTheory.MvPoly.l1Norm_prod_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:21:18.437796+00:00
-- url     : https://prove2.me/submissions/0135a193-82ab-4fb2-afe2-0b67a4b62575

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial
import Theorems.Thm_GlobalTheory_MvPoly_l1Norm_nonneg
import Theorems.Thm_GlobalTheory_MvPoly_l1Norm_prod_le
import Theorems.Thm_GlobalTheory_MvPoly_l1Norm_pow_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open GlobalTheory GlobalTheory.MvPoly
variable {σ τ K L : Type*}
variable [NormedCommRing K] [NormedCommRing L]
namespace GlobalTheory.MvPoly
theorem _root_.solution [NormOneClass K] {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial σ K) (c : ι → ℕ) (B : ι → ℝ) (h : ∀ i ∈ s, l1Norm (f i) ≤ B i) :
    l1Norm (∏ i ∈ s, f i ^ c i) ≤ ∏ i ∈ s, B i ^ c i :=
  (l1Norm_prod_le _ _).trans <| prod_le_prod (fun _ _ ↦ l1Norm_nonneg _) fun i hi ↦
    (l1Norm_pow_le _ _).trans (pow_le_pow_left₀ (l1Norm_nonneg _) (h i hi) _)
end GlobalTheory.MvPoly
