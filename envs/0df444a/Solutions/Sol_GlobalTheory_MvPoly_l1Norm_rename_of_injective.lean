-- Prove2me | solution 1 for GlobalTheory.MvPoly.l1Norm_rename_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:02:24.766679+00:00
-- url     : https://prove2.me/submissions/babf32e1-9da7-4dca-a23f-3290042cc3cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial

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
theorem _root_.solution {f : σ → τ} (hf : Function.Injective f)
    (P : MvPolynomial σ K) : l1Norm (rename f P) = l1Norm P := by
  classical
  rw [l1Norm, support_rename_of_injective hf,
    sum_image fun _ _ _ _ h ↦ Finsupp.mapDomain_injective hf h, l1Norm]
  simp [coeff_rename_mapDomain f hf]
end GlobalTheory.MvPoly
