-- Prove2me | solution 1 for GlobalTheory.FiniteQuotOmega.jacobian_smul_kaehler_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:48:20.748788+00:00
-- url     : https://prove2.me/submissions/e9e7bf0f-bb73-4d61-9582-d51035ba078b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JacobianSmulKaehlerEqZero
import Theorems.Thm_GlobalTheory_FiniteQuotOmega_det_smul_kaehler_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FiniteQuotOmega
open MvPowerSeries IsLocalRing
open scoped TensorProduct
namespace GlobalTheory.FiniteQuotOmega
theorem _root_.solution :
    ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T] (σ : Type) [Fintype σ] [DecidableEq σ] (f : σ → MvPowerSeries σ T), Module.Finite T (MvPowerSeries σ T ⧸ Ideal.span (Set.range f)) → ∀ ω : KaehlerDifferential T (MvPowerSeries σ T ⧸ Ideal.span (Set.range f)), (Ideal.Quotient.mk (Ideal.span (Set.range f)) (Matrix.det (Matrix.of fun i j => pderiv T j (f i)))) • ω = 0 := by
  intro T _ _ _ σ _ _ f hfin ω
  exact det_smul_kaehler_eq_zero (Ideal.Quotient.mkₐ T (Ideal.span (Set.range f)))
    Ideal.Quotient.mk_surjective f
    (fun i => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)) ω
end GlobalTheory.FiniteQuotOmega
