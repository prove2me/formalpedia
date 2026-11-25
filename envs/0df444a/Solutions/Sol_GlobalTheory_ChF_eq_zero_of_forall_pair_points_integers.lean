-- Prove2me | solution 1 for GlobalTheory.ChF.eq_zero_of_forall_pair_points_integers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:35:05.608484+00:00
-- url     : https://prove2.me/submissions/f9ee6a3c-b121-4a8b-ba2f-53c56d189450

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesEvalOfPowMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MemSupSpanXPowIffAndIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EqZeroOfForallPairPointsValuationIntegers
import Theorems.Thm_GlobalTheory_ChF_eq_zero_of_forall_pair_points

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ChF
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace GlobalTheory.ChF
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (W : (PS O 1 d →ₐ[O] O) → Prop), (∀ f : PS O 1 d, (∀ φ, W φ → φ f = 0) → f = 0) → ∀ f : PS O 2 d, (∀ (Φ : PS O 2 d →ₐ[O] O) (φ φ' : PS O 1 d →ₐ[O] O), (∀ u, Φ (ev (n := 2) ![pt O d 0] u) = φ u) → (∀ u, Φ (ev (n := 2) ![pt O d 1] u) = φ' u) → W φ → W φ' → Φ f = 0) → f = 0 :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ W hW f hf => eq_zero_of_forall_pair_points W hW f hf
end GlobalTheory.ChF
