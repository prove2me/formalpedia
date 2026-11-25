-- Prove2me | solution 1 for GlobalTheory.OrderProductDifference.target
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:05:23.248945+00:00
-- url     : https://prove2.me/submissions/9b890a33-75d4-499f-9424-7b3581b80401

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrderProdSubProd
import Theorems.Thm_GlobalTheory_OrderProductDifference_order_prod_sub_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.OrderProductDifference
open MvPowerSeries
namespace GlobalTheory.OrderProductDifference
theorem _root_.solution : ∀ {R τ ι : Type} [inst : CommRing R] (s : Finset ι) (a b : ι → MvPowerSeries τ R) (k : ι → ℕ), (∀ i ∈ s, (↑(k i) : ℕ∞) ≤ MvPowerSeries.order (a i)) → (∀ i ∈ s, (↑(k i) : ℕ∞) ≤ MvPowerSeries.order (b i)) → (∀ i ∈ s, (↑(k i) : ℕ∞) + (1 : ℕ∞) ≤ MvPowerSeries.order (a i - b i)) → ∑ i ∈ s, (↑(k i) : ℕ∞) + (1 : ℕ∞) ≤ MvPowerSeries.order (∏ i ∈ s, a i - ∏ i ∈ s, b i) :=
  fun s a b k ha hb hab => order_prod_sub_prod s a b k ha hb hab
end GlobalTheory.OrderProductDifference
