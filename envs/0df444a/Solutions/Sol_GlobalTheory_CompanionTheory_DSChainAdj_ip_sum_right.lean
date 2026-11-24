-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSChainAdj.ip_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:26:23.829214+00:00
-- url     : https://prove2.me/submissions/6f268f9a-1aa4-4956-9bc4-6f9b2e4a1816

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SumInsertErase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSChainAdj
open CompanionTheory.D.DSIC
variable {n : ℕ} {ε : Fin n → Bool}
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace GlobalTheory.CompanionTheory.DSChainAdj
theorem _root_.solution {ι : Type} (s : Finset ι) (f : ι → Ch ε V) (w : Ch ε V) :
    ip w (∑ i ∈ s, f i) = ∑ i ∈ s, ip w (f i) := by
  unfold ip
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [Finset.sum_apply, inner_sum]
end GlobalTheory.CompanionTheory.DSChainAdj
