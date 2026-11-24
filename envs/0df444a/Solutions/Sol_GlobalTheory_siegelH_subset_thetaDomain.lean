-- Prove2me | solution 1 for GlobalTheory.siegelH_subset_thetaDomain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:33:53.477362+00:00
-- url     : https://prove2.me/submissions/8a98711f-8938-4c75-a125-0d1e6e7ddba4

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemThetaDomainIffIsSiegelAddTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology ReciprocityTheory.PTheta
open GlobalTheory
variable {ι : Type*} [Fintype ι]
namespace GlobalTheory
theorem _root_.solution : SiegelH ι ⊆ ThetaDomain ι := by
  intro τ hτ
  obtain ⟨hs, hp⟩ := hτ
  have ht : (τ.map Complex.im)ᵀ = τ.map Complex.im := by
    rw [← Matrix.transpose_map, hs.eq]
  show (τ.map Complex.im + (τ.map Complex.im)ᵀ).PosDef
  rw [ht]
  exact hp.add hp
end GlobalTheory
