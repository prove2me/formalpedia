-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSStabLink.exp_mem_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:43:55.82948+00:00
-- url     : https://prove2.me/submissions/5cd8c818-bce0-4dbd-b565-274046924160

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExpMemUJ
import Theorems.Thm_GlobalTheory_CompanionTheory_DSStabLink_inK_smul
import Theorems.Thm_Formalism_REAL_maximal_compact_facts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology Set
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSStabLink
open PI.UpqRep CompanionTheory.D.DSIC
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.DSStabLink
theorem _root_.solution (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Kset ε :=
  (Formalism.REAL.maximal_compact_facts n ε).2.2.2.1 _ (inK_smul ε hX t)
end GlobalTheory.CompanionTheory.DSStabLink
