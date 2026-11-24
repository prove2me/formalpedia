-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.chi_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:51:47.69977+00:00
-- url     : https://prove2.me/submissions/2346a569-8799-4408-822a-a67d771f9817

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormCharacterOnIdempotentPartFrameProperties
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_norm_ne_zero_of_isUnit
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_twist_mul
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_twist_isUnit
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_eS_idem
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_eta_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
open GlobalTheory.UnitLemma Polynomial Filter Topology
variable {K : UQ} (B : InvAlg K)
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.UnitLemma.Desc
theorem _root_.solution {e : ι → B.A} (he : OrthogonalIdempotents e) (I : Finset ι) {x y : B.A} (hx : IsUnit x)
    (hy : IsUnit y) : chi B e I (x * y) = chi B e I x * chi B e I y := by
  unfold chi
  have hE := eS_idem B he I
  rw [← twist_mul B hE, map_mul, eta_mul (norm_ne_zero_of_isUnit B (twist_isUnit B hE hx))
    (norm_ne_zero_of_isUnit B (twist_isUnit B hE hy))]
end GlobalTheory.UnitLemma.Desc
