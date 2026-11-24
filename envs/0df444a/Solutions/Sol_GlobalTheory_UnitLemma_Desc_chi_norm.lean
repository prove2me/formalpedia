-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.chi_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:21:13.022813+00:00
-- url     : https://prove2.me/submissions/42b8a390-e7c2-4fb2-a5b8-17cb6791df19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormCharacterOnIdempotentPartFrameProperties
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_eta_norm_mul_sigma
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_twist_mul
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_twist_isUnit
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_eS_idem
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_sigma_eS

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
theorem _root_.solution {e : ι → B.A} {S : Finset ι} (h : IsPre B e S) (I : Finset ι) {w : B.A} (hw : IsUnit w) :
    chi B e I (w * B.σ w) = 1 := by
  unfold chi
  have hE := eS_idem B h.1.toOrthogonalIdempotents I
  have hσ : B.σ (w * eS B e I + (1 - eS B e I)) = B.σ w * eS B e I + (1 - eS B e I) := by
    rw [map_add, map_mul, map_sub, map_one, sigma_eS B h]
  rw [← twist_mul B hE, ← hσ]
  exact eta_norm_mul_sigma B (twist_isUnit B hE hw)
end GlobalTheory.UnitLemma.Desc
