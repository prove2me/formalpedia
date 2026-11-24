-- Prove2me | solution 1 for GlobalTheory.T.shear_iso_action_projection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:22:21.118963+00:00
-- url     : https://prove2.me/submissions/be0065aa-3446-4c82-b73c-a498e66f1dc4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_ShearIsoActionProjection
import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreeHom
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_ShearIsoActionProjectionStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotProof_exists_iso_swap_action_snd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X], ∃ σ : G ⊗ X ⟶ G ⊗ X, IsIso σ ∧ σ ≫ snd G X = γ[G, X] ∧ σ ≫ γ[G, X] = snd G X := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotProof.exists_iso_swap_action_snd | exact GlobalTheory.CompanionTheory.FreeQuotProof.exists_iso_swap_action_snd | (intros; apply GlobalTheory.CompanionTheory.FreeQuotProof.exists_iso_swap_action_snd <;> assumption)
end _root_.GlobalTheory.T
