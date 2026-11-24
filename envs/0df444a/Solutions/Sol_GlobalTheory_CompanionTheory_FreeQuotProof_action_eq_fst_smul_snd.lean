-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FreeQuotProof.action_eq_fst_smul_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:33:11.452803+00:00
-- url     : https://prove2.me/submissions/1111aa3e-47da-4024-b33b-1f4fa781f6b8

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreeHom
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_ShearIsoActionProjection

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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FreeQuotProof
namespace GlobalTheory.CompanionTheory.FreeQuotProof
theorem _root_.solution {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X] :
    (γ[G, X] : G ⊗ X ⟶ X) = (fst G X) • (snd G X) := by
  rw [CategoryTheory.Hom.smul_def, lift_fst_snd, Category.id_comp]
end GlobalTheory.CompanionTheory.FreeQuotProof
