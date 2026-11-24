-- Prove2me | solution 1 for GlobalTheory.T.finite_free_pullback_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:09:35.810423+00:00
-- url     : https://prove2.me/submissions/3ce1f114-5af2-4d71-9ae9-2681293c9c2f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreePullbackAffine
import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreeHom
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreePullbackAffineStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotProof_Nbhd_finiteFreeHom_appTop_of_isPullback


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
theorem _root_.solution : ∀ {P Q D W : Scheme.{0}} {u : P ⟶ Q} {v : P ⟶ D} {g : Q ⟶ W} {h : D ⟶ W} [IsAffine P] [IsAffine Q] [IsAffine D] [IsAffine W], IsPullback u v g h → GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.FiniteFreeHom g.appTop.hom → GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.FiniteFreeHom v.appTop.hom := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_appTop_of_isPullback | exact GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_appTop_of_isPullback | (intros; apply GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_appTop_of_isPullback <;> assumption)
end _root_.GlobalTheory.T
