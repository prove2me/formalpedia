-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_stableUnderComposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:49:34.524802+00:00
-- url     : https://prove2.me/submissions/499a5fd7-5b9e-4347-be80-88fd9a0d3b41

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreeHom
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreePullbackAffine
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotProof_Nbhd_finiteFreeHom_comp

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd
namespace GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd
theorem _root_.solution :
    RingHom.StableUnderComposition (fun {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) =>
      FiniteFreeHom f) := by
  intro A B C _ _ _ f g hf hg
  exact GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_comp f g hf hg
end GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd
