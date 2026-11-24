-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_isStableUnderBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:24:15.984272+00:00
-- url     : https://prove2.me/submissions/ab3cf249-87d1-44e9-a2d0-6c17673756fd

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreeHom
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreePullbackAffine
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotProof_Nbhd_finiteFreeHom_algebraMap_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotProof_Nbhd_finiteFreeHom_respectsIso

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
    RingHom.IsStableUnderBaseChange (fun {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) =>
      FiniteFreeHom f) := by
  refine RingHom.IsStableUnderBaseChange.mk GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_respectsIso ?_
  intro R S T _ _ _ _ _ h
  obtain ⟨h₁, h₂⟩ := GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_algebraMap_iff.1 h
  exact GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_algebraMap_iff.2 ⟨inferInstance, inferInstance⟩
end GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd
