-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_appTop_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:41:37.326194+00:00
-- url     : https://prove2.me/submissions/83a8797c-2a2f-4a40-8352-4ba8cabbd8f5

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreeHom
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFreePullbackAffine
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotProof_Nbhd_finiteFreeHom_respectsIso
import Theorems.Thm_GlobalTheory_CompanionTheory_FreeQuotProof_Nbhd_finiteFreeHom_isStableUnderBaseChange

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
    ∀ {P Q D W : Scheme.{0}} {u : P ⟶ Q} {v : P ⟶ D} {g : Q ⟶ W} {h : D ⟶ W} [IsAffine P] [IsAffine Q] [IsAffine D] [IsAffine W], IsPullback u v g h → GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.FiniteFreeHom g.appTop.hom → GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.FiniteFreeHom v.appTop.hom := by
  intro P Q D W u v g h _ _ _ _ hpb hg
  have hbc := RingHom.IsStableUnderBaseChange.pullback_fst_appTop @GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.FiniteFreeHom
    GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_isStableUnderBaseChange GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_respectsIso h g hg
  haveI : IsIso hpb.flip.isoPullback.hom.appTop := by
    rw [← Scheme.Γ_map_op]
    exact (Scheme.Γ.mapIso hpb.flip.isoPullback.op).isIso_hom
  rw [← hpb.flip.isoPullback_hom_fst, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  exact (RingHom.RespectsIso.cancel_right_isIso GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.finiteFreeHom_respectsIso _ _).2 hbc
end GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd
