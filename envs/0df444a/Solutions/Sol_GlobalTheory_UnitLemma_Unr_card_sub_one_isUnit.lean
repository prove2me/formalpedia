-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.card_sub_one_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:01:48.797734+00:00
-- url     : https://prove2.me/submissions/e3d11a2b-aa24-48f2-b128-2ff5d8e2e922

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MonicDvdXPowCardSubOneExistsRootStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvolutionResiduePowAndRootsOfUnityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralIntegersUnramifiedInvolutionExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinPrimitiveRootEqIntegersUnramifiedQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnramifiedInvolutionFieldEmbedding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma Polynomial IsLocalRing
namespace GlobalTheory.UnitLemma.Unr
theorem _root_.solution (S : Type*) [CommRing S] [IsLocalRing S] [Finite (ResidueField S)] :
    IsUnit ((Nat.card (ResidueField S) - 1 : ℕ) : S) := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast, Nat.cast_sub Nat.card_pos, Nat.cast_one]
  haveI := Fintype.ofFinite (ResidueField S)
  rw [Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero]
  simp
end GlobalTheory.UnitLemma.Unr
