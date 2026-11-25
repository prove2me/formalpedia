-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.herm_eq_hform
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:57:20.827559+00:00
-- url     : https://prove2.me/submissions/8df2ffde-fe8e-4ed0-96e4-d9573374c989

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_PerpendicularEmbedding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
open MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal
open MeasureTheory Matrix
open scoped ENNReal
namespace GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
theorem _root_.solution {P Q : ℕ} (x y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.herm x y = _root_.Formalism.UG.hform (starRingEnd ℂ) (_root_.Formalism.UG.Jpq P Q) y x := by
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.herm, _root_.Formalism.UG.hform, _root_.Formalism.UG.Jpq, Fintype.sum_sum_type,
    fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
    Matrix.one_apply, Matrix.neg_apply, Matrix.zero_apply, Complex.star_def]
  simp [mul_comm, sub_eq_add_neg, Finset.sum_neg_distrib]
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
end GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
