-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.herm_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:52:51.181297+00:00
-- url     : https://prove2.me/submissions/6103ffde-41d5-4568-add1-9e9bea5e602b

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
theorem _root_.solution {P Q : ℕ} (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.Sp P Q) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.herm x x = (_root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.qf x : ℂ) := by
  simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.herm, _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding.qf, Complex.star_def,
    Complex.mul_conj]
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
end GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
