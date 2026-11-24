-- Prove2me | solution 1 for GlobalTheory.SortedCartan.permUnit_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:14:35.400771+00:00
-- url     : https://prove2.me/submissions/6399b533-6bdf-4f17-b7e0-c1e1c9a7f465

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_IsCoType
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ValuationDivZpowOrd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CartanAntitone
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
noncomputable section
open GlobalTheory GlobalTheory.SortedCartan
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SortedCartan
theorem _root_.solution {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    ((permUnit σ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = σ.toPEquiv.toMatrix := by
  ext i j
  simp only [permUnit, permUnitO, Matrix.GeneralLinearGroup.map_apply, RingHom.mapMatrix_apply,
    Matrix.map_apply, PEquiv.toMatrix_apply]
  split_ifs <;> simp
end GlobalTheory.SortedCartan
