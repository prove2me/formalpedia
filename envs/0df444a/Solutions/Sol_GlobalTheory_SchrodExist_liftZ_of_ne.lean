-- Prove2me | solution 1 for GlobalTheory.SchrodExist.liftZ_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:35:14.909353+00:00
-- url     : https://prove2.me/submissions/444591d2-db2c-4be5-ad5a-5a1e9452551f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegersModNatFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsNeZeroOfEventually
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsSchrodingerIntertwinerIntegralMatrices

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel GlobalTheory.SplitWeil Matrix
noncomputable section
open GlobalTheory GlobalTheory.SchrodExist
open GlobalTheory.PlaceModel
namespace GlobalTheory.SchrodExist
theorem _root_.solution {A Z : Type} [AddCommGroup Z] [TopologicalSpace A] (Φ : SB A) {g : A × Z} (h : g.2 ≠ 0) :
    liftZ Φ g = 0 := by
  simp [liftZ, h]
end GlobalTheory.SchrodExist
