-- Prove2me | solution 1 for GlobalTheory.SchrodExist.mem_intLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:35:50.371773+00:00
-- url     : https://prove2.me/submissions/f6ea131f-ba39-43bf-9b9c-60b30b5d5527

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
theorem _root_.solution {k : Type} [Field k] [ValuativeRel k] {Y Y' : Type} {x : Matrix Y Y' k} :
    x ∈ intLat k Y Y' ↔ ∀ r q, x r q ∈ 𝒪[k] := Iff.rfl
end GlobalTheory.SchrodExist
