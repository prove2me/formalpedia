-- Prove2me | solution 1 for GlobalTheory.SchrodExist.mem_annLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:35:49.527108+00:00
-- url     : https://prove2.me/submissions/8ffc8d11-6be4-4d10-9945-94290c21ae7b

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
theorem _root_.solution {k : Type} [Field k] [ValuativeRel k] {Y Y' Z : Type} [AddCommGroup Z]
    {χ : Matrix Y Y' k → Z → ℂ} {hr : ∀ a z z', χ a (z + z') = χ a z * χ a z'} {h0 : ∀ a, χ a 0 = 1} {z : Z} :
    z ∈ annLat χ hr h0 ↔ ∀ u : Matrix Y Y' k, (∀ r q, u r q ∈ 𝒪[k]) → χ u z = 1 := Iff.rfl
end GlobalTheory.SchrodExist
