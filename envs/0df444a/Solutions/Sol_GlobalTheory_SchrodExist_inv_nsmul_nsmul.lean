-- Prove2me | solution 1 for GlobalTheory.SchrodExist.inv_nsmul_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:34:17.351975+00:00
-- url     : https://prove2.me/submissions/dbee7677-b931-46f9-998d-0e560d0a1c83

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
theorem _root_.solution {k : Type} [Field k] [CharZero k] {Y Y' : Type} (n : ℕ) (hn : 0 < n)
    (m : Matrix Y Y' k) : (n : k)⁻¹ • (n • m) = m := by
  rw [← Nat.cast_smul_eq_nsmul k n m, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), one_smul]
end GlobalTheory.SchrodExist
