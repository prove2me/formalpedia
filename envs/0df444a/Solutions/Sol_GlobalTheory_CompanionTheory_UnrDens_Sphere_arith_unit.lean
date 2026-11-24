-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.Sphere.arith_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:52:07.062962+00:00
-- url     : https://prove2.me/submissions/539e992d-826a-4c9a-a4ff-0a13215d2362

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardNonzeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardZeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianSpaceAnisotropicUnitStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianVectorValuesCard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.Sphere
namespace GlobalTheory.CompanionTheory.UnrDens.Sphere
theorem _root_.solution (q ε x Q : ℝ) (hq : q ≠ 0) :
    (q - ε) * (Q / q * (1 + (q - 1) * x)) + (q ^ 2 - (q - ε)) * (Q / q * (1 - x)) =
      Q * q ^ 2 / q * (1 - x * (ε / q)) := by
  field_simp
  ring
end GlobalTheory.CompanionTheory.UnrDens.Sphere
