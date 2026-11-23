-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.NormUnit.fixed_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:05.334007+00:00
-- url     : https://prove2.me/submissions/ae623ec1-2299-489e-b813-2010fc6c164f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardNonzero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.NormUnit
variable {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}
namespace GlobalTheory.CompanionTheory.UnrDens.NormUnit
theorem _root_.solution {s v : E} (hs : τ s = s) (hv : s * v = 1) : τ v = v := by
  have h2 : s * τ v = 1 := by
    have h3 := congrArg τ hv
    rwa [map_mul, map_one, hs] at h3
  calc τ v = (v * s) * τ v := by rw [mul_comm v s, hv, one_mul]
    _ = v := by rw [mul_assoc, h2, mul_one]
end GlobalTheory.CompanionTheory.UnrDens.NormUnit
