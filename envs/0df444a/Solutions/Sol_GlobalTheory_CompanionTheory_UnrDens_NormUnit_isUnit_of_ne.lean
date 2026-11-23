-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.NormUnit.isUnit_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:27:43.685788+00:00
-- url     : https://prove2.me/submissions/35826d74-aed0-4aaa-be3e-ab3ce0aa40a9

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
theorem _root_.solution (hf : IsField E) {a : E} (ha : a ≠ 0) : IsUnit a := by
  obtain ⟨b, hb⟩ := hf.mul_inv_cancel ha
  exact IsUnit.of_mul_eq_one b hb
end GlobalTheory.CompanionTheory.UnrDens.NormUnit
