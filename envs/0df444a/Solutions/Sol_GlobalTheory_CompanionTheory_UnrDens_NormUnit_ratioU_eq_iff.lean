-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.NormUnit.ratioU_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:04.839958+00:00
-- url     : https://prove2.me/submissions/1e3831d8-09bc-4a4f-9cec-cb4311e659af

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardNonzero
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_ratioU_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_coe_tauU

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
theorem _root_.solution {c a : Eˣ} : ratioU τ c = a ↔ (c : E) = a * τ c := by
  rw [ratioU_apply, div_eq_iff_eq_mul, Units.ext_iff, Units.val_mul, coe_tauU]
end GlobalTheory.CompanionTheory.UnrDens.NormUnit
