-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.NormUnit.mem_ker_normU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:05.447805+00:00
-- url     : https://prove2.me/submissions/fa041ca6-e4ca-4e57-ae3c-bd848066b223

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardNonzero
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_normU_apply
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
theorem _root_.solution {k : Eˣ} : k ∈ (normU τ).ker ↔ (k : E) * τ k = 1 := by
  rw [MonoidHom.mem_ker, normU_apply, Units.ext_iff, Units.val_mul, coe_tauU, Units.val_one]
end GlobalTheory.CompanionTheory.UnrDens.NormUnit
