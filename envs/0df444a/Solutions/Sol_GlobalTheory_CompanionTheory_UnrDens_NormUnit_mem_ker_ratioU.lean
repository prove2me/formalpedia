-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.NormUnit.mem_ker_ratioU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:52:01.7644+00:00
-- url     : https://prove2.me/submissions/7da9e50d-766a-4029-b739-ddd73e11c8fc

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardNonzero
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_ratioU_eq_iff

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
theorem _root_.solution {k : Eˣ} : k ∈ (ratioU τ).ker ↔ (k : E) = τ k := by
  rw [MonoidHom.mem_ker, ratioU_eq_iff, Units.val_one, one_mul]
end GlobalTheory.CompanionTheory.UnrDens.NormUnit
