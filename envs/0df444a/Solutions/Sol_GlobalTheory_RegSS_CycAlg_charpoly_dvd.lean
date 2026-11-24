-- Prove2me | solution 1 for GlobalTheory.RegSS.CycAlg.charpoly_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:14:01.200103+00:00
-- url     : https://prove2.me/submissions/903437ca-a4bf-48df-97d7-1548328dd1a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CyclicVectorGeneratedAlgebraStructure
import Theorems.Thm_GlobalTheory_RegSS_CycAlg_aeval_lowPoly_mulVec
import Theorems.Thm_GlobalTheory_RegSS_CycAlg_exists_lowPoly
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix Polynomial GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open GlobalTheory GlobalTheory.RegSS GlobalTheory.RegSS.CycAlg
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.RegSS.CycAlg
theorem _root_.solution {M : Matrix n n A} {v : n → A} (h : IsUnit (krylov M v).det) {p : A[X]}
    (hp : aeval M p *ᵥ v = 0) : M.charpoly ∣ p := by
  obtain ⟨c, hc⟩ := exists_lowPoly M p
  rw [Matrix.aeval_eq_aeval_mod_charpoly, hc, aeval_lowPoly_mulVec] at hp
  have h0 : c = 0 := by
    have := congrArg (fun w => (krylov M v)⁻¹ *ᵥ w) hp
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h] using this
  rw [← modByMonic_eq_zero_iff_dvd M.charpoly_monic, hc, h0]
  simp [lowPoly]
end GlobalTheory.RegSS.CycAlg
