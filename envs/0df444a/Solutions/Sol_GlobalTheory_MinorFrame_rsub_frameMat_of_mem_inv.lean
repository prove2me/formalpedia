-- Prove2me | solution 1 for GlobalTheory.MinorFrame.rsub_frameMat_of_mem_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:20:35.429117+00:00
-- url     : https://prove2.me/submissions/f0fc6684-ed12-474b-b586-3f131a2002a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupFamilyZariskiDenseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FockPairingLinearSubstitutionAdjointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CauchyBinetColumnFrameProdDetPowEqSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FockDetCharInvariantsLeSpanProdMaximalMinors
import Theorems.Thm_GlobalTheory_MinorFrame_eval_rsub_frameMat
import Theorems.Thm_GlobalTheory_MinorFrame_eval_detG
import Theorems.Thm_GlobalTheory_T_unitaryGroup_family_zariski_dense


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.MinorFrame
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.MinorFrame
theorem _root_.solution {a d : ℕ} {n : ι → ℕ} (x₀ : Var ι d a → ℂ) {P : Pol ι d a}
    (hP : P ∈ inv a d n) : rsub (frameMat x₀) P = eval x₀ P • detG a n := by
  rw [← sub_eq_zero]
  apply GlobalTheory.T.unitaryGroup_family_zariski_dense
  intro g
  rw [map_sub, eval_rsub_frameMat x₀ (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P, hP g, smul_eval, smul_eval,
    eval_detG a n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ))]
  ring
end GlobalTheory.MinorFrame
