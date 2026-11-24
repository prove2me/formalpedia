-- Prove2me | solution 1 for GlobalTheory.HermUnimod.unimodular_hermitian_eq_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:53:06.090908+00:00
-- url     : https://prove2.me/submissions/68d5d398-ce83-4811-943f-ce7ea466915f

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormOneAddEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHermitianMatrixCongruentOne
import Theorems.Thm_GlobalTheory_HermUnimod_good_all
import Theorems.Thm_GlobalTheory_HermUnimod_pivot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.HermUnimod
namespace GlobalTheory.HermUnimod
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (s : ℕ) (G : Matrix (Fin s) (Fin s) E), G.IsHermitian →
    (∀ i j, ‖G i j‖ ≤ 1) → ‖G.det‖ = 1 →
    ∃ h : Matrix (Fin s) (Fin s) E, (∀ i j, ‖h i j‖ ≤ 1) ∧ ‖h.det‖ = 1 ∧ hᴴ * G * h = 1 := by
  intro F E _ _ _ _ _ s G hG hGi hGd
  haveI := Unram.ultraE (F := F) (E := E)
  exact good_all (Unram.norm_star (F := F)) (fun n _ _ _ G hG hGi hGd => pivot (F := F) (E := E) G hG hGi hGd) s (Fin s)
    (Fintype.card_fin s) G hG hGi hGd
end GlobalTheory.HermUnimod
