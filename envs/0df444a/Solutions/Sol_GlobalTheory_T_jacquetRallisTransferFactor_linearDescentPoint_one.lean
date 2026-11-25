-- Prove2me | solution 1 for GlobalTheory.T.jacquetRallisTransferFactor_linearDescentPoint_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:24:48.213166+00:00
-- url     : https://prove2.me/submissions/d2515241-9636-44d5-941d-2083f55efc19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorLinearDescentPointOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorLinearDescentPointOneStatement
import Theorems.Thm_GlobalTheory_JR_LinDesc_omega_pt_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∃ κ₀ : ℂ, ∀ a : A.K, IsUnit a → ∀ g : GL (Fin r) F, omega (act g (LinDesc.pt A hG lam 1 a)) = κ₀ * eta ((g : Matrix (Fin r) (Fin r) F).det) * A.etaK a := by
  first | exact @GlobalTheory.JR.LinDesc.omega_pt_one | exact GlobalTheory.JR.LinDesc.omega_pt_one | (intros; apply GlobalTheory.JR.LinDesc.omega_pt_one <;> assumption)
end _root_.GlobalTheory.T
