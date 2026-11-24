-- Prove2me | solution 1 for GlobalTheory.EtaChar.eta_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:09:45.841342+00:00
-- url     : https://prove2.me/submissions/d91428df-0551-4ffb-9027-bfac744b5e16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNorm
import Theorems.Thm_GlobalTheory_EtaChar_exists_unif
import Theorems.Thm_GlobalTheory_EtaChar_eta_of_exp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.EtaChar
namespace GlobalTheory.EtaChar
theorem _root_.solution (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F] (x y : F)
    (hx : x ≠ 0) (hy : y ≠ 0) : eta (x * y) = eta x * eta y := by
  obtain ⟨π, h0, h1, hall⟩ := exists_unif F
  obtain ⟨k, hk⟩ := hall x hx
  obtain ⟨l, hl⟩ := hall y hy
  have hkl : ‖x * y‖ = ‖π‖ ^ (k + l) := by rw [norm_mul, hk, hl, zpow_add₀ h0.ne']
  rw [eta_of_exp h0 h1 hall hk, eta_of_exp h0 h1 hall hl, eta_of_exp h0 h1 hall hkl]
  by_cases ek : Even k <;> by_cases el : Even l <;> simp [ek, el, Int.even_add]
end GlobalTheory.EtaChar
