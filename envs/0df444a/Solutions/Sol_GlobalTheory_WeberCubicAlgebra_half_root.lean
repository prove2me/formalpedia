-- Prove2me | solution 1 for GlobalTheory.WeberCubicAlgebra.half_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:36:13.161668+00:00
-- url     : https://prove2.me/submissions/aa1f2f54-5815-44a9-84b1-beca141f0fa6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeberFunctionsRootsOfCubicOfHalfPeriodDiff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open Polynomial
open UpperHalfPlane hiding I
noncomputable section
open GlobalTheory GlobalTheory.WeberCubicAlgebra
namespace GlobalTheory.WeberCubicAlgebra
theorem _root_.solution (L : PeriodPair) {t : ℂ} (h2 : 2 * t ∈ L.lattice) (ht : t ∉ L.lattice) :
    4 * L.weierstrassP t ^ 3 - L.g₂ * L.weierstrassP t - L.g₃ = 0 := by
  have e1 := L.derivWeierstrassP_add_coe (-t) ⟨2 * t, h2⟩
  rw [L.derivWeierstrassP_neg] at e1
  have e2 : -t + 2 * t = t := by ring
  simp only [e2] at e1
  have e3 : L.derivWeierstrassP t = 0 := by linear_combination e1 / 2
  rw [← L.derivWeierstrassP_sq t ht, e3]
  simp
end GlobalTheory.WeberCubicAlgebra
